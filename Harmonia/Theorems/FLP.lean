import Harmonia.Core.Execution

/-! A deterministic, asynchronous message-passing model. Buffer multiplicities
are integer-valued for a simple commutative representation; enabled delivery
requires a positive multiplicity, and protocol sends add natural counts. -/
namespace Harmonia.FLP

universe u v w

inductive Decision where
  | zero | one
  deriving DecidableEq, Repr

def Decision.flip : Decision → Decision
  | .zero => .one
  | .one => .zero

structure Event (Node : Type u) (Msg : Type v) where
  target : Node
  msg : Option Msg
  deriving DecidableEq

structure Config (Node : Type u) (Msg : Type v) (Local : Type w) where
  state : Node → Local
  buffer : Node → Msg → Int
  decision : Node → Option Decision

theorem Config.ext {c d : Config Node Msg Local}
    (hs : ∀ n, c.state n = d.state n)
    (hb : ∀ n m, c.buffer n m = d.buffer n m)
    (hd : ∀ n, c.decision n = d.decision n) : c = d := by
  cases c with
  | mk s b v =>
    cases d with
    | mk s' b' v' =>
      have h₁ : s = s' := funext hs
      have h₂ : b = b' := funext (fun n => funext (hb n))
      have h₃ : v = v' := funext hd
      cases h₁; cases h₂; cases h₃; rfl

/-- One process reads only its own local state and its delivered message. -/
structure Protocol (Node : Type u) (Msg : Type v) (Local : Type w) where
  update : Node → Local → Option Msg → Local
  decide : Node → Local → Option Msg → Option Decision
  send : Node → Local → Option Msg → Node → Msg → Nat

variable {Node : Type u} {Msg : Type v} {Local : Type w}
variable [DecidableEq Node] [DecidableEq Msg]

def Enabled (c : Config Node Msg Local) (e : Event Node Msg) : Prop :=
  match e.msg with
  | none => True
  | some m => 0 < c.buffer e.target m

instance (c : Config Node Msg Local) (e : Event Node Msg) : Decidable (Enabled c e) := by
  unfold Enabled
  cases e.msg <;> infer_instance

/-- Apply an event. The enablement guard is kept separate so algebraic laws
can be proved without partial `Option` expressions. -/
def advance (p : Protocol Node Msg Local) (c : Config Node Msg Local)
    (e : Event Node Msg) : Config Node Msg Local where
  state n := if n = e.target then p.update e.target (c.state e.target) e.msg else c.state n
  decision n := match c.decision n with
    | some v => some v
    | none => if n = e.target then p.decide e.target (c.state e.target) e.msg else none
  buffer n m := c.buffer n m + Int.ofNat (p.send e.target (c.state e.target) e.msg n m) -
    (if e.msg = some m ∧ e.target = n then 1 else 0)

def step (p : Protocol Node Msg Local) (c : Config Node Msg Local)
    (e : Event Node Msg) : Option (Config Node Msg Local) :=
  if Enabled c e then some (advance p c e) else none

def NonnegativeBuffer (c : Config Node Msg Local) : Prop :=
  ∀ n m, 0 ≤ c.buffer n m

theorem nonnegative_buffer_advance (p : Protocol Node Msg Local)
    (c : Config Node Msg Local) (e : Event Node Msg)
    (hc : NonnegativeBuffer c) (he : Enabled c e) :
    NonnegativeBuffer (advance p c e) := by
  intro n m
  change 0 ≤ c.buffer n m +
    Int.ofNat (p.send e.target (c.state e.target) e.msg n m) -
      (if e.msg = some m ∧ e.target = n then 1 else 0)
  have hsend : 0 ≤ Int.ofNat (p.send e.target (c.state e.target) e.msg n m) :=
    Int.natCast_nonneg _
  by_cases hconsumed : e.msg = some m ∧ e.target = n
  · obtain ⟨hmsg, htarget⟩ := hconsumed
    have hpositive : 0 < c.buffer n m := by
      simpa [Enabled, hmsg, htarget] using he
    simp [hmsg, htarget]
    omega
  · simp [hconsumed]
    have hbase := hc n m
    omega

theorem enabled_after_other (p : Protocol Node Msg Local) (c : Config Node Msg Local)
    (e f : Event Node Msg) (hdisjoint : e.target ≠ f.target)
    (hf : Enabled c f) : Enabled (advance p c e) f := by
  cases hmsg : f.msg with
  | none => simp [Enabled, hmsg]
  | some m =>
    simp only [Enabled, hmsg] at hf ⊢
    change 0 < c.buffer f.target m +
      Int.ofNat (p.send e.target (c.state e.target) e.msg f.target m) -
      (if e.msg = some m ∧ e.target = f.target then 1 else 0)
    have h : ¬ (e.msg = some m ∧ e.target = f.target) := by
      intro h; exact hdisjoint h.2
    simp [h]
    have hn : 0 ≤ Int.ofNat (p.send e.target (c.state e.target) e.msg f.target m) :=
      Int.natCast_nonneg _
    omega

/-- Independent process events commute exactly, including concurrent sends
to the same mailbox, because buffers use commutative multiplicities. -/
theorem flp_lemma1_diamond (p : Protocol Node Msg Local)
    (c : Config Node Msg Local) (e f : Event Node Msg)
    (hdisjoint : e.target ≠ f.target) :
    advance p (advance p c e) f = advance p (advance p c f) e := by
  have hfe : f.target ≠ e.target := Ne.symm hdisjoint
  apply Config.ext
  · intro n
    by_cases hn : n = e.target <;> by_cases hm : n = f.target
    · exact False.elim (hdisjoint (hn.symm.trans hm))
    all_goals simp [advance, hn, hm, hdisjoint, hfe]
  · intro n m
    have he : ¬ (e.target = f.target) := hdisjoint
    have hf : ¬ (f.target = e.target) := hfe
    simp only [advance]
    simp only [ite_eq_right he, ite_eq_right hf]
    omega
  · intro n
    by_cases hn : n = e.target <;> by_cases hm : n = f.target
    · exact False.elim (hdisjoint (hn.symm.trans hm))
    all_goals simp [advance, hn, hm, hdisjoint, hfe]
    all_goals cases h : c.decision e.target <;>
      cases h' : c.decision f.target <;> simp_all
    all_goals cases hd : p.decide e.target (c.state e.target) e.msg <;>
      cases hf : p.decide f.target (c.state f.target) f.msg <;> simp_all

theorem flp_lemma1_step_diamond (p : Protocol Node Msg Local)
    (c : Config Node Msg Local) (e f : Event Node Msg)
    (hdisjoint : e.target ≠ f.target)
    (he : Enabled c e) (hf : Enabled c f) :
    step p (advance p c e) f = step p (advance p c f) e := by
  simp [step, enabled_after_other p c e f hdisjoint hf,
    enabled_after_other p c f e (Ne.symm hdisjoint) he,
    flp_lemma1_diamond p c e f hdisjoint]

inductive Schedule (p : Protocol Node Msg Local) :
    Config Node Msg Local → List (Event Node Msg) → Config Node Msg Local → Prop where
  | nil (c) : Schedule p c [] c
  | cons {c d} (e : Event Node Msg) (he : Enabled c e)
      {es : List (Event Node Msg)} (tail : Schedule p (advance p c e) es d) :
      Schedule p c (e :: es) d

theorem Schedule.append (p : Protocol Node Msg Local)
    {a b c : Config Node Msg Local}
    {xs ys : List (Event Node Msg)}
    (hab : Schedule p a xs b) (hbc : Schedule p b ys c) :
    Schedule p a (xs ++ ys) c := by
  induction hab with
  | nil => exact hbc
  | cons e he _ ih => exact .cons e he (ih hbc)

/-- Paper Lemma 1 for a finite schedule that omits the target of `f`.
The schedule can run before or after `f`, with the same final configuration. -/
theorem flp_lemma1_schedule (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} {es : List (Event Node Msg)}
    (h : Schedule p c es d) (f : Event Node Msg) (hf : Enabled c f)
    (hdisjoint : ∀ e ∈ es, e.target ≠ f.target) :
    Schedule p (advance p c f) es (advance p d f) ∧ Enabled d f := by
  induction h with
  | nil => exact ⟨.nil _, hf⟩
  | @cons c d e he es tail ih =>
    have hne : e.target ≠ f.target := hdisjoint e (List.mem_cons_self ..)
    have htail : ∀ x ∈ es, x.target ≠ f.target := by
      intro x hx
      exact hdisjoint x (List.mem_cons_of_mem e hx)
    obtain ⟨hafter, hend⟩ := ih (enabled_after_other p c e f hne hf) htail
    have he' : Enabled (advance p c f) e :=
      enabled_after_other p c f e (Ne.symm hne) he
    constructor
    · apply Schedule.cons e he'
      simpa only [flp_lemma1_diamond p c e f hne] using hafter
    · exact hend

/-- Paper Lemma 1 for two finite schedules whose events target disjoint
sets of processes. Both execution orders reach the same configuration. -/
theorem flp_lemma1_schedules (p : Protocol Node Msg Local)
    {c a b : Config Node Msg Local} {es fs : List (Event Node Msg)}
    (ha : Schedule p c es a) (hb : Schedule p c fs b)
    (hdisjoint : ∀ e ∈ es, ∀ f ∈ fs, e.target ≠ f.target) :
    ∃ z, Schedule p a fs z ∧ Schedule p b es z := by
  induction hb generalizing a es with
  | nil => exact ⟨a, .nil _, ha⟩
  | @cons c d f hf fs tail ih =>
    have hcrossF : ∀ e ∈ es, e.target ≠ f.target := by
      intro e he
      exact hdisjoint e he f (List.mem_cons_self ..)
    obtain ⟨ha', hf'⟩ := flp_lemma1_schedule p ha f hf hcrossF
    have hcrossTail : ∀ e ∈ es, ∀ g ∈ fs, e.target ≠ g.target := by
      intro e he g hg
      exact hdisjoint e he g (List.mem_cons_of_mem f hg)
    obtain ⟨z, hfs, hes⟩ := ih ha' hcrossTail
    exact ⟨z, .cons f hf' hfs, hes⟩

/-- A finite schedule keeps explicit evidence that each event was enabled. -/
inductive Reachable (p : Protocol Node Msg Local) :
    Config Node Msg Local → Config Node Msg Local → Prop where
  | refl (c) : Reachable p c c
  | tail {c d} (h : Reachable p c d) (e : Event Node Msg)
      (he : Enabled d e) : Reachable p c (advance p d e)

namespace Reachable
variable {p : Protocol Node Msg Local} {a b c : Config Node Msg Local}

theorem trans (hab : Reachable p a b) (hbc : Reachable p b c) :
    Reachable p a c := by
  induction hbc with
  | refl => exact hab
  | tail _ e he ih => exact .tail ih e he

end Reachable

theorem Schedule.reachable (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} {events : List (Event Node Msg)}
    (h : Schedule p c events d) : Reachable p c d := by
  induction h with
  | nil => exact .refl _
  | cons e he _ ih => exact (Reachable.tail (.refl _) e he).trans ih

theorem Reachable.schedule (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} (h : Reachable p c d) :
    ∃ events, Schedule p c events d := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | tail _ e he ih =>
    obtain ⟨events, hr⟩ := ih
    exact ⟨events ++ [e], hr.append p (.cons e he (.nil _))⟩

theorem nonnegative_buffer_reachable (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} (h : Reachable p c d)
    (hc : NonnegativeBuffer c) : NonnegativeBuffer d := by
  induction h with
  | refl => exact hc
  | tail _ e he ih => exact nonnegative_buffer_advance p _ e ih he

def DecidedIn (c : Config Node Msg Local) (v : Decision) : Prop :=
  ∃ n, c.decision n = some v

def ReachableDecision (p : Protocol Node Msg Local)
    (c : Config Node Msg Local) (v : Decision) : Prop :=
  ∃ d, Reachable p c d ∧ DecidedIn d v

def IsBivalent (p : Protocol Node Msg Local) (c : Config Node Msg Local) : Prop :=
  ReachableDecision p c .zero ∧ ReachableDecision p c .one

def IsUnivalent (p : Protocol Node Msg Local)
    (c : Config Node Msg Local) (v : Decision) : Prop :=
  ReachableDecision p c v ∧ ¬ ReachableDecision p c v.flip

theorem reachableDecision_of_reachable (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} (hcd : Reachable p c d)
    {v : Decision} (hd : ReachableDecision p d v) :
    ReachableDecision p c v := by
  obtain ⟨z, hdz, hv⟩ := hd
  exact ⟨z, hcd.trans hdz, hv⟩

theorem bivalent_of_reachable (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} (hcd : Reachable p c d)
    (hd : IsBivalent p d) : IsBivalent p c :=
  ⟨reachableDecision_of_reachable p hcd hd.1,
   reachableDecision_of_reachable p hcd hd.2⟩

theorem univalent_excludes_opposite_after (p : Protocol Node Msg Local)
    {c d : Config Node Msg Local} {v : Decision}
    (hc : IsUnivalent p c v) (hcd : Reachable p c d) :
    ¬ ReachableDecision p d v.flip := by
  intro hd
  exact hc.2 (reachableDecision_of_reachable p hcd hd)

/-- Safety expressed over every finite execution from an initial state. -/
def Agreement (p : Protocol Node Msg Local) (initial : Config Node Msg Local) : Prop :=
  ∀ c, Reachable p initial c → ¬ (DecidedIn c .zero ∧ DecidedIn c .one)

/-- A decision cannot be retracted by any process step. -/
def DecisionsPersist (p : Protocol Node Msg Local) : Prop :=
  ∀ c e v, Enabled c e → DecidedIn c v → DecidedIn (advance p c e) v

theorem decisions_persist_step (p : Protocol Node Msg Local) : DecisionsPersist p := by
  intro c e v _ hv
  obtain ⟨n, hn⟩ := hv
  exact ⟨n, by simp [advance, hn]⟩

theorem decided_persists_along (p : Protocol Node Msg Local)
    (hp : DecisionsPersist p) {c d : Config Node Msg Local}
    (hcd : Reachable p c d) {v : Decision} (hv : DecidedIn c v) :
    DecidedIn d v := by
  induction hcd with
  | refl => exact hv
  | tail _ e he ih => exact hp _ e _ he ih

theorem decided_univalent (p : Protocol Node Msg Local)
    (initial c : Config Node Msg Local) (hag : Agreement p initial)
    (hp : DecisionsPersist p) (hc : Reachable p initial c)
    {v : Decision} (hv : DecidedIn c v) : IsUnivalent p c v := by
  constructor
  · exact ⟨c, .refl c, hv⟩
  · rintro ⟨d, hcd, hopposite⟩
    have hpersistent := decided_persists_along p hp hcd hv
    cases v with
    | zero => exact hag d (hc.trans hcd) ⟨hpersistent, hopposite⟩
    | one => exact hag d (hc.trans hcd) ⟨hopposite, hpersistent⟩

/-- A reachable bivalent configuration cannot already contain a decision. -/
theorem bivalent_undecided (p : Protocol Node Msg Local)
    (initial c : Config Node Msg Local) (hag : Agreement p initial)
    (hp : DecisionsPersist p) (hc : Reachable p initial c)
    (hb : IsBivalent p c) :
    ¬ DecidedIn c .zero ∧ ¬ DecidedIn c .one := by
  constructor
  · intro hzero
    obtain ⟨d, hcd, hone⟩ := hb.2
    exact hag d (hc.trans hcd) ⟨decided_persists_along p hp hcd hzero, hone⟩
  · intro hone
    obtain ⟨d, hcd, hzero⟩ := hb.1
    exact hag d (hc.trans hcd) ⟨hzero, decided_persists_along p hp hcd hone⟩

/-- An infinite asynchronous execution records every chosen event. -/
structure InfiniteRun (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local) where
  state : Nat → Config Node Msg Local
  event : Nat → Event Node Msg
  starts : state 0 = initial
  enabled : ∀ t, Enabled (state t) (event t)
  evolves : ∀ t, state (t + 1) = advance p (state t) (event t)

/-- Count deliveries of one destination/payload pair in an inclusive interval. -/
def deliveryCount (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (r : InfiniteRun p initial) (first last : Nat)
    (n : Node) (m : Msg) : Nat :=
  ((List.range (last + 1 - first)).filter
    (fun offset => r.event (first + offset) = ⟨n, some m⟩)).length

/-- A process is nonfaulty exactly when it takes arbitrarily late steps. -/
def NonFaulty {p : Protocol Node Msg Local} {initial : Config Node Msg Local}
    (r : InfiniteRun p initial) (n : Node) : Prop :=
  ∀ t, ∃ k, t ≤ k ∧ (r.event k).target = n

/-- Every process except possibly one takes arbitrarily late steps. For each
positive buffer count present at a time, enough later matching deliveries
occur to account for every pending copy, even if further copies are sent. -/
def Admissible (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (r : InfiniteRun p initial) : Prop :=
  (∃ faulty : Option Node, ∀ n, some n ≠ faulty → NonFaulty r n) ∧
    (∀ n m, NonFaulty r n → ∀ t, 0 < (r.state t).buffer n m →
      ∃ k, t ≤ k ∧ Int.toNat ((r.state t).buffer n m) ≤
        deliveryCount p initial r t k n m)

def GuaranteedTermination (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local) : Prop :=
  ∀ r : InfiniteRun p initial, Admissible p initial r →
    ∃ t v, DecidedIn (r.state t) v

theorem run_reachable (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (r : InfiniteRun p initial)
    (t : Nat) : Reachable p initial (r.state t) := by
  induction t with
  | zero => rw [r.starts]; exact .refl initial
  | succ t ih =>
    rw [r.evolves t]
    exact .tail ih (r.event t) (r.enabled t)

theorem run_nonnegative_buffer (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (r : InfiniteRun p initial)
    (hinitial : NonnegativeBuffer initial) (t : Nat) :
    NonnegativeBuffer (r.state t) :=
  nonnegative_buffer_reachable p (run_reachable p initial r t) hinitial

/-- The final contradiction once a fair bivalence-preserving adversary has
been constructed. The construction of such an adversary is the hard FLP
extension-and-scheduling obligation, not part of this theorem's hypotheses. -/
theorem no_termination_of_fair_bivalent_run (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local)
    (agreement : Agreement p initial) (persist : DecisionsPersist p)
    (r : InfiniteRun p initial) (fair : Admissible p initial r)
    (bivalent : ∀ t, IsBivalent p (r.state t)) :
    ¬ GuaranteedTermination p initial := by
  intro terminates
  obtain ⟨t, v, decided⟩ := terminates r fair
  have h := bivalent_undecided p initial (r.state t) agreement persist
    (run_reachable p initial r t) (bivalent t)
  cases v with
  | zero => exact h.1 decided
  | one => exact h.2 decided

end Harmonia.FLP
