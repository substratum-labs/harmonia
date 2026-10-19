import Harmonia.Theorems.FLP

/-! The finite initial-bivalence argument of FLP. The assumptions below are
semantic obligations for a concrete deterministic message-passing protocol:
steps by processes other than `p` replay across states indistinguishable to
everyone except `p`, and their decisions replay as well. No global fairness
assumption is used here; `crashDeciding` is the finite consequence of
termination for a run in which `p` never takes a step. -/

namespace Harmonia.FLP.Initial

universe u v w

abbrev Decision := Harmonia.FLP.Decision

/-- A local step and the observation relation for a process that stays silent. -/
structure System (Config : Type u) (Event : Type v) (Node : Type w) where
  initial : Config → Prop
  step : Config → Event → Config → Prop
  target : Event → Node
  decidedBy : Config → Node → Decision → Prop
  indistinguishableExcept : Node → Config → Config → Prop
  replayOther : ∀ {p c d e c'},
    indistinguishableExcept p c d → target e ≠ p → step c e c' →
    ∃ d', step d e d' ∧ indistinguishableExcept p c' d'
  decisionOther : ∀ {p q c d value},
    indistinguishableExcept p c d → q ≠ p → decidedBy c q value →
    decidedBy d q value

variable {Config : Type u} {Event : Type v} {Node : Type w}
variable (sys : System Config Event Node)

/-- A finite execution, without an assumption that every event is enabled. -/
inductive Run : Config → List Event → Config → Prop where
  | nil : Run c [] c
  | cons : sys.step c e d → Run d es t → Run c (e :: es) t

def ReachDecision (c : Config) (value : Decision) : Prop :=
  ∃ es t q, Run sys c es t ∧ sys.decidedBy t q value

def Bivalent (c : Config) : Prop :=
  ReachDecision sys c .zero ∧ ReachDecision sys c .one

/-- One edge of the binary-input initial-configuration cube. The concrete
protocol must show that states differing in just `p`'s input satisfy this
relation. The orientation records the direction in which replay is used. -/
def Adjacent (c d : Config) : Prop :=
  ∃ p, sys.indistinguishableExcept p c d

/-- A finite chain of initial configurations. In a concrete finite-node
instance, flipping input bits one at a time supplies such a chain. -/
inductive InitialChain : Config → Config → Prop where
  | singleton : sys.initial c → InitialChain c c
  | cons : sys.initial c → Adjacent sys c d → InitialChain d z → InitialChain c z

theorem InitialChain.last_initial {c d : Config}
    (h : InitialChain sys c d) : sys.initial d := by
  induction h with
  | singleton hi => exact hi
  | cons _ _ _ ih => exact ih

theorem replay_run {p c d es t} (hrel : sys.indistinguishableExcept p c d)
    (hrun : Run sys c es t) (hother : ∀ e ∈ es, sys.target e ≠ p) :
    ∃ t', Run sys d es t' ∧ sys.indistinguishableExcept p t t' := by
  induction hrun generalizing d with
  | nil => exact ⟨d, .nil, hrel⟩
  | @cons c e mid es t hstep htail ih =>
    have he : sys.target e ≠ p := hother e (by simp)
    obtain ⟨d', hdstep, hdrel⟩ := sys.replayOther hrel he hstep
    have htailOther : ∀ event ∈ es, sys.target event ≠ p := by
      intro event he'
      exact hother event (by simp [he'])
    obtain ⟨t', hrun', hrel'⟩ := ih hdrel htailOther
    exact ⟨t', .cons hdstep hrun', hrel'⟩

theorem Run.append_one {c d : Config} {es : List Event}
    (hrun : Run sys c es d) {e : Event} {t : Config}
    (hstep : sys.step d e t) : Run sys c (es ++ [e]) t := by
  induction hrun with
  | nil => exact .cons hstep .nil
  | cons hs _ ih => exact .cons hs (ih hstep)

/-- The decision is made by a process that continues while `p` is silent. -/
def CrashDeciding : Prop :=
  ∀ c p, sys.initial c →
    ∃ es t q value, Run sys c es t ∧
      (∀ e ∈ es, sys.target e ≠ p) ∧ q ≠ p ∧ sys.decidedBy t q value

theorem adjacent_shares_valence (hcrash : CrashDeciding sys)
    {c d : Config} (hi : sys.initial c) (hadj : Adjacent sys c d)
    (hnot : ¬ Bivalent sys c) (hv : ReachDecision sys c value) :
    ReachDecision sys d value := by
  obtain ⟨p, hrel⟩ := hadj
  obtain ⟨es, t, q, crashValue, hrun, hother, hq, hdec⟩ := hcrash c p hi
  have hc : ReachDecision sys c crashValue := ⟨es, t, q, hrun, hdec⟩
  have heq : crashValue = value := by
    cases crashValue <;> cases value
    · rfl
    · exact False.elim (hnot ⟨hc, hv⟩)
    · exact False.elim (hnot ⟨hv, hc⟩)
    · rfl
  obtain ⟨t', hrun', hrel'⟩ := replay_run sys hrel hrun hother
  exact ⟨es, t', q, hrun', heq ▸ sys.decisionOther hrel' hq hdec⟩

theorem adjacent_progress (hcrash : CrashDeciding sys)
    {c d : Config} (hi : sys.initial c) (hadj : Adjacent sys c d)
    (hv : ReachDecision sys c .zero) :
    Bivalent sys c ∨ ReachDecision sys d .zero := by
  obtain ⟨p, hrel⟩ := hadj
  obtain ⟨es, t, q, crashValue, hrun, hother, hq, hdec⟩ := hcrash c p hi
  cases crashValue with
  | one =>
    exact .inl ⟨hv, ⟨es, t, q, hrun, hdec⟩⟩
  | zero =>
    obtain ⟨t', hrun', hrel'⟩ := replay_run sys hrel hrun hother
    exact .inr ⟨es, t', q, hrun', sys.decisionOther hrel' hq hdec⟩

theorem chain_progress (hcrash : CrashDeciding sys)
    {c d : Config} (hchain : InitialChain sys c d)
    (hv : ReachDecision sys c .zero) :
    (∃ x, sys.initial x ∧ Bivalent sys x) ∨ ReachDecision sys d .zero := by
  induction hchain with
  | singleton _ => exact .inr hv
  | cons hi hadj _ ih =>
    cases adjacent_progress sys hcrash hi hadj hv with
    | inl hb => exact .inl ⟨_, hi, hb⟩
    | inr hd => exact ih hd

/-- FLP Lemma 2: nontrivial binary decision outcomes at ends of a finite
input chain and one-crash termination force some initial configuration to be
bivalent. The conclusion includes its initial-state certificate. -/
theorem initial_bivalent_of_chain (hcrash : CrashDeciding sys)
    {first last : Config} (hchain : InitialChain sys first last)
    (hzero : ReachDecision sys first .zero)
    (hone : ReachDecision sys last .one) :
    ∃ c, sys.initial c ∧ Bivalent sys c := by
  cases chain_progress sys hcrash hchain hzero with
  | inl witness => exact witness
  | inr hz => exact ⟨last, InitialChain.last_initial sys hchain, hz, hone⟩

end Harmonia.FLP.Initial

namespace Harmonia.FLP

universe u v w

variable {Node : Type u} {Msg : Type v} {Local : Type w}
variable [DecidableEq Node] [DecidableEq Msg]

/-- The FLP transition system as an instance of the finite-chain argument.
`replay` is the concrete crash-indistinguishability obligation: any step by
another process remains enabled and preserves the relation. `decision` says
an unchanged process has the same decision in related configurations. -/
def initialSystem (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local → Prop)
    (indist : Node → Config Node Msg Local → Config Node Msg Local → Prop)
    (replay : ∀ {silent c d e}, indist silent c d → e.target ≠ silent →
      Enabled c e → Enabled d e ∧
        indist silent (advance protocol c e) (advance protocol d e))
    (decision : ∀ {silent q c d value}, indist silent c d → q ≠ silent →
      c.decision q = some value → d.decision q = some value) :
    Initial.System (Config Node Msg Local) (Event Node Msg) Node where
  initial := initial
  step c e d := Enabled c e ∧ d = advance protocol c e
  target e := e.target
  decidedBy c q value := c.decision q = some value
  indistinguishableExcept := indist
  replayOther := by
    intro silent c d e c' hrel htarget hstep
    rcases hstep with ⟨he, rfl⟩
    obtain ⟨hd, hrel'⟩ := replay hrel htarget he
    exact ⟨advance protocol d e, ⟨hd, rfl⟩, hrel'⟩
  decisionOther := by
    intro silent q c d value hrel hq hv
    exact decision hrel hq hv

private theorem initial_run_to_reachable (protocol : Protocol Node Msg Local)
    (sys : Initial.System (Config Node Msg Local) (Event Node Msg) Node)
    (hstep : ∀ {c e d}, sys.step c e d → Enabled c e ∧ d = advance protocol c e)
    {c d : Config Node Msg Local} {es : List (Event Node Msg)}
    (hrun : Initial.Run sys c es d) : Reachable protocol c d := by
  induction hrun with
  | nil => exact .refl _
  | cons hs _ ih =>
    obtain ⟨he, rfl⟩ := hstep hs
    exact (Reachable.tail (.refl _) _ he).trans ih

private theorem reachable_to_initial_run (protocol : Protocol Node Msg Local)
    (sys : Initial.System (Config Node Msg Local) (Event Node Msg) Node)
    (hstep : ∀ {c e}, sys.step c e (advance protocol c e) ↔ Enabled c e)
    {c d : Config Node Msg Local} (hr : Reachable protocol c d) :
    ∃ es, Initial.Run sys c es d := by
  induction hr with
  | refl => exact ⟨[], .nil⟩
  | tail _ e he ih =>
    obtain ⟨es, hrun⟩ := ih
    exact ⟨es ++ [e], Initial.Run.append_one sys hrun (hstep.mpr he)⟩

/-- Initial bivalence for the concrete FLP configuration and transition
semantics. `hchain` is a finite chain of binary-input initial states, while
`hcrash` is the finite decision trace promised when each chosen process may
remain silent. No valence conclusion is part of either premise. -/
theorem flp_lemma2_initial_bivalent (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local → Prop)
    (indist : Node → Config Node Msg Local → Config Node Msg Local → Prop)
    (replay : ∀ {silent c d e}, indist silent c d → e.target ≠ silent →
      Enabled c e → Enabled d e ∧
        indist silent (advance protocol c e) (advance protocol d e))
    (decision : ∀ {silent q c d value}, indist silent c d → q ≠ silent →
      c.decision q = some value → d.decision q = some value)
    (hcrash : Initial.CrashDeciding
      (initialSystem protocol initial indist replay decision))
    {first last : Config Node Msg Local}
    (hchain : Initial.InitialChain
      (initialSystem protocol initial indist replay decision) first last)
    (hzero : ReachableDecision protocol first .zero)
    (hone : ReachableDecision protocol last .one) :
    ∃ c, initial c ∧ IsBivalent protocol c := by
  let sys := initialSystem protocol initial indist replay decision
  have toRun : ∀ {c d}, Reachable protocol c d →
      ∃ es, Initial.Run sys c es d := by
    intro c d hr
    exact reachable_to_initial_run protocol sys (by
      intro c e
      simp [sys, initialSystem]) hr
  have toReach : ∀ {c d es}, Initial.Run sys c es d → Reachable protocol c d := by
    intro c d es hr
    exact initial_run_to_reachable protocol sys (by
      intro c e d hs
      exact hs) hr
  have toInitial : ∀ {c value}, ReachableDecision protocol c value →
      Initial.ReachDecision sys c value := by
    intro c value hv
    obtain ⟨d, hr, q, hd⟩ := hv
    obtain ⟨es, hrun⟩ := toRun hr
    exact ⟨es, d, q, hrun, hd⟩
  obtain ⟨c, hi, hz, ho⟩ :=
    Initial.initial_bivalent_of_chain sys hcrash hchain (toInitial hzero) (toInitial hone)
  refine ⟨c, hi, ?_, ?_⟩
  · obtain ⟨es, d, q, hrun, hd⟩ := hz
    exact ⟨d, toReach hrun, ⟨q, hd⟩⟩
  · obtain ⟨es, d, q, hrun, hd⟩ := ho
    exact ⟨d, toReach hrun, ⟨q, hd⟩⟩

end Harmonia.FLP
