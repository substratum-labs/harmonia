import Harmonia.Theorems.Causal

namespace Harmonia.Causal.Vector

open Harmonia.Causal

abbrev VectorClock (N : Nat) := Fin N → Nat

def le {N : Nat} (a b : VectorClock N) : Prop := ∀ i, a i ≤ b i

def lt {N : Nat} (a b : VectorClock N) : Prop :=
  le a b ∧ ∃ i, a i < b i

def increment {N : Nat} (v : VectorClock N) (i : Fin N) : VectorClock N :=
  fun j => if j = i then v j + 1 else v j

def merge {N : Nat} (a b : VectorClock N) : VectorClock N :=
  fun j => max (a j) (b j)

theorem le_refl {N : Nat} (v : VectorClock N) : le v v := by
  intro i; exact Nat.le_refl _

theorem le_trans {N : Nat} {a b c : VectorClock N}
    (hab : le a b) (hbc : le b c) : le a c := by
  intro i; exact Nat.le_trans (hab i) (hbc i)

theorem le_antisymm {N : Nat} {a b : VectorClock N}
    (hab : le a b) (hba : le b a) : a = b := by
  funext i
  exact Nat.le_antisymm (hab i) (hba i)

theorem lt_irrefl {N : Nat} (v : VectorClock N) : ¬ lt v v := by
  intro h
  obtain ⟨i, hi⟩ := h.2
  exact (Nat.lt_irrefl _) hi

theorem lt_trans {N : Nat} {a b c : VectorClock N}
    (hab : lt a b) (hbc : lt b c) : lt a c := by
  constructor
  · exact le_trans hab.1 hbc.1
  · obtain ⟨i, hi⟩ := hab.2
    exact ⟨i, Nat.lt_of_lt_of_le hi (hbc.1 i)⟩

theorem le_increment {N : Nat} (v : VectorClock N) (i : Fin N) :
    le v (increment v i) := by
  intro j
  unfold increment
  split <;> omega

theorem increment_strict {N : Nat} (v : VectorClock N) (i : Fin N) :
    v i < increment v i i := by
  simp [increment]

theorem le_merge_left {N : Nat} (a b : VectorClock N) : le a (merge a b) := by
  intro i; exact Nat.le_max_left _ _

theorem le_merge_right {N : Nat} (a b : VectorClock N) : le b (merge a b) := by
  intro i; exact Nat.le_max_right _ _

/-- Operational vector rule plus explicit local-rank and component-frontier
invariants for a well-formed finite execution. -/
structure Clocking (t : Trace) (N : Nat) where
  nodeIndex : Event → Fin N
  node_index : ∀ e, e ∈ t.events → t.node e = (nodeIndex e).val
  clock : Event → VectorClock N
  before : Event → VectorClock N
  messageClock : MessageId → VectorClock N
  local_precedes : ∀ {e f}, ProgramOrder t e f → le (clock e) (before f)
  tick : ∀ e, clock e = increment
    (match t.kind e with
     | .receive m => merge (before e) (messageClock m)
     | _ => before e) (nodeIndex e)
  attach : ∀ {e m}, t.kind e = .send m → messageClock m = clock e
  rank : Event → Nat
  rank_self : ∀ e, e ∈ t.events → clock e (nodeIndex e) = rank e
  rank_positive : ∀ e, e ∈ t.events → 0 < rank e
  process_prefix : ∀ e f, e ∈ t.events → f ∈ t.events →
    nodeIndex e = nodeIndex f → rank e ≤ rank f →
    e = f ∨ HappensBefore t e f
  component_frontier : ∀ f i, f ∈ t.events → 0 < clock f i →
    ∃ p, p ∈ t.events ∧ nodeIndex p = i ∧ rank p = clock f i ∧
      (p = f ∨ HappensBefore t p f)

theorem Clocking.origin {t : Trace} {N : Nat} (v : Clocking t N)
    (e f : Event) (he : e ∈ t.events) (hf : f ∈ t.events)
    (h : v.clock e (v.nodeIndex e) ≤ v.clock f (v.nodeIndex e)) :
    e = f ∨ HappensBefore t e f := by
  have hp : 0 < v.clock f (v.nodeIndex e) := by
    rw [v.rank_self e he] at h
    exact Nat.lt_of_lt_of_le (v.rank_positive e he) h
  obtain ⟨p, hpm, hnode, hrank, hpf⟩ :=
    v.component_frontier f (v.nodeIndex e) hf hp
  have hr : v.rank e ≤ v.rank p := by
    rw [← v.rank_self e he, hrank]
    exact h
  rcases v.process_prefix e p he hpm hnode.symm hr with hep | hep
  · subst p
    exact hpf
  · rcases hpf with rfl | hpf
    · exact Or.inr hep
    · exact Or.inr (HappensBefore.trans hep hpf)


private theorem Clocking.before_input {t : Trace} {N : Nat} (v : Clocking t N)
    (e : Event) : le (v.before e)
      (match t.kind e with
       | .receive m => merge (v.before e) (v.messageClock m)
       | _ => v.before e) := by
  cases h : t.kind e with
  | internal => exact le_refl _
  | send m => exact le_refl _
  | receive m => exact le_merge_left _ _

private theorem Clocking.input_lt_clock {t : Trace} {N : Nat} (v : Clocking t N)
    (e : Event) (i : Fin N) :
    (match t.kind e with
     | .receive m => merge (v.before e) (v.messageClock m)
     | _ => v.before e) i ≤ v.clock e i := by
  rw [v.tick e]
  exact le_increment _ _ i

private theorem Clocking.input_strict {t : Trace} {N : Nat} (v : Clocking t N)
    (e : Event) :
    (match t.kind e with
     | .receive m => merge (v.before e) (v.messageClock m)
     | _ => v.before e) (v.nodeIndex e) < v.clock e (v.nodeIndex e) := by
  rw [v.tick e]
  exact increment_strict _ _

private theorem Clocking.before_lt_clock {t : Trace} {N : Nat} (v : Clocking t N)
    (e : Event) : lt (v.before e) (v.clock e) := by
  constructor
  · exact le_trans (v.before_input e) (fun i => v.input_lt_clock e i)
  · refine ⟨v.nodeIndex e, ?_⟩
    exact Nat.lt_of_le_of_lt (v.before_input e (v.nodeIndex e)) (v.input_strict e)

private theorem Clocking.message_le_input {t : Trace} {N : Nat} (v : Clocking t N)
    {e m : Nat} (h : t.kind e = .receive m) :
    le (v.messageClock m)
      (match t.kind e with
       | .receive k => merge (v.before e) (v.messageClock k)
       | _ => v.before e) := by
  simp only [h]
  exact le_merge_right _ _

theorem Clocking.local_sound {t : Trace} {N : Nat} (v : Clocking t N)
    {e f : Event} (h : ProgramOrder t e f) : lt (v.clock e) (v.clock f) := by
  have hp := v.local_precedes h
  have ht := v.before_lt_clock f
  constructor
  · exact le_trans hp ht.1
  · exact ⟨v.nodeIndex f, Nat.lt_of_le_of_lt (hp _) (by
      exact Nat.lt_of_le_of_lt (v.before_input f _) (v.input_strict f))⟩

theorem Clocking.message_sound {t : Trace} {N : Nat} (v : Clocking t N)
    {e f m : Nat} (hs : t.kind e = .send m) (hr : t.kind f = .receive m) :
    lt (v.clock e) (v.clock f) := by
  have hm : le (v.clock e)
      (match t.kind f with
       | .receive k => merge (v.before f) (v.messageClock k)
       | _ => v.before f) := by
    rw [← v.attach hs]
    exact v.message_le_input hr
  constructor
  · exact le_trans hm (fun i => v.input_lt_clock f i)
  · exact ⟨v.nodeIndex f, Nat.lt_of_le_of_lt (hm _) (v.input_strict f)⟩

theorem Clocking.sound {t : Trace} {N : Nat} (v : Clocking t N)
    {e f : Event} (h : HappensBefore t e f) : lt (v.clock e) (v.clock f) := by
  induction h with
  | local_step he => exact v.local_sound he
  | msg_step _ _ hs hr => exact v.message_sound hs hr
  | trans _ _ ih₁ ih₂ => exact lt_trans ih₁ ih₂

theorem Clocking.complete {t : Trace} {N : Nat} (v : Clocking t N)
    {e f : Event} (he : e ∈ t.events) (hf : f ∈ t.events)
    (h : lt (v.clock e) (v.clock f)) : HappensBefore t e f := by
  rcases v.origin e f he hf (h.1 (v.nodeIndex e)) with heq | hb
  · subst f
    exact False.elim ((lt_irrefl (v.clock e)) h)
  · exact hb

theorem Clocking.iff_happensBefore {t : Trace} {N : Nat} (v : Clocking t N)
    (e f : Event) (he : e ∈ t.events) (hf : f ∈ t.events) :
    HappensBefore t e f ↔ lt (v.clock e) (v.clock f) :=
  ⟨v.sound, v.complete he hf⟩

theorem Clocking.concurrent_iff_incomparable {t : Trace} {N : Nat}
    (v : Clocking t N) (e f : Event)
    (he : e ∈ t.events) (hf : f ∈ t.events) :
    Concurrent t e f ↔
      ¬ le (v.clock e) (v.clock f) ∧ ¬ le (v.clock f) (v.clock e) := by
  constructor
  · intro hc
    constructor
    · intro hle
      rcases v.origin e f he hf (hle (v.nodeIndex e)) with heq | hb
      · exact hc.2.2 heq
      · exact hc.1 hb
    · intro hle
      rcases v.origin f e hf he (hle (v.nodeIndex f)) with heq | hb
      · exact hc.2.2 heq.symm
      · exact hc.2.1 hb
  · intro hi
    refine ⟨?_, ?_, ?_⟩
    · intro hb; exact hi.1 (v.sound hb).1
    · intro hb; exact hi.2 (v.sound hb).1
    · intro heq; subst f; exact hi.1 (le_refl _)

end Harmonia.Causal.Vector

namespace Harmonia.Causal.Vector.Canonical

open Harmonia.Causal

/-- Maximum observed local rank in a finite causal past. -/
def foldMax {α : Type} (xs : List α) (g : α → Nat) : Nat :=
  xs.foldr (fun x n => max (g x) n) 0

theorem foldMax_mem {α : Type} (xs : List α) (g : α → Nat) {p : α}
    (hp : p ∈ xs) : g p ≤ foldMax xs g := by
  induction xs with
  | nil => cases hp
  | cons x xs ih =>
      simp only [List.mem_cons] at hp
      simp only [foldMax, List.foldr_cons]
      rcases hp with rfl | hp
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hp) (Nat.le_max_right _ _)

theorem foldMax_mono {α : Type} (xs : List α) (g h : α → Nat)
    (hm : ∀ p ∈ xs, g p ≤ h p) : foldMax xs g ≤ foldMax xs h := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      have hx := hm x (by simp)
      have hxs : ∀ p ∈ xs, g p ≤ h p := by
        intro p hp; exact hm p (by simp [hp])
      have ht := ih hxs
      change max (g x) (foldMax xs g) ≤ max (h x) (foldMax xs h)
      omega

theorem foldMax_lt {α : Type} (xs : List α) (g : α → Nat) (M : Nat)
    (hM : 0 < M) (hall : ∀ p ∈ xs, g p < M) : foldMax xs g < M := by
  induction xs with
  | nil => simpa [foldMax] using hM
  | cons x xs ih =>
      have hx := hall x (by simp)
      have hxs : ∀ p ∈ xs, g p < M := by
        intro p hp; exact hall p (by simp [hp])
      have ht := ih hxs
      change max (g x) (foldMax xs g) < M
      omega

theorem foldMax_le {α : Type} (xs : List α) (g : α → Nat) (M : Nat)
    (hall : ∀ p ∈ xs, g p ≤ M) : foldMax xs g ≤ M := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      have hx := hall x (by simp)
      have hxs : ∀ p ∈ xs, g p ≤ M := by
        intro p hp; exact hall p (by simp [hp])
      change max (g x) (foldMax xs g) ≤ M
      exact Nat.max_le_of_le_of_le hx (ih hxs)

theorem foldMax_attains {α : Type} (xs : List α) (g : α → Nat)
    (hpos : 0 < foldMax xs g) : ∃ p, p ∈ xs ∧ g p = foldMax xs g := by
  induction xs with
  | nil => simp [foldMax] at hpos
  | cons x xs ih =>
      change 0 < max (g x) (foldMax xs g) at hpos
      change ∃ p, p ∈ x :: xs ∧ g p = max (g x) (foldMax xs g)
      rcases Nat.le_total (g x) (foldMax xs g) with h | h
      · have hm : max (g x) (foldMax xs g) = foldMax xs g := Nat.max_eq_right h
        rw [hm] at hpos ⊢
        obtain ⟨p, hp, hval⟩ := ih hpos
        exact ⟨p, by simp [hp], hval⟩
      · have hm : max (g x) (foldMax xs g) = g x := Nat.max_eq_left h
        rw [hm]
        exact ⟨x, by simp, rfl⟩

/-- A finite causal history with computable reachability and increasing
per-process ranks. These are execution-shape obligations, not clock facts. -/
structure History (t : Trace) (N : Nat) where
  nodeIndex : Event → Fin N
  node_index : ∀ e, e ∈ t.events → t.node e = (nodeIndex e).val
  rank : Event → Nat
  rank_positive : ∀ e, e ∈ t.events → 0 < rank e
  rank_strict : ∀ e f, e ∈ t.events → f ∈ t.events →
    t.node e = t.node f → e < f → rank e < rank f
  rank_reflect : ∀ e f, e ∈ t.events → f ∈ t.events →
    t.node e = t.node f → rank e ≤ rank f → e ≤ f
  knows : Event → Event → Bool
  knows_correct : ∀ p f, knows p f = true ↔
    p = f ∨ HappensBefore t p f

def contribution {t : Trace} {N : Nat} (h : History t N)
    (p f : Event) (i : Fin N) : Nat :=
  if h.nodeIndex p = i ∧ h.knows p f = true then h.rank p else 0

def clock {t : Trace} {N : Nat} (h : History t N)
    (f : Event) : VectorClock N :=
  fun i => foldMax t.events (fun p => contribution h p f i)

private theorem contribution_self {t : Trace} {N : Nat} (h : History t N)
    (e : Event) : contribution h e e (h.nodeIndex e) = h.rank e := by
  simp [contribution, (h.knows_correct e e).2 (Or.inl rfl)]

private theorem contribution_mono {t : Trace} {N : Nat} (h : History t N)
    {e f : Event} (hef : HappensBefore t e f) (p : Event) (i : Fin N) :
    contribution h p e i ≤ contribution h p f i := by
  by_cases hp : h.nodeIndex p = i ∧ h.knows p e = true
  · have hk : p = e ∨ HappensBefore t p e := (h.knows_correct p e).1 hp.2
    have hkf : p = f ∨ HappensBefore t p f := by
      rcases hk with rfl | hpe
      · exact Or.inr hef
      · exact Or.inr (HappensBefore.trans hpe hef)
    have hpf : h.nodeIndex p = i ∧ h.knows p f = true :=
      ⟨hp.1, (h.knows_correct p f).2 hkf⟩
    simp [contribution, hp, hpf]
  · simp [contribution, hp]

theorem sound {t : Trace} {N : Nat} (h : History t N)
    {e f : Event} (hef : HappensBefore t e f) :
    lt (clock h e) (clock h f) := by
  have he := happensBefore_source hef
  have hf := happensBefore_target hef
  have hforward := happensBefore_forward hef
  constructor
  · intro i
    apply foldMax_mono
    intro p _
    exact contribution_mono h hef p i
  · refine ⟨h.nodeIndex f, ?_⟩
    have hright : h.rank f ≤ clock h f (h.nodeIndex f) :=
      (contribution_self h f) ▸ foldMax_mem t.events
        (fun p => contribution h p f (h.nodeIndex f)) hf
    have hleft : clock h e (h.nodeIndex f) < h.rank f := by
      apply foldMax_lt t.events _ _ (h.rank_positive f hf)
      intro p hp
      by_cases hc : h.nodeIndex p = h.nodeIndex f ∧ h.knows p e = true
      · have hpe : p = e ∨ HappensBefore t p e := (h.knows_correct p e).1 hc.2
        have hpf : p < f := by
          rcases hpe with rfl | hpe
          · exact hforward
          · exact Nat.lt_trans (happensBefore_forward hpe) hforward
        have hn : t.node p = t.node f := by
          rw [h.node_index p hp, h.node_index f hf, hc.1]
        simpa [contribution, hc] using h.rank_strict p f hp hf hn hpf
      · simp [contribution, hc]
        exact h.rank_positive f hf
    exact Nat.lt_of_lt_of_le hleft hright

theorem le_origin {t : Trace} {N : Nat} (h : History t N)
    {e f : Event} (he : e ∈ t.events) (hf : f ∈ t.events)
    (hv : le (clock h e) (clock h f)) : e = f ∨ HappensBefore t e f := by
  have hself : h.rank e ≤ clock h e (h.nodeIndex e) :=
    (contribution_self h e) ▸ foldMax_mem t.events
      (fun p => contribution h p e (h.nodeIndex e)) he
  have hbound : h.rank e ≤ clock h f (h.nodeIndex e) :=
    Nat.le_trans hself (hv (h.nodeIndex e))
  have hpos : 0 < clock h f (h.nodeIndex e) :=
    Nat.lt_of_lt_of_le (h.rank_positive e he) hbound
  obtain ⟨p, hp, hval⟩ := foldMax_attains t.events
    (fun p => contribution h p f (h.nodeIndex e)) hpos
  have hcontrib : contribution h p f (h.nodeIndex e) = clock h f (h.nodeIndex e) := hval
  by_cases hc : h.nodeIndex p = h.nodeIndex e ∧ h.knows p f = true
  · have hrank : h.rank e ≤ h.rank p := by
      rw [← hcontrib] at hbound
      simpa [contribution, hc] using hbound
    have hn : t.node e = t.node p := by
      rw [h.node_index e he, h.node_index p hp, hc.1]
    have hep : e ≤ p := h.rank_reflect e p he hp hn hrank
    have hpf : p = f ∨ HappensBefore t p f := (h.knows_correct p f).1 hc.2
    rcases Nat.eq_or_lt_of_le hep with heq | hlt
    · subst p
      rcases hpf with hsame | hbefore
      · exact Or.inl hsame
      · exact Or.inr hbefore
    · have hl : HappensBefore t e p :=
        .local_step ⟨he, hp, hn, hlt⟩
      rcases hpf with rfl | hpf
      · exact Or.inr hl
      · exact Or.inr (.trans hl hpf)
  · have hz : clock h f (h.nodeIndex e) = 0 := by
      simpa [contribution, hc] using hcontrib.symm
    exact False.elim ((Nat.ne_of_gt hpos) hz)

theorem complete {t : Trace} {N : Nat} (h : History t N)
    {e f : Event} (he : e ∈ t.events) (hf : f ∈ t.events)
    (hv : lt (clock h e) (clock h f)) : HappensBefore t e f := by
  rcases le_origin h he hf hv.1 with heq | hb
  · subst f
    exact False.elim ((lt_irrefl (clock h e)) hv)
  · exact hb

def pastContribution {t : Trace} {N : Nat} (h : History t N)
    (p f : Event) (i : Fin N) : Nat :=
  if p ≠ f ∧ h.nodeIndex p = i ∧ h.knows p f = true then h.rank p else 0

def pastClock {t : Trace} {N : Nat} (h : History t N)
    (f : Event) : VectorClock N :=
  fun i => foldMax t.events (fun p => pastContribution h p f i)

private theorem past_le_clock {t : Trace} {N : Nat} (h : History t N)
    (f : Event) (i : Fin N) : pastClock h f i ≤ clock h f i := by
  apply foldMax_mono
  intro p _
  by_cases hp : p ≠ f ∧ h.nodeIndex p = i ∧ h.knows p f = true
  · have hc : h.nodeIndex p = i ∧ h.knows p f = true := ⟨hp.2.1, hp.2.2⟩
    simp [pastContribution, contribution, hp]
  · simp [pastContribution, hp]

private theorem clock_decompose {t : Trace} {N : Nat} (h : History t N)
    (f : Event) (hf : f ∈ t.events) (i : Fin N) :
    clock h f i = max (pastClock h f i)
      (if h.nodeIndex f = i then h.rank f else 0) := by
  apply Nat.le_antisymm
  · apply foldMax_le t.events _ _
    intro p hp
    by_cases hpf : p = f
    · subst p
      by_cases hi : h.nodeIndex f = i
      · have hk : h.knows f f = true := (h.knows_correct f f).2 (Or.inl rfl)
        simp [contribution, hi, hk]
        exact Nat.le_max_right _ _
      · simp [contribution, hi]
    · have hpc : pastContribution h p f i = contribution h p f i := by
        simp [pastContribution, contribution, hpf]
      rw [← hpc]
      exact Nat.le_trans (foldMax_mem t.events
        (fun q => pastContribution h q f i) hp) (Nat.le_max_left _ _)
  · apply Nat.max_le_of_le_of_le
    · exact past_le_clock h f i
    · by_cases hi : h.nodeIndex f = i
      · simp [hi]
        have hm := foldMax_mem t.events
          (fun p => contribution h p f i) hf
        have hs : contribution h f f i = h.rank f := by
          simp [contribution, hi, (h.knows_correct f f).2 (Or.inl rfl)]
        exact hs ▸ hm
      · simp [hi]

theorem tick {t : Trace} {N : Nat} (h : History t N)
    (e : Event) (he : e ∈ t.events)
    (hrank : h.rank e = pastClock h e (h.nodeIndex e) + 1) :
    clock h e = increment (pastClock h e) (h.nodeIndex e) := by
  funext i
  rw [clock_decompose h e he i]
  by_cases hi : h.nodeIndex e = i
  · subst i
    simp [increment, hrank]
  · simp [increment, hi, Ne.symm hi]

theorem receive_tick {t : Trace} {N : Nat} (h : History t N)
    (e : Event) (he : e ∈ t.events) (m : MessageId)
    (_hr : t.kind e = .receive m)
    (before message : VectorClock N)
    (hinput : pastClock h e = merge before message)
    (hrank : h.rank e = pastClock h e (h.nodeIndex e) + 1) :
    clock h e = increment (merge before message) (h.nodeIndex e) := by
  rw [tick h e he hrank, hinput]

theorem local_tick {t : Trace} {N : Nat} (h : History t N)
    (e : Event) (he : e ∈ t.events)
    (before : VectorClock N) (hinput : pastClock h e = before)
    (hrank : h.rank e = pastClock h e (h.nodeIndex e) + 1) :
    clock h e = increment before (h.nodeIndex e) := by
  rw [tick h e he hrank, hinput]

theorem iff_happensBefore {t : Trace} {N : Nat} (h : History t N)
    (e f : Event) (he : e ∈ t.events) (hf : f ∈ t.events) :
    HappensBefore t e f ↔ lt (clock h e) (clock h f) :=
  ⟨sound h, complete h he hf⟩

/-- A process register and message payload correctly represent the strict
causal past. This separates execution input consistency from clock ordering. -/
structure OperationalHistory (t : Trace) (N : Nat) where
  history : History t N
  before : Event → VectorClock N
  messageClock : MessageId → VectorClock N
  input_eq : ∀ e, e ∈ t.events → pastClock history e =
    (match t.kind e with
     | .receive m => merge (before e) (messageClock m)
     | _ => before e)
  rank_next : ∀ e, e ∈ t.events →
    history.rank e = pastClock history e (history.nodeIndex e) + 1
  attach : ∀ {e m}, e ∈ t.events → t.kind e = .send m →
    messageClock m = clock history e

theorem OperationalHistory.clock_tick {t : Trace} {N : Nat}
    (o : OperationalHistory t N) (e : Event) (he : e ∈ t.events) :
    clock o.history e = increment
      (match t.kind e with
       | .receive m => merge (o.before e) (o.messageClock m)
       | _ => o.before e) (o.history.nodeIndex e) := by
  rw [tick o.history e he (o.rank_next e he), o.input_eq e he]

theorem OperationalHistory.operational_iff {t : Trace} {N : Nat}
    (o : OperationalHistory t N) (e f : Event)
    (he : e ∈ t.events) (hf : f ∈ t.events) :
    HappensBefore t e f ↔ lt (clock o.history e) (clock o.history f) :=
  Canonical.iff_happensBefore o.history e f he hf

theorem concurrent_iff_incomparable {t : Trace} {N : Nat}
    (h : History t N) (e f : Event)
    (he : e ∈ t.events) (hf : f ∈ t.events) :
    Concurrent t e f ↔
      ¬ le (clock h e) (clock h f) ∧ ¬ le (clock h f) (clock h e) := by
  constructor
  · intro hc
    constructor
    · intro hle
      rcases le_origin h he hf hle with heq | hb
      · exact hc.2.2 heq
      · exact hc.1 hb
    · intro hle
      rcases le_origin h hf he hle with heq | hb
      · exact hc.2.2 heq.symm
      · exact hc.2.1 hb
  · intro hi
    refine ⟨?_, ?_, ?_⟩
    · intro hb; exact hi.1 (sound h hb).1
    · intro hb; exact hi.2 (sound h hb).1
    · intro heq; subst f; exact hi.1 (le_refl _)

end Harmonia.Causal.Vector.Canonical
