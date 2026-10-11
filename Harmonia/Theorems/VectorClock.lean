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
  local_precedes : ∀ {e f}, t.localEdge e f → le (clock e) (before f)
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
    {e f : Event} (h : t.localEdge e f) : lt (v.clock e) (v.clock f) := by
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
  | local_step _ _ he => exact v.local_sound he
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
