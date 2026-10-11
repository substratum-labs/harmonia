import Harmonia.Theorems.Causal
import Harmonia.Theorems.Lamport
import Harmonia.Theorems.VectorClock

open Harmonia.Causal

example (t : Trace) (e f : Event) (h : HappensBefore t e f) : e < f :=
  happensBefore_forward h
example (t : Trace) (e f : Event) (h : HappensBefore t e f) :
    ¬ HappensBefore t f e := happensBefore_asymm h
example (t : Trace) (e f : Event) (h : Concurrent t e f) :
    Concurrent t f e := concurrent_symm h
example (t : Trace) (c : Lamport.Clocking t) (e f : Event)
    (h : HappensBefore t e f) : c.clock e < c.clock f := c.sound h
example (t : Trace) (v : Vector.Clocking t 2) (e f : Event)
    (he : e ∈ t.events) (hf : f ∈ t.events) :
    HappensBefore t e f ↔ Vector.lt (v.clock e) (v.clock f) :=
  v.iff_happensBefore e f he hf

private def testIndex (e : Event) : Fin 2 :=
  if e = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

private def testZero : Vector.VectorClock 2 := fun _ => 0

private def independentVector : Vector.Clocking Lamport.independentTrace 2 where
  nodeIndex := testIndex
  node_index := by
    intro e he
    simp [Lamport.independentTrace] at he
    rcases he with rfl | rfl <;> decide
  clock := fun e => Vector.increment testZero (testIndex e)
  before := fun _ => testZero
  messageClock := fun _ => testZero
  local_precedes := by intros; contradiction
  tick := by intro e; rfl
  attach := by intros; contradiction
  rank := fun _ => 1
  rank_self := by
    intro e _
    simp [Vector.increment, testZero]
  rank_positive := by intros; simp
  process_prefix := by
    intro e f he hf hnode _
    simp [Lamport.independentTrace] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact Or.inl rfl
    · simp [testIndex] at hnode
    · simp [testIndex] at hnode
    · exact Or.inl rfl
  component_frontier := by
    intro f i hf hp
    have hi : i = testIndex f := by
      by_cases h : i = testIndex f
      · exact h
      · simp [Vector.increment, testZero, h] at hp
    refine ⟨f, hf, hi.symm, ?_, Or.inl rfl⟩
    simp [hi, Vector.increment, testZero]


example : Concurrent Lamport.independentTrace 0 1 := Lamport.scalar_incomplete.2
example : ¬ Vector.le (independentVector.clock 0) (independentVector.clock 1) ∧
    ¬ Vector.le (independentVector.clock 1) (independentVector.clock 0) :=
  (independentVector.concurrent_iff_incomparable 0 1 (by decide) (by decide)).mp
    Lamport.scalar_incomplete.2

private def sampleKind (e : Event) : EventKind :=
  if e = 1 then .send 0 else if e = 2 then .receive 0 else .internal

private def sampleTrace : Trace where
  events := [0, 1, 2]
  nodup := by decide
  node := fun e => if e = 2 then 1 else 0
  kind := sampleKind
  localEdge := fun e f => e = 0 ∧ f = 1
  local_same := by
    intro e f h
    rcases h with ⟨rfl, rfl⟩
    rfl
  local_forward := by
    intro e f h
    rcases h with ⟨rfl, rfl⟩
    decide
  message_forward := by
    intro e f m hs hr
    have he : e = 1 := by
      by_cases h : e = 1
      · exact h
      · by_cases h2 : e = 2
        · simp [sampleKind, h, h2] at hs
        · simp [sampleKind, h, h2] at hs
    have hf : f = 2 := by
      by_cases h : f = 2
      · exact h
      · by_cases h1 : f = 1
        · simp [sampleKind, h1] at hr
        · simp [sampleKind, h1, h] at hr
    subst e
    subst f
    decide

private theorem sample_local : HappensBefore sampleTrace 0 1 :=
  .local_step (by decide) (by decide) ⟨rfl, rfl⟩

private theorem sample_message : HappensBefore sampleTrace 1 2 :=
  HappensBefore.msg_step (m := 0) (by decide) (by decide) (by decide) (by decide)

example : HappensBefore sampleTrace 0 2 :=
  .trans sample_local sample_message

example (c : Lamport.Clocking sampleTrace) : c.clock 0 < c.clock 2 :=
  c.sound (.trans sample_local sample_message)

example (v : Vector.Clocking sampleTrace 2) :
    Vector.lt (v.clock 0) (v.clock 2) :=
  v.sound (.trans sample_local sample_message)
