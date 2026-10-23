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
  local_precedes := by
    intro e f h
    have hn : e = f := h.2.2.1
    exact False.elim ((Nat.lt_irrefl _) (hn ▸ h.2.2.2))
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
  message_forward := by
    intro e f m _ _ hs hr
    have he : e = 1 := by
      by_cases h : e = 1
      · exact h
      · by_cases h2 : e = 2
        · simp [sampleKind, h2] at hs
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
  send_unique := by
    intro e f m _ _ hs hf
    have he : e = 1 := by
      by_cases h : e = 1
      · exact h
      · by_cases h2 : e = 2
        · simp [sampleKind, h2] at hs
        · simp [sampleKind, h, h2] at hs
    have hf' : f = 1 := by
      by_cases h : f = 1
      · exact h
      · by_cases h2 : f = 2
        · simp [sampleKind, h2] at hf
        · simp [sampleKind, h, h2] at hf
    exact he.trans hf'.symm

private theorem sample_local : HappensBefore sampleTrace 0 1 :=
  .local_step ⟨by decide, by decide, rfl, by decide⟩

private theorem sample_message : HappensBefore sampleTrace 1 2 :=
  HappensBefore.msg_step (m := 0) (by decide) (by decide) (by decide) (by decide)

example : HappensBefore sampleTrace 0 2 :=
  .trans sample_local sample_message

example (c : Lamport.Clocking sampleTrace) : c.clock 0 < c.clock 2 :=
  c.sound (.trans sample_local sample_message)

example (v : Vector.Clocking sampleTrace 2) :
    Vector.lt (v.clock 0) (v.clock 2) :=
  v.sound (.trans sample_local sample_message)

example (t : Trace) (c : Lamport.Clocking t) (e : Event) :
    ¬ Lamport.LamportTotalOrder c e e := Lamport.total_irrefl c e
example (t : Trace) (c : Lamport.Clocking t) (e f g : Event)
    (hef : Lamport.LamportTotalOrder c e f)
    (hfg : Lamport.LamportTotalOrder c f g) :
    Lamport.LamportTotalOrder c e g := Lamport.total_trans c hef hfg
example (t : Trace) (c : Lamport.Clocking t) (e f : Event) :
    Lamport.LamportTotalOrder c e f ∨ e = f ∨
      Lamport.LamportTotalOrder c f e := Lamport.total_trichotomy c e f
example (t : Trace) (c : Lamport.Clocking t) (e f : Event)
    (h : HappensBefore t e f) : Lamport.LamportTotalOrder c e f :=
  Lamport.total_extends_causality c h

example (t : Trace) (h : Vector.Canonical.History t 2) (e f : Event)
    (he : e ∈ t.events) (hf : f ∈ t.events) :
    HappensBefore t e f ↔
      Vector.lt (Vector.Canonical.clock h e) (Vector.Canonical.clock h f) :=
  Vector.Canonical.iff_happensBefore h e f he hf

private def messageKind (e : Event) : EventKind :=
  if e = 0 then .send 0 else if e = 1 then .receive 0 else .internal

private def messageTrace : Trace where
  events := [0, 1]
  nodup := by decide
  node := id
  kind := messageKind
  message_forward := by
    intro e f m _ _ hs hr
    have he : e = 0 := by
      by_cases h0 : e = 0
      · exact h0
      · by_cases h1 : e = 1
        · simp [messageKind, h1] at hs
        · simp [messageKind, h0, h1] at hs
    have hf : f = 1 := by
      by_cases h0 : f = 0
      · simp [messageKind, h0] at hr
      · by_cases h1 : f = 1
        · exact h1
        · simp [messageKind, h0, h1] at hr
    subst e; subst f; decide
  send_unique := by
    intro e f m _ _ hs hf
    have he : e = 0 := by
      by_cases h0 : e = 0
      · exact h0
      · by_cases h1 : e = 1
        · simp [messageKind, h1] at hs
        · simp [messageKind, h0, h1] at hs
    have hf' : f = 0 := by
      by_cases h0 : f = 0
      · exact h0
      · by_cases h1 : f = 1
        · simp [messageKind, h1] at hf
        · simp [messageKind, h0, h1] at hf
    exact he.trans hf'.symm

private theorem message_edge : HappensBefore messageTrace 0 1 :=
  HappensBefore.msg_step (m := 0) (by decide) (by decide) (by decide) (by decide)

private theorem message_hb_iff (p f : Event) :
    HappensBefore messageTrace p f ↔ p = 0 ∧ f = 1 := by
  constructor
  · intro h
    have hp := happensBefore_source h
    have hf := happensBefore_target h
    have hlt := happensBefore_forward h
    simp [messageTrace] at hp hf
    rcases hp with rfl | rfl <;> rcases hf with rfl | rfl
    · exact False.elim ((by decide : ¬ (0 < 0)) hlt)
    · exact ⟨rfl, rfl⟩
    · exact False.elim ((by decide : ¬ (1 < 0)) hlt)
    · exact False.elim ((by decide : ¬ (1 < 1)) hlt)
  · rintro ⟨rfl, rfl⟩
    exact message_edge

private def messageIndex (e : Event) : Fin 2 :=
  if e = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

private def messageHistory : Vector.Canonical.History messageTrace 2 where
  nodeIndex := messageIndex
  node_index := by
    intro e he
    simp [messageTrace] at he
    rcases he with rfl | rfl <;> decide
  rank := fun _ => 1
  rank_positive := by intros; simp
  rank_strict := by
    intro e f _ _ hn hlt
    have heq : e = f := hn
    exact False.elim ((Nat.ne_of_lt hlt) heq)
  rank_reflect := by
    intro e f _ _ hn _
    exact Nat.le_of_eq hn
  knows := fun p f => decide (p = f ∨ (p = 0 ∧ f = 1))
  knows_correct := by
    intro p f
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      rcases h with heq | hp
      · exact Or.inl heq
      · exact Or.inr ((message_hb_iff p f).2 hp)
    · intro h
      rcases h with heq | hp
      · exact Or.inl heq
      · exact Or.inr ((message_hb_iff p f).1 hp)

example : Vector.lt (Vector.Canonical.clock messageHistory 0)
    (Vector.Canonical.clock messageHistory 1) :=
  Vector.Canonical.sound messageHistory message_edge
example : HappensBefore messageTrace 0 1 :=
  (Vector.Canonical.iff_happensBefore messageHistory 0 1 (by decide) (by decide)).2
    (Vector.Canonical.sound messageHistory message_edge)

example : Vector.Canonical.clock messageHistory 0 =
    Vector.increment testZero (⟨0, by decide⟩ : Fin 2) := by
  apply funext
  exact (Fin.forall_fin_two (p := fun i =>
    Vector.Canonical.clock messageHistory 0 i =
      Vector.increment testZero (⟨0, by decide⟩ : Fin 2) i)).2
        ⟨by decide, by decide⟩
example : Vector.Canonical.clock messageHistory 1 =
    Vector.increment
      (Vector.merge testZero (Vector.Canonical.clock messageHistory 0))
      (⟨1, by decide⟩ : Fin 2) := by
  apply funext
  exact (Fin.forall_fin_two (p := fun i =>
    Vector.Canonical.clock messageHistory 1 i =
      Vector.increment
        (Vector.merge testZero (Vector.Canonical.clock messageHistory 0))
        (⟨1, by decide⟩ : Fin 2) i)).2 ⟨by decide, by decide⟩

private def messageOperational : Vector.Canonical.OperationalHistory messageTrace 2 where
  history := messageHistory
  before := fun _ => testZero
  messageClock := fun _ => Vector.Canonical.clock messageHistory 0
  input_eq := by
    intro e he
    simp [messageTrace] at he
    rcases he with rfl | rfl
    · apply funext
      exact (Fin.forall_fin_two (p := fun i =>
        Vector.Canonical.pastClock messageHistory 0 i = testZero i)).2
          ⟨by decide, by decide⟩
    · apply funext
      exact (Fin.forall_fin_two (p := fun i =>
        Vector.Canonical.pastClock messageHistory 1 i =
          Vector.merge testZero (Vector.Canonical.clock messageHistory 0) i)).2
            ⟨by decide, by decide⟩
  rank_next := by
    intro e he
    simp [messageTrace] at he
    rcases he with rfl | rfl <;> decide
  attach := by
    intro e m he hs
    simp [messageTrace] at he
    rcases he with rfl | rfl
    · simp [messageTrace, messageKind] at hs
      subst m
      rfl
    · simp [messageTrace, messageKind] at hs

example : Vector.Canonical.clock messageOperational.history 1 =
    Vector.increment
      (Vector.merge (messageOperational.before 1)
        (messageOperational.messageClock 0))
      (messageOperational.history.nodeIndex 1) := by
  simpa [messageTrace, messageKind] using
    messageOperational.clock_tick 1 (by decide)

example : HappensBefore messageTrace 0 1 ↔
    Vector.lt (Vector.Canonical.clock messageOperational.history 0)
      (Vector.Canonical.clock messageOperational.history 1) :=
  messageOperational.operational_iff 0 1 (by decide) (by decide)

private def independentHistory : Vector.Canonical.History Lamport.independentTrace 2 where
  nodeIndex := testIndex
  node_index := by
    intro e he
    simp [Lamport.independentTrace] at he
    rcases he with rfl | rfl <;> decide
  rank := fun _ => 1
  rank_positive := by intros; simp
  rank_strict := by
    intro e f _ _ hn hlt
    have heq : e = f := hn
    exact False.elim ((Nat.ne_of_lt hlt) heq)
  rank_reflect := by
    intro e f _ _ hn _
    exact Nat.le_of_eq hn
  knows := fun p f => decide (p = f)
  knows_correct := by
    intro p f
    simp only [decide_eq_true_eq]
    constructor
    · intro heq; exact Or.inl heq
    · intro h
      rcases h with heq | hb
      · exact heq
      · exact False.elim (Lamport.independent_no_causality hb)

example : Concurrent Lamport.independentTrace 0 1 ↔
    ¬ Vector.le (Vector.Canonical.clock independentHistory 0)
        (Vector.Canonical.clock independentHistory 1) ∧
    ¬ Vector.le (Vector.Canonical.clock independentHistory 1)
        (Vector.Canonical.clock independentHistory 0) :=
  Vector.Canonical.concurrent_iff_incomparable independentHistory 0 1
    (by decide) (by decide)
