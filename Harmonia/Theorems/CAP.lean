import Harmonia.Core.Execution

/-! A partitioned, asynchronous two-component register model. A local silent
step can stand for any finite internal computation. A completed operation is
the externally visible request/response pair. No fairness or deterministic
scheduler is assumed. -/
namespace Harmonia.CAP

universe u v w x

inductive Op (V : Type u) where
  | write (val : V)
  | read
  deriving DecidableEq

inductive Resp (V : Type u) where
  | ok
  | val (val : V)
  deriving DecidableEq

inductive LocalAction (V : Type u) where
  | silent
  | complete (op : Op V) (response : Resp V)

inductive Side where | left | right

/-- Nonempty disjoint node components. The product semantics below enforces
that no transition transfers information across this cut. -/
structure Partition (N : Type u) where
  g1 : List N
  g2 : List N
  left_nonempty : g1 ≠ []
  right_nonempty : g2 ≠ []
  disjoint : ∀ n, n ∈ g1 → n ∉ g2

/-- Each side has only its own state and transitions. Cross-cut messages have
no delivery rule; arbitrary local silent steps model asynchronous delay. -/
structure Protocol (V : Type u) (S₁ : Type v) (S₂ : Type w) where
  left : Foundation.TransitionSystem S₁ (LocalAction V) Unit
  right : Foundation.TransitionSystem S₂ (LocalAction V) Unit
  initialLeft : S₁
  initialRight : S₂
  left_init : left.init initialLeft
  right_init : right.init initialRight

def partitionSystem (cut : Partition N) (p : Protocol V S₁ S₂) :
    Foundation.TransitionSystem (S₁ × S₂) (Side × LocalAction V) Unit where
  init s := p.left.init s.1 ∧ p.right.init s.2
  step s a o t :=
    cut.g1 ≠ [] ∧ cut.g2 ≠ [] ∧ (∀ n, n ∈ cut.g1 → n ∉ cut.g2) ∧
    ((a.1 = .left ∧ s.2 = t.2 ∧ p.left.step s.1 a.2 o t.1) ∨
     (a.1 = .right ∧ s.1 = t.1 ∧ p.right.step s.2 a.2 o t.2))

def tag (side : Side) (xs : List (LocalAction V × Unit)) :
    List ((Side × LocalAction V) × Unit) :=
  xs.map (fun x => ((side, x.1), x.2))

theorem lift_left (cut : Partition N) (p : Protocol V S₁ S₂) (r : S₂)
    (h : Foundation.Execution p.left s xs t) :
    Foundation.Execution (partitionSystem cut p) (s, r) (tag .left xs) (t, r) := by
  induction h with
  | nil => exact .nil
  | @cons s a o m labels t hs _ ih =>
    simp only [tag, List.map_cons]
    exact Foundation.Execution.cons (m := (m, r))
      ⟨cut.left_nonempty, cut.right_nonempty, cut.disjoint,
        Or.inl ⟨rfl, rfl, hs⟩⟩ ih

theorem lift_right (cut : Partition N) (p : Protocol V S₁ S₂) (l : S₁)
    (h : Foundation.Execution p.right s xs t) :
    Foundation.Execution (partitionSystem cut p) (l, s) (tag .right xs) (l, t) := by
  induction h with
  | nil => exact .nil
  | @cons s a o m labels t hs _ ih =>
    simp only [tag, List.map_cons]
    exact Foundation.Execution.cons (m := (l, m))
      ⟨cut.left_nonempty, cut.right_nonempty, cut.disjoint,
        Or.inr ⟨rfl, rfl, hs⟩⟩ ih

/-- G2's identical local trace remains possible after any G1 trace. This is
the local indistinguishability fact used in the impossibility argument. -/
theorem partition_replay (cut : Partition N) (p : Protocol V S₁ S₂)
    (hw : Foundation.Execution p.left p.initialLeft writes leftEnd)
    (hr : Foundation.Execution p.right p.initialRight reads rightEnd) :
    Foundation.Execution (partitionSystem cut p) (p.initialLeft, p.initialRight)
      (tag .left writes ++ tag .right reads) (leftEnd, rightEnd) := by
  exact (lift_left cut p p.initialRight hw).append (lift_right cut p leftEnd hr)

def completed : List (LocalAction V × Unit) → List (Op V × Resp V)
  | [] => []
  | (.silent, _) :: xs => completed xs
  | (.complete op response, _) :: xs => (op, response) :: completed xs

def globalCompleted : List ((Side × LocalAction V) × Unit) → List (Op V × Resp V)
  | [] => []
  | ((_, .silent), _) :: xs => globalCompleted xs
  | ((_, .complete op response), _) :: xs => (op, response) :: globalCompleted xs

theorem globalCompleted_tag (side : Side) (xs : List (LocalAction V × Unit)) :
    globalCompleted (tag side xs) = completed xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [tag] at ih
    cases x with
    | mk action observation =>
      cases action <;> simp [tag, globalCompleted, completed, ih]

theorem globalCompleted_append (xs ys : List ((Side × LocalAction V) × Unit)) :
    globalCompleted (xs ++ ys) = globalCompleted xs ++ globalCompleted ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨⟨side, action⟩, observation⟩
    cases action <;> simp [globalCompleted, ih]

/-- Sequential specification of a single register. -/
def register (V : Type u) : Foundation.TransitionSystem V (Op V) (Resp V) where
  init _ := True
  step before op response after :=
    (∃ value, op = .write value ∧ response = .ok ∧ after = value) ∨
    (op = .read ∧ response = .val before ∧ after = before)

/-- Every finite completed partitioned history has a sequential register
witness in its observed order. This is a strong atomicity condition: in
particular it preserves the real-time order of nonoverlapping operations. -/
def Linearizable (cut : Partition N) (p : Protocol V S₁ S₂) (initial : V) : Prop :=
  ∀ {labels finalState},
    Foundation.Execution (partitionSystem cut p) (p.initialLeft, p.initialRight)
      labels finalState →
    ∃ final, Foundation.Execution (register V) initial
      (globalCompleted labels) final

/-- Finite traces complete the specified requests with the specified response
shape. The read trace begins in G2's unchanged initial state. -/
def FiniteAvailable (p : Protocol V S₁ S₂) (value : V) : Prop :=
  (∃ xs leftEnd, Foundation.Execution p.left p.initialLeft xs leftEnd ∧
    completed xs = [(.write value, .ok)]) ∧
  (∃ ys rightEnd answer, Foundation.Execution p.right p.initialRight ys rightEnd ∧
    completed ys = [(.read, .val answer)])

def ValidResponse : Op V → Resp V → Prop
  | .write _, .ok => True
  | .read, .val _ => True
  | _, _ => False

/-- Availability at every reachable local state: after a request is issued,
a finite local trace completes that request with a correctly shaped response.
The trace may contain arbitrarily many silent steps. -/
def Available (p : Protocol V S₁ S₂) : Prop :=
  (∀ s, Foundation.Reachable p.left s → ∀ op,
    ∃ xs t response, Foundation.Execution p.left s xs t ∧
      completed xs = [(op, response)] ∧ ValidResponse op response) ∧
  (∀ s, Foundation.Reachable p.right s → ∀ op,
    ∃ xs t response, Foundation.Execution p.right s xs t ∧
      completed xs = [(op, response)] ∧ ValidResponse op response)

theorem available_implies_finite (p : Protocol V S₁ S₂) (value : V)
    (h : Available p) : FiniteAvailable p value := by
  obtain ⟨xs, leftEnd, writeResponse, hw, hwShape, hwValid⟩ :=
    h.1 p.initialLeft (.init p.left_init) (.write value)
  obtain ⟨ys, rightEnd, readResponse, hr, hrShape, hrValid⟩ :=
    h.2 p.initialRight (.init p.right_init) .read
  cases writeResponse with
  | ok =>
    cases readResponse with
    | val answer => exact ⟨⟨xs, leftEnd, hw, hwShape⟩,
        ⟨ys, rightEnd, answer, hr, hrShape⟩⟩
    | ok => exact False.elim hrValid
  | val _ => exact False.elim hwValid

private theorem initial_read {V : Type u} {initial answer final : V}
    (h : Foundation.Execution (register V) initial
      [(.read, .val answer)] final) : answer = initial := by
  cases h with
  | cons hs tail =>
    rcases hs with ⟨_, hbad, _⟩ | ⟨_, hr, _⟩
    · cases hbad
    · cases hr; rfl

private theorem write_then_read {V : Type u} {initial written answer final : V}
    (h : Foundation.Execution (register V) initial
      [(.write written, .ok), (.read, .val answer)] final) :
    answer = written := by
  cases h with
  | cons hs tail =>
    rcases hs with ⟨value, hw, _, he⟩ | ⟨hbad, _, _⟩
    · cases hw
      cases he
      exact initial_read tail
    · cases hbad

/-- Gilbert–Lynch CAP contradiction for a completed G1 write followed in real
time by a G2 read. Availability supplies finite local traces. Partition replay
keeps the G2 response identical with and without the G1 write; linearizability
requires respectively the initial and written values. -/
theorem cap_impossibility_from_witnesses (cut : Partition N)
    (p : Protocol V S₁ S₂) (v₀ v₁ : V)
    (different : v₀ ≠ v₁) (available : FiniteAvailable p v₁)
    (atomic : Linearizable cut p v₀) : False := by
  rcases available with ⟨⟨xs, leftEnd, hw, hwShape⟩,
    ⟨ys, rightEnd, answer, hr, hrShape⟩⟩
  obtain ⟨baseFinal, hbase⟩ := atomic (lift_right cut p p.initialLeft hr)
  rw [globalCompleted_tag, hrShape] at hbase
  have stale : answer = v₀ := initial_read hbase
  obtain ⟨writtenFinal, hwritten⟩ := atomic (partition_replay cut p hw hr)
  rw [globalCompleted_append, globalCompleted_tag, globalCompleted_tag,
    hwShape, hrShape] at hwritten
  have fresh : answer = v₁ := write_then_read hwritten
  exact different (stale.symm.trans fresh)

theorem cap_impossibility (cut : Partition N) (p : Protocol V S₁ S₂) (v₀ v₁ : V)
    (different : v₀ ≠ v₁) (available : Available p)
    (atomic : Linearizable cut p v₀) : False :=
  cap_impossibility_from_witnesses cut p v₀ v₁ different
    (available_implies_finite p v₁ available) atomic

end Harmonia.CAP
