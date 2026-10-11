import Init

namespace Harmonia.Causal

abbrev NodeId := Nat
abbrev MessageId := Nat
abbrev Event := Nat

inductive EventKind where
  | internal
  | send (message : MessageId)
  | receive (message : MessageId)
  deriving DecidableEq, Repr

/-- Event IDs enumerate one acyclic execution. A local edge joins successive
process events; message edges join the matching send and receive. -/
structure Trace where
  events : List Event
  nodup : events.Nodup
  node : Event → Nat
  kind : Event → EventKind
  localEdge : Event → Event → Prop
  local_same : ∀ {e f}, localEdge e f → node e = node f
  local_forward : ∀ {e f}, localEdge e f → e < f
  message_forward : ∀ {e f m}, kind e = .send m → kind f = .receive m → e < f

inductive HappensBefore (t : Trace) : Event → Event → Prop where
  | local_step {e f} : e ∈ t.events → f ∈ t.events →
      t.localEdge e f → HappensBefore t e f
  | msg_step {e f m} : e ∈ t.events → f ∈ t.events →
      t.kind e = .send m → t.kind f = .receive m → HappensBefore t e f
  | trans {e f g} : HappensBefore t e f → HappensBefore t f g →
      HappensBefore t e g

theorem happensBefore_forward {t : Trace} {e f : Event}
    (h : HappensBefore t e f) : e < f := by
  induction h with
  | local_step _ _ h => exact t.local_forward h
  | msg_step _ _ hs hr => exact t.message_forward hs hr
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

theorem happensBefore_irrefl (t : Trace) (e : Event) :
    ¬ HappensBefore t e e := by
  intro h
  exact (Nat.lt_irrefl e) (happensBefore_forward h)

theorem happensBefore_asymm {t : Trace} {e f : Event}
    (h : HappensBefore t e f) : ¬ HappensBefore t f e := by
  intro hback
  exact Nat.lt_asymm (happensBefore_forward h) (happensBefore_forward hback)

theorem happensBefore_trans {t : Trace} {e f g : Event}
    (h₁ : HappensBefore t e f) (h₂ : HappensBefore t f g) :
    HappensBefore t e g := .trans h₁ h₂

def Concurrent (t : Trace) (e f : Event) : Prop :=
  ¬ HappensBefore t e f ∧ ¬ HappensBefore t f e ∧ e ≠ f

theorem concurrent_symm {t : Trace} {e f : Event}
    (h : Concurrent t e f) : Concurrent t f e :=
  ⟨h.2.1, h.1, Ne.symm h.2.2⟩

end Harmonia.Causal
