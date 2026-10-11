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
  message_forward : ∀ {e f m}, e ∈ events → f ∈ events →
    kind e = .send m → kind f = .receive m → e < f
  send_unique : ∀ {e f m}, e ∈ events → f ∈ events →
    kind e = .send m → kind f = .send m → e = f

def ProgramOrder (t : Trace) (e f : Event) : Prop :=
  e ∈ t.events ∧ f ∈ t.events ∧ t.node e = t.node f ∧ e < f

inductive HappensBefore (t : Trace) : Event → Event → Prop where
  | local_step {e f} : ProgramOrder t e f → HappensBefore t e f
  | msg_step {e f m} : e ∈ t.events → f ∈ t.events →
      t.kind e = .send m → t.kind f = .receive m → HappensBefore t e f
  | trans {e f g} : HappensBefore t e f → HappensBefore t f g →
      HappensBefore t e g

theorem happensBefore_forward {t : Trace} {e f : Event}
    (h : HappensBefore t e f) : e < f := by
  induction h with
  | local_step h => exact h.2.2.2
  | msg_step he hf hs hr => exact t.message_forward he hf hs hr
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

theorem happensBefore_source {t : Trace} {e f : Event}
    (h : HappensBefore t e f) : e ∈ t.events := by
  induction h with
  | local_step hp => exact hp.1
  | msg_step hp _ _ _ => exact hp
  | trans _ _ ih _ => exact ih

theorem happensBefore_target {t : Trace} {e f : Event}
    (h : HappensBefore t e f) : f ∈ t.events := by
  induction h with
  | local_step hp => exact hp.2.1
  | msg_step _ hp _ _ => exact hp
  | trans _ _ _ ih => exact ih

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
