/-
  Harmonia.Core.Event
  Foundational event calculus, Lamport logical clocks, and happens-before causal order.
-/

namespace Harmonia.Core

/-- Unique identifier for a participating node / replica. -/
abbrev NodeId := Nat

/-- Logical timestamp (Lamport clock scalar or sequence). -/
structure LogicalTime where
  epoch : Nat
  seq   : Nat
deriving DecidableEq, Repr, Inhabited

instance : LT LogicalTime where
  lt a b := a.epoch < b.epoch ∨ (a.epoch = b.epoch ∧ a.seq < b.seq)

instance : LE LogicalTime where
  le a b := a < b ∨ a = b

/-- An atomic event executed at a specific node. -/
structure Event (Payload : Type) where
  id        : Nat
  node      : NodeId
  timestamp : LogicalTime
  payload   : Payload
deriving Repr

/-- Lamport's happens-before relation (≺) on events. -/
def HappensBefore {α : Type} (e1 e2 : Event α) : Prop :=
  (e1.node = e2.node ∧ e1.timestamp < e2.timestamp) ∨
  (e1.timestamp < e2.timestamp)

end Harmonia.Core
