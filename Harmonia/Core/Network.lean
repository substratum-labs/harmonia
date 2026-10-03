/-
  Harmonia.Core.Network
  Asynchronous message pool semantics, packet omission, and network transitions.
-/

import Harmonia.Core.Event

namespace Harmonia.Core

/-- Network packet containing sender, target, and payload. -/
structure Message (Payload : Type) where
  id   : Nat
  src  : NodeId
  dst  : NodeId
  body : Payload
deriving DecidableEq, Repr

/-- In-flight message pool in an asynchronous network.
    Modeled as an unordered collection with non-deterministic delivery. -/
structure NetworkState (Payload : Type) where
  inFlight : List (Message Payload)
deriving Repr

namespace NetworkState

def empty {Payload : Type} : NetworkState Payload :=
  { inFlight := [] }

/-- Inject a new message into the network pool. -/
def send {Payload : Type} (net : NetworkState Payload) (msg : Message Payload) : NetworkState Payload :=
  { inFlight := msg :: net.inFlight }

/-- Non-deterministic packet drop (network omission failure). -/
def drop {Payload : Type} (net : NetworkState Payload) (msg : Message Payload) : NetworkState Payload :=
  { inFlight := net.inFlight.erase msg }

/-- Consume a delivered message from the flight pool. -/
def deliver {Payload : Type} (net : NetworkState Payload) (msg : Message Payload) : NetworkState Payload :=
  { inFlight := net.inFlight.erase msg }

end NetworkState

end Harmonia.Core
