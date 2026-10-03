/-
  Harmonia.Core.SmallStep
  Global small-step operational semantics, interleaved execution, and invariants.
-/

import Harmonia.Core.Network

namespace Harmonia.Core

/-- Result of a node-local transition step: new state and outbound messages. -/
structure StepResult (NodeState Payload : Type) where
  nextState : NodeState
  outMsgs   : List (Message Payload)

/-- Abstract local protocol specification running on a node. -/
structure ProtocolSpec (NodeState Payload : Type) where
  init        : NodeId → NodeState
  stepReceive : NodeId → NodeState → Message Payload → StepResult NodeState Payload
  stepTimeout : NodeId → NodeState → Option (StepResult NodeState Payload)

/-- Global state of the entire distributed system. -/
structure GlobalState (NodeState Payload : Type) where
  nodes   : NodeId → NodeState
  network : NetworkState Payload

def applyReceive {NodeState Payload : Type} [DecidableEq Payload]
    (spec : ProtocolSpec NodeState Payload) (s : GlobalState NodeState Payload) (m : Message Payload) :
    GlobalState NodeState Payload :=
  let res := spec.stepReceive m.dst (s.nodes m.dst) m
  {
    nodes := fun n => if n = m.dst then res.nextState else s.nodes n,
    network := { inFlight := (s.network.deliver m).inFlight ++ res.outMsgs }
  }

def applyTimeout {NodeState Payload : Type}
    (s : GlobalState NodeState Payload) (nid : NodeId) (res : StepResult NodeState Payload) :
    GlobalState NodeState Payload :=
  {
    nodes := fun n => if n = nid then res.nextState else s.nodes n,
    network := { inFlight := s.network.inFlight ++ res.outMsgs }
  }

def applyDrop {NodeState Payload : Type} [DecidableEq Payload]
    (s : GlobalState NodeState Payload) (m : Message Payload) :
    GlobalState NodeState Payload :=
  { nodes := s.nodes, network := s.network.drop m }

inductive GlobalStep {NodeState Payload : Type} [DecidableEq Payload] (spec : ProtocolSpec NodeState Payload) :
    GlobalState NodeState Payload → GlobalState NodeState Payload → Prop where
  | deliverMsg (s : GlobalState NodeState Payload) (m : Message Payload) (hIn : m ∈ s.network.inFlight) :
      GlobalStep spec s (applyReceive spec s m)

  | triggerTimeout (s : GlobalState NodeState Payload) (nid : NodeId) (res : StepResult NodeState Payload)
      (hTimeout : spec.stepTimeout nid (s.nodes nid) = some res) :
      GlobalStep spec s (applyTimeout s nid res)

  | dropMsg (s : GlobalState NodeState Payload) (m : Message Payload) (hIn : m ∈ s.network.inFlight) :
      GlobalStep spec s (applyDrop s m)

/-- Inductive reachability of a global system configuration. -/
inductive Reachable {NodeState Payload : Type} [DecidableEq Payload] (spec : ProtocolSpec NodeState Payload) :
    GlobalState NodeState Payload → Prop where
  | init : Reachable spec { nodes := spec.init, network := NetworkState.empty }
  | step {s1 s2 : GlobalState NodeState Payload} :
      Reachable spec s1 → GlobalStep spec s1 s2 → Reachable spec s2

/-- An invariant holds if it is satisfied in every reachable state. -/
def HoldsInvariant (NodeState : Type) (Payload : Type) [DecidableEq Payload]
    (spec : ProtocolSpec NodeState Payload) (inv : GlobalState NodeState Payload → Prop) : Prop :=
  ∀ (s : GlobalState NodeState Payload), Reachable spec s → inv s

end Harmonia.Core
