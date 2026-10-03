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

inductive GlobalStep {NodeState Payload : Type} (spec : ProtocolSpec NodeState Payload) :
    GlobalState NodeState Payload → GlobalState NodeState Payload → Prop where
  | deliverMsg (m : Message Payload) (hIn : m ∈ s.network.inFlight) :
      let res := spec.stepReceive m.dst (s.nodes m.dst) m
      let newNodes := fun n => if n = m.dst then res.nextState else s.nodes n
      let newNet := (s.network.deliver m).inFlight ++ res.outMsgs
      GlobalStep spec s { nodes := newNodes, network := { inFlight := newNet } }

  | triggerTimeout (nid : NodeId) (res : StepResult NodeState Payload)
      (hTimeout : spec.stepTimeout nid (s.nodes nid) = some res) :
      let newNodes := fun n => if n = nid then res.nextState else s.nodes n
      let newNet := s.network.inFlight ++ res.outMsgs
      GlobalStep spec s { nodes := newNodes, network := { inFlight := newNet } }

  | dropMsg (m : Message Payload) (hIn : m ∈ s.network.inFlight) :
      GlobalStep spec s { nodes := s.nodes, network := s.network.drop m }

/-- Inductive reachability of a global system configuration. -/
inductive Reachable {NodeState Payload : Type} (spec : ProtocolSpec NodeState Payload) :
    GlobalState NodeState Payload → Prop where
  | init : Reachable spec { nodes := spec.init, network := NetworkState.empty }
  | step {s1 s2 : GlobalState NodeState Payload} :
      Reachable spec s1 → GlobalStep spec s1 s2 → Reachable spec s2

/-- An invariant holds if it is satisfied in every reachable state. -/
def HoldsInvariant {NodeState Payload : Type} (spec : ProtocolSpec NodeState Payload)
    (inv : GlobalState NodeState Payload → Prop) : Prop :=
  ∀ s, Reachable spec s → inv s

end Harmonia.Core
