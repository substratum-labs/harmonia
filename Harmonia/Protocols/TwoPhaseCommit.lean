/-
  Harmonia.Protocols.TwoPhaseCommit
  Tracer slice: Formal specification, operational semantics, and safety invariants of Two-Phase Commit (2PC).
-/

import Harmonia.Core.SmallStep

namespace Harmonia.Protocols.TwoPhaseCommit

open Harmonia.Core

/-- Role in the Two-Phase Commit transaction. -/
inductive Role where
  | coordinator
  | participant
deriving DecidableEq, Repr

/-- Lifecycle transaction state for a 2PC participant or coordinator. -/
inductive TxState where
  | init
  | prepared
  | committed
  | aborted
deriving DecidableEq, Repr

/-- Node local execution state. -/
structure NodeState where
  role            : Role
  state           : TxState
  votes           : List (NodeId × Bool)
  willingToCommit : Bool
deriving DecidableEq, Repr

/-- Protocol message types exchanged across the network. -/
inductive Payload where
  | prepare
  | vote (accept : Bool)
  | commit
  | abort
deriving DecidableEq, Repr

def coordinatorId : NodeId := 0

/-- Topology configuration for the 2PC cluster. -/
structure SystemConfig where
  participants : List NodeId
deriving Repr

/-- Helper to broadcast a message payload to a target list of nodes. -/
def broadcast (src : NodeId) (dsts : List NodeId) (body : Payload) : List (Message Payload) :=
  dsts.map (fun dst => { id := 0, src := src, dst := dst, body := body })

/-- Initial state for each node under configuration. -/
def initNodeState (willing : NodeId → Bool) (nid : NodeId) : NodeState :=
  if nid = coordinatorId then
    { role := Role.coordinator, state := TxState.init, votes := [], willingToCommit := true }
  else
    { role := Role.participant, state := TxState.init, votes := [], willingToCommit := willing nid }

/-- Helper checking if all participants have cast an affirmative vote. -/
def allParticipantsVotedYes (participants : List NodeId) (votes : List (NodeId × Bool)) : Bool :=
  participants.all (fun p =>
    match votes.find? (fun (voter, _) => voter = p) with
    | some (_, true) => true
    | _ => false)

/-- Step transition triggered on receiving a network message. -/
def stepReceive (cfg : SystemConfig) (nid : NodeId) (st : NodeState) (msg : Message Payload) :
    StepResult NodeState Payload :=
  match st.role with
  | Role.coordinator =>
    match msg.body with
    | Payload.vote accept =>
      if st.state = TxState.init then
        if ¬accept then
          -- One participant rejected: Coordinator aborts and broadcasts GlobalAbort
          { nextState := { st with state := TxState.aborted },
            outMsgs := broadcast coordinatorId cfg.participants Payload.abort }
        else
          let newVotes := (msg.src, true) :: st.votes
          if allParticipantsVotedYes cfg.participants newVotes then
            -- All participants voted yes: Coordinator commits and broadcasts GlobalCommit
            { nextState := { st with state := TxState.committed, votes := newVotes },
              outMsgs := broadcast coordinatorId cfg.participants Payload.commit }
          else
            -- Continue collecting votes
            { nextState := { st with votes := newVotes }, outMsgs := [] }
      else
        { nextState := st, outMsgs := [] }
    | _ => { nextState := st, outMsgs := [] }

  | Role.participant =>
    match msg.body with
    | Payload.prepare =>
      if st.state = TxState.init then
        if st.willingToCommit then
          -- Vote yes and transition to prepared (blocking)
          { nextState := { st with state := TxState.prepared },
            outMsgs := [{ id := 0, src := nid, dst := coordinatorId, body := Payload.vote true }] }
        else
          -- Vote no and transition to aborted
          { nextState := { st with state := TxState.aborted },
            outMsgs := [{ id := 0, src := nid, dst := coordinatorId, body := Payload.vote false }] }
      else
        { nextState := st, outMsgs := [] }

    | Payload.commit =>
      if st.state = TxState.prepared then
        { nextState := { st with state := TxState.committed }, outMsgs := [] }
      else
        { nextState := st, outMsgs := [] }

    | Payload.abort =>
      -- Can abort from init or prepared
      if st.state = TxState.init ∨ st.state = TxState.prepared then
        { nextState := { st with state := TxState.aborted }, outMsgs := [] }
      else
        { nextState := st, outMsgs := [] }

    | _ => { nextState := st, outMsgs := [] }

/-- Step transition triggered on internal timeout or coordinator trigger. -/
def stepTimeout (cfg : SystemConfig) (_ : NodeId) (st : NodeState) :
    Option (StepResult NodeState Payload) :=
  match st.role with
  | Role.coordinator =>
    if st.state = TxState.init then
      if st.votes.isEmpty then
        -- Coordinator transaction start: broadcast prepare to all participants
        some { nextState := st, outMsgs := broadcast coordinatorId cfg.participants Payload.prepare }
      else
        -- Timeout waiting for all votes: abort transaction
        some { nextState := { st with state := TxState.aborted },
               outMsgs := broadcast coordinatorId cfg.participants Payload.abort }
    else
      none

  | Role.participant =>
    if st.state = TxState.init then
      -- Participant timeout before prepare received: unilateral abort
      some { nextState := { st with state := TxState.aborted }, outMsgs := [] }
    else
      -- CRITICAL 2PC INVARIANT: A prepared participant CANNOT abort unilaterally (it must block!)
      none

/-- Full Protocol Specification instance for 2PC. -/
def twoPhaseCommitSpec (cfg : SystemConfig) (willing : NodeId → Bool) :
    ProtocolSpec NodeState Payload where
  init := initNodeState willing
  stepReceive := stepReceive cfg
  stepTimeout := stepTimeout cfg

/- -------------------------------------------------------------------------
   Safety Invariants
   ------------------------------------------------------------------------- -/

/-- Invariant 1: Agreement / Consistency
    No node can decide Committed if any other node has decided Aborted. -/
def AgreementInvariant (s : GlobalState NodeState Payload) : Prop :=
  ∀ (n1 n2 : NodeId),
    (s.nodes n1).state = TxState.committed → (s.nodes n2).state ≠ TxState.aborted

/-- Invariant 2: Validity
    A node can only be Committed if all participants were originally willing to commit. -/
def ValidityInvariant (cfg : SystemConfig) (s : GlobalState NodeState Payload) : Prop :=
  ∀ (n : NodeId),
    (s.nodes n).state = TxState.committed →
      (∀ (p : NodeId), p ∈ cfg.participants → (s.nodes p).willingToCommit = true)

/-- Initial state satisfies the Agreement invariant trivially. -/
theorem init_satisfies_agreement (cfg : SystemConfig) (willing : NodeId → Bool) :
    AgreementInvariant { nodes := (twoPhaseCommitSpec cfg willing).init, network := NetworkState.empty } := by
  intro n1 n2 h1
  unfold twoPhaseCommitSpec initNodeState at h1
  dsimp at h1
  split at h1 <;> contradiction

end Harmonia.Protocols.TwoPhaseCommit
