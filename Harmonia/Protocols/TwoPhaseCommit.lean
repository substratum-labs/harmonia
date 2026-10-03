/-
  Harmonia.Protocols.TwoPhaseCommit
  Tracer slice: Formal specification and inductive safety invariant of Two-Phase Commit (2PC).
-/

import Harmonia.Core.SmallStep

namespace Harmonia.Protocols.TwoPhaseCommit

open Harmonia.Core

inductive Role where
  | coordinator
  | participant
deriving DecidableEq, Repr

inductive TxState where
  | init
  | prepared
  | committed
  | aborted
deriving DecidableEq, Repr

structure NodeState where
  role  : Role
  state : TxState
  votes : List (NodeId × Bool)
deriving DecidableEq, Repr

inductive Payload where
  | prepare
  | vote (accept : Bool)
  | commit
  | abort
deriving DecidableEq, Repr

def coordinatorId : NodeId := 0

/-- Safety Invariant: Agreement / Consistency
    No participant can be in Committed state while another is in Aborted state. -/
def AgreementInvariant (s : GlobalState NodeState Payload) : Prop :=
  ∀ (n1 n2 : NodeId),
    (s.nodes n1).state = TxState.committed → (s.nodes n2).state ≠ TxState.aborted

end Harmonia.Protocols.TwoPhaseCommit
