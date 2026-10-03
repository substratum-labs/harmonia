/-
  Harmonia.Protocols.RaftElection
  Demonstrating the Harmonia eDSL on Raft Leader Election.
-/

import Harmonia.DSL.Syntax

open Harmonia.DSL

declare_protocol RaftElection where
  roles := [follower, candidate, leader]
  states := [follower_init, requesting_votes, elected_leader, stepped_down]
  messages := [request_vote, vote_granted, vote_denied, heartbeat]

namespace RaftElection

/-- Invariant: Leader Uniqueness
    At most one leader can be elected in any epoch/term. -/
def atMostOneLeader (nodes : List RaftElection.NodeState) : Prop :=
  (nodes.filter (fun n => n.role = RaftElection.Role.leader)).length ≤ 1

end RaftElection
