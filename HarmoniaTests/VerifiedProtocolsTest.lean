import Harmonia.VerifiedProtocols

namespace Harmonia.VerifiedProtocols.Tests
open Harmonia.Distributed Harmonia.VerifiedProtocols.QuorumLease

def cluster3 : Config Nat := ⟨[0, 1, 2], by decide⟩
def node0 : Member cluster3 := ⟨0, by decide⟩
def node1 : Member cluster3 := ⟨1, by decide⟩
def node2 : Member cluster3 := ⟨2, by decide⟩

theorem singleton_not_quorum : ¬ IsQuorum cluster3 1 [node2] := by unfold IsQuorum; decide

abbrev S := State (Member cluster3) (LeaseDurable cluster3 Nat)
  (LeaseVolatile cluster3 Nat) Nat (LeaseMsg cluster3 Nat)
abbrev A := Label (Member cluster3) Nat (LeaseMsg cluster3 Nat) (LeaseCmd cluster3 Nat) Empty

def protocol := quorumLeaseProtocol (Val := Nat) cluster3 1

def start : S := ⟨fun _ => ⟨⟨fun _ => none, fun _ => none⟩, ⟨fun _ => []⟩, .running⟩, [], 0⟩

def grantOut : List (Outgoing (Member cluster3) Nat (LeaseMsg cluster3 Nat)) :=
  [⟨node0, 1, .voteGrant 1 node0⟩]
def grant (actor : Member cluster3) (tid : Nat) : Transmission (Member cluster3) Nat (LeaseMsg cluster3 Nat) :=
  ⟨tid, ⟨actor, node0, 1, .voteGrant 1 node0⟩⟩
def castLabel (actor : Member cluster3) : A := .process actor (.local (.castVote 1 node0)) grantOut

def castState (s : S) (actor : Member cluster3) : S :=
  ⟨setNode s.nodes actor
    ⟨{ (s.nodes actor).durable with
        votedFor := fun e => if e = 1 then some node0 else (s.nodes actor).durable.votedFor e },
      (s.nodes actor).volatile, .running⟩,
    s.pending ++ allocate actor s.next grantOut, s.next + 1⟩

def grantState (s : S) (sender : Member cluster3)
    (rest : List (Transmission (Member cluster3) Nat (LeaseMsg cluster3 Nat))) : S :=
  ⟨setNode s.nodes node0
    ⟨(s.nodes node0).durable,
      ⟨fun e => if e = 1 then
        (if sender ∈ (s.nodes node0).volatile.collectedVotes 1 then
          (s.nodes node0).volatile.collectedVotes 1 else sender :: (s.nodes node0).volatile.collectedVotes 1)
        else (s.nodes node0).volatile.collectedVotes e⟩, .running⟩,
    rest, s.next⟩

def crashState (s : S) : S :=
  ⟨setNode s.nodes node2 ⟨(s.nodes node2).durable, ⟨fun _ => []⟩, .crashed⟩, s.pending, s.next⟩
def recoverState (s : S) : S :=
  ⟨setNode s.nodes node2 ⟨(s.nodes node2).durable, ⟨fun _ => []⟩, .running⟩, s.pending, s.next⟩

def commitOut : List (Outgoing (Member cluster3) Nat (LeaseMsg cluster3 Nat)) :=
  [⟨node1, 1, .fencedCommit 1 node0 42⟩]
def commitLabel : A := .process node0 (.local (.acquireAndCommit 1 42 [node1])) commitOut
def commitState (s : S) : S :=
  ⟨setNode s.nodes node0
    ⟨{ (s.nodes node0).durable with
        committed := fun e => if e = 1 then some (node0, 42) else (s.nodes node0).durable.committed e },
      (s.nodes node0).volatile, .running⟩,
    s.pending ++ allocate node0 s.next commitOut, s.next + 1⟩
def commitMessage (tid : Nat) : Transmission (Member cluster3) Nat (LeaseMsg cluster3 Nat) :=
  ⟨tid, ⟨node0, node1, 1, .fencedCommit 1 node0 42⟩⟩
def followerState (s : S) : S :=
  ⟨setNode s.nodes node1
    ⟨{ (s.nodes node1).durable with
        committed := fun e => if e = 1 then some (node0, 42) else (s.nodes node1).durable.committed e },
      (s.nodes node1).volatile, .running⟩, [], s.next⟩

def voted0 := castState start node0
def voted1 := castState voted0 node1
def delivered0 := grantState voted1 node0 [grant node1 1]
def delivered1 := grantState delivered0 node1 []
def crashed := crashState delivered1
def recovered := recoverState crashed
def committed := commitState recovered
def final := followerState committed

theorem initial (fp : FaultProfile) : (system cluster3 protocol fp).init start :=
  ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

theorem cast0_step (fp : FaultProfile) : Step cluster3 protocol fp start (castLabel node0) voted0 :=
  .process rfl (.castVote rfl) (.refl _)
theorem cast1_step (fp : FaultProfile) : Step cluster3 protocol fp voted0 (castLabel node1) voted1 :=
  .process rfl (.castVote rfl) (.refl _)
theorem grant0_step (fp : FaultProfile) : Step cluster3 protocol fp voted1 (.deliver (grant node0 0) []) delivered0 :=
  .deliver rfl (.refl _) (.voteGrant rfl) (.refl _)
theorem grant1_step (fp : FaultProfile) : Step cluster3 protocol fp delivered0 (.deliver (grant node1 1) []) delivered1 :=
  .deliver rfl (.refl _) (.voteGrant rfl) (.refl _)
theorem crash_step : Step cluster3 protocol .crashRecovery delivered1 (.crash node2) crashed :=
  .crash rfl rfl
theorem recover_step : Step cluster3 protocol .crashRecovery crashed (.recover node2) recovered :=
  .recover rfl rfl
theorem commit_step (fp : FaultProfile) : Step cluster3 protocol fp recovered commitLabel committed :=
  .process rfl (.acquireAndCommit (by unfold IsQuorum; decide) rfl) (.refl _)
theorem follower_step (fp : FaultProfile) : Step cluster3 protocol fp committed (.deliver (commitMessage 2) []) final :=
  .deliver rfl (.refl _) (.fencedCommit rfl rfl) (.refl _)

def crashRecoveryLabels : List (A × A) :=
  [(castLabel node0, castLabel node0), (castLabel node1, castLabel node1),
   (.deliver (grant node0 0) [], .deliver (grant node0 0) []),
   (.deliver (grant node1 1) [], .deliver (grant node1 1) []),
   (.crash node2, .crash node2), (.recover node2, .recover node2),
   (commitLabel, commitLabel), (.deliver (commitMessage 2) [], .deliver (commitMessage 2) [])]

theorem crashRecovery_trace : Foundation.Execution (system cluster3 protocol .crashRecovery)
    start crashRecoveryLabels final :=
  .cons ⟨cast0_step _, rfl⟩ (.cons ⟨cast1_step _, rfl⟩
    (.cons ⟨grant0_step _, rfl⟩ (.cons ⟨grant1_step _, rfl⟩
      (.cons ⟨crash_step, rfl⟩ (.cons ⟨recover_step, rfl⟩
        (.cons ⟨commit_step _, rfl⟩ (.cons ⟨follower_step _, rfl⟩ .nil)))))))

theorem crashRecovery_reachable : Foundation.Reachable (system cluster3 protocol .crashRecovery) final :=
  Foundation.execution_reachable (initial _) crashRecovery_trace

theorem crashRecovery_commits :
    (final.nodes node0).durable.committed 1 = some (node0, 42) ∧
    (final.nodes node1).durable.committed 1 = some (node0, 42) := by decide

-- The omission trace gives the duplicate a fresh transport ID, then drops that copy.
def duplicated : S := ⟨voted0.nodes, [grant node0 1, grant node0 0], 2⟩
def dropped : S := ⟨voted0.nodes, [grant node0 0], 2⟩
def omissionVoted := castState dropped node1
def omissionGrant0 := grantState omissionVoted node0 [grant node1 2]
def omissionGrant1 := grantState omissionGrant0 node1 []
def omissionCrashed := crashState omissionGrant1
def omissionRecovered := recoverState omissionCrashed
def omissionCommitted := commitState omissionRecovered
def omissionFinal := followerState omissionCommitted

theorem duplicate_step : Step cluster3 protocol .omission voted0 (.duplicate (grant node0 0)) duplicated :=
  .duplicate rfl (by simp [voted0, castState, start, grantOut, allocate, grant]) (.refl _)
theorem drop_step : Step cluster3 protocol .omission duplicated (.drop (grant node0 1)) dropped :=
  .drop rfl (.refl _)
theorem omission_cast1 : Step cluster3 protocol .omission dropped (castLabel node1) omissionVoted :=
  .process rfl (.castVote rfl) (.refl _)
theorem omission_grant0 : Step cluster3 protocol .omission omissionVoted (.deliver (grant node0 0) []) omissionGrant0 :=
  .deliver rfl (.refl _) (.voteGrant rfl) (.refl _)
theorem omission_grant1 : Step cluster3 protocol .omission omissionGrant0 (.deliver (grant node1 2) []) omissionGrant1 :=
  .deliver rfl (.refl _) (.voteGrant rfl) (.refl _)
theorem omission_crash : Step cluster3 protocol .omission omissionGrant1 (.crash node2) omissionCrashed :=
  .crash rfl rfl
theorem omission_recover : Step cluster3 protocol .omission omissionCrashed (.recover node2) omissionRecovered :=
  .recover rfl rfl
theorem omission_commit : Step cluster3 protocol .omission omissionRecovered commitLabel omissionCommitted :=
  .process rfl (.acquireAndCommit (by unfold IsQuorum; decide) rfl) (.refl _)
theorem omission_follower : Step cluster3 protocol .omission omissionCommitted (.deliver (commitMessage 3) []) omissionFinal :=
  .deliver rfl (.refl _) (.fencedCommit rfl rfl) (.refl _)

def omissionLabels : List (A × A) :=
  [(castLabel node0, castLabel node0), (.duplicate (grant node0 0), .duplicate (grant node0 0)),
   (.drop (grant node0 1), .drop (grant node0 1)), (castLabel node1, castLabel node1),
   (.deliver (grant node0 0) [], .deliver (grant node0 0) []),
   (.deliver (grant node1 2) [], .deliver (grant node1 2) []),
   (.crash node2, .crash node2), (.recover node2, .recover node2),
   (commitLabel, commitLabel), (.deliver (commitMessage 3) [], .deliver (commitMessage 3) [])]

theorem omission_trace : Foundation.Execution (system cluster3 protocol .omission)
    start omissionLabels omissionFinal :=
  .cons ⟨cast0_step _, rfl⟩ (.cons ⟨duplicate_step, rfl⟩ (.cons ⟨drop_step, rfl⟩
    (.cons ⟨omission_cast1, rfl⟩ (.cons ⟨omission_grant0, rfl⟩ (.cons ⟨omission_grant1, rfl⟩
      (.cons ⟨omission_crash, rfl⟩ (.cons ⟨omission_recover, rfl⟩
        (.cons ⟨omission_commit, rfl⟩ (.cons ⟨omission_follower, rfl⟩ .nil)))))))))

theorem omission_reachable : Foundation.Reachable (system cluster3 protocol .omission) omissionFinal :=
  Foundation.execution_reachable (initial _) omission_trace

theorem omission_commits :
    (omissionFinal.nodes node0).durable.committed 1 = some (node0, 42) ∧
    (omissionFinal.nodes node1).durable.committed 1 = some (node0, 42) := by decide

-- A singleton candidate cannot pass the concrete protocol's acquisition guard.
def singletonState : S :=
  ⟨fun _ => ⟨⟨fun _ => none, fun _ => none⟩, ⟨fun _ => [node2]⟩, .running⟩, [], 0⟩
theorem singleton_cannot_commit (fp : FaultProfile) (outs) (t : S) :
    ¬ Step cluster3 protocol fp singletonState
      (.process node2 (.local (.acquireAndCommit 1 42 [node1])) outs) t := by
  intro h
  cases h with
  | process _ reaction _ =>
    cases reaction with
    | acquireAndCommit quorum _ => exact singleton_not_quorum quorum

def cluster5 : Config Nat := ⟨[0, 1, 2, 3, 4], by decide⟩
def m0 : Member cluster5 := ⟨0, by decide⟩
def m1 : Member cluster5 := ⟨1, by decide⟩
def m2 : Member cluster5 := ⟨2, by decide⟩
def m3 : Member cluster5 := ⟨3, by decide⟩
def m4 : Member cluster5 := ⟨4, by decide⟩
def q1 : List (Member cluster5) := [m0, m1, m2, m3]
def q2 : List (Member cluster5) := [m1, m2, m3, m4]
theorem cluster5_strict : 2 * 1 + 1 < cluster5.members.length := by decide
theorem cluster5_not_exact_bound : ¬ cluster5.members.length ≤ 2 * 1 + 1 := by decide
theorem cluster5_q1 : IsQuorum cluster5 1 q1 := by unfold IsQuorum; decide
theorem cluster5_q2 : IsQuorum cluster5 1 q2 := by unfold IsQuorum; decide
theorem cluster5_intersection : ∃ voter, voter ∈ q1 ∧ voter ∈ q2 :=
  quorum_voters_intersect cluster5 1 q1 q2 cluster5_q1 cluster5_q2



namespace Atomic
open TwoPhaseCommit
abbrev S := TwoPCState cluster3
abbrev A := TwoPCLabel cluster3
def protocol := twoPCProtocol cluster3 node0
def start : S := ⟨fun _ => ⟨⟨fun _ => none,fun _ => none,fun _ => none⟩,⟨fun _ => []⟩,.running⟩,[],0⟩
def applyLocal (s : S) (actor : Member cluster3) (d : TwoPCDurable cluster3)
    (v : TwoPCVolatile cluster3) (outs : List (Outgoing (Member cluster3) Nat (TwoPCMsg cluster3))) : S :=
  ⟨setNode s.nodes actor ⟨d,v,.running⟩,s.pending ++ allocate actor s.next outs,s.next + outs.length⟩
def receive (s : S) (actor : Member cluster3) (d : TwoPCDurable cluster3)
    (v : TwoPCVolatile cluster3) (rest : List (Transmission (Member cluster3) Nat (TwoPCMsg cluster3)))
    (outs : List (Outgoing (Member cluster3) Nat (TwoPCMsg cluster3))) : S :=
  ⟨setNode s.nodes actor ⟨d,v,.running⟩,rest ++ allocate actor s.next outs,s.next + outs.length⟩
def voteOut (yes : Bool) : List (Outgoing (Member cluster3) Nat (TwoPCMsg cluster3)) :=
  [⟨node0,1,if yes then .voteYes 1 else .voteNo 1⟩]
def vote (s : S) (actor : Member cluster3) (yes : Bool) : S :=
  applyLocal s actor
    { (s.nodes actor).durable with
      voted := fun k => if k = 1 then some yes else (s.nodes actor).durable.voted k,
      outcome := if yes then (s.nodes actor).durable.outcome else
        fun k => if k = 1 then some false else (s.nodes actor).durable.outcome k }
    (s.nodes actor).volatile (voteOut yes)
def voteMsg (actor : Member cluster3) (id : Nat) (yes : Bool) : Transmission (Member cluster3) Nat (TwoPCMsg cluster3) :=
  ⟨id,actor,node0,1,if yes then .voteYes 1 else .voteNo 1⟩
def collect (s : S) (sender : Member cluster3) (rest : List (Transmission (Member cluster3) Nat (TwoPCMsg cluster3))) : S :=
  receive s node0 (s.nodes node0).durable
    ⟨fun k => if k = 1 then
      (if sender ∈ (s.nodes node0).volatile.yesVoters 1 then (s.nodes node0).volatile.yesVoters 1
       else sender :: (s.nodes node0).volatile.yesVoters 1) else (s.nodes node0).volatile.yesVoters k⟩ rest []
def decideOut (b : Bool) (peers : List (Member cluster3)) : List (Outgoing (Member cluster3) Nat (TwoPCMsg cluster3)) :=
  peers.map fun peer => ⟨peer,1,.decide 1 b⟩
def decideDurable (s : S) (b : Bool) : TwoPCDurable cluster3 :=
  { (s.nodes node0).durable with
    coordDecision := fun k => if k = 1 then some b else (s.nodes node0).durable.coordDecision k,
    outcome := fun k => if k = 1 then some b else (s.nodes node0).durable.outcome k }
def decideMsg (actor : Member cluster3) (id : Nat) (b : Bool) : Transmission (Member cluster3) Nat (TwoPCMsg cluster3) :=
  ⟨id,node0,actor,1,.decide 1 b⟩
def follower (s : S) (actor : Member cluster3) (b : Bool) (rest : List (Transmission (Member cluster3) Nat (TwoPCMsg cluster3))) : S :=
  receive s actor { (s.nodes actor).durable with
    outcome := fun k => if k = 1 then some b else (s.nodes actor).durable.outcome k }
    (s.nodes actor).volatile rest []
def voted0 := vote start node0 true
def voted1 := vote voted0 node1 true
def voted2 := vote voted1 node2 true
def collected0 := collect voted2 node0 [voteMsg node1 1 true,voteMsg node2 2 true]
def collected1 := collect collected0 node1 [voteMsg node2 2 true]
def collected2 := collect collected1 node2 []
def crashed : S := ⟨setNode collected2.nodes node2
  ⟨(collected2.nodes node2).durable,⟨fun _ => []⟩,.crashed⟩,collected2.pending,collected2.next⟩
def recovered : S := ⟨setNode crashed.nodes node2
  ⟨(crashed.nodes node2).durable,⟨fun _ => []⟩,.running⟩,crashed.pending,crashed.next⟩
def committed := applyLocal recovered node0 (decideDurable recovered true)
  (recovered.nodes node0).volatile (decideOut true [node1,node2])
def final := follower committed node1 true [decideMsg node2 4 true]
theorem initial (fp : FaultProfile) : (system cluster3 protocol fp).init start :=
  ⟨rfl,rfl,fun _ => ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
theorem vote0_step : Step cluster3 protocol .crashRecovery start (.process node0 (.local (.castVoteYes 1)) (voteOut true)) voted0 :=
  .process rfl (.castVoteYes rfl rfl) (.refl _)
theorem vote1_step : Step cluster3 protocol .crashRecovery voted0 (.process node1 (.local (.castVoteYes 1)) (voteOut true)) voted1 :=
  .process rfl (.castVoteYes rfl rfl) (.refl _)
theorem vote2_step : Step cluster3 protocol .crashRecovery voted1 (.process node2 (.local (.castVoteYes 1)) (voteOut true)) voted2 :=
  .process rfl (.castVoteYes rfl rfl) (.refl _)
theorem collect0_step : Step cluster3 protocol .crashRecovery voted2 (.deliver (voteMsg node0 0 true) []) collected0 :=
  .deliver rfl (.refl _) (.recvVoteYes rfl) (.refl _)
theorem collect1_step : Step cluster3 protocol .crashRecovery collected0 (.deliver (voteMsg node1 1 true) []) collected1 :=
  .deliver rfl (.refl _) (.recvVoteYes rfl) (.refl _)
theorem collect2_step : Step cluster3 protocol .crashRecovery collected1 (.deliver (voteMsg node2 2 true) []) collected2 :=
  .deliver rfl (.refl _) (.recvVoteYes rfl) (.refl _)
theorem crash_step : Step cluster3 protocol .crashRecovery collected2 (.crash node2) crashed :=
  .crash rfl rfl
theorem recover_step : Step cluster3 protocol .crashRecovery crashed (.recover node2) recovered :=
  .recover rfl rfl
theorem commit_step : Step cluster3 protocol .crashRecovery recovered (.process node0 (.local (.coordCommit 1 [node1,node2])) (decideOut true [node1,node2])) committed :=
  .process rfl (.coordCommit rfl (by unfold IsAllMembers; decide) rfl rfl) (.refl _)
theorem follower_step : Step cluster3 protocol .crashRecovery committed (.deliver (decideMsg node1 3 true) []) final :=
  .deliver rfl (.refl _) (.recvDecide rfl rfl) (.refl _)
def twoPC_commit_traceLabels : List (A × A) :=
  [(.process node0 (.local (.castVoteYes 1)) (voteOut true),.process node0 (.local (.castVoteYes 1)) (voteOut true)),
   (.process node1 (.local (.castVoteYes 1)) (voteOut true),.process node1 (.local (.castVoteYes 1)) (voteOut true)),
   (.process node2 (.local (.castVoteYes 1)) (voteOut true),.process node2 (.local (.castVoteYes 1)) (voteOut true)),
   (.deliver (voteMsg node0 0 true) [],.deliver (voteMsg node0 0 true) []),
   (.deliver (voteMsg node1 1 true) [],.deliver (voteMsg node1 1 true) []),
   (.deliver (voteMsg node2 2 true) [],.deliver (voteMsg node2 2 true) []),
   (.crash node2,.crash node2),
   (.recover node2,.recover node2),
   (.process node0 (.local (.coordCommit 1 [node1,node2])) (decideOut true [node1,node2]),.process node0 (.local (.coordCommit 1 [node1,node2])) (decideOut true [node1,node2])),
   (.deliver (decideMsg node1 3 true) [],.deliver (decideMsg node1 3 true) [])]
theorem twoPC_commit_trace : Foundation.Execution (system cluster3 protocol .crashRecovery) start twoPC_commit_traceLabels final :=
  .cons ⟨vote0_step,rfl⟩ (.cons ⟨vote1_step,rfl⟩ (.cons ⟨vote2_step,rfl⟩ (.cons ⟨collect0_step,rfl⟩ (.cons ⟨collect1_step,rfl⟩ (.cons ⟨collect2_step,rfl⟩ (.cons ⟨crash_step,rfl⟩ (.cons ⟨recover_step,rfl⟩ (.cons ⟨commit_step,rfl⟩ (.cons ⟨follower_step,rfl⟩ (.nil))))))))))
theorem twoPC_commit_outcomes : (final.nodes node0).durable.outcome 1 = some true ∧
    (final.nodes node1).durable.outcome 1 = some true := by decide

def noVoted := vote start node1 false
def aborted := receive noVoted node0 (decideDurable noVoted false) (noVoted.nodes node0).volatile
  [] (decideOut false cluster3.members.attach)
def abortFinal := follower aborted node2 false [decideMsg node0 1 false,decideMsg node1 2 false]
theorem no_step : Step cluster3 protocol .reliable start (.process node1 (.local (.castVoteNo 1)) (voteOut false)) noVoted :=
  .process rfl (.castVoteNo (by decide) rfl rfl) (.refl _)
theorem abort_step : Step cluster3 protocol .reliable noVoted (.deliver (voteMsg node1 0 false) (decideOut false cluster3.members.attach)) aborted :=
  .deliver rfl (.refl _) (.recvVoteNo rfl rfl rfl) (.refl _)
theorem abort_follower_step : Step cluster3 protocol .reliable aborted (.deliver (decideMsg node2 3 false) []) abortFinal :=
  .deliver rfl (Take.middle [decideMsg node0 1 false,decideMsg node1 2 false] [] _) (.recvDecide rfl rfl) (.refl _)
def twoPC_abort_traceLabels : List (A × A) :=
  [(.process node1 (.local (.castVoteNo 1)) (voteOut false),.process node1 (.local (.castVoteNo 1)) (voteOut false)),
   (.deliver (voteMsg node1 0 false) (decideOut false cluster3.members.attach),.deliver (voteMsg node1 0 false) (decideOut false cluster3.members.attach)),
   (.deliver (decideMsg node2 3 false) [],.deliver (decideMsg node2 3 false) [])]
theorem twoPC_abort_trace : Foundation.Execution (system cluster3 protocol .reliable) start twoPC_abort_traceLabels abortFinal :=
  .cons ⟨no_step,rfl⟩ (.cons ⟨abort_step,rfl⟩ (.cons ⟨abort_follower_step,rfl⟩ (.nil)))
theorem twoPC_abort_outcomes : (abortFinal.nodes node0).durable.outcome 1 = some false ∧
    (abortFinal.nodes node1).durable.outcome 1 = some false ∧
    (abortFinal.nodes node2).durable.outcome 1 = some false := by decide

theorem partial_not_unanimous : ¬ IsAllMembers cluster3 [node0,node1] := by unfold IsAllMembers; decide

def partialState : S := ⟨fun _ => ⟨⟨fun _ => none,fun _ => none,fun _ => none⟩,
  ⟨fun _ => [node0,node1]⟩,.running⟩,[],0⟩
theorem twoPC_partial_cannot_commit (fp : FaultProfile) (outs) (t : S) :
    ¬ Step cluster3 protocol fp partialState (.process node0 (.local (.coordCommit 1 [node1,node2])) outs) t := by
  intro hs
  cases hs with
  | process _ reaction _ =>
    cases reaction with
    | coordCommit _ quorum _ _ => exact partial_not_unanimous quorum

theorem twoPC_coord_cannot_castVoteNo (fp : FaultProfile) (s t : S) (outs) :
    ¬ Step cluster3 protocol fp s (.process node0 (.local (.castVoteNo 1)) outs) t := by
  intro hs
  cases hs with
  | process _ reaction _ =>
    cases reaction with
    | castVoteNo ha _ _ => exact ha rfl
end Atomic

namespace Byzantine
open BFTQuorumCommit

def cluster4 : Config Nat := ⟨[0,1,2,3],by decide⟩
def bnode0 : Member cluster4 := ⟨0,by decide⟩
def bnode1 : Member cluster4 := ⟨1,by decide⟩
def bnode2 : Member cluster4 := ⟨2,by decide⟩
def bnode3 : Member cluster4 := ⟨3,by decide⟩
def faulty : List (Member cluster4) := [bnode3]
theorem fault_bound : FaultyBounded cluster4 1 faulty := by unfold FaultyBounded; decide
abbrev S := BFTState cluster4 Nat
abbrev A := BFTLabel cluster4 Nat
def protocol := bftCommitProtocol (Val := Nat) cluster4 1 faulty
def start : S := ⟨fun _ => ⟨⟨fun _ => none,fun _ => none⟩,⟨fun _ _ => []⟩,.running⟩,[],0⟩
def applyLocal (s : S) (actor : Member cluster4) (d : BFTDurable cluster4 Nat)
    (v : BFTVolatile cluster4 Nat) (outs : List (Outgoing (Member cluster4) Nat (BFTMsg cluster4 Nat))) : S :=
  ⟨setNode s.nodes actor ⟨d,v,.running⟩,s.pending ++ allocate actor s.next outs,s.next + outs.length⟩
def receive (s : S) (actor : Member cluster4) (d : BFTDurable cluster4 Nat)
    (v : BFTVolatile cluster4 Nat) (rest : List (Transmission (Member cluster4) Nat (BFTMsg cluster4 Nat)))
    (outs : List (Outgoing (Member cluster4) Nat (BFTMsg cluster4 Nat))) : S :=
  ⟨setNode s.nodes actor ⟨d,v,.running⟩,rest ++ allocate actor s.next outs,s.next + outs.length⟩
def voteOut (proposer : Member cluster4) (val : Nat) : List (Outgoing (Member cluster4) Nat (BFTMsg cluster4 Nat)) :=
  [⟨proposer,1,.vote 1 proposer val⟩]
def voteMsg (sender proposer : Member cluster4) (val id : Nat) : Transmission (Member cluster4) Nat (BFTMsg cluster4 Nat) :=
  ⟨id,sender,proposer,1,.vote 1 proposer val⟩
def equivocate (s : S) (proposer : Member cluster4) (val : Nat) : S :=
  applyLocal s bnode3 (s.nodes bnode3).durable (s.nodes bnode3).volatile (voteOut proposer val)
def vote (s : S) (actor : Member cluster4) : S :=
  applyLocal s actor { (s.nodes actor).durable with
    votedFor := fun k => if k = 1 then some (bnode0,10) else (s.nodes actor).durable.votedFor k }
    (s.nodes actor).volatile (voteOut bnode0 10)
def collect (s : S) (sender : Member cluster4)
    (rest : List (Transmission (Member cluster4) Nat (BFTMsg cluster4 Nat))) : S :=
  receive s bnode0 (s.nodes bnode0).durable
    ⟨fun k val => if k = 1 ∧ val = 10 then
      (if sender ∈ (s.nodes bnode0).volatile.tally 1 10 then (s.nodes bnode0).volatile.tally 1 10
       else sender :: (s.nodes bnode0).volatile.tally 1 10) else (s.nodes bnode0).volatile.tally k val⟩ rest []
def bad0 := equivocate start bnode0 10
def bad1 := equivocate bad0 bnode1 99
def voted0 := vote bad1 bnode0
def voted1 := vote voted0 bnode1
def collected3 := collect voted1 bnode3 [voteMsg bnode3 bnode1 99 1,voteMsg bnode0 bnode0 10 2,voteMsg bnode1 bnode0 10 3]
def collected1 := collect collected3 bnode1 [voteMsg bnode3 bnode1 99 1,voteMsg bnode0 bnode0 10 2]
def collected0 := collect collected1 bnode0 [voteMsg bnode3 bnode1 99 1]
def commitOut : List (Outgoing (Member cluster4) Nat (BFTMsg cluster4 Nat)) := [⟨bnode1,1,.commitQC 1 bnode0 10⟩]
def commitMsg : Transmission (Member cluster4) Nat (BFTMsg cluster4 Nat) := ⟨4,bnode0,bnode1,1,.commitQC 1 bnode0 10⟩
def committed := applyLocal collected0 bnode0
  { (collected0.nodes bnode0).durable with
    committed := fun k => if k = 1 then some (bnode0,10) else (collected0.nodes bnode0).durable.committed k }
  (collected0.nodes bnode0).volatile commitOut
def final := receive committed bnode1
  { (committed.nodes bnode1).durable with
    committed := fun k => if k = 1 then some (bnode0,10) else (committed.nodes bnode1).durable.committed k }
  (committed.nodes bnode1).volatile [voteMsg bnode3 bnode1 99 1] []
theorem initial : (system cluster4 protocol .omission).init start :=
  ⟨rfl,rfl,fun _ => ⟨rfl,rfl,rfl,rfl⟩⟩
theorem bad0_step : Step cluster4 protocol .omission start (.process bnode3 (.local (.byzantineEquivocate 1 bnode0 10)) (voteOut bnode0 10)) bad0 :=
  .process rfl (.byzantineEquivocate (by decide)) (.refl _)
theorem bad1_step : Step cluster4 protocol .omission bad0 (.process bnode3 (.local (.byzantineEquivocate 1 bnode1 99)) (voteOut bnode1 99)) bad1 :=
  .process rfl (.byzantineEquivocate (by decide)) (.refl _)
theorem vote0_step : Step cluster4 protocol .omission bad1 (.process bnode0 (.local (.castHonestVote 1 bnode0 10)) (voteOut bnode0 10)) voted0 :=
  .process rfl (.castHonestVote rfl) (.refl _)
theorem vote1_step : Step cluster4 protocol .omission voted0 (.process bnode1 (.local (.castHonestVote 1 bnode0 10)) (voteOut bnode0 10)) voted1 :=
  .process rfl (.castHonestVote rfl) (.refl _)
theorem collect3_step : Step cluster4 protocol .omission voted1 (.deliver (voteMsg bnode3 bnode0 10 0) []) collected3 :=
  .deliver rfl (.refl _) (.recvVote rfl) (.refl _)
theorem collect1_step : Step cluster4 protocol .omission collected3 (.deliver (voteMsg bnode1 bnode0 10 3) []) collected1 :=
  .deliver rfl (Take.middle [voteMsg bnode3 bnode1 99 1,voteMsg bnode0 bnode0 10 2] [] _) (.recvVote rfl) (.refl _)
theorem collect0_step : Step cluster4 protocol .omission collected1 (.deliver (voteMsg bnode0 bnode0 10 2) []) collected0 :=
  .deliver rfl (Take.middle [voteMsg bnode3 bnode1 99 1] [] _) (.recvVote rfl) (.refl _)
theorem commit_step : Step cluster4 protocol .omission collected0 (.process bnode0 (.local (.formQCAndCommit 1 10 [bnode1])) commitOut) committed :=
  .process rfl (.formQCAndCommit (by unfold IsBFTQuorum; decide) rfl) (.refl _)
theorem follower_step : Step cluster4 protocol .omission committed (.deliver commitMsg []) final :=
  .deliver rfl (Take.middle [voteMsg bnode3 bnode1 99 1] [] _) (.recvCommitQC rfl rfl) (.refl _)
def bft_equivocation_labels : List (A × A) :=
  [(.process bnode3 (.local (.byzantineEquivocate 1 bnode0 10)) (voteOut bnode0 10),.process bnode3 (.local (.byzantineEquivocate 1 bnode0 10)) (voteOut bnode0 10)),
   (.process bnode3 (.local (.byzantineEquivocate 1 bnode1 99)) (voteOut bnode1 99),.process bnode3 (.local (.byzantineEquivocate 1 bnode1 99)) (voteOut bnode1 99)),
   (.process bnode0 (.local (.castHonestVote 1 bnode0 10)) (voteOut bnode0 10),.process bnode0 (.local (.castHonestVote 1 bnode0 10)) (voteOut bnode0 10)),
   (.process bnode1 (.local (.castHonestVote 1 bnode0 10)) (voteOut bnode0 10),.process bnode1 (.local (.castHonestVote 1 bnode0 10)) (voteOut bnode0 10)),
   (.deliver (voteMsg bnode3 bnode0 10 0) [],.deliver (voteMsg bnode3 bnode0 10 0) []),
   (.deliver (voteMsg bnode1 bnode0 10 3) [],.deliver (voteMsg bnode1 bnode0 10 3) []),
   (.deliver (voteMsg bnode0 bnode0 10 2) [],.deliver (voteMsg bnode0 bnode0 10 2) []),
   (.process bnode0 (.local (.formQCAndCommit 1 10 [bnode1])) commitOut,.process bnode0 (.local (.formQCAndCommit 1 10 [bnode1])) commitOut),
   (.deliver commitMsg [],.deliver commitMsg [])]
theorem bft_equivocation_trace : Foundation.Execution (system cluster4 protocol .omission) start bft_equivocation_labels final :=
  .cons ⟨bad0_step,rfl⟩ (.cons ⟨bad1_step,rfl⟩ (.cons ⟨vote0_step,rfl⟩ (.cons ⟨vote1_step,rfl⟩ (.cons ⟨collect3_step,rfl⟩ (.cons ⟨collect1_step,rfl⟩ (.cons ⟨collect0_step,rfl⟩ (.cons ⟨commit_step,rfl⟩ (.cons ⟨follower_step,rfl⟩ (.nil)))))))))
theorem bft_equivocation_commits :
    (final.nodes bnode0).durable.committed 1 = some (bnode0,10) ∧
    (final.nodes bnode1).durable.committed 1 = some (bnode0,10) := by decide

theorem bft_equivocation_reachable : Foundation.Reachable (system cluster4 protocol .omission) final :=
  Foundation.execution_reachable initial bft_equivocation_trace

theorem bft_honest_cannot_equivocate (fp : FaultProfile) (s t : S) (outs) :
    ¬ Step cluster4 protocol fp s (.process bnode0 (.local (.byzantineEquivocate 1 bnode1 99)) outs) t := by
  intro hs
  cases hs with
  | process _ reaction _ =>
    cases reaction with
    | byzantineEquivocate hf => exact (by decide : bnode0 ∉ faulty) hf

theorem subquorum : ¬ IsBFTQuorum cluster4 1 [bnode0,bnode1] := by unfold IsBFTQuorum; decide
def partialState : S := ⟨fun _ => ⟨⟨fun _ => none,fun _ => none⟩,
  ⟨fun _ _ => [bnode0,bnode1]⟩,.running⟩,[],0⟩
theorem bft_subquorum_cannot_commit (fp : FaultProfile) (outs) (t : S) :
    ¬ Step cluster4 protocol fp partialState (.process bnode0 (.local (.formQCAndCommit 1 10 [bnode1])) outs) t := by
  intro hs
  cases hs with
  | process _ reaction _ =>
    cases reaction with
    | formQCAndCommit quorum _ => exact subquorum quorum

/-- A distinct collector is refused even for a hypothetical quorum-sized tally. -/
theorem bft_second_proposer_refusal_of_inv (s t : S) (hi : BFTCommitInv cluster4 1 faulty s)
    (cert : BFTCertified cluster4 1 faulty s 1 bnode0 10) (fp : FaultProfile) (outs) :
    ¬ Step cluster4 protocol fp s (.process bnode1 (.local (.formQCAndCommit 1 99 [bnode2])) outs) t := by
  intro hs
  cases hs with
  | process _ reaction _ =>
    cases reaction with
    | formQCAndCommit quorum _ =>
      obtain ⟨_,Q,hq,hv⟩ := cert
      have he := bft_quorum_candidates_unique fault_bound quorum hq
        (hi.tally_honest_valid bnode1 1 99) hv
      exact (by decide : bnode1 ≠ bnode0) he.1

theorem bft_second_proposer_cannot_commit (t : S) (outs) :
    ¬ Step cluster4 protocol .omission final
      (.process bnode1 (.local (.formQCAndCommit 1 99 [bnode2])) outs) t := by
  have hi := reachable_bftCommitInv cluster4 1 faulty .omission bft_equivocation_reachable
  exact bft_second_proposer_refusal_of_inv final t hi
    (hi.qc_has_quorum.2 bnode0 1 bnode0 10 bft_equivocation_commits.1) .omission outs
end Byzantine

end Harmonia.VerifiedProtocols.Tests
