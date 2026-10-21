import Harmonia.VerifiedProtocols.QuorumLease

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

end Harmonia.VerifiedProtocols.Tests
