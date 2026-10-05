import Harmonia.Examples.Distributed
namespace Harmonia.Distributed.Tests.Traces
open Harmonia.Distributed Harmonia.Distributed.Examples
theorem initial_witness : ∃ s, (system pair counting .crashRecovery).init s := ⟨start,initial⟩
theorem inflight : Foundation.Execution (system pair counting .crashRecovery) start
    [(sendLabel,sendLabel),(.crash right,.crash right),(.recover right,.recover right),
     (.deliver e0 [],.deliver e0 [])] deliveredState := send_crash_recover_deliver
theorem duplicate_twice : Foundation.Execution (system pair counting .omission) start
    [(sendLabel,sendLabel),(.duplicate e0,.duplicate e0),(.deliver e1 [],.deliver e1 []),
     (.deliver e0 [],.deliver e0 [])] twiceState := duplicated_delivery
theorem duplicated_count : (twiceState.nodes right).durable = 2 := by decide
theorem volatile_lost : (lostState.nodes right).durable = 1 ∧ (lostState.nodes right).volatile = 0 := by decide
theorem rebuilt : (rebuiltState.nodes right).durable = 1 ∧ (rebuiltState.nodes right).volatile = 1 := by decide
end Harmonia.Distributed.Tests.Traces
namespace Harmonia.Distributed.Tests.Traces
open Harmonia.Distributed Harmonia.Distributed.Examples
theorem retry_trace : Foundation.Execution (system pair counting .reliable) start
  [(sendLabel,sendLabel),(sendLabel,sendLabel),(.deliver e1 [],.deliver e1 []),
   (.deliver e0 [],.deliver e0 [])] retryTwice := retry_delivery
theorem third_frame : (tripleAfter.nodes third).durable = 0 := by decide
theorem raw_malformed_replay : ∃ t r, Step pair counting .reliable malformed (.deliver e0 []) t ∧
    Step pair counting .reliable t (.deliver e0 []) r := malformed_replay
end Harmonia.Distributed.Tests.Traces
namespace Harmonia.Distributed.Tests.Traces
open Harmonia.Distributed Harmonia.Distributed.Examples
theorem inflight_survives : crashedState.pending = sentState.pending ∧ recoveredState.pending = sentState.pending := ⟨rfl,rfl⟩
theorem durable_trace : Foundation.Execution (system pair counting .crashRecovery) start
  [(sendLabel,sendLabel),(.deliver e0 [],.deliver e0 []),(.crash right,.crash right),
   (.recover right,.recover right)] rebuiltState := durable_recovery_trace
theorem duplicate_identity : e1.envelope = e0.envelope ∧ e1.tid ≠ e0.tid := ⟨rfl,by decide⟩
theorem reliable_retry_ids : retryState.pending.map (fun e => (e.tid,e.envelope.logical)) = [(0,7),(1,7)] := rfl
theorem peer_running_timeout : Step pair counting .reliable start (.process left (.timeout ()) [])
    ⟨setNode start.nodes left ⟨0,1,.running⟩,[],0⟩ ∧ (start.nodes right).status = .running :=
  ⟨.process rfl ⟨rfl,rfl,rfl⟩ (.refl _),rfl⟩
theorem nonhead_drop : Step pair counting .omission retryState (.drop e1)
    ⟨retryState.nodes,[e0],2⟩ := .drop rfl (List.Perm.swap e1 e0 [])
def reorderedState : S := ⟨retryState.nodes,[e1,e0],2⟩
theorem reordered_eq : PoolEq retryState reorderedState := ⟨rfl,rfl,List.Perm.swap e1 e0 []⟩
theorem reordered_receive : ∃ t, Step pair counting .reliable reorderedState (.deliver e1 []) t ∧ PoolEq retryOnce t :=
  Step.permutation_lift reordered_eq nonhead_receive

theorem sent_reachable : Foundation.Reachable (system pair counting .reliable) sentState :=
  .step (a := sendLabel) (.init initial) ⟨send_step,rfl⟩
theorem no_spent_replay (r : S) : ¬ Step pair counting .reliable receivedState (.deliver e0 []) r :=
  Step.no_replay_reachable sent_reachable first_receive
theorem malformed_not_reachable : ¬ Foundation.Reachable (system pair counting .reliable) malformed := by
  intro hr
  have hw := reachable_wf hr
  simp [WF,malformed] at hw

theorem receive_keeps_sender : receivedState.nodes left = sentState.nodes left :=
  Step.frame (first_receive (f := .reliable)) left (by decide)
theorem third_unchanged_send : tripleSent.nodes third = tripleStart.nodes third :=
  Step.frame (triple_send (f := .reliable)) third (by decide)
theorem third_unchanged_receive : tripleReceived.nodes third = tripleSent.nodes third :=
  Step.frame (triple_receive (f := .reliable)) third (by decide)
theorem third_unchanged_crash : tripleLost.nodes third = tripleReceived.nodes third :=
  Step.frame triple_crash third (by decide)
theorem third_unchanged_recover : tripleAfter.nodes third = tripleLost.nodes third :=
  Step.frame triple_recover third (by decide)

theorem self_send : Step pair counting .reliable start (.process left (.local left) [⟨left,7,()⟩])
    ⟨setNode start.nodes left ⟨1,1,.running⟩,[⟨0,⟨left,left,7,()⟩⟩],1⟩ :=
  .process rfl ⟨rfl,rfl,rfl⟩ (.refl _)
def multi : Protocol M Nat Nat Nat Unit Unit Unit where
  initial _ d v := d=0 ∧ v=0
  react _ d v _ d' v' outs := d'=d ∧ v'=v ∧ outs=[⟨left,7,()⟩,⟨right,7,()⟩]
  crashReset _ _ := 0
  recover := id
theorem multiple_sends : Step pair multi .reliable start (.process left (.local ()) [⟨left,7,()⟩,⟨right,7,()⟩])
    ⟨setNode start.nodes left ⟨0,0,.running⟩,[⟨0,⟨left,left,7,()⟩⟩,⟨1,⟨left,right,7,()⟩⟩],2⟩ :=
  .process rfl ⟨rfl,rfl,rfl⟩ (.refl _)
def nondeterministic : Protocol M Nat Nat Nat Unit Unit Unit where
  initial _ d v := d=0 ∧ v=0
  react _ d v _ d' v' outs := (d'=d ∨ d'=d+1) ∧ v'=v ∧ outs=[]
  crashReset _ _ := 0
  recover := id
theorem choice_zero : Step pair nondeterministic .reliable start (.process left (.local ()) [])
    ⟨setNode start.nodes left ⟨0,0,.running⟩,[],0⟩ := .process rfl ⟨.inl rfl,rfl,rfl⟩ (.refl _)
theorem choice_one : Step pair nondeterministic .reliable start (.process left (.local ()) [])
    ⟨setNode start.nodes left ⟨1,0,.running⟩,[],0⟩ := .process rfl ⟨.inr rfl,rfl,rfl⟩ (.refl _)
theorem choices_differ : (setNode start.nodes left ⟨0,0,.running⟩ left).durable ≠
    (setNode start.nodes left ⟨1,0,.running⟩ left).durable := by decide
end Harmonia.Distributed.Tests.Traces
