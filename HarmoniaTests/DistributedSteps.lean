import Harmonia.Distributed.Semantics
namespace Harmonia.Distributed.Tests.Steps
open Harmonia.Distributed

def pair : Config Nat := ⟨[0,1], by decide⟩
abbrev M := Member pair
def left : M := ⟨0,by decide⟩
def right : M := ⟨1,by decide⟩
def counting : Protocol M Nat Nat Nat Unit M Unit where
  initial _ d v := d = 0 ∧ v = 0
  react _ d v input d' v' outs := match input with
    | .scheduled (.local peer) => d' = d+1 ∧ v' = v+1 ∧ outs = [⟨peer,7,()⟩]
    | .scheduled (.timeout ()) => d' = d ∧ v' = v+1 ∧ outs = []
    | .message _ => d' = d+1 ∧ v' = v+1 ∧ outs = []
  crashReset _ _ := 0
  recover := id
abbrev S := State M Nat Nat Nat Unit
abbrev A := Label M Nat Unit M Unit
def start : S := ⟨fun _ => ⟨0,0,.running⟩,[],0⟩
def e0 : Transmission M Nat Unit := ⟨0,⟨left,right,7,()⟩⟩
def down : S := ⟨fun _ => ⟨0,0,.crashed⟩,[e0],1⟩
theorem sent : Step pair counting .reliable start (.process left (.local right) [⟨right,7,()⟩])
    ⟨setNode start.nodes left ⟨1,1,.running⟩,[e0],1⟩ :=
  .process rfl ⟨rfl,rfl,rfl⟩ (List.Perm.refl _)
theorem no_timeout (t : S) : ¬ Step pair counting .omission down (.process right (.timeout ()) []) t :=
  no_process_crashed rfl
theorem no_local (t : S) : ¬ Step pair counting .omission down (.process right (.local left) [⟨left,7,()⟩]) t :=
  no_process_crashed rfl
theorem no_receive (t : S) : ¬ Step pair counting .omission down (.deliver e0 []) t := no_deliver_crashed rfl
theorem no_crash_down (t : S) : ¬ Step pair counting .omission down (.crash right) t := no_crash_crashed rfl
theorem no_recover_running (t : S) : ¬ Step pair counting .omission start (.recover right) t := Harmonia.Distributed.no_recover_running rfl
theorem wrong_process_outs (t : S) : ¬ Step pair counting .omission start (.process left (.local right) []) t := by
  intro h
  cases h with
  | process _ hr _ => simp [counting] at hr
def queued : S := ⟨start.nodes,[e0],1⟩
theorem wrong_deliver_outs (t : S) : ¬ Step pair counting .omission queued (.deliver e0 [⟨left,7,()⟩]) t := by
  intro h
  cases h with
  | deliver _ _ hr _ => simp [counting] at hr
theorem deliver_actor : actorOf (.deliver e0 [] : A) = some right := rfl
theorem drop_actor : actorOf (.drop e0 : A) = none := rfl
theorem duplicate_actor : actorOf (.duplicate e0 : A) = none := rfl
end Harmonia.Distributed.Tests.Steps

namespace Harmonia.Distributed.Tests.Steps
open Harmonia.Distributed
theorem reliable_drop (t : S) : ¬ Step pair counting .reliable queued (.drop e0) t := reliable_no_drop
theorem reliable_dup (t : S) : ¬ Step pair counting .reliable queued (.duplicate e0) t := reliable_no_duplicate
theorem reliable_crash (t : S) : ¬ Step pair counting .reliable start (.crash left) t := reliable_no_crash
theorem reliable_recover (t : S) : ¬ Step pair counting .reliable down (.recover right) t := reliable_no_recover
theorem independent_recover (t : S) : ¬ Step pair counting ⟨false,false,true,false⟩ down (.recover right) t := no_recover_disabled rfl
theorem independent_crash (t : S) : ¬ Step pair counting ⟨false,false,false,true⟩ start (.crash left) t := no_crash_disabled rfl
theorem process_actor : actorOf (.process left (.timeout ()) [] : A) = some left := rfl
theorem crash_actor : actorOf (.crash left : A) = some left := rfl
theorem recover_actor : actorOf (.recover right : A) = some right := rfl
theorem wrong_observation (t : S) : ¬ (system pair counting .omission).step start (.crash left) (.recover left) t := by
  intro h; cases h.2
theorem nonempty_init : ¬ (system pair counting .omission).init queued := by
  intro h; cases h.1
end Harmonia.Distributed.Tests.Steps
namespace Harmonia.Distributed.Tests.Steps
open Harmonia.Distributed
def empty : Config Nat := ⟨[],by decide⟩
theorem empty_member (m : Member empty) : False := by
  have h := m.property; simpa [empty] using h
def emptyProtocol : Protocol (Member empty) Nat Nat Nat Unit Unit Unit where
  initial _ _ _ := False
  react _ _ _ _ _ _ _ := False
  crashReset _ _ := 0
  recover := id
def emptyState : State (Member empty) Nat Nat Nat Unit :=
  ⟨fun m => False.elim (empty_member m),[],0⟩
theorem empty_initial : (system empty emptyProtocol .reliable).init emptyState :=
  ⟨rfl,rfl,fun m => False.elim (empty_member m)⟩
theorem empty_zero : Foundation.Execution (system empty emptyProtocol .reliable) emptyState [] emptyState := .nil
theorem empty_label (a : Label (Member empty) Nat Unit Unit Unit) : False := by
  cases a with
  | process m _ _ => exact empty_member m
  | deliver e _ => exact empty_member e.envelope.sender
  | drop e => exact empty_member e.envelope.sender
  | duplicate e => exact empty_member e.envelope.sender
  | crash m => exact empty_member m
  | recover m => exact empty_member m
theorem empty_no_step (s t : State (Member empty) Nat Nat Nat Unit)
    (a : Label (Member empty) Nat Unit Unit Unit) : ¬ Step empty emptyProtocol .reliable s a t :=
  fun _ => empty_label a
end Harmonia.Distributed.Tests.Steps
