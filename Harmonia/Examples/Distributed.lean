import Harmonia.Distributed.Properties
namespace Harmonia.Distributed.Examples
open Harmonia.Distributed
def pair : Config Nat := ⟨[0,1], by decide⟩
abbrev M := Member pair
def left : M := ⟨0,by decide⟩
def right : M := ⟨1,by decide⟩
def counterProtocol (c : Config Nat) : Protocol (Member c) Nat Nat Nat Unit (Member c) Unit where
  initial _ d v := d = 0 ∧ v = 0
  react _ d v input d' v' outs := match input with
    | .scheduled (.local peer) => d' = d+1 ∧ v' = v+1 ∧ outs = [⟨peer,7,()⟩]
    | .scheduled (.timeout ()) => d' = d ∧ v' = v+1 ∧ outs = []
    | .message _ => d' = d+1 ∧ v' = v+1 ∧ outs = []
  crashReset _ _ := 0
  recover := id
def counting := counterProtocol pair
abbrev S := State M Nat Nat Nat Unit
abbrev A := Label M Nat Unit M Unit
def start : S := ⟨fun _ => ⟨0,0,.running⟩,[],0⟩
def e0 : Transmission M Nat Unit := ⟨0,⟨left,right,7,()⟩⟩
def down : S := ⟨fun _ => ⟨0,0,.crashed⟩,[e0],1⟩
def queued : S := ⟨start.nodes,[e0],1⟩

def sendLabel : A := .process left (.local right) [⟨right,7,()⟩]
def sentState : S := ⟨setNode start.nodes left ⟨1,1,.running⟩,[e0],1⟩
def crashedState : S := ⟨setNode sentState.nodes right ⟨0,0,.crashed⟩,[e0],1⟩
def recoveredState : S := ⟨setNode crashedState.nodes right ⟨0,0,.running⟩,[e0],1⟩
def deliveredState : S := ⟨setNode recoveredState.nodes right ⟨1,1,.running⟩,[],1⟩
def e1 : Transmission M Nat Unit := ⟨1,e0.envelope⟩
def duplicatedState : S := ⟨sentState.nodes,[e1,e0],2⟩
def onceState : S := ⟨setNode duplicatedState.nodes right ⟨1,1,.running⟩,[e0],2⟩
def twiceState : S := ⟨setNode onceState.nodes right ⟨2,2,.running⟩,[],2⟩
def receivedState : S := ⟨setNode sentState.nodes right ⟨1,1,.running⟩,[],1⟩
def lostState : S := ⟨setNode receivedState.nodes right ⟨1,0,.crashed⟩,[],1⟩
def rebuiltState : S := ⟨setNode lostState.nodes right ⟨1,1,.running⟩,[],1⟩

theorem initial : (system pair counting f).init start := ⟨rfl,rfl,fun _ => ⟨rfl,rfl,rfl⟩⟩
theorem send_step : Step pair counting f start sendLabel sentState :=
  .process rfl ⟨rfl,rfl,rfl⟩ (.refl _)
theorem crash_step : Step pair counting .crashRecovery sentState (.crash right) crashedState := by
  exact .crash rfl rfl
theorem recover_step : Step pair counting .crashRecovery crashedState (.recover right) recoveredState := by
  exact .recover rfl rfl
theorem deliver_step : Step pair counting f recoveredState (.deliver e0 []) deliveredState :=
  .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem send_crash_recover_deliver : Foundation.Execution (system pair counting .crashRecovery) start
    [(sendLabel,sendLabel),(.crash right,.crash right),(.recover right,.recover right),
     (.deliver e0 [],.deliver e0 [])] deliveredState :=
  .cons ⟨send_step,rfl⟩ (.cons ⟨crash_step,rfl⟩ (.cons ⟨recover_step,rfl⟩ (.cons ⟨deliver_step,rfl⟩ .nil)))
theorem duplicate_step : Step pair counting .omission sentState (.duplicate e0) duplicatedState :=
  .duplicate rfl (by simp [sentState]) (.refl _)
theorem deliver_copy : Step pair counting f duplicatedState (.deliver e1 []) onceState :=
  .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem deliver_original : Step pair counting f onceState (.deliver e0 []) twiceState :=
  .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem duplicated_delivery : Foundation.Execution (system pair counting .omission) start
    [(sendLabel,sendLabel),(.duplicate e0,.duplicate e0),(.deliver e1 [],.deliver e1 []),
     (.deliver e0 [],.deliver e0 [])] twiceState :=
  .cons ⟨send_step,rfl⟩ (.cons ⟨duplicate_step,rfl⟩ (.cons ⟨deliver_copy,rfl⟩ (.cons ⟨deliver_original,rfl⟩ .nil)))
theorem first_receive : Step pair counting f sentState (.deliver e0 []) receivedState :=
  .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem lose_volatile : Step pair counting .crashRecovery receivedState (.crash right) lostState :=
  .crash rfl rfl
theorem rebuild_volatile : Step pair counting .crashRecovery lostState (.recover right) rebuiltState :=
  .recover rfl rfl
theorem durable_recovery_trace : Foundation.Execution (system pair counting .crashRecovery) start
    [(sendLabel,sendLabel),(.deliver e0 [],.deliver e0 []),(.crash right,.crash right),
     (.recover right,.recover right)] rebuiltState :=
  .cons ⟨send_step,rfl⟩ (.cons ⟨first_receive,rfl⟩ (.cons ⟨lose_volatile,rfl⟩ (.cons ⟨rebuild_volatile,rfl⟩ .nil)))

def retryState : S := ⟨setNode sentState.nodes left ⟨2,2,.running⟩,[e0,e1],2⟩
def retryOnce : S := ⟨setNode retryState.nodes right ⟨1,1,.running⟩,[e0],2⟩
def retryTwice : S := ⟨setNode retryOnce.nodes right ⟨2,2,.running⟩,[],2⟩
theorem retry_step : Step pair counting f sentState sendLabel retryState :=
  .process rfl ⟨rfl,rfl,rfl⟩ (.refl _)
theorem nonhead_receive : Step pair counting f retryState (.deliver e1 []) retryOnce :=
  .deliver rfl (List.Perm.swap e1 e0 []) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem retry_last : Step pair counting f retryOnce (.deliver e0 []) retryTwice :=
  .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem retry_delivery : Foundation.Execution (system pair counting .reliable) start
    [(sendLabel,sendLabel),(sendLabel,sendLabel),(.deliver e1 [],.deliver e1 []),
     (.deliver e0 [],.deliver e0 [])] retryTwice :=
  .cons ⟨send_step,rfl⟩ (.cons ⟨retry_step,rfl⟩ (.cons ⟨nonhead_receive,rfl⟩ (.cons ⟨retry_last,rfl⟩ .nil)))

def malformed : S := ⟨start.nodes,[e0,e0],1⟩
theorem malformed_replay : ∃ t r, Step pair counting .reliable malformed (.deliver e0 []) t ∧
    Step pair counting .reliable t (.deliver e0 []) r := by
  refine ⟨⟨setNode start.nodes right ⟨1,1,.running⟩,[e0],1⟩,
    ⟨setNode (setNode start.nodes right ⟨1,1,.running⟩) right ⟨2,2,.running⟩,[],1⟩,?_,?_⟩
  · exact .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
  · exact .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)

def triple : Config Nat := ⟨[0,1,2],by decide⟩
def first : Member triple := ⟨0,by decide⟩
def second : Member triple := ⟨1,by decide⟩
def third : Member triple := ⟨2,by decide⟩
def tripleStart : State (Member triple) Nat Nat Nat Unit := ⟨fun _ => ⟨0,0,.running⟩,[],0⟩
def tripleMessage : Transmission (Member triple) Nat Unit := ⟨0,⟨first,second,7,()⟩⟩
def tripleSent : State (Member triple) Nat Nat Nat Unit :=
  ⟨setNode tripleStart.nodes first ⟨1,1,.running⟩,[tripleMessage],1⟩
def tripleReceived : State (Member triple) Nat Nat Nat Unit :=
  ⟨setNode tripleSent.nodes second ⟨1,1,.running⟩,[],1⟩
def tripleLost : State (Member triple) Nat Nat Nat Unit :=
  ⟨setNode tripleReceived.nodes second ⟨1,0,.crashed⟩,[],1⟩
def tripleAfter : State (Member triple) Nat Nat Nat Unit :=
  ⟨setNode tripleLost.nodes second ⟨1,1,.running⟩,[],1⟩
theorem triple_send : Step triple (counterProtocol triple) f tripleStart
    (.process first (.local second) [⟨second,7,()⟩]) tripleSent :=
  .process rfl ⟨rfl,rfl,rfl⟩ (.refl _)
theorem triple_receive : Step triple (counterProtocol triple) f tripleSent (.deliver tripleMessage []) tripleReceived :=
  .deliver rfl (.refl _) ⟨rfl,rfl,rfl⟩ (.refl _)
theorem triple_crash : Step triple (counterProtocol triple) .crashRecovery tripleReceived (.crash second) tripleLost :=
  .crash rfl rfl
theorem triple_recover : Step triple (counterProtocol triple) .crashRecovery tripleLost (.recover second) tripleAfter :=
  .recover rfl rfl
end Harmonia.Distributed.Examples
