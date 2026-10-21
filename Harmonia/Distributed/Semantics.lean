import Harmonia.Distributed.Network
import Harmonia.Core.Invariant
namespace Harmonia.Distributed
universe u
structure State (M D V L P : Type u) where
  nodes : M → Local D V
  pending : List (Transmission M L P)
  next : Nat
inductive Label (M L P C K : Type u) where
  | process : M → Stimulus C K → List (Outgoing M L P) → Label M L P C K
  | deliver : Transmission M L P → List (Outgoing M L P) → Label M L P C K
  | drop : Transmission M L P → Label M L P C K
  | duplicate : Transmission M L P → Label M L P C K
  | crash : M → Label M L P C K
  | recover : M → Label M L P C K
  deriving DecidableEq

def actorOf : Label M L P C K → Option M
  | .process m _ _ | .crash m | .recover m => some m
  | .deliver e _ => some e.envelope.recipient
  | .drop _ | .duplicate _ => none

def setNode [DecidableEq M] (nodes : M → Local D V) (actor : M) (value : Local D V) : M → Local D V :=
  fun peer => if peer = actor then value else nodes peer
@[simp] theorem setNode_self {M D V : Type u} [DecidableEq M]
    {nodes : M → Local D V} {actor : M} {value : Local D V} : setNode nodes actor value actor = value := by simp [setNode]
theorem setNode_other {M D V : Type u} [DecidableEq M]
    {nodes : M → Local D V} {actor peer : M} {value : Local D V} (h : peer ≠ actor) : setNode nodes actor value peer = nodes peer := by
  simp [setNode,h]

variable {N D V L P C K : Type u} [DecidableEq N]
/-- Local update and publication are atomic in this model, not physical IO.
Supply/IDs are global mathematical bookkeeping, never protocol arguments. -/
inductive Step (c : Config N) (p : Protocol (Member c) D V L P C K) (f : FaultProfile) :
    State (Member c) D V L P → Label (Member c) L P C K → State (Member c) D V L P → Prop where
  | process {s actor stimulus d v outs result}
      (running : (s.nodes actor).status = .running)
      (reaction : p.react actor (s.nodes actor).durable (s.nodes actor).volatile (.scheduled stimulus) d v outs)
      (publish : Publish actor s.next outs s.pending result) :
      Step c p f s (.process actor stimulus outs)
        ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩
  | deliver {s e rest d v outs result}
      (running : (s.nodes e.envelope.recipient).status = .running)
      (take : Take s.pending e rest)
      (reaction : p.react e.envelope.recipient (s.nodes e.envelope.recipient).durable
        (s.nodes e.envelope.recipient).volatile (.message e.envelope) d v outs)
      (publish : Publish e.envelope.recipient s.next outs rest result) :
      Step c p f s (.deliver e outs)
        ⟨setNode s.nodes e.envelope.recipient ⟨d,v,.running⟩,result,s.next + outs.length⟩
  | drop {s e rest} (allowed : f.allowDrop = true) (take : Take s.pending e rest) :
      Step c p f s (.drop e) ⟨s.nodes,rest,s.next⟩
  | duplicate {s e result} (allowed : f.allowDuplicate = true) (present : e ∈ s.pending)
      (copy : result.Perm (freshCopy e s.next :: s.pending)) :
      Step c p f s (.duplicate e) ⟨s.nodes,result,s.next+1⟩
  | crash {s actor} (allowed : f.allowCrash = true) (running : (s.nodes actor).status = .running) :
      Step c p f s (.crash actor)
        ⟨setNode s.nodes actor ⟨(s.nodes actor).durable,
          p.crashReset (s.nodes actor).durable (s.nodes actor).volatile,.crashed⟩,s.pending,s.next⟩
  | recover {s actor} (allowed : f.allowRecover = true) (crashed : (s.nodes actor).status = .crashed) :
      Step c p f s (.recover actor)
        ⟨setNode s.nodes actor ⟨(s.nodes actor).durable,p.recover (s.nodes actor).durable,.running⟩,s.pending,s.next⟩

def system (c : Config N) (p : Protocol (Member c) D V L P C K) (f : FaultProfile) :
    Foundation.TransitionSystem (State (Member c) D V L P) (Label (Member c) L P C K) (Label (Member c) L P C K) where
  init s := s.pending = [] ∧ s.next = 0 ∧ ∀ m,
    (s.nodes m).status = .running ∧ p.initial m (s.nodes m).durable (s.nodes m).volatile
  step s a o t := Step c p f s a t ∧ o = a

variable {c : Config N} {p : Protocol (Member c) D V L P C K} {f : FaultProfile}
variable {s t : State (Member c) D V L P}
theorem no_process_crashed (h : (s.nodes actor).status = .crashed) : ¬ Step c p f s (.process actor stimulus outs) t := by
  intro hs; cases hs with
  | process hr _ _ => rw [h] at hr; cases hr
theorem no_deliver_crashed (h : (s.nodes e.envelope.recipient).status = .crashed) : ¬ Step c p f s (.deliver e outs) t := by
  intro hs; cases hs with
  | deliver hr _ _ _ => rw [h] at hr; cases hr
theorem no_crash_crashed (h : (s.nodes actor).status = .crashed) : ¬ Step c p f s (.crash actor) t := by
  intro hs; cases hs with
  | crash _ hr => rw [h] at hr; cases hr
theorem no_recover_running (h : (s.nodes actor).status = .running) : ¬ Step c p f s (.recover actor) t := by
  intro hs; cases hs with
  | recover _ hr => rw [h] at hr; cases hr

theorem no_drop_disabled (h : f.allowDrop = false) : ¬ Step c p f s (.drop e) t := by
  intro hs; cases hs with
  | drop ha _ => rw [h] at ha; cases ha
theorem no_duplicate_disabled (h : f.allowDuplicate = false) : ¬ Step c p f s (.duplicate e) t := by
  intro hs; cases hs with
  | duplicate ha _ _ => rw [h] at ha; cases ha
theorem no_crash_disabled (h : f.allowCrash = false) : ¬ Step c p f s (.crash actor) t := by
  intro hs; cases hs with
  | crash ha _ => rw [h] at ha; cases ha
theorem no_recover_disabled (h : f.allowRecover = false) : ¬ Step c p f s (.recover actor) t := by
  intro hs; cases hs with
  | recover ha _ => rw [h] at ha; cases ha

theorem reliable_no_drop : ¬ Step c p .reliable s (.drop e) t := no_drop_disabled rfl
theorem reliable_no_duplicate : ¬ Step c p .reliable s (.duplicate e) t := no_duplicate_disabled rfl
theorem reliable_no_crash : ¬ Step c p .reliable s (.crash actor) t := no_crash_disabled rfl
theorem reliable_no_recover : ¬ Step c p .reliable s (.recover actor) t := no_recover_disabled rfl
end Harmonia.Distributed
