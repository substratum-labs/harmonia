import Harmonia.Distributed.Properties
namespace Harmonia.Distributed.Tests.Network
open Harmonia.Distributed
variable {M L P : Type}
theorem nonhead (x y : Transmission M L P) : Take [x,y] y [x] := List.Perm.swap y x []
theorem one_occurrence (x : Transmission M L P) : Take [x,x] x [x] := List.Perm.refl _
theorem not_two (x : Transmission M L P) : ¬ Take [x] x [x] := by
  intro h
  have hl := Take.length h
  simp at hl
theorem reordered {xs ys : List (Transmission M L P)} (h : xs.Perm ys) :
    Take xs e rest ↔ Take ys e rest := Take.perm_left h
theorem two_ids (actor peer : M) :
    (allocate actor 9 ([⟨actor,7,()⟩,⟨peer,7,()⟩] : List (Outgoing M Nat Unit))).map
      (fun e => e.tid) = [9,10] := rfl
theorem no_emissions (actor : M) : allocate (L := L) (P := P) actor 9 [] = [] := rfl
theorem same_id_distinct_payload (a b : M) :
    (allocate a 0 ([⟨b,7,false⟩,⟨b,7,true⟩] : List (Outgoing M Nat Bool))).map
      (fun e => (e.envelope.logical, e.envelope.payload)) = [(7,false),(7,true)] := rfl
end Harmonia.Distributed.Tests.Network

namespace Harmonia.Distributed.Tests.Properties
open Harmonia.Distributed
variable {N D V L P C K : Type} [DecidableEq N] {c : Config N}
variable {p : Protocol (Member c) D V L P C K} {f : FaultProfile}
variable {s t : State (Member c) D V L P}
theorem invariant_probe (h : Foundation.Reachable (system c p f) s) : WF s := reachable_wf h
theorem frame_probe (h : Step c p f s a t) (hn : actorOf a ≠ some m) : t.nodes m = s.nodes m := Step.frame h m hn
omit [DecidableEq N] in
theorem symmetry_probe (h : PoolEq s t) : PoolEq t s := h.symm
theorem init_transport (h : PoolEq s t) : (system c p f).init s ↔ (system c p f).init t := h.init_iff
omit [DecidableEq N] in
theorem wf_transport (h : PoolEq s t) : WF s ↔ WF t := h.wf_iff
end Harmonia.Distributed.Tests.Properties

namespace Harmonia.Distributed.Tests.Properties
open Harmonia.Distributed
variable {N D V L P C K : Type} [DecidableEq N] {c : Config N}
variable {p : Protocol (Member c) D V L P C K} {f : FaultProfile}
variable {s t s' : State (Member c) D V L P}
theorem lift_probe (he : PoolEq s s') (h : Step c p f s a t) :
    ∃ t', Step c p f s' a t' ∧ PoolEq t t' := Step.permutation_lift he h
theorem path_lift (he : PoolEq s s') (h : Foundation.Execution (system c p f) s labels t) :
    ∃ t', Foundation.Execution (system c p f) s' labels t' ∧ PoolEq t t' := execution_permutation he h
theorem origin_probe (hi : (system c p f).init s) (h : Foundation.Execution (system c p f) s labels t)
    (he : e ∈ t.pending) : SentIn h e.envelope := provenance_history hi h he
theorem consume_probe (h : Step c p f s (.deliver e outs) t) :
    t.pending.length+1 = s.pending.length+outs.length := Step.deliver_length h
end Harmonia.Distributed.Tests.Properties
namespace Harmonia.Distributed.Tests.Network
open Harmonia.Distributed
def badPool : State Nat Nat Nat Nat Unit :=
  ⟨fun _ => ⟨0,0,.running⟩,[⟨0,⟨0,1,7,()⟩⟩,⟨0,⟨0,1,7,()⟩⟩],1⟩
theorem malformed_not_wf : ¬ WF badPool := by
  simp [WF,badPool]
end Harmonia.Distributed.Tests.Network
