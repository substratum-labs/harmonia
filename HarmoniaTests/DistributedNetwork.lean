import Harmonia.Distributed.Network
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
