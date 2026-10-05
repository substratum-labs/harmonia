import Harmonia.Distributed.Protocol
namespace Harmonia.Distributed.Tests
open Harmonia.Distributed

def pair : Config Nat := ⟨[0, 1], by decide⟩
def empty : Config Nat := ⟨[], by decide⟩
theorem duplicate_rejected : Config.checked ([0,0] : List Nat) = none := rfl
theorem pair_accepted : (Config.checked ([0,1] : List Nat)).isSome = true := by decide
theorem empty_accepted : (Config.checked ([] : List Nat)).isSome = true := by decide
theorem outside_lookup : pair.member? 2 = none := by decide
theorem configured (m : Member pair) : m.val ∈ pair.members := m.property
theorem outside_impossible (m : Member pair) : m.val ≠ 2 := by
  intro h
  have hm := m.property
  simp [pair, h] at hm
theorem empty_impossible (m : Member empty) : False := by
  have hm := m.property
  simp [empty] at hm
theorem actor_type_rejected : pair.member? 2 = none := by
  fail_if_success have bad : Member pair := (2 : Nat)
  rfl
theorem endpoint_type_rejected : pair.member? 2 = none := by
  fail_if_success have bad : Outgoing (Member pair) Nat Unit :=
    { recipient := (2 : Nat), logical := 7, payload := () }
  rfl
theorem global_react_type_rejected : pair.member? 2 = none := by
  fail_if_success have bad : Protocol (Member pair) Nat Nat Nat Unit Unit Unit :=
    { initial := fun _ _ _ => True,
      react := fun (_ : Member pair) (_ : Member pair → Nat) => True,
      crashReset := fun _ _ => 0, recover := id }
  rfl
end Harmonia.Distributed.Tests
