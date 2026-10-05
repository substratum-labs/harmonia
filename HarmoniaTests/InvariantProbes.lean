import Harmonia.Core.Invariant
namespace Harmonia.Foundation.Tests
open Harmonia.Foundation

def bounded : TransitionSystem Nat Unit Nat where
  init s := s = 0
  step s _ o t := s < 2 ∧ t = s + 1 ∧ o = t

theorem bounded_initial : ∃ s, bounded.init s := ⟨0, rfl⟩
theorem bounded_safe (h : Reachable bounded s) : s ≤ 2 := by
  apply invariant (I := fun s => s ≤ 2) ?_ ?_ s h
  · intro s hi; cases hi; exact Nat.zero_le _
  · intro s a o t _ hs
    rw [hs.2.1]
    exact hs.1

theorem bound_disabled : ¬ bounded.step 2 () o t := by
  intro hs; exact Nat.lt_irrefl 2 hs.1

def unsafeSystem : TransitionSystem Nat Unit Nat where
  init s := s = 0
  step _ _ o t := t = 3 ∧ o = t

theorem unsafe_initial : ∃ s, unsafeSystem.init s := ⟨0, rfl⟩
theorem unsafe_reachable : Reachable unsafeSystem 3 :=
  .step (a := ()) (.init rfl) ⟨rfl, rfl⟩
theorem unsafe_preservation_fails : ¬ Preserved unsafeSystem (fun s => s ≤ 2) := by
  intro hp
  have bad : 3 ≤ 2 := hp 0 () 3 3 (Nat.zero_le _) ⟨rfl, rfl⟩
  exact (by decide : ¬ (3 ≤ 2)) bad

theorem generic_induction {T : TransitionSystem S A O} {I : S → Prop}
    (hi : Initially T I) (hp : Preserved T I) (h : Reachable T s) : I s :=
  invariant hi hp s h
end Harmonia.Foundation.Tests
