import Harmonia.Core.Refinement
namespace Harmonia.Foundation.Examples

def counter : TransitionSystem Nat Unit Nat where
  init s := s = 0
  step s _ o t := s < 2 ∧ t = s + 1 ∧ o = t

theorem counter_initial : ∃ s, counter.init s := ⟨0, rfl⟩

theorem counter_safe (h : Reachable counter s) : s ≤ 2 := by
  apply invariant (I := fun s => s ≤ 2) ?_ ?_ s h
  · intro s hi; cases hi; exact Nat.zero_le _
  · intro s a o t _ hs
    rw [hs.2.1]
    exact hs.1

/-- Extra bookkeeping may change nondeterministically at every step. -/
def concrete : TransitionSystem (Nat × Bool) Unit (Nat × Bool) where
  init c := c = (0, false)
  step c _ o c' := c.1 < 2 ∧ c'.1 = c.1 + 1 ∧ o = c'

theorem concrete_initial : ∃ c, concrete.init c := ⟨(0, false), rfl⟩

theorem simulation : ForwardSimulation concrete counter (fun c b => c.1 = b) Prod.fst := by
  constructor
  · intro c hi
    cases hi
    exact ⟨0, rfl, rfl⟩
  · intro c a o c' b hr hs
    refine ⟨(), c'.1, ⟨?_, ?_, ?_⟩, rfl⟩
    · rw [← hr]; exact hs.1
    · rw [← hr]; exact hs.2.1
    · rw [hs.2.2]

theorem concrete_safe (h : Reachable concrete c) : c.1 ≤ 2 :=
  simulation.transfer_invariant (fun _ hb => counter_safe hb)
    (fun _ _ hr hi => hr ▸ hi) h

theorem concrete_choices :
    concrete.step (0, false) () (1, true) (1, true) ∧
    concrete.step (0, false) () (1, false) (1, false) :=
  ⟨⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩⟩
end Harmonia.Foundation.Examples
