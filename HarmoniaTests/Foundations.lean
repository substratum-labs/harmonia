import Harmonia.Core.Execution
namespace Harmonia.Foundation.Tests
open Harmonia.Foundation

def fork : TransitionSystem Nat Bool Nat where
  init s := s = 0
  step s a o t := a = true ∧ (t = s + 1 ∨ t = s + 2) ∧ o = t

 theorem initial_witness : ∃ s, fork.init s := ⟨0, rfl⟩
 theorem first : Execution fork 0 [(true, 1)] 1 :=
  .cons ⟨rfl, Or.inl rfl, rfl⟩ .nil
 theorem alternate : Execution fork 0 [(true, 2)] 2 :=
  .cons ⟨rfl, Or.inr rfl, rfl⟩ .nil
 theorem disabled : ¬ fork.step 0 false 1 1 := by
  intro h; cases h.1
 theorem wrong_observation : ¬ fork.step 0 true 99 1 := by
  intro h; cases h.2.2
 theorem wrong_trace : ¬ Execution fork 0 [(true, 99)] 1 := by
  intro h
  cases h with
  | cons hs tail => cases tail; exact wrong_observation hs
 theorem zero_endpoint (h : Execution fork 0 [] t) : t = 0 := by cases h; rfl
 theorem zero_observations : observations ([] : List (Bool × Nat)) = [] := rfl
 theorem ordered : Execution fork 0 [(true, 1), (true, 2)] 2 :=
  Execution.append first (.cons ⟨rfl, Or.inl rfl, rfl⟩ .nil)
 theorem observed_order : observations [(true, 1), (true, 2)] = [1, 2] := rfl
 theorem prefix_valid (h : Execution fork s (xs ++ ys) t) :
     ∃ m, Execution fork s xs m ∧ Execution fork m ys t := Execution.split h
 theorem observations_concat (xs ys : List (Bool × Nat)) :
     observations (xs ++ ys) = observations xs ++ observations ys := observations_append xs ys
 theorem reached : Reachable fork 2 := execution_reachable (show fork.init 0 from rfl) alternate
 theorem correspondence (s : Nat) : Reachable fork s ↔
     ∃ i labels, fork.init i ∧ Execution fork i labels s := reachable_iff_execution
 theorem missing_initial : ¬ Reachable
     ({init := fun _ : Nat => False, step := fun _ (_ : Unit) (_ : Unit) _ => True} :
       TransitionSystem Nat Unit Unit) s := by
  intro h
  obtain ⟨_, _, hi, _⟩ := reachable_iff_execution.mp h
  exact hi
end Harmonia.Foundation.Tests
