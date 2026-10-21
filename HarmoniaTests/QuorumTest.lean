import Harmonia.Theorems.Quorum

open Harmonia.Quorum

example : ([1, 2] ++ diff ([0, 1] : List Nat) [1, 2]).length +
    (inter [0, 1] [1, 2]).length = 2 + 2 := by
  exact inclusion_exclusion [0, 1] [1, 2]

example : (inter ([0, 1] : List Nat) [1, 2]).length ≥ 1 := by
  apply cft_intersection [0, 1] [1, 2] [0, 1, 2] 1
  all_goals decide
example : (inter ([0, 1, 2] : List Nat) [1, 2, 3]).length ≥ 2 := by
  apply bft_intersection [0, 1, 2] [1, 2, 3] [0, 1, 2, 3] 1
  all_goals decide

example : (diff (inter ([0, 1, 2] : List Nat) [1, 2, 3]) [1]).length ≥ 1 := by
  apply bft_honest_cardinality [0, 1, 2] [1, 2, 3] [0, 1, 2, 3] [1] 1
  all_goals decide

example : ∃ x, x ∈ inter ([0, 1, 2] : List Nat) [1, 2, 3] ∧ x ∉ [1] := by
  apply bft_honest_exists [0, 1, 2] [1, 2, 3] [0, 1, 2, 3] [1] 1
  all_goals decide

example : 1 ≤ (inter ([0, 1, 2] : List Nat) [1, 2, 3]).length := by
  apply cft_intersection_at_least [0, 1, 2] [1, 2, 3] [0, 1, 2, 3] 1
  all_goals decide

example : 2 ≤ (inter ([0, 1, 2, 3] : List Nat) [1, 2, 3, 4]).length := by
  apply bft_intersection_at_least [0, 1, 2, 3] [1, 2, 3, 4] [0, 1, 2, 3, 4] 1
  all_goals decide

example : ∃ x, x ∈ inter ([0, 1, 2, 3] : List Nat) [1, 2, 3, 4] ∧ x ∉ [1] := by
  apply bft_honest_exists_at_least [0, 1, 2, 3] [1, 2, 3, 4] [0, 1, 2, 3, 4] [1] 1
  all_goals decide
