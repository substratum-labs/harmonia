import Harmonia.Core.TransitionSystem
namespace Harmonia.Foundation

/-- A finite valid path; initialization is a separate obligation. -/
inductive Execution (T : TransitionSystem S A O) : S → List (A × O) → S → Prop where
  | nil : Execution T s [] s
  | cons : T.step s a o m → Execution T m labels t →
      Execution T s ((a, o) :: labels) t

def observations (labels : List (A × O)) : List O := labels.map Prod.snd

theorem observations_append (xs ys : List (A × O)) :
    observations (xs ++ ys) = observations xs ++ observations ys := List.map_append Prod.snd xs ys

namespace Execution
variable {T : TransitionSystem S A O}

theorem append (hx : Execution T s xs m) (hy : Execution T m ys t) :
    Execution T s (xs ++ ys) t := by
  induction hx with
  | nil => exact hy
  | cons hs _ ih => exact .cons hs (ih hy)

/-- Every cut of a valid execution gives a valid prefix and suffix. -/
theorem split {xs ys : List (A × O)} (h : Execution T s (xs ++ ys) t) :
    ∃ m, Execution T s xs m ∧ Execution T m ys t := by
  induction xs generalizing s with
  | nil => exact ⟨s, .nil, h⟩
  | cons label xs ih =>
    cases h with
    | cons hs tail =>
      obtain ⟨m, hp, hq⟩ := ih tail
      exact ⟨m, .cons hs hp, hq⟩

 theorem nil_iff : Execution T s [] t ↔ s = t := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil
end Execution

 theorem execution_reachable {T : TransitionSystem S A O}
    (hi : T.init s) (h : Execution T s labels t) : Reachable T t := by
  have extend : ∀ {s t labels}, Execution T s labels t → Reachable T s → Reachable T t := by
    intro s t labels path
    induction path with
    | nil => exact id
    | cons hs _ ih => intro hr; exact ih (.step hr hs)
  exact extend h (.init hi)

 theorem reachable_iff_execution {T : TransitionSystem S A O} :
    Reachable T t ↔ ∃ s labels, T.init s ∧ Execution T s labels t := by
  constructor
  · intro h
    induction h with
    | init hi => exact ⟨_, [], hi, .nil⟩
    | step _ hs ih =>
      obtain ⟨s, labels, hi, path⟩ := ih
      exact ⟨s, labels ++ [(_, _)], hi, path.append (.cons hs .nil)⟩
  · rintro ⟨s, labels, hi, path⟩
    exact execution_reachable hi path
end Harmonia.Foundation
