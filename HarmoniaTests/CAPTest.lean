import Harmonia.Theorems.CAP

open Harmonia.CAP Harmonia.Foundation

private def cut : Partition Bool where
  g1 := [false]
  g2 := [true]
  left_nonempty := by decide
  right_nonempty := by decide
  disjoint := by decide

private def apLocal : TransitionSystem Unit (LocalAction Nat) Unit where
  init _ := True
  step _ _ _ _ := True

private def ap : Protocol Nat Unit Unit where
  left := apLocal
  right := apLocal
  initialLeft := ()
  initialRight := ()
  left_init := trivial
  right_init := trivial

private theorem apAvailableLocal (s : Unit) (op : Op Nat) :
    ∃ xs t response, Execution apLocal s xs t ∧
      completed xs = [(op, response)] ∧ ValidResponse op response := by
  cases op with
  | write value =>
    refine ⟨[(.complete (.write value) .ok, ())], (), .ok, ?_, rfl, trivial⟩
    exact .cons trivial .nil
  | read =>
    refine ⟨[(.complete .read (.val 0), ())], (), .val 0, ?_, rfl, trivial⟩
    exact .cons trivial .nil

private theorem ap_available : Available ap := by
  constructor
  · intro s _ op; exact apAvailableLocal s op
  · intro s _ op; exact apAvailableLocal s op

example : ¬ Linearizable cut ap 0 := by
  intro atomic
  exact cap_impossibility cut ap 0 1 (by decide) ap_available atomic

-- An always responding implementation admits a stale read witness.
example : FiniteAvailable ap 1 := by
  constructor
  · refine ⟨[(.complete (.write 1) .ok, ())], (), ?_, rfl⟩
    exact .cons trivial .nil
  · refine ⟨[(.complete .read (.val 0), ())], (), 0, ?_, rfl⟩
    exact .cons trivial .nil

private def cpLocal : TransitionSystem Unit (LocalAction Nat) Unit where
  init _ := True
  step _ _ _ _ := False

private def cp : Protocol Nat Unit Unit where
  left := cpLocal
  right := cpLocal
  initialLeft := ()
  initialRight := ()
  left_init := trivial
  right_init := trivial

-- No operation completes. The empty history is linearizable, but the
-- required write cannot finish, so this is a consistent unavailable model.
example : Linearizable cut cp 0 := by
  intro labels finalState hexec
  cases hexec with
  | nil => exact ⟨0, .nil⟩
  | cons hs _ =>
    rcases hs with ⟨_, _, _, hside⟩
    rcases hside with ⟨_, _, impossible⟩ | ⟨_, _, impossible⟩
    · exact False.elim impossible
    · exact False.elim impossible

example : ¬ FiniteAvailable cp 1 := by
  intro h
  rcases h.1 with ⟨xs, _, hexec, hshape⟩
  cases hexec with
  | nil => cases hshape
  | cons hs _ => exact hs

example : ¬ Available cp := by
  intro h
  have finite := available_implies_finite cp 1 h
  have impossible : ¬ FiniteAvailable cp 1 := by
    intro hf
    rcases hf.1 with ⟨xs, _, hexec, hshape⟩
    cases hexec with
    | nil => cases hshape
    | cons hs _ => exact hs
  exact impossible finite
