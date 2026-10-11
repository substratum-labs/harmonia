import Harmonia.Theorems.FLPIndistinguishability
import Harmonia.Theorems.FLPExtension

open Harmonia.FLP

private def conflicting : Protocol Bool Unit Decision where
  update _ s _ := s
  decide _ s _ := some s
  send _ _ _ _ _ := 0

private def initial : Config Bool Unit Decision where
  state n := if n then .one else .zero
  buffer _ _ := 0
  decision _ := none

private def tick (n : Bool) : Event Bool Unit := ⟨n, none⟩

-- Either process can decide its own input in one asynchronous step. This
-- protocol is intentionally unsafe; its initial configuration is bivalent.
example : IsBivalent conflicting initial := by
  constructor
  · refine ⟨advance conflicting initial (tick false), ?_, ?_⟩
    · exact .tail (.refl initial) (tick false) trivial
    · refine ⟨false, ?_⟩
      rfl
  · refine ⟨advance conflicting initial (tick true), ?_, ?_⟩
    · exact .tail (.refl initial) (tick true) trivial
    · refine ⟨true, ?_⟩
      rfl

example : ¬ DecidedIn initial .zero ∧ ¬ DecidedIn initial .one := by
  constructor <;> intro h <;> obtain ⟨n, hn⟩ := h <;> cases hn

-- Distinct enabled ticks have the same final configuration in either order.
example : advance conflicting (advance conflicting initial (tick false)) (tick true) =
    advance conflicting (advance conflicting initial (tick true)) (tick false) :=
  flp_lemma1_diamond conflicting initial (tick false) (tick true) (by decide)

private def silent : Protocol Bool Unit Decision where
  update _ s _ := s
  decide _ _ _ := none
  send _ _ _ _ _ := 0

-- A silent protocol cannot produce a decision; this is a negative witness
-- for bivalence and a counterexample to unconditional termination.
private theorem silent_no_decision {c : Config Bool Unit Decision}
    (h : Reachable silent initial c) : ∀ n, c.decision n = none := by
  induction h with
  | refl => intro n; rfl
  | tail _ e _ ih =>
    intro n
    by_cases hn : n = e.target
    · simp [advance, hn, silent]
    · simp [advance, hn, ih n]

example : ¬ IsBivalent silent initial := by
  intro h
  obtain ⟨c, hc, ⟨n, hn⟩⟩ := h.1
  rw [silent_no_decision hc n] at hn
  cases hn
