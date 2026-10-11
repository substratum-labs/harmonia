import Harmonia.Theorems.FLPIndistinguishability
import Harmonia.Theorems.FLPExtension
import Harmonia.Theorems.FLPBounds
import Harmonia.Theorems.FLPInputs

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

private def inputConfig (inputs : Bool → Decision) : Config Bool Unit Decision where
  state := inputs
  buffer _ _ := 0
  decision _ := none

private def inputInitial (c : Config Bool Unit Decision) : Prop :=
  ∃ inputs, c = inputConfig inputs

-- The finite Boolean input cube has an explicit one-process-at-a-time chain.
example : Initial.InitialChain
    (initialSystem conflicting inputInitial IndistinguishableExcept
      (replay_other_process conflicting) decision_other_process)
    (inputConfig (mixedInput []))
    (inputConfig (mixedInput [false, true])) := by
  apply binary_input_chain conflicting inputInitial inputConfig
  · intro inputs
    exact ⟨inputs, rfl⟩
  · intro inputs inputs' p hsame
    refine ⟨?_, ?_, ?_⟩
    · intro n hn; exact hsame n hn
    · intro n m _; rfl
    · intro n _; rfl

example : ∀ n : Bool, n ∈ [false, true] := by
  intro n
  cases n <;> simp

example : BinaryValidity conflicting inputConfig := by
  constructor
  · refine ⟨advance conflicting (inputConfig (fun _ => .zero)) (tick false),
      .tail (.refl _) (tick false) trivial, false, ?_⟩
    rfl
  · refine ⟨advance conflicting (inputConfig (fun _ => .one)) (tick true),
      .tail (.refl _) (tick true) trivial, true, ?_⟩
    rfl

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

private theorem silent_advance :
    advance silent initial (tick true) = initial := by
  apply Config.ext
  · intro n
    by_cases hn : n = true <;> simp [advance, silent, initial, hn]
  · intro n m
    simp [advance, silent, initial, tick]
  · intro n
    by_cases hn : n = true <;> simp [advance, silent, initial, hn]

private def oneCrashRun : InfiniteRun silent initial where
  state _ := initial
  event _ := tick true
  starts := rfl
  enabled _ := trivial
  evolves _ := silent_advance.symm

-- The silent protocol has an admissible run with one fail-stop process and
-- no decisions. This witnesses that the liveness specification is nonvacuous.
example : Admissible silent initial oneCrashRun := by
  refine ⟨some false, ?_, ?_⟩
  · intro n hn t
    cases n
    · exact False.elim (hn rfl)
    · exact ⟨t, Nat.le_refl t, rfl⟩
  · intro n m hn t hbuffer
    have : (oneCrashRun.state t).buffer n m = 0 := rfl
    omega

example : ¬ GuaranteedTermination silent initial := by
  intro h
  obtain ⟨t, v, ⟨n, hn⟩⟩ := h oneCrashRun (by
    refine ⟨some false, ?_, ?_⟩
    · intro q hq k
      cases q
      · exact False.elim (hq rfl)
      · exact ⟨k, Nat.le_refl k, rfl⟩
    · intro q m hq k hbuffer
      have : (oneCrashRun.state k).buffer q m = 0 := rfl
      omega)
  cases hn
