import Harmonia.Applications.Kadmos.Bridge.Fixtures
import Harmonia.Applications.Kadmos.Interpreter

namespace Harmonia.Applications.Kadmos.Generated

open Harmonia.Applications.Kadmos
open Harmonia.Applications.Kadmos.BridgeFixtures

def generatedBalanceState (b : Int) : State 1 1 := ⟨0, fun _ => b⟩
def generatedBalanceRequest (n : Int) : Request 1 :=
  ⟨"DEBIT", fun _ => .int n, none⟩

theorem generated_balance_initialized :
    «initialize» balanceCandidate = .ok (generatedBalanceState 100) := by
  have hv : validateWorld balanceCandidate = .ok (0 : Fin 1) := by decide +kernel
  have hctx : (fun j : Fin 1 => (balanceCandidate.variables j).defaultValue.getD 0) =
      (fun _ => 100) := by
    funext j
    have hj : j = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
    rw [hj]
    decide +kernel
  have hc : checkState balanceCandidate (generatedBalanceState 100) = true := by decide +kernel
  simp only [«initialize», hv]
  simpa [generatedBalanceState, hctx, hc]
theorem generated_balance_lookup (n : Int) :
    lookupAction balanceCandidate (generatedBalanceRequest n).actionId = some 0 := rfl

private theorem finOne_context (c : Fin 1 → Int) (n : Int)
    (h : c 0 = n) : c = fun _ => n := by
  funext y
  have hy : y = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ y.isLt))
  rw [hy]
  exact h

theorem generated_balance_bounds (b : Int) (hb : 0 ≤ b) (hB : b ≤ S) :
    checkBounds balanceCandidate (generatedBalanceState b) = none := by
  have hs : safeInt b := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have hB' : b ≤ 9007199254740991 := by simpa [S] using hB
  simp [checkBounds, inBounds, balanceCandidate, generatedBalanceState, hs, hb, hB']

theorem generated_balance_invariants (b : Int) (hb : 0 ≤ b) (hB : b ≤ S) :
    checkInvariants balanceCandidate (generatedBalanceState b) = none := by
  have hs : safeInt b := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have hneg : ¬ b < 0 := by omega
  simp [checkInvariants, checkInvariantList, balanceCandidate, generatedBalanceState,
    eval, requireInt, checkedInt, hs, invariantPass, Bind.bind, Functor.map,
    Pure.pure, Except.bind, Except.map, Except.pure,
    show safeInt 0 by decide, hneg, requireBool]

theorem generated_balance_runAction (b n : Int)
    (sb : safeInt b) (sn : safeInt n) (sd : safeInt (b - n)) (hn : 0 < n) :
    runAction balanceCandidate 0 (generatedBalanceState b) (generatedBalanceRequest n) =
      publishCandidate balanceCandidate (generatedBalanceState (b - n)) := by
  have hc : setContext (fun _ : Fin 1 => b) 0 (b - n) = (fun _ => b - n) :=
    finOne_context _ _ (by simp)
  have hle : ¬ n ≤ 0 := by omega
  simp [runAction, generatedBalanceRequest, balanceCandidate, generatedBalanceState,
    decode, inputValid, rawInt, sn, sb, sd, eval, requireInt, requireBool,
    checkedInt, show safeInt 0 by decide, hle, runTransitionEffects,
    runEffects, runEffect, Bind.bind, Functor.map, Pure.pure, Except.bind,
    Except.mapError, Except.map, Except.pure, hc]

theorem generated_balance_guard_reject (b n : Int)
    (hb : 0 ≤ b) (hB : b ≤ S) (hn : -S ≤ n) (hN : n ≤ 0) :
    interpret balanceCandidate (generatedBalanceState b) (generatedBalanceRequest n) =
      ⟨generatedBalanceState b, ⟨.rejected .guardFalse, none⟩⟩ := by
  have sb : safeInt b := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have sn : safeInt n := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  simp only [interpret, attempt, generated_balance_initialized, generated_balance_lookup]
  simp [
    runAction, generatedBalanceRequest, balanceCandidate, generatedBalanceState,
    decode, inputValid, rawInt, sn, sb, eval, requireInt, requireBool,
    checkedInt, show safeInt 0 by decide, hN, Bind.bind, Functor.map,
    Pure.pure, Except.bind, Except.mapError, Except.map, Except.pure]

theorem generated_balance_accept (b n : Int)
    (hb : 0 ≤ b) (hB : b ≤ S) (hn : 0 < n) (hnb : n ≤ b) :
    interpret balanceCandidate (generatedBalanceState b) (generatedBalanceRequest n) =
      ⟨generatedBalanceState (b - n), ⟨.accepted, none⟩⟩ := by
  have sb : safeInt b := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have sn : safeInt n := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have sd : safeInt (b - n) := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have hd : 0 ≤ b - n := by omega
  have hD : b - n ≤ S := by omega
  simp only [interpret, attempt, generated_balance_initialized, generated_balance_lookup]
  rw [generated_balance_runAction b n sb sn sd hn]
  rw [publishCandidate_ok (generated_balance_bounds (b - n) hd hD)
    (generated_balance_invariants (b - n) hd hD)]
  rfl

theorem generated_balance_negative_bounds (d : Int) (hd : d < 0) :
    checkBounds balanceCandidate (generatedBalanceState d) = some 0 := by
  have hf : ¬ ∀ j, inBounds balanceCandidate (generatedBalanceState d) j := by
    intro h
    have hz := (h 0).2.1
    change 0 ≤ d at hz
    omega
  rw [checkBounds, if_neg hf]
  change some (if inBounds balanceCandidate (generatedBalanceState d) 0 then 0 else 0) = some 0
  simp

theorem generated_balance_bounds_reject (b n : Int)
    (hb : 0 ≤ b) (hB : b ≤ S) (hbn : b < n) (hN : n ≤ S) :
    interpret balanceCandidate (generatedBalanceState b) (generatedBalanceRequest n) =
      ⟨generatedBalanceState b, ⟨.rejected (.bounds 0), none⟩⟩ := by
  have sb : safeInt b := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have sn : safeInt n := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have sd : safeInt (b - n) := by
    unfold safeInt
    constructor <;> (unfold S at *; omega)
  have hn : 0 < n := by omega
  have hd : b - n < 0 := by omega
  have hpub : publishCandidate balanceCandidate (generatedBalanceState (b - n)) =
      .error (.bounds 0) := by
    unfold publishCandidate
    split
    · rename_i j heq
      rw [generated_balance_negative_bounds (b - n) hd] at heq
      cases Option.some.inj heq
      rfl
    · rename_i heq
      have hbad := generated_balance_negative_bounds (b - n) hd
      rw [heq] at hbad
      cases hbad
  simp only [interpret, attempt, generated_balance_initialized, generated_balance_lookup]
  rw [generated_balance_runAction b n sb sn sd hn, hpub]
  rfl

end Harmonia.Applications.Kadmos.Generated
