import Harmonia.Applications.Kadmos.Generated.BalanceStepModels

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option pp.maxSteps 100
private theorem balanceStep_ts_reject_zero (b : Int)  :
    evalExpr 100 (balanceProgram .ts)
      (debitCallEntry .ts (balanceCanonicalConstructed .ts b) 0).1
      (debitCallEntry .ts (balanceCanonicalConstructed .ts b) 0).2
      (debitCallExpression .ts) =
      .ok ⟨balanceStepTsRejected b 0, .ok (.object 71)⟩ := by
  simp only [debitCallEntry, debitCallExpression, balanceStepTsRejected,
    balanceCanonicalConstructed, balanceInvariantTsCopied, balanceInvariantTsReset,
    balanceInvariantTsBound, balanceInvariantTsFinal]
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  with_unfolding_all rfl


set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option pp.maxSteps 100
private theorem balanceStep_ts_reject_negative (b : Int) (k : Nat) :
    evalExpr 100 (balanceProgram .ts)
      (debitCallEntry .ts (balanceCanonicalConstructed .ts b) (Int.negSucc k)).1
      (debitCallEntry .ts (balanceCanonicalConstructed .ts b) (Int.negSucc k)).2
      (debitCallExpression .ts) =
      .ok ⟨balanceStepTsRejected b (Int.negSucc k), .ok (.object 71)⟩ := by
  simp only [debitCallEntry, debitCallExpression, balanceStepTsRejected,
    balanceCanonicalConstructed, balanceInvariantTsCopied, balanceInvariantTsReset,
    balanceInvariantTsBound, balanceInvariantTsFinal]
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  with_unfolding_all rfl


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option pp.maxSteps 100

/-- Complete stored TS DEBIT rejection, including rollback and finally cleanup. -/
theorem balanceStep_ts_guard_reject_execute (b n : Int) (hn : n ≤ 0) :
    evalExpr 100 (balanceProgram .ts)
      (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).1
      (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).2
      (debitCallExpression .ts) =
      .ok ⟨balanceStepTsRejected b n, .ok (.object 71)⟩ := by
  cases n with
  | ofNat m =>
      have hm : m = 0 := Nat.le_zero.mp (Int.ofNat_le.mp hn)
      subst m
      exact balanceStep_ts_reject_zero b
  | negSucc k => exact balanceStep_ts_reject_negative b k



end Harmonia.Applications.Kadmos.Generated
