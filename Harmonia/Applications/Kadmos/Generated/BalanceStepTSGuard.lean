import Harmonia.Applications.Kadmos.Generated.BalanceStepSource

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false
set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem balanceStep_ts_guard_execute (b n : Int) :
    balanceStepGuardRun .ts b n =
      .ok ⟨balanceStepTsGuard b n, .ok (.bool (decide (0 < n)))⟩ := by
  change evalExpr 69 (balanceProgram .ts) (balanceStepTsPrefix b n)
    balanceStepTsPrefixFrame (balanceStepGuardExpression .ts) = _
  rw [balanceStep_ts_guard_source]
  simp only [balanceStepTsPrefix, balanceStepTsPrefixFrame, balanceStepTsGuard,
    balanceCanonicalConstructed, balanceInvariantTsCopied, balanceInvariantTsReset,
    balanceInvariantTsBound, balanceInvariantTsFinal]
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  with_unfolding_all rfl


/-- Actual emitted guard value, uniformly in the tagged amount. -/
theorem balanceStep_ts_guard_value (b n : Int) :
 (balanceStepGuardRun .ts b n).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < n)))) := by
 rw [balanceStep_ts_guard_execute]
 rfl

end Harmonia.Applications.Kadmos.Generated
