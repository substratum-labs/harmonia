import Harmonia.Applications.Kadmos.Generated.BalanceStepModels

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option pp.maxSteps 100
theorem balanceStep_py_guard_zero_execute (b : Int)  :
    evalExpr 100 (balanceProgram .python)
      (debitCallEntry .python (balanceCanonicalConstructed .python b) 0).1
      (debitCallEntry .python (balanceCanonicalConstructed .python b) 0).2
      (debitCallExpression .python) =
      .ok ⟨balanceStepPyRejected b 0, .ok (.object 142)⟩ := by
  simp only [debitCallEntry, debitCallExpression, balanceStepPyRejected,
    balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
    balanceInvariantPyBound, balanceInvariantPyFinal]
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  with_unfolding_all rfl


end Harmonia.Applications.Kadmos.Generated
