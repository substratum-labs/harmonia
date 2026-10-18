import Harmonia.Applications.Kadmos.Generated.BalanceStepModels
import Harmonia.Applications.Kadmos.Generated.BalanceStepSyntax

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem balanceStep_py_prefix_source :
 takeStepStmts 21 (balanceStepProtected .python).body = balanceStepPyPrefixSyntax := by
 simp only [balanceStepProtected, balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source]
 rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

theorem balanceStep_ts_guard_source :
    balanceStepGuardExpression .ts = balanceStepTsGuardSyntax := by
  simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
    balanceStepAfterBusy, balanceStep_stored_source]
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  with_unfolding_all rfl


theorem balanceStep_py_guard_source :
 balanceStepGuardExpression .python = balanceStepPyGuardSyntax := by
 simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
   balanceStepAfterBusy, balanceStep_stored_source]
 rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

end Harmonia.Applications.Kadmos.Generated
