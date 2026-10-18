import Harmonia.Applications.Kadmos.Generated.BalanceStepSnapshots
import Harmonia.Applications.Kadmos.Generated.BalanceStepSource
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option Elab.async false

/-- Unconditional reduction to the actual stored-source Python prefix executor. -/
theorem balanceStep_py_prefix_entry (b n : Int) :
    balanceStepPrefixRun .python b n =
      execStmt 90 (balanceProgram .python) (balanceStepPySnapshots b n)
        balanceStepPySnapshotsFrame balanceStepPyPrefixSyntax := by
  have hs := balanceStep_py_snapshots_execute b n
  simp only [balanceStepPrefixRun, hs, Bind.bind, Except.bind]
  change execStmt 90 (balanceProgram .python) (balanceStepPySnapshots b n)
    balanceStepPySnapshotsFrame (takeStepStmts 21 (balanceStepProtected .python).body) = _
  rw [balanceStep_py_prefix_source]

end Harmonia.Applications.Kadmos.Generated
