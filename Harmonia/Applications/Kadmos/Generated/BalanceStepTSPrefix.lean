import Harmonia.Applications.Kadmos.Generated.BalanceStepSnapshots

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option smartUnfolding false
set_option Elab.async false
attribute [local irreducible] hostCall binaryValue

theorem balanceStep_ts_prefix_execute (b n : Int) :
    balanceStepPrefixRun .ts b n =
    .ok ⟨balanceStepTsPrefix b n, balanceStepTsPrefixFrame, .normal⟩ := by
  have hs := balanceStep_ts_snapshots_execute b n
  simp only [balanceStepPrefixRun, hs, Bind.bind, Except.bind]
  simp only [balanceStepProtected, balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source, balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  simp only [balanceStepTsSnapshots, balanceStepTsPrefix, balanceStepTsSnapshotsFrame, balanceStepTsPrefixFrame,
    balanceCanonicalConstructed, balanceInvariantTsCopied, balanceInvariantTsReset, balanceInvariantTsBound, balanceInvariantTsFinal]
  simp only [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  with_unfolding_all rfl


end Harmonia.Applications.Kadmos.Generated
