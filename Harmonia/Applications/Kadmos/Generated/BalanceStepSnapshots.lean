import Harmonia.Applications.Kadmos.Generated.BalanceStepModels

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 200000
set_option maxHeartbeats 3000000
set_option smartUnfolding false
theorem balanceStep_ts_snapshots_execute (b n : Int) : balanceStepSnapshotRun .ts b n =
    .ok ⟨balanceStepTsSnapshots b n, balanceStepTsSnapshotsFrame, .normal⟩ := by
  unfold balanceStepSnapshotRun balanceStepSnapshots balanceStepAfterBusy balanceStepTsSnapshots balanceStepTsSnapshotsFrame
  rw [balanceStep_stored_source]
  simp only [balanceStepSnapshotStart, balanceStepCanonicalBound, balanceStepCanonicalUnbound, debitCallEntry,
    balanceCanonicalConstructed, balanceInvariantTsCopied, balanceInvariantTsReset, balanceInvariantTsBound, balanceInvariantTsFinal]
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  with_unfolding_all rfl
theorem balanceStep_py_snapshots_execute (b n : Int) : balanceStepSnapshotRun .python b n =
    .ok ⟨balanceStepPySnapshots b n, balanceStepPySnapshotsFrame, .normal⟩ := by
  unfold balanceStepSnapshotRun balanceStepSnapshots balanceStepAfterBusy balanceStepPySnapshots balanceStepPySnapshotsFrame
  rw [balanceStep_stored_source]
  simp only [balanceStepSnapshotStart, balanceStepCanonicalBound, balanceStepCanonicalUnbound, debitCallEntry,
    balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset, balanceInvariantPyBound, balanceInvariantPyFinal]
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  with_unfolding_all rfl

/-- All actual source snapshot siblings terminate normally with exact saved
context/history, Python undo and rollback closure, for every input payload. -/
theorem balanceStep_canonical_snapshots_execute (lang : TargetLang) (b n : Int) :
 balanceStepSnapshotRun lang b n =
  .ok ⟨(balanceStepCanonicalSnapshots lang b n).1,
       (balanceStepCanonicalSnapshots lang b n).2, .normal⟩ := by
 cases lang
 · exact balanceStep_ts_snapshots_execute b n
 · exact balanceStep_py_snapshots_execute b n


/-- The actual full call reaches the saved snapshot model and retains the
original protected source subtree, including handler and finally cleanup. -/
theorem balanceStep_canonical_snapshot_continuation (lang : TargetLang) (b n : Int) :
 evalExpr 100 (balanceProgram lang)
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).1
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).2
   (debitCallExpression lang) = (do
     let body ← execStmt (if lang == .ts then 93 else 92) (balanceProgram lang)
       (balanceStepCanonicalSnapshots lang b n).1 (balanceStepCanonicalSnapshots lang b n).2
       (dropStmts (if lang == .ts then 4 else 5) (balanceStepSnapshots lang))
     closureResult lang body) := by
 rw [balanceStep_canonical_snapshots_entry]
 have hex : execStmt 97 (balanceProgram lang)
     (balanceStepSnapshotStart lang b n).1 (balanceStepSnapshotStart lang b n).2
     (balanceStepSnapshots lang) =
   execStmt (if lang == .ts then 93 else 92) (balanceProgram lang)
     (balanceStepCanonicalSnapshots lang b n).1 (balanceStepCanonicalSnapshots lang b n).2
     (dropStmts (if lang == .ts then 4 else 5) (balanceStepSnapshots lang)) := by
  cases lang
  · exact execStepPrefix_normal 4 92 (balanceProgram .ts)
      (balanceStepSnapshotStart .ts b n).1 (balanceStepSnapshotStart .ts b n).2
      (balanceStepSnapshots .ts) (balanceStepTsSnapshots b n) balanceStepTsSnapshotsFrame
      (stepPrefixShape_of_snapshot (balanceStep_snapshot_shape .ts))
      (balanceStep_ts_snapshots_execute b n)
  · exact execStepPrefix_normal 5 91 (balanceProgram .python)
      (balanceStepSnapshotStart .python b n).1 (balanceStepSnapshotStart .python b n).2
      (balanceStepSnapshots .python) (balanceStepPySnapshots b n) balanceStepPySnapshotsFrame
      (stepPrefixShape_of_snapshot (balanceStep_snapshot_shape .python))
      (balanceStep_py_snapshots_execute b n)
 rw [hex]

end Harmonia.Applications.Kadmos.Generated
