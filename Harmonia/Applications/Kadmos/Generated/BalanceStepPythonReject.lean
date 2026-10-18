import Harmonia.Applications.Kadmos.Generated.BalanceStepContinuation
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonGuard
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonZero

namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false
set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option pp.maxSteps 100

/-- The proved prefix and guard compose with the stored rejection and finally code. -/
theorem balanceStep_py_guard_reject_execute (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hle : n ≤ 0) :
    evalExpr 100 (balanceProgram .python)
      (debitCallEntry .python (balanceCanonicalConstructed .python b) n).1
      (debitCallEntry .python (balanceCanonicalConstructed .python b) n).2
      (debitCallExpression .python) =
      .ok ⟨balanceStepPyRejected b n, .ok (.object 142)⟩ := by
  let tail := dropStmts 21 (balanceStepProtected .python).body
  let p := protectedSyntax (firstStmt tail)
  let guardName := match firstStmt p.body with
    | .assign (.local name) _ => name
    | _ => ""
  have hseq : tail = .sequence (firstStmt tail) (restStmt tail) := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    with_unfolding_all rfl
  have htry : firstStmt tail = p.stmt := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    with_unfolding_all rfl
  have hbody : p.body = .sequence (firstStmt p.body) (restStmt p.body) := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    with_unfolding_all rfl
  have hassign : firstStmt p.body = .assign (.local guardName) (balanceStepGuardExpression .python) := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    with_unfolding_all rfl
  rw [balanceStep_canonical_prefix_continuation .python b n hn]
  unfold balanceStepPrefixContinuation balanceStepSequenceContinuation balanceStepProtectedContinuation
  simp only [show (TargetLang.python == TargetLang.ts) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, balanceStepCanonicalPrefix]
  dsimp only [tail] at hseq htry
  rw [hseq, execSequence_eq 68, htry, execProtectedSyntax_eq 67,
    hbody, execSequence_eq 66, hassign, execStmt.eq_def]
  dsimp only
  have hg := balanceStep_py_guard_execute b n (signed_natAbs hn)
  change evalExpr 65 (balanceProgram .python) (balanceStepPyPrefix b n)
    balanceStepPyPrefixFrame (balanceStepGuardExpression .python) = _ at hg
  rw [hg, decide_eq_false (Int.not_lt.mpr hle)]
  simp only [tail, p, guardName, balanceStepGuardExpression, balanceStepProtected,
    balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source,
    balanceStepPyGuard, balanceStepPyRejected, balanceStepPyPrefix,
    balanceStepPyPrefixFrame, balanceCanonicalConstructed, balanceInvariantPyCopied,
    balanceInvariantPyReset, balanceInvariantPyBound, balanceInvariantPyFinal]
  simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  simp only [decide_eq_false (Int.not_lt.mpr hle)]
  with_unfolding_all rfl

end Harmonia.Applications.Kadmos.Generated
