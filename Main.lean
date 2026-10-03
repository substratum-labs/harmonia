import Harmonia

open Harmonia.SMT
open Harmonia.SMT.TwoPhaseCommitVC

def main : IO Unit := do
  IO.println Harmonia.welcomeBanner
  IO.println "================================================================="
  IO.println "  Harmonia SMT Automation & Invariant Verification Pipeline"
  IO.println "================================================================="

  -- 1. Verify Clean 2PC Inductive Invariant Preservation
  IO.println "\n[Phase 1] Verifying Sound 2PC Inductive Invariant Preservation..."
  IO.println "  Goal: Assert Inv(s) ∧ ValidTransitions(s, s') ∧ ¬Inv(s')"
  IO.println "  Expected SMT Verdict: UNSAT (No violation reachable in single step)"

  let verifyResult ← solveWithZ3 buildVerificationScript "2pc_verify"
  match verifyResult.status with
  | SolverStatus.unsat =>
      IO.println "  ✓ VERIFIED [UNSAT]: Z3 proved inductive invariant is preserved across all transitions!"
  | SolverStatus.sat =>
      IO.println "  ✗ FAILED [SAT]: Counterexample found to sound protocol!"
      if let some model := verifyResult.model then
        IO.println "  --- Phase 1 Counterexample ---"
        IO.println model
  | SolverStatus.unknown =>
      IO.println "  ? UNKNOWN: Solver timed out or could not decide."
  | SolverStatus.error msg =>
      IO.println s!"  ! ERROR: {msg}"

  -- 2. Falsify Buggy 2PC (Injecting Unilateral Prepared Timeout)
  IO.println "\n[Phase 2] Falsifying Buggy 2PC (Injecting Premature Prepared Timeout)..."
  IO.println "  Bug: Participant in prepared state prematurely aborts on timeout"
  IO.println "  Goal: Search for Counterexample Trace leading to Agreement Violation"
  IO.println "  Expected SMT Verdict: SAT (Counterexample synthesized)"

  let falsifyResult ← solveWithZ3 buildFalsificationScript "2pc_falsify"
  match falsifyResult.status with
  | SolverStatus.sat =>
      IO.println "  ✓ FALSIFICATION SUCCESS [SAT]: Z3 synthesized a counterexample trace!"
      if let some model := falsifyResult.model then
        IO.println "  ----------------- Counterexample Assignment -----------------"
        IO.println model
        IO.println "  -------------------------------------------------------------"
        IO.println "  Diagnosis: Coordinator committed while Participant unilaterally aborted!"
  | SolverStatus.unsat =>
      IO.println "  ✗ UNEXPECTED [UNSAT]: Solver failed to detect the injected bug."
  | SolverStatus.unknown =>
      IO.println "  ? UNKNOWN: Solver timed out or could not decide."
  | SolverStatus.error msg =>
      IO.println s!"  ! ERROR: {msg}"

  IO.println "\n================================================================="
  IO.println "  Pipeline Run Complete: Push-Button Verification & CEGIS Ready"
  IO.println "================================================================="
