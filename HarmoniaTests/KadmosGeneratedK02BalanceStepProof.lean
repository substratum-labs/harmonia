import HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS
import HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython

-- These twelve boundary facts check actual executor output and heap contents.
-- Universal helper/branch simulation is not inferred from finite checks.

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos

-- Conditional arithmetic covers every bounded b/n; effects need n > 0.
theorem kadmos_generated_accept_numeric_domain {b n : Int}
    (hb : 0 ≤ b ∧ b ≤ S) (hn : 0 < n ∧ n ≤ b) :
    (b - n).natAbs ≤ 9007199254740991 :=
  signed_natAbs (balance_accept_difference_bounds hb hn)

theorem kadmos_generated_bounds_numeric_domain {b n : Int}
    (hb : 0 ≤ b ∧ b ≤ S) (hn : b < n ∧ n ≤ S) :
    (b - n).natAbs ≤ 9007199254740991 :=
  signed_natAbs (balance_reject_difference_bounds hb hn)

-- Safe signed requests reach the exact call entry; no step success is assumed.
theorem kadmos_generated_step_entry_all_safe_requests (lang : TargetLang)
    (m : TargetMachine) {n : Int} (hn : -S ≤ n ∧ n ≤ S) :
    targetStep (balanceProgram lang) m (canonicalDebitRequest lang n) = (do
      let result ← evalExpr 100 (balanceProgram lang)
        (debitCallEntry lang m n).1 (debitCallEntry lang m n).2 (debitCallExpression lang)
      match result.result with
      | .ok verdict => pure ⟨result.machine, verdict⟩
      | .error e => throw (.sourceException e)) :=
  targetStep_balance_entry lang m hn

#print axioms kadmos_generated_step_entry_all_safe_requests

-- This reached branch is the first statement of the actual stored step body.
theorem kadmos_generated_step_busy_prefix_source (lang : TargetLang) :
    (balanceStepLookup lang).isSome = true ∧
    (balanceStoredStep lang).2.body =
      .sequence (balanceStepBusyPrefix lang) (balanceStepAfterBusy lang) ∧
    balanceStepBusyPrefix lang =
      .ifThenElse (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (balanceStepBusyThrow lang) .empty :=
  balanceStepBusyPrefix_shape lang

theorem kadmos_generated_step_idle_prefix_depth {lang m f}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    DepthDerivesStmt (balanceProgram lang) m f (balanceStepBusyPrefix lang)
      ⟨m, f, .normal⟩ 2 :=
  balanceStep_idle_prefix hr hi

theorem kadmos_generated_step_idle_prefix_runs {lang m f}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    StmtRuns (balanceProgram lang) m f (balanceStepBusyPrefix lang) ⟨m, f, .normal⟩ :=
  stmt_path_runs (kadmos_generated_step_idle_prefix_depth hr hi)

#print axioms kadmos_generated_step_busy_prefix_source
#print axioms kadmos_generated_step_idle_prefix_depth
#print axioms kadmos_generated_step_idle_prefix_runs

theorem kadmos_generated_step_idle_prefix_adequate {lang m f}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    execStmt 3 (balanceProgram lang) m f (balanceStepBusyPrefix lang) =
      .ok ⟨m, f, .normal⟩ :=
  execStmt_adequate (kadmos_generated_step_idle_prefix_depth hr hi) (by decide)

#print axioms kadmos_generated_step_idle_prefix_adequate

-- Busy acquisition is actual source execution; snapshots, validation,
-- guard/effect/bounds paths and finalization remain separate obligations.
example {lang m f} (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    execStmt 99 (balanceProgram lang) m f (balanceStoredStep lang).2.body =
      execStmt 97 (balanceProgram lang) (balanceSetBusy m true) f
        (restStmt (balanceStepAfterBusy lang)) :=
  balanceStep_idle_entry hr hi (by decide)

example (m : TargetMachine) :
    (balanceSetBusy m true).classMethods = m.classMethods ∧
    (balanceSetBusy m true).closures = m.closures ∧
    (balanceSetBusy m true).globals = m.globals ∧
    (balanceSetBusy m true).cells = m.cells ∧
    (balanceSetBusy m true).objects = m.objects :=
  balanceSetBusy_preserves_bindings m true

#print axioms balanceStep_afterBusy_shape
#print axioms balanceStep_idle_entry
#print axioms balanceSetBusy_preserves_bindings

-- Structural reset checks stay separate from full branch correspondence.
example (lang : TargetLang) :
    statementSpineCheck (if lang == .ts then 12 else 11) (balanceResetProtected lang).body = true :=
  (balanceReset_body_spine lang).1

-- The source finalizer runs from any receiver-bound frame, including a
-- frame carrying an earlier control value. Its write does not allocate.
example {lang m f} (hr : f.receiver = some m.checkerRef) :
    execStmt 4 (balanceProgram lang) m f (balanceResetProtected lang).cleanup =
      .ok ⟨balanceSetBusy m false, f, .normal⟩ :=
  balanceReset_cleanup_execute hr (by decide)

example {lang m f candidate} (hr : f.receiver = some m.checkerRef)
    (hc : localValue m f "candidate" = .ok (.object candidate))
    (hi : lang = .python → localValue m f "_INITIAL" = .ok (.string "Ready")) :
    execStmt 8 (balanceProgram lang) m f (resetPublication lang) =
      .ok ⟨resetPublished lang m candidate, f, .normal⟩ :=
  balanceReset_publication_execute (k := 0) hr hc hi

example (lang : TargetLang) (m : TargetMachine) (candidate : ObjRef) :
    (resetPublished lang m candidate).checker.busy = m.checker.busy ∧
    (resetPublished lang m candidate).checker.context = candidate ∧
    (resetPublished lang m candidate).checker.undo = none := ⟨rfl, rfl, rfl⟩

-- Wrong cleanup values and missing publication writes cannot equal the
-- selected source suffix. These are small AST mutations, not source admission.
example : resetPublicationTemplate .ts ≠ resetPublicationTemplate .python := by decide +kernel
example : statementSpineCheck 1 (.sequence (.assign (.property (.local "this") "#busy") (.bool false)) .empty) = true ∧
    statementSpineCheck 2 (.sequence (.assign (.property (.local "this") "#busy") (.bool false)) .empty) = false := by decide +kernel

#print axioms balanceReset_body_spine
#print axioms balanceReset_cleanup_execute
#print axioms balanceReset_publication_shape
#print axioms balanceReset_publication_execute

example (lang : TargetLang) :
    (balanceResetProtected lang).cleanup ≠ .sequence
      (.assign (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (.bool true)) .empty := by
  rw [(balanceReset_body_spine lang).2]
  cases lang <;> decide +kernel

example (lang : TargetLang) : resetPublication lang ≠ .empty := by
  rw [balanceReset_publication_shape]
  cases lang <;> decide +kernel
