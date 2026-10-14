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

-- Headers expose every middle sibling while keeping generated branch/loop
-- bodies opaque. Wrong helper names and seed-presence operators are detected.
example (lang : TargetLang) :
    ((List.range (if lang == .ts then 7 else 6)).map
      (fun i => resetMiddleHeader (balanceResetMiddleStmt lang (i + 1)))) =
      resetMiddleExpectedHeaders lang :=
  balanceReset_middle_shapes lang

example : resetMiddleHeader (.ifThenElse (.local "invalid") .empty .empty) ≠
    ResetMiddleHeader.branch (.local "violated") := by decide +kernel

example : resetSeedPresenceExpr .python ≠
    .binary .isIdentity (.local "ctx") .null := by decide +kernel

example : resetBoundsCall .ts ≠ .call (.property (.local "this") "checkInvariants")
    (.sequence (.local "candidate") .empty) := by decide +kernel

-- Every symbolic seed reaches the untouched statement-2 continuation. This
-- does not assume that overlay, bounds or invariant helpers will succeed.
example (lang : TargetLang) (b : Int) :
    let e := balanceCanonicalResetStage lang b 3
    execStmt 16 (balanceProgram lang) e.1 e.2 (balanceResetProtected lang).body =
      execStmt 14 (balanceProgram lang)
        (balanceResetMiddleEntry lang b).1 (balanceResetMiddleEntry lang b).2
        (dropStmts 2 (balanceResetProtected lang).body) :=
  balanceReset_canonical_body_prefix_execute lang b 8

-- Normal completion of the body runs the actual finally block and retains
-- its resulting frame. The open body execution is an explicit premise.
example {lang m f final ff}
    (hb : execStmt 8 (balanceProgram lang) m f (balanceResetProtected lang).body =
      .ok ⟨final, ff, .normal⟩)
    (hr : ff.receiver = some final.checkerRef) :
    execStmt 9 (balanceProgram lang) m f (balanceResetProtected lang).stmt =
      .ok ⟨balanceSetBusy final false, ff, .normal⟩ :=
  balanceReset_protected_normal hb hr

#print axioms balanceReset_middle_shapes
#print axioms balanceReset_canonical_body_prefix_execute
#print axioms balanceReset_protected_normal
#print axioms balanceReset_canonical_snapshots_normal

-- Presence tests choose different source branches in the two languages.
example {m f ref} (hp : localValue m f "initialContext" = .ok (.object ref)) :
    execStmt 9 (balanceProgram .ts) m f (balanceResetMiddleStmt .ts 2) =
      execStmt 8 (balanceProgram .ts) m f (ifNoStmt (balanceResetMiddleStmt .ts 2)) :=
  balanceReset_ts_seed_present (k := 4) hp

example {m f ref} (hp : localValue m f "ctx" = .ok (.object ref)) :
    execStmt 9 (balanceProgram .python) m f (balanceResetMiddleStmt .python 2) =
      execStmt 8 (balanceProgram .python) m f (ifYesStmt (balanceResetMiddleStmt .python 2)) :=
  balanceReset_python_seed_present (k := 4) hp

-- The real Python type host accepts a physical plain dict. No overlay-loop
-- or numeric/invariant helper result is assumed or inferred here.
example {m f ref object}
    (hp : localValue m f "ctx" = .ok (.object ref))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m ref = .ok object) (hk : object.kind = .pythonDict) :
    evalExpr 8 (balanceProgram .python) m f resetPythonPlainGuardExpr =
      .ok ⟨m, .ok (.bool false)⟩ :=
  resetPythonPlainGuard_execute (k := 4) hp ht hd ho hk

example (m : TargetMachine) (f : TargetFrame) :
    execStmt 1 (balanceProgram .ts) m f (balanceResetMiddleStmt .ts 1) =
      .error .exhaustedFuel := by
  rw [balanceReset_middle_entry_shape]
  simp [execStmt, evalExpr, Bind.bind, Pure.pure, Except.bind, Except.pure]

#print axioms balanceReset_seed_presence_header
#print axioms resetSeedPresence_execute
#print axioms balanceReset_ts_seed_present
#print axioms balanceReset_python_seed_present
#print axioms balanceReset_python_plain_guard_header
#print axioms resetPythonPlainGuard_execute

-- All four actual validation rejection sites accept a null helper result.
example (lang : TargetLang) (invariant : Bool) {m f}
    (hv : localValue m f (if invariant then "violated" else "invalid") = .ok .null) :
    let i := if invariant then (if lang == .ts then 7 else 6) else (if lang == .ts then 5 else 4)
    execStmt 2 (balanceProgram lang) m f (balanceResetMiddleStmt lang i) =
      .ok ⟨m, f, .normal⟩ :=
  balanceReset_validation_rejection_execute invariant hv

-- The source write executes with a symbolic payload on an existing candidate.
example {m f ref b}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hv : localValue m f "value" = .ok (integerValue .ts b))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m 100)) :
    execStmt 3 (balanceProgram .ts) m f (balanceResetOverlayWrite .ts) =
      .ok ⟨balanceOverlayUpdated .ts m ref b, f, .normal⟩ :=
  balanceReset_overlay_write_ts_execute hc hn hv (writeOwn_balance_existing ho)

example {m f ref b}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hi : localValue m f "int" = .ok (.builtin .int))
    (ht : evalExpr 5 (balanceProgram .python) m f resetPythonOverlayStringTest =
      .ok ⟨m, .ok (.bool false)⟩)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (ho : objectAt m ref = .ok (balanceHeapObject .python m 100)) :
    execStmt 7 (balanceProgram .python) m f (balanceResetOverlayWrite .python) =
      .ok ⟨balanceOverlayUpdated .python m ref b, f, .normal⟩ :=
  balanceReset_overlay_write_python_execute hc hn hv hi ht (balance_natAbs hb)
    (writeOwn_balance_existing ho)

-- Exhaustion is an actual interpreter result, not just an inferred rank.
example (m : TargetMachine) (f : TargetFrame) :
    execStmt 1 (balanceProgram .ts) m f (balanceResetOverlayWrite .ts) =
      .error .exhaustedFuel := by
  rw [balanceReset_overlay_write_shape]
  simp only [execStmt, evalExpr, Bind.bind, Except.bind]

example : resetOverlayValue .ts ≠ .local "value" := by decide +kernel
example : resetOverlayValue .python ≠ .local "value" := by decide +kernel

#print axioms balanceReset_validation_rejection_execute
#print axioms balanceReset_overlay_write_shape

-- TS helpers' emitted success sentinel is undefined, distinct from Python None.
example {m f} (invariant : Bool)
    (hv : localValue m f (if invariant then "violated" else "invalid") = .ok .undefined) :
    execStmt 2 (balanceProgram .ts) m f
      (balanceResetMiddleStmt .ts (if invariant then 7 else 5)) = .ok ⟨m, f, .normal⟩ :=
  balanceReset_ts_validation_rejection_undefined invariant hv

-- A concrete live heap/frame makes the indexed-write premises nonvacuous.
def resetOverlayTestFrame : TargetFrame :=
  ⟨"overlay-test", [], [("candidate", 0), ("name", 1), ("value", 2), ("int", 3), ("_WORLD", 4)],
    [], none, .normal⟩

def resetOverlayTestMachine (lang : TargetLang) (b : Int) : TargetMachine :=
  { TargetMachine.empty with
    objects := [(1, balanceHeapObject lang TargetMachine.empty 100),
      (2, { literalObject lang TargetMachine.empty with
        own := [("context", ⟨some (.object 3), none, none, true, true, true⟩)] }),
      (3, { literalObject lang TargetMachine.empty with
        own := [("balance", ⟨some (.object 4), none, none, true, true, true⟩)] }),
      (4, { literalObject lang TargetMachine.empty with
        own := [("type", ⟨some (.string "integer"), none, none, true, true, true⟩)] })],
    cells := [(0, .object 1), (1, .string "balance"), (2, integerValue lang b),
      (3, .builtin .int), (4, .object 2)], nextCell := 5, nextObject := 5 }

example (b : Int) :
    execStmt 3 (balanceProgram .ts) (resetOverlayTestMachine .ts b) resetOverlayTestFrame
      (balanceResetOverlayWrite .ts) =
        .ok ⟨balanceOverlayUpdated .ts (resetOverlayTestMachine .ts b) 1 b,
          resetOverlayTestFrame, .normal⟩ :=
  balanceReset_overlay_write_ts_execute rfl rfl rfl (writeOwn_balance_existing rfl)

-- The checker projects the non-DecidableEq ExprOutcome wrapper to its two
-- decidable physical fields; soundness recovers the complete result.
private theorem resetOverlayTest_eval {result : Except TargetError ExprOutcome} {m value}
    (h : result.toOption.map (fun out => (out.machine, out.result)) = some (m, .ok value)) :
    result = .ok ⟨m, .ok value⟩ := by
  cases result with
  | error error => simp [Except.toOption] at h
  | ok out =>
      cases out with
      | mk final returned =>
          simp only [Except.toOption, Option.map, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl

-- Closed kernel checks inspect no full source body.
theorem resetOverlayPythonTest_type_zero :
    evalExpr 5 (balanceProgram .python) (resetOverlayTestMachine .python 0)
      resetOverlayTestFrame resetPythonOverlayStringTest = .ok ⟨resetOverlayTestMachine .python 0,
        .ok (.bool false)⟩ :=
  resetOverlayTest_eval (by
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    decide +kernel)

example :
    execStmt 7 (balanceProgram .python) (resetOverlayTestMachine .python 0) resetOverlayTestFrame
      (balanceResetOverlayWrite .python) =
        .ok ⟨balanceOverlayUpdated .python (resetOverlayTestMachine .python 0) 1 0,
          resetOverlayTestFrame, .normal⟩ :=
  balanceReset_overlay_write_python_execute rfl rfl rfl rfl
    resetOverlayPythonTest_type_zero (by decide +kernel) (writeOwn_balance_existing rfl)

example :
    execStmt 7 (balanceProgram .python) (resetOverlayTestMachine .python 9007199254740991)
      resetOverlayTestFrame (balanceResetOverlayWrite .python) =
        .ok ⟨balanceOverlayUpdated .python (resetOverlayTestMachine .python 9007199254740991)
          1 9007199254740991, resetOverlayTestFrame, .normal⟩ :=
  balanceReset_overlay_write_python_execute rfl rfl rfl rfl
    (resetOverlayTest_eval (by
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    decide +kernel)) (by decide +kernel) (writeOwn_balance_existing rfl)

-- Closed reached-loop regressions inspect both normal control and the actual
-- candidate descriptor; they are not all-input constructor theorems.
example :
    let e := balanceResetMiddleEntry .python 0
    resetOverlaySuccessCheck .python 0
      (execStmt 40 (balanceProgram .python) e.1 e.2 (balanceResetOverlayLoop .python)) :=
  balanceReset_python_overlay_zero_check

example :
    let e := balanceResetMiddleEntry .ts 0
    ∃ m f,
      execStmt 40 (balanceProgram .ts) e.1 e.2
        (.sequence (ifNoStmt (balanceResetMiddleStmt .ts 2)) (balanceResetOverlayLoop .ts)) =
          .ok ⟨m, f, .normal⟩ ∧
      resetCandidateBalanceRead m f = .ok (some (integerValue .ts 0)) :=
  resetOverlaySuccessCheck_sound balanceReset_ts_overlay_zero_check

example {m f k}
    (hn : localValue m f "name" = .ok (.string "balance"))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hs : localValue m f "str" = .ok (.builtin .strType)) :
    evalExpr (k + 4) (balanceProgram .python) m f resetPythonOverlayNameTest =
      .ok ⟨m, .ok (.bool false)⟩ :=
  resetPythonOverlayName_execute hn ht hs

#print axioms balanceReset_overlay_loop_shape
#print axioms balanceReset_overlay_loop_execute
#print axioms balanceReset_python_known_key_execute
#print axioms resetOverlaySuccessCheck_sound
#print axioms balanceReset_python_overlay_zero_check
#print axioms balanceReset_ts_overlay_zero_check

example {lang m source final f ff listRef pairRef list pair value k}
    (he : evalExpr (k + 2) (balanceProgram lang) m f (resetOverlayIterable lang) =
      .ok ⟨source, .ok (.object listRef)⟩)
    (hl : objectAt source listRef = .ok list)
    (hk : list.kind = (if lang == .ts then .jsArray else .pythonList))
    (hi : list.items = [.object pairRef])
    (hp : objectAt source pairRef = .ok pair)
    (hv : pair.items = [.string "balance", value])
    (hn : lang = .python → f.locals.lookup "name" = none)
    (hf : lang = .python → f.locals.lookup "value" = none)
    (hb : execStmt (k + 1) (balanceProgram lang)
      (resetOverlayPairBinding lang source f value).1
      (resetOverlayPairBinding lang source f value).2
      (resetLoopBody (balanceResetOverlayLoop lang)) = .ok ⟨final, ff, .normal⟩) :
    execStmt (k + 3) (balanceProgram lang) m f (balanceResetOverlayLoop lang) =
      .ok ⟨final, (if lang == .ts then f else ff), .normal⟩ :=
  balanceReset_overlay_loop_execute he hl hk hi hp hv hn hf hb

-- The known-key helper is exercised on a live context-definition object.
example :
    evalExpr 4 (balanceProgram .python) (resetOverlayTestMachine .python 0)
      resetOverlayTestFrame resetPythonOverlayKnownKeyTest =
        .ok ⟨resetOverlayTestMachine .python 0, .ok (.bool false)⟩ := by
  apply balanceReset_python_known_key_execute (ref := 3) (object :=
    { literalObject .python TargetMachine.empty with
      own := [("balance", ⟨some (.object 4), none, none, true, true, true⟩)] })
  · rfl
  · apply resetOverlayTest_eval
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    decide +kernel
  · rfl
  · rfl
  · rfl

-- Closed canonical tables are tested at the actual fresh iteration binding,
-- rather than only on the small synthetic heap used by the unit regression.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
example :
    let e := balanceResetMiddleEntry .python 0
    let bound := resetOverlayPairBinding .python e.1 e.2 (integerValue .python 0)
    evalExpr 5 (balanceProgram .python) bound.1 bound.2 resetPythonOverlayStringTest =
      .ok ⟨bound.1, .ok (.bool false)⟩ := by
  apply resetOverlayTest_eval
  unfold balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
example :
    let e := balanceResetMiddleEntry .python 0
    let bound := resetOverlayPairBinding .python e.1 e.2 (integerValue .python 0)
    evalExpr 4 (balanceProgram .python) bound.1 bound.2 resetPythonOverlayKnownKeyTest =
      .ok ⟨bound.1, .ok (.bool false)⟩ := by
  apply resetOverlayTest_eval
  unfold balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel
