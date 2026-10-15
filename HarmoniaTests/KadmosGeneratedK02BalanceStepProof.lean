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

-- This interface discharges the real iterable and iterator tail for all b;
-- the body premise remains explicit and is not a constructor certificate.
example {b k final ff}
    (hb : let e := balanceResetMiddleEntry .python b
      execStmt (k + 4) (balanceProgram .python)
        (resetOverlayPairBinding .python (resetIterableMachine .python e.1 b)
          e.2 (integerValue .python b)).1
        (resetOverlayPairBinding .python (resetIterableMachine .python e.1 b)
          e.2 (integerValue .python b)).2
        (resetLoopBody (balanceResetOverlayLoop .python)) = .ok ⟨final, ff, .normal⟩) :
    let e := balanceResetMiddleEntry .python b
    execStmt (k + 6) (balanceProgram .python) e.1 e.2 (balanceResetOverlayLoop .python) =
      .ok ⟨final, ff, .normal⟩ :=
  balanceReset_python_canonical_loop_execute hb

example {m f ref object b k}
    (hc : readPropertyValue .ts m (.object object) "entries" =
      .ok ⟨m, .ok (.builtin .objectEntries)⟩)
    (hg : localValue m f "Object" = .ok (.object object))
    (hr : localValue m f "overrides" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b)) :
    evalExpr (k + 4) (balanceProgram .ts) m f (resetOverlayIterable .ts) =
      .ok ⟨resetIterableMachine .ts m b, .ok (.object (resetIterableRef .ts m))⟩ :=
  balanceReset_ts_iterable_execute hc hg hr ho

#print axioms hostEntries_one
#print axioms evalList_copy
#print axioms balanceReset_python_canonical_loop_execute
#print axioms balanceReset_ts_iterable_execute

example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) (b : Int) :
    let bound := resetOverlayPairBinding lang m f (integerValue lang b)
    localValue bound.1 bound.2 "name" = .ok (.string "balance") ∧
    localValue bound.1 bound.2 "value" = .ok (integerValue lang b) :=
  resetOverlayPairBinding_reads lang m f (integerValue lang b)

#print axioms resetOverlayPairBinding_reads

-- Symbolic safe-domain execution must discharge the actual TS loop guard.
#check balanceReset_ts_overlay_body_safe
#check resetTsOverlayGuard_execute

-- A live, nonvacuous TS environment exercises both the actual guard and write
-- for symbolic safe signed values, including the negative half of the domain.
def resetTsBodyTestMachine (b : Int) : TargetMachine :=
  { resetOverlayTestMachine .ts b with
    objects := (5, { literalObject .ts TargetMachine.empty with
      own := [("hasOwn", ⟨some (.builtin .objectHasOwn), none, none, true, true, true⟩),
        ("entries", ⟨some (.builtin .objectEntries), none, none, true, true, true⟩)] }) ::
      (6, { literalObject .ts TargetMachine.empty with
      own := [("isSafeInteger", ⟨some (.builtin .jsIsSafeInteger), none, none, true, true, true⟩)] }) ::
      (resetOverlayTestMachine .ts b).objects,
    cells := [(5, .object 5), (6, .object 6), (7, .object 2), (8, .object 3)] ++
      (resetOverlayTestMachine .ts b).cells,
    globals := [("Object", 5), ("Number", 6), ("world", 7), ("contextDefinitions", 8)],
    nextCell := 9, nextObject := 7 }

def resetTsBodyTest_physical (b : Int) :
    ResetTsOverlayPhysical (resetTsBodyTestMachine b) resetOverlayTestFrame b := by
  refine ⟨5, 2, 3, 3, 4, 6, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨⟨some (.object 4), none, none, true, true, true⟩, rfl⟩

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    execStmt 10 (balanceProgram .ts) (resetTsBodyTestMachine b) resetOverlayTestFrame
      (resetLoopBody (balanceResetOverlayLoop .ts)) =
        .ok ⟨balanceOverlayUpdated .ts (resetTsBodyTestMachine b) 1 b, resetOverlayTestFrame, .normal⟩ :=
  balanceReset_ts_overlay_body_safe (resetTsBodyTest_physical b) rfl rfl hb

example :
    execStmt 10 (balanceProgram .ts) (resetTsBodyTestMachine (-9007199254740991)) resetOverlayTestFrame
      (resetLoopBody (balanceResetOverlayLoop .ts)) =
        .ok ⟨balanceOverlayUpdated .ts (resetTsBodyTestMachine (-9007199254740991)) 1 (-9007199254740991),
          resetOverlayTestFrame, .normal⟩ :=
  balanceReset_ts_overlay_body_safe (resetTsBodyTest_physical _) rfl rfl (by decide)

#print axioms balanceReset_ts_overlay_body_shape
#print axioms resetTsOverlayGuard_execute
#print axioms balanceReset_ts_overlay_body_safe
#print axioms balanceReset_ts_overlay_loop_safe

-- Inspect the actual post-body candidate, rather than just its normal control.
example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    resetOverlaySuccessCheck .ts b
      (execStmt 10 (balanceProgram .ts) (resetTsBodyTestMachine b) resetOverlayTestFrame
        (resetLoopBody (balanceResetOverlayLoop .ts))) :=
  balanceReset_ts_overlay_body_success (resetTsBodyTest_physical b) rfl rfl hb

#print axioms balanceOverlayUpdated_candidate_read
#print axioms balanceReset_ts_overlay_body_success

-- Run the actual TS Object.entries loop with fresh pair bindings and an outer
-- frame containing old name/value bindings, then inspect the restored frame.
def resetTsLoopTestMachine (b : Int) : TargetMachine :=
  { resetTsBodyTestMachine b with
    objects := (7, balanceHeapObject .ts TargetMachine.empty b) :: (resetTsBodyTestMachine b).objects,
    cells := (9, .object 7) :: (resetTsBodyTestMachine b).cells,
    globals := ("overrides", 9) :: (resetTsBodyTestMachine b).globals,
    nextCell := 10, nextObject := 8 }

def resetTsLoopTest_physical (b : Int) :
    let source := resetIterableMachine .ts (resetTsLoopTestMachine b) b
    let bound := resetOverlayPairBinding .ts source resetOverlayTestFrame (integerValue .ts b)
    ResetTsOverlayPhysical bound.1 bound.2 b := by
  refine ⟨5, 2, 3, 3, 4, 6, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨⟨some (.object 4), none, none, true, true, true⟩, rfl⟩

theorem resetTsLoopTest_execute (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    execStmt 12 (balanceProgram .ts) (resetTsLoopTestMachine b) resetOverlayTestFrame
      (balanceResetOverlayLoop .ts) =
        .ok ⟨balanceOverlayUpdated .ts
          (resetOverlayPairBinding .ts (resetIterableMachine .ts (resetTsLoopTestMachine b) b)
            resetOverlayTestFrame (integerValue .ts b)).1 1 b,
          resetOverlayTestFrame, .normal⟩ := by
  exact balanceReset_ts_seed_loop_safe rfl rfl rfl rfl
    (resetTsLoopTest_physical b) rfl rfl hb

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    resetOverlaySuccessCheck .ts b
      (execStmt 12 (balanceProgram .ts) (resetTsLoopTestMachine b) resetOverlayTestFrame
        (balanceResetOverlayLoop .ts)) := by
  rw [resetTsLoopTest_execute b hb]
  unfold resetOverlaySuccessCheck
  simp only [Except.toOption, Option.map, Option.some.injEq, Prod.mk.injEq]
  exact ⟨True.intro, balanceOverlayUpdated_candidate_read rfl rfl⟩

#print axioms resetTsLoopTest_execute

#print axioms balanceReset_ts_seed_loop_safe

-- A live frozen context table exercises the mapping-proxy own-key rule.
def resetProxyMembershipTestMachine (b : Int) : TargetMachine :=
  { resetOverlayTestMachine .python b with objects :=
    (3, ⟨.mappingProxy, none,
      [("balance", ⟨some (.object 4), none, none, true, true, true⟩)], [], [], true, false⟩) ::
      (resetOverlayTestMachine .python b).objects }

example (b : Int) (k : Nat) :
    evalExpr (k + 4) (balanceProgram .python) (resetProxyMembershipTestMachine b) resetOverlayTestFrame
      resetPythonOverlayKnownKeyTest = .ok ⟨resetProxyMembershipTestMachine b, .ok (.bool false)⟩ := by
  apply balanceReset_python_known_key_proxy_execute (ref := 3)
    (object := ⟨.mappingProxy, none,
      [("balance", ⟨some (.object 4), none, none, true, true, true⟩)], [], [], true, false⟩)
  · rfl
  · simp only [evalExpr, Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang]; rfl
  · rfl
  · rfl
  · rfl

-- Safe signed overlay acceptance and later nonnegative bounds remain separate.
example :
    execStmt 10 (balanceProgram .ts) (resetTsBodyTestMachine 9007199254740991) resetOverlayTestFrame
      (resetLoopBody (balanceResetOverlayLoop .ts)) =
        .ok ⟨balanceOverlayUpdated .ts (resetTsBodyTestMachine 9007199254740991) 1 9007199254740991,
          resetOverlayTestFrame, .normal⟩ :=
  balanceReset_ts_overlay_body_safe (resetTsBodyTest_physical _) rfl rfl (by decide)

#print axioms balanceReset_python_known_key_proxy_execute

-- Definition-table tests depend on the name, never on the signed payload.
-- This is a canonical overlay fact; later nonnegative validation is separate.
example (b : Int) (k : Nat) :
    let e := balanceResetPythonOverlayBound b
    evalExpr (k + 8) (balanceProgram .python) e.1 e.2 resetPythonOverlayGuardType =
      .ok ⟨resetPythonOverlayTypedMachine e.1, .ok (.bool false)⟩ :=
  (balanceReset_python_canonical_table_tests b k).1

example (b : Int) (k : Nat) :
    let e := balanceResetPythonOverlayBound b
    evalExpr (k + 5) (balanceProgram .python) e.1 e.2 resetPythonOverlayStringTest =
      .ok ⟨e.1, .ok (.bool false)⟩ :=
  (balanceReset_python_canonical_table_tests b k).2

#print axioms balanceReset_python_canonical_table_tests

-- The actual canonical Python iterable, pair binding and helper-backed body
-- compose without a body-success or environment premise.
example (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    execStmt (k + 22) (balanceProgram .python) e.1 e.2 (balanceResetOverlayLoop .python) =
      .ok ⟨balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b,
        (balanceResetPythonOverlayBound b).2, .normal⟩ :=
  (balanceReset_python_canonical_overlay_safe b hb k).1

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetPythonOverlayBound b
    execStmt (k + 20) (balanceProgram .python) e.1 e.2
      (resetLoopBody (balanceResetOverlayLoop .python)) =
        .ok ⟨balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b, e.2, .normal⟩ :=
  balanceReset_python_canonical_overlay_body_safe b hb k

-- Boundary instantiation observes statement-2 success, rather than merely a
-- primitive safe-integer test at the largest positive supported payload.
example :
    let b : Int := 9007199254740991
    let e := balanceResetMiddleEntry .python b
    execStmt 25 (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 2) =
      .ok ⟨balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b,
        (balanceResetPythonOverlayBound b).2, .normal⟩ :=
  (balanceReset_python_canonical_overlay_safe (9007199254740991 : Int) (by decide) 0).2

example (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 7) (balanceProgram .ts) e.1 e.2 (ifNoStmt (balanceResetMiddleStmt .ts 2)) =
      execStmt (k + 6) (balanceProgram .ts) e.1 e.2
        (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) :=
  balanceReset_ts_canonical_plain_guard_skip b k

#print axioms balanceReset_python_canonical_overlay_body_safe
#print axioms balanceReset_python_canonical_overlay_safe
#print axioms balanceReset_ts_canonical_plain_guard_skip

-- Primitive bounds checks include both endpoints in each target language.
example (lang : TargetLang) (m : TargetMachine) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    binaryValue lang m .lt (integerValue lang b) (integerValue lang 0) =
      .ok (.ok (.bool false)) ∧
    binaryValue lang m .gt (integerValue lang b) (integerValue lang 9007199254740991) =
      .ok (.ok (.bool false)) := resetBounds_reject_comparisons m hb

-- The separate TS entries loop shifts the validation binding by one node.
example : balanceResetMiddleStmt .ts 4 = snapshotBindStmt .ts "invalid" (resetBoundsCall .ts) ∧
    balanceResetMiddleStmt .python 3 = snapshotBindStmt .python "invalid" (resetBoundsCall .python) :=
  ⟨(balanceReset_validation_shapes .ts).1, (balanceReset_validation_shapes .python).1⟩

example {lang m f candidate k}
    (hv : localValue m f "candidate" = .ok (.object candidate))
    (hs : lang = .python → localValue m f "_INITIAL" = .ok (.string "Ready")) :
    evalArgValues (k + 3) (balanceProgram lang) m f
      (.sequence (if lang == .ts then .string "Ready" else .local "_INITIAL")
        (.sequence (.local "candidate") .empty)) =
      .ok ⟨m, .ok [.string "Ready", .object candidate]⟩ :=
  resetInvariantCall_args_execute hv hs

#print axioms resetBounds_reject_comparisons
#print axioms resetBounds_comparison_execute
#print axioms balanceReset_validation_shapes

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 27) (balanceProgram .ts) e.1 e.2
      (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts)) =
      .ok ⟨balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b,
        (balanceResetTsDescriptorEntry b).2, .normal⟩ :=
  balanceReset_ts_canonical_overlay_safe b hb k

example :
    let b : Int := 9007199254740991
    let e := balanceResetMiddleEntry .ts b
    execStmt 27 (balanceProgram .ts) e.1 e.2
      (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts)) =
      .ok ⟨balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b,
        (balanceResetTsDescriptorEntry b).2, .normal⟩ :=
  balanceReset_ts_canonical_overlay_safe (9007199254740991 : Int) (by decide) 0

-- A negative safe value survives the overlay and fails the later minimum
-- predicate; it does not acquire a constructor-success claim.
example :
    let final := balanceOverlayUpdated .ts (balanceResetTsOverlayBound (-1)).1 23 (-1)
    resetCandidateBalanceRead final (balanceResetTsDescriptorEntry (-1)).2 =
      .ok (some (integerValue .ts (-1))) ∧
    binaryValue .ts final .lt (integerValue .ts (-1)) (integerValue .ts 0) =
      .ok (.ok (.bool true)) :=
  ⟨balanceReset_ts_canonical_overlay_candidate_read (-1), rfl⟩

#print axioms balanceReset_ts_canonical_overlay_loop_safe
#print axioms balanceReset_ts_canonical_overlay_safe
#print axioms balanceReset_ts_canonical_overlay_bounded

#print axioms balanceReset_ts_canonical_overlay_bounds_bind
#print axioms balanceReset_python_canonical_overlay_bounds_bind

-- Batch 15: actual emitted bounds execution on the complete canonical overlay.
example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetPostOverlay lang b
    evalExpr (k + 24) (balanceProgram lang) e.1 e.2 (resetBoundsCall lang) =
      .ok ⟨balanceBoundsFinal lang b, .ok (resetValidationResult lang)⟩ :=
  balanceReset_bounds_call_execute lang b hb k

example (lang : TargetLang) (k : Nat) :
    let e := balanceResetPostOverlay lang 0
    evalExpr (k + 24) (balanceProgram lang) e.1 e.2 (resetBoundsCall lang) =
      .ok ⟨balanceBoundsFinal lang 0, .ok (resetValidationResult lang)⟩ :=
  balanceReset_bounds_call_execute lang 0 (by decide) k

example (lang : TargetLang) (k : Nat) :
    let e := balanceResetPostOverlay lang 9007199254740991
    evalExpr (k + 24) (balanceProgram lang) e.1 e.2 (resetBoundsCall lang) =
      .ok ⟨balanceBoundsFinal lang 9007199254740991, .ok (resetValidationResult lang)⟩ :=
  balanceReset_bounds_call_execute lang 9007199254740991 (by decide) k

-- The Pratt routine's numeric comparison is universal; whole runtime parsing
-- and invariant-body execution are still distinct obligations.
example (lang : TargetLang) (m : TargetMachine) (b : Int) (hb : 0 ≤ b) :
    binaryValue lang m .ge (integerValue lang b) (integerValue lang 0) =
      .ok (.ok (.bool true)) := resetInvariant_ge_nonnegative lang m hb

#print axioms balanceReset_bounds_body_execute
#print axioms balanceReset_bounds_call_execute
#print axioms balanceReset_ts_canonical_overlay_bounds_bind_complete
#print axioms balanceReset_python_canonical_overlay_bounds_bind_complete
#print axioms resetInvariantCall_eq_body
#print axioms resetInvariant_ts_identifier_execute
#print axioms resetInvariant_python_identifier_execute
#print axioms balanceReset_invariant_publication_cleanup

-- The optional event binding matches the actual installed invariant methods.
example (lang : TargetLang) :
    (balanceStoredInvariant lang).params = resetInvariantParams lang ∧
    (lang = .python → (balanceStoredInvariant lang).pythonDefaults =
      [none, none, some TargetValue.null]) := balanceStoredInvariant_params lang

-- These are the source Pratt routines' identifier expressions, not a closed
-- zero-only interpreter run.
example {m f ref b k}
    (he : localValue m f "env" = .ok (.object ref))
    (ht : localValue m f "token" = .ok (.string "balance"))
    (hc : ref ≠ m.checkerRef) (hp : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b)) :
    evalExpr (k + 2) (balanceProgram .ts) m f
      (.index (.local "env") (.local "token")) =
      .ok ⟨m, .ok (integerValue .ts b)⟩ :=
  resetInvariant_ts_identifier_execute he ht hc hp ho rfl rfl

example {m f ref fallback b k}
    (he : localValue m f "environment" = .ok (.object ref))
    (ht : localValue m f "token" = .ok (.string "balance"))
    (hu : localValue m f "_UNDEFINED" = .ok fallback)
    (hc : ref ≠ m.checkerRef) (hp : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok (balanceHeapObject .python m b)) :
    evalExpr (k + 4) (balanceProgram .python) m f
      (.call (.property (.local "environment") "get")
        (.sequence (.local "token") (.sequence (.local "_UNDEFINED") .empty))) =
      .ok ⟨m, .ok (integerValue .python b)⟩ :=
  resetInvariant_python_identifier_execute he ht hu hc hp ho rfl rfl

-- The actual source invariant suffix and cleanup retain helper allocations.
example {lang m final f candidate k}
    (he : evalExpr (k + 10) (balanceProgram lang) m f (resetInvariantCall lang) =
      .ok ⟨final, .ok (resetValidationResult lang)⟩)
    (hn : lang = .python → snapshotAddress m f "violated" = none)
    (hr : let bound := snapshotBound lang final f "violated" (resetValidationResult lang)
      bound.2.receiver = some bound.1.checkerRef)
    (hc : let bound := snapshotBound lang final f "violated" (resetValidationResult lang)
      localValue bound.1 bound.2 "candidate" = .ok (.object candidate))
    (hi : let bound := snapshotBound lang final f "violated" (resetValidationResult lang)
      lang = .python → localValue bound.1 bound.2 "_INITIAL" = .ok (.string "Ready")) :
    let bound := snapshotBound lang final f "violated" (resetValidationResult lang)
    execStmt (k + 13) (balanceProgram lang) m f
      (.sequence
        (dropStmts (resetValidationIndex lang + 2) (balanceResetProtected lang).body)
        (balanceResetProtected lang).cleanup) =
      .ok ⟨balanceSetBusy (resetPublished lang bound.1 candidate) false, bound.2, .normal⟩ :=
  balanceReset_invariant_publication_cleanup he hn hr hc hi

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    let bound := snapshotBound .ts (balanceBoundsFinal .ts b)
      (balanceResetTsDescriptorEntry b).2 "invalid" .undefined
    execStmt (k + 28) (balanceProgram .ts) e.1 e.2
      (.sequence (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts))
        (balanceResetMiddleStmt .ts 4)) = .ok ⟨bound.1, bound.2, .normal⟩ ∧
    execStmt (k + 27) (balanceProgram .ts) bound.1 bound.2
      (balanceResetMiddleStmt .ts 5) = .ok ⟨bound.1, bound.2, .normal⟩ :=
  balanceReset_ts_canonical_overlay_bounds_bind_complete b hb k

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    let bound := snapshotBound .python (balanceBoundsFinal .python b)
      (balanceResetPythonOverlayBound b).2 "invalid" .null
    execStmt (k + 26) (balanceProgram .python) e.1 e.2
      (.sequence (balanceResetMiddleStmt .python 2) (balanceResetMiddleStmt .python 3)) =
      .ok ⟨bound.1, bound.2, .normal⟩ ∧
    execStmt (k + 25) (balanceProgram .python) bound.1 bound.2
      (balanceResetMiddleStmt .python 4) = .ok ⟨bound.1, bound.2, .normal⟩ :=
  balanceReset_python_canonical_overlay_bounds_bind_complete b hb k

-- Execute the two provided arguments and omitted event default using the
-- actual installed invariant closure's parameter/default metadata.
example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame)
    (candidate : ObjRef) (k : Nat) :
    bindCallParams (k + 4) (balanceProgram lang) m f
      (balanceStoredInvariant lang).params (balanceStoredInvariant lang).pythonDefaults
      [.string "Ready", .object candidate] =
      .ok ⟨(resetInvariantBindings lang m f candidate).1,
        (resetInvariantBindings lang m f candidate).2, .ok ()⟩ := by
  rw [(balanceStoredInvariant_params lang).1]
  exact resetInvariant_bindCallParams (balanceStoredInvariant_params lang).2

-- Batch 16: direct contracts, mirrored in both requested regression roots.

section Batch16NumericCleanContracts

open Harmonia.Applications.Kadmos.Generated.T398Batch16Numeric

example (m : TargetMachine) (f : TargetFrame) (k : Nat) :
    execStmt (k + 3) (balanceProgram .ts) m f tsDefinition =
      .ok ⟨definedMachine .ts m f "numeric" tsBody, definedFrame m f "numeric", .normal⟩ := by
  apply tsCreate_execute <;> assumption

example {m f b k} (h : TsPhysical m f b) :
    execStmt (k + 8) (balanceProgram .ts) m f tsBody =
      .ok ⟨m, f, .returned (.number .jsNumber b)⟩ := by
  apply tsBody_execute <;> assumption

example {m f callee arg ref closure b k}
    (hc : localValue m f callee = .ok (.closure ref))
    (hv : localValue m f arg = .ok (.number .jsNumber b))
    (hr : closureAt m ref = .ok closure)
    (hp : closure.params = [⟨"value", none⟩])
    (hs : closure.body = tsBody)
    (h : let e := callEntry m closure (.number .jsNumber b)
      TsPhysical e.1 e.2 b) :
    evalExpr (k + 9) (balanceProgram .ts) m f
      (.call (.local callee) (.sequence (.local arg) .empty)) =
      .ok ⟨(callEntry m closure (.number .jsNumber b)).1, .ok (.number .jsNumber b)⟩ := by
  apply tsCall_execute <;> assumption

example {m f b k} (h : PyPhysical m f b)
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 10) (balanceProgram .python) m f pyClosure.body =
      .ok ⟨resetSafeTupleMachine m, f, .returned (.number .pyFloat b)⟩ := by
  apply pyBody_execute <;> assumption

example {m f callee arg ref closure b k}
    (hc : localValue m f callee = .ok (.closure ref))
    (hv : localValue m f arg = .ok (.number .pyInt b))
    (hr : closureAt m ref = .ok closure)
    (hp : closure.params = [⟨"value", none⟩]) (hs : closure.body = pyClosure.body)
    (h : let e := callEntry m closure (.number .pyInt b)
      PyPhysical e.1 e.2 b)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    evalExpr (k + 11) (balanceProgram .python) m f
      (.call (.local callee) (.sequence (.local arg) .empty)) =
      .ok ⟨resetSafeTupleMachine (callEntry m closure (.number .pyInt b)).1,
        .ok (.number .pyFloat b)⟩ := by
  apply pyCall_interval <;> assumption

example {m f callee arg ref closure k}
    (hc : localValue m f callee = .ok (.closure ref))
    (hv : localValue m f arg = .ok (.number .pyFloat 0))
    (hr : closureAt m ref = .ok closure)
    (hp : closure.params = [⟨"value", none⟩]) (hs : closure.body = pyClosure.body)
    (h : let e := callEntry m closure (.number .pyFloat 0)
      PyFloatPhysical e.1 e.2 0) :
    evalExpr (k + 11) (balanceProgram .python) m f
      (.call (.local callee) (.sequence (.local arg) .empty)) =
      .ok ⟨resetSafeTupleMachine (callEntry m closure (.number .pyFloat 0)).1,
        .ok (.number .pyFloat 0)⟩ := by
  apply pyFloatCall_zero <;> assumption

example {m f b k} (h : PyFloatPhysical m f b)
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 10) (balanceProgram .python) m f pyClosure.body =
      .ok ⟨resetSafeTupleMachine m, f, .returned (.number .pyFloat b)⟩ := by
  apply pyFloatBody_execute <;> assumption

example {m f ref closure b k}
    (hc : localValue m f "numeric" = .ok (.closure ref))
    (hl : localValue m f "left" = .ok (.number .jsNumber b))
    (hr : closureAt m ref = .ok closure)
    (hp : closure.params = [⟨"value", none⟩]) (hs : closure.body = tsBody)
    (h : let e := callEntry m closure (.number .jsNumber b)
      TsPhysical e.1 e.2 b)
    (hc2 : let n := (callEntry m closure (.number .jsNumber b)).1
      localValue n f "numeric" = .ok (.closure ref))
    (hz : let n := (callEntry m closure (.number .jsNumber b)).1
      localValue n f "right" = .ok (.number .jsNumber 0))
    (h2 : let n := (callEntry m closure (.number .jsNumber b)).1
      let e := callEntry n closure (.number .jsNumber 0)
      TsPhysical e.1 e.2 0)
    (hb : 0 ≤ b) :
    let n := (callEntry m closure (.number .jsNumber b)).1
    evalExpr (k + 10) (balanceProgram .ts) m f
      (.binary .ge
        (.call (.local "numeric") (.sequence (.local "left") .empty))
        (.call (.local "numeric") (.sequence (.local "right") .empty))) =
      .ok ⟨(callEntry n closure (.number .jsNumber 0)).1, .ok (.bool true)⟩ := by
  apply tsGe_execute <;> assumption

example {m f ref closure b k}
    (hc : localValue m f "_number" = .ok (.closure ref))
    (hl : localValue m f "left" = .ok (.number .pyInt b))
    (hr : closureAt m ref = .ok closure)
    (hp : closure.params = [⟨"value", none⟩]) (hs : closure.body = pyClosure.body)
    (h : let e := callEntry m closure (.number .pyInt b)
      PyPhysical e.1 e.2 b)
    (hc2 : let n := resetSafeTupleMachine (callEntry m closure (.number .pyInt b)).1
      localValue n f "_number" = .ok (.closure ref))
    (hz : let n := resetSafeTupleMachine (callEntry m closure (.number .pyInt b)).1
      localValue n f "right" = .ok (.number .pyFloat 0))
    (h2 : let n := resetSafeTupleMachine (callEntry m closure (.number .pyInt b)).1
      let e := callEntry n closure (.number .pyFloat 0)
      PyFloatPhysical e.1 e.2 0)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    let n := resetSafeTupleMachine (callEntry m closure (.number .pyInt b)).1
    evalExpr (k + 12) (balanceProgram .python) m f
      (.binary .ge
        (.call (.local "_number") (.sequence (.local "left") .empty))
        (.call (.local "_number") (.sequence (.local "right") .empty))) =
      .ok ⟨resetSafeTupleMachine (callEntry n closure (.number .pyFloat 0)).1, .ok (.bool true)⟩ := by
  apply pyGe_execute <;> assumption

example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame)
    (name : String) (body : TargetStmt) :
    let n := definedMachine lang m f name body
    n.nextCell = m.nextCell + 1 ∧ n.nextClosure = m.nextClosure + 1 ∧
    n.nextObject = m.nextObject ∧ n.objects = m.objects ∧ n.checker = m.checker ∧
    n.globals = m.globals := by
  apply definedMachine_effects <;> assumption

end Batch16NumericCleanContracts

section Batch16CompositionContracts

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    execStmt (k + (if lang == .ts then 33 else 32)) (balanceProgram lang)
      (balanceCanonicalResetStage lang b 3).1 (balanceCanonicalResetStage lang b 3).2
      (balanceResetProtected lang).body =
    execStmt (k + 27) (balanceProgram lang)
      (balanceResetPostBounds lang b).1 (balanceResetPostBounds lang b).2
      (dropStmts (resetValidationIndex lang + 2) (balanceResetProtected lang).body) := by
  apply balanceReset_canonical_to_invariant <;> assumption

example {lang b final candidate}
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991)
    (h : BalanceResetInvariantEvidence lang b final candidate (if lang == .ts then 80 else 74)) :
    execStmt (if lang == .ts then 96 else 89) (balanceProgram lang)
      (balanceResetOriginalEntry lang b).1 (balanceResetOriginalEntry lang b).2
      (balanceStoredReset lang).2.body =
      .ok ⟨balanceResetCanonicalFinal lang b final candidate,
        (balanceResetAfterInvariant lang b final).2, .normal⟩ := by
  apply balanceReset_canonical_execute_of_invariant <;> assumption

example {lang b final candidate}
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991)
    (h : BalanceResetInvariantEvidence lang b final candidate (if lang == .ts then 80 else 74))
    (hc : BalanceConstructorCopyEvidence lang b (balanceResetCanonicalFinal lang b final candidate)) :
    execStmt 99 (balanceProgram lang)
      (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (balanceStoredConstructor lang).2.body =
      .ok ⟨balanceConstructorCopied lang (balanceResetCanonicalFinal lang b final candidate) b,
        (balanceConstructorBodyEntry lang b).2, .normal⟩ := by
  apply balanceConstructor_canonical_execute_of_invariant <;> assumption

example {lang b final candidate}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (h : BalanceResetInvariantEvidence lang b final candidate (if lang == .ts then 80 else 74))
    (hc : BalanceConstructorCopyEvidence lang b (balanceResetCanonicalFinal lang b final candidate)) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) =
      .ok (balanceConstructorCopied lang (balanceResetCanonicalFinal lang b final candidate) b) := by
  apply targetConstruct_balance_of_invariant <;> assumption

example {lang b m}
    (hw : HeapWF lang (balanceConstructorCopied lang m b))
    (hr : m.checker.state = "Ready")
    (hc : objectAt m m.checker.context = .ok (balanceHeapObject lang m b))
    (hh : objectAt m m.checker.history = .ok (emptyBalanceHistory lang m))
    (hu : m.checker.undo = none) (hi : m.checker.busy = false)
    (hnc : m.checker.context ≠ m.nextObject)
    (hnh : m.checker.history ≠ m.nextObject) :
    BalanceRep lang b (balanceConstructorCopied lang m b) := by
  apply balanceConstructorCopied_rep <;> assumption

example {lang b final candidate}
    (hc : objectAt final candidate = .ok (balanceHeapObject lang final b))
    (hn : candidate ≠ final.nextObject)
    (hnext : candidate ≠ final.nextObject + 1)
    (hw : HeapWF lang
      (balanceConstructorCopied lang (balanceResetCanonicalFinal lang b final candidate) b)) :
    BalanceRep lang b
      (balanceConstructorCopied lang (balanceResetCanonicalFinal lang b final candidate) b) := by
  apply balanceResetCanonicalFinal_rep_after_copy <;> assumption

example {lang b final candidate}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (h : BalanceResetInvariantEvidence lang b final candidate (if lang == .ts then 80 else 74))
    (hcopy : BalanceConstructorCopyEvidence lang b (balanceResetCanonicalFinal lang b final candidate))
    (hc : objectAt final candidate = .ok (balanceHeapObject lang final b))
    (hn : candidate ≠ final.nextObject)
    (hnext : candidate ≠ final.nextObject + 1)
    (hw : HeapWF lang
      (balanceConstructorCopied lang (balanceResetCanonicalFinal lang b final candidate) b)) :
    ∃ m, targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) = .ok m ∧
      BalanceRep lang b m := by
  apply targetConstruct_balance_rep_of_invariant <;> assumption

end Batch16CompositionContracts






-- Batch 16: canonical execution contracts, mirrored in both regression roots.
section Batch16CanonicalContracts

example : HeapWF .ts (balanceInvariantTsCopied 0) := by
  apply balanceInvariant_ts_heapWF_zero <;> assumption

example (b : Int) :
    heapWFCheck .ts (balanceInvariantTsCopied b) = heapWFCheck .ts (balanceInvariantTsCopied 0) := by
  apply balanceInvariant_ts_heapWF_footprint <;> assumption

example : HeapWF .python (balanceInvariantPyCopied 0) := by
  apply balanceInvariant_py_heapWF_zero <;> assumption

example (b : Int) :
    heapWFCheck .python (balanceInvariantPyCopied b) = heapWFCheck .python (balanceInvariantPyCopied 0) := by
  apply balanceInvariant_py_heapWF_footprint <;> assumption

example (b : Int) :
    balanceResetPostBounds .ts b = (balanceInvariantTsInput b, balanceInvariantTsInputFrame) := by
  apply balanceInvariant_ts_input_eq <;> assumption

example (n : Nat) :
    evalExpr 80 (balanceProgram .ts) (balanceInvariantTsInput (Int.ofNat n))
      balanceInvariantTsInputFrame (resetInvariantCall .ts) =
      .ok ⟨balanceInvariantTsFinal (Int.ofNat n), .ok .undefined⟩ := by
  apply balanceInvariant_ts_call_nat <;> assumption

example (b : Int) (hb : 0 ≤ b) :
    evalExpr 80 (balanceProgram .ts)
      (balanceResetPostBounds .ts b).1 (balanceResetPostBounds .ts b).2
      (resetInvariantCall .ts) = .ok ⟨balanceInvariantTsFinal b, .ok .undefined⟩ := by
  apply BalanceCanonicalTS.canonical_call <;> assumption

example (b : Int) (hb : 0 ≤ b) :
    BalanceResetInvariantEvidence .ts b (balanceInvariantTsFinal b) 23 80 := by
  apply BalanceCanonicalTS.invariant_evidence <;> assumption

example (b : Int) :
    balanceResetAfterInvariant .ts b (balanceInvariantTsFinal b) = balanceInvariantTsBound b := by
  apply BalanceCanonicalTS.after_invariant_eq <;> assumption

example (b : Int) :
    balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23 = balanceInvariantTsReset b := by
  apply BalanceCanonicalTS.reset_final_eq <;> assumption

example (b : Int) : HeapWF .ts (balanceInvariantTsCopied b) := by
  apply BalanceCanonicalTS.copied_heapWF <;> assumption

example (b : Int) :
    ∀ e ∈ (balanceInvariantTsReset b).objects, e.1 ≠ (balanceInvariantTsReset b).nextObject := by
  apply BalanceCanonicalTS.reset_object_fresh <;> assumption

example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) :
    (resetSnapshotsInstalled lang m f).1.checkerRef = m.checkerRef := by
  apply BalanceCanonicalTS.snapshots_ref <;> assumption

example (lang : TargetLang) (b : Int) :
    (balanceConstructorBodyEntry lang b).1.checkerRef =
      (balancePreparation lang).1.checkerRef := by
  apply BalanceCanonicalTS.constructor_ref <;> assumption

example (m : TargetMachine) (busy : Bool) :
    (balanceSetBusy m busy).checkerRef = m.checkerRef := by
  apply BalanceCanonicalTS.busy_ref <;> assumption

example (lang : TargetLang) (b : Int) :
    (balanceResetBodyEntry lang b).1.checkerRef =
      (balanceConstructorBodyEntry lang b).1.checkerRef := by
  apply BalanceCanonicalTS.reset_entry_ref <;> assumption

example : (balancePreparation .ts).1.checkerRef = 1 := by
  apply BalanceCanonicalTS.preparation_ref <;> assumption

example (b : Int) :
    BalanceConstructorCopyEvidence .ts b
      (balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23) := by
  apply BalanceCanonicalTS.copy_evidence <;> assumption

example (b : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    execStmt 96 (balanceProgram .ts)
      (balanceResetOriginalEntry .ts b).1 (balanceResetOriginalEntry .ts b).2
      (balanceStoredReset .ts).2.body =
      .ok ⟨balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23,
        (balanceResetAfterInvariant .ts b (balanceInvariantTsFinal b)).2, .normal⟩ := by
  apply BalanceCanonicalTS.canonical_reset <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    execStmt 99 (balanceProgram .ts)
      (balanceConstructorBodyEntry .ts b).1 (balanceConstructorBodyEntry .ts b).2
      (balanceStoredConstructor .ts).2.body =
      .ok ⟨balanceConstructorCopied .ts
          (balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23) b,
        (balanceConstructorBodyEntry .ts b).2, .normal⟩ := by
  apply BalanceCanonicalTS.canonical_constructor <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram .ts) (canonicalBalanceSeed .ts b) =
      .ok (balanceConstructorCopied .ts
        (balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23) b) := by
  apply BalanceCanonicalTS.targetConstruct_sound <;> assumption

example (b : Int) :
    balanceConstructorCopied .ts
      (balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23) b =
      balanceInvariantTsCopied b := by
  apply BalanceCanonicalTS.copied_eq <;> assumption

example (b : Int) :
    HeapWF .ts (balanceConstructorCopied .ts
      (balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23) b) := by
  apply BalanceCanonicalTS.canonical_copied_heapWF <;> assumption

example (b : Int) :
    BalanceRep .ts b (balanceConstructorCopied .ts
      (balanceResetCanonicalFinal .ts b (balanceInvariantTsFinal b) 23) b) := by
  apply BalanceCanonicalTS.canonical_balance_rep <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram .ts) (canonicalBalanceSeed .ts b) =
      .ok (balanceInvariantTsCopied b) := by
  apply BalanceCanonicalTS.targetConstruct_literal <;> assumption

example (b : Int) : BalanceRep .ts b (balanceInvariantTsCopied b) := by
  apply BalanceCanonicalTS.literal_balance_rep <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    ∃ m, targetConstruct (balanceProgram .ts) (canonicalBalanceSeed .ts b) = .ok m ∧
      BalanceRep .ts b m := by
  apply BalanceCanonicalTS.targetConstruct_balance_rep <;> assumption

example (b : Int) :
    (balanceInvariantTsFinal b).nextObject = 44 ∧
    (balanceInvariantTsReset b).nextObject = 45 ∧
    (balanceInvariantTsCopied b).nextObject = 46 ∧
    (balanceInvariantTsCopied b).checker.context = 23 ∧
    (balanceInvariantTsCopied b).checker.history = 44 ∧
    (balanceInvariantTsCopied b).checker.constructorSeed = some 45 ∧
    (balanceInvariantTsCopied b).nextCell = 69 ∧
    (balanceInvariantTsCopied b).nextClosure = 19 := by
  apply BalanceCanonicalTS.canonical_allocations <;> assumption

example (b : Int) :
    (balanceInvariantTsCopied b).frames = (balanceInvariantTsInput b).frames ∧
    (balanceInvariantTsCopied b).globals = (balanceInvariantTsFinal b).globals ∧
    (balanceInvariantTsCopied b).cells = (balanceInvariantTsBound b).1.cells ∧
    (balanceInvariantTsCopied b).closures = (balanceInvariantTsFinal b).closures ∧
    (balanceInvariantTsCopied b).classMethods = (balanceInvariantTsFinal b).classMethods := by
  apply BalanceCanonicalTS.canonical_bindings <;> assumption

example :
    balancePreparation .python = (balanceInvariantPyPreparedModel 0, balanceInvariantPyPreparedFrame) := by
  apply balanceInvariant_python_prepared_eq <;> assumption

example (b : Int) :
    balanceResetPostBounds .python b = (balanceInvariantPyInput b, balanceInvariantPyInputFrame) := by
  apply balanceInvariant_py_input_eq <;> assumption

example (b : Int)
    (hCall : evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩) :
    BalanceResetInvariantEvidence .python b (balanceInvariantPyFinal b) 79 74 := by
  apply BalanceCanonicalPython.invariant_evidence_of_call <;> assumption

example (b : Int) :
    balanceResetAfterInvariant .python b (balanceInvariantPyFinal b) = balanceInvariantPyBound b := by
  apply BalanceCanonicalPython.after_invariant_eq <;> assumption

example (b : Int) :
    balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79 = balanceInvariantPyReset b := by
  apply BalanceCanonicalPython.reset_final_eq <;> assumption

example (b : Int) : HeapWF .python (balanceInvariantPyCopied b) := by
  apply BalanceCanonicalPython.copied_heapWF <;> assumption

example (lang : TargetLang) (b : Int) :
    (balanceConstructorBodyEntry lang b).1.checkerRef =
      (balancePreparation lang).1.checkerRef := by
  apply BalanceCanonicalPython.constructor_ref <;> assumption

example : (balancePreparation .python).1.checkerRef = 1 := by
  apply BalanceCanonicalPython.preparation_ref <;> assumption

example (lang : TargetLang) (b : Int) :
    (balanceConstructorBodyEntry lang b).2.locals =
      [(balanceConstructorParam lang, (balanceConstructorBoundEntry lang b).1.nextCell)] := by
  apply BalanceCanonicalPython.constructor_locals <;> assumption

example (lang : TargetLang) (b : Int) :
    (balanceConstructorBodyEntry lang b).2.captures =
      (balanceStoredConstructor lang).2.captures := by
  apply BalanceCanonicalPython.constructor_captures <;> assumption

example (m : TargetMachine) (f : TargetFrame) (name : String)
    (hl : f.locals.lookup name = none) (hc : f.captures.lookup name = none)
    (hg : m.globals.lookup name = some 1) : snapshotAddress m f name = some 1 := by
  apply BalanceCanonicalPython.address_of_bindings <;> assumption

example (ref : CellRef) :
    [(balanceConstructorParam .python, ref)].lookup "dict" = none := by
  apply BalanceCanonicalPython.singleton_other <;> assumption

example (b : Int) :
    snapshotAddress (balanceInvariantPyReset b) (balanceConstructorBodyEntry .python b).2
      "dict" = some 1 := by
  apply BalanceCanonicalPython.constructor_dict_address <;> assumption

example (b : Int) :
    BalanceConstructorCopyEvidence .python b (balanceInvariantPyReset b) := by
  apply BalanceCanonicalPython.literal_copy_evidence <;> assumption

example (b : Int) :
    BalanceConstructorCopyEvidence .python b
      (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) := by
  apply BalanceCanonicalPython.copy_evidence <;> assumption

example (b : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hCall : evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩) :
    execStmt 89 (balanceProgram .python)
      (balanceResetOriginalEntry .python b).1 (balanceResetOriginalEntry .python b).2
      (balanceStoredReset .python).2.body =
      .ok ⟨balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79,
        (balanceResetAfterInvariant .python b (balanceInvariantPyFinal b)).2, .normal⟩ := by
  apply BalanceCanonicalPython.canonical_reset <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hCall : evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩) :
    execStmt 99 (balanceProgram .python)
      (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      (balanceStoredConstructor .python).2.body =
      .ok ⟨balanceConstructorCopied .python
          (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b,
        (balanceConstructorBodyEntry .python b).2, .normal⟩ := by
  apply BalanceCanonicalPython.canonical_constructor <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hCall : evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩) :
    targetConstruct (balanceProgram .python) (canonicalBalanceSeed .python b) =
      .ok (balanceConstructorCopied .python
        (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b) := by
  apply BalanceCanonicalPython.targetConstruct_sound <;> assumption

example (b : Int) :
    balanceConstructorCopied .python
      (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b =
      balanceInvariantPyCopied b := by
  apply BalanceCanonicalPython.copied_eq <;> assumption

example (b : Int) :
    HeapWF .python (balanceConstructorCopied .python
      (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b) := by
  apply BalanceCanonicalPython.canonical_copied_heapWF <;> assumption

example (b : Int) :
    BalanceRep .python b (balanceConstructorCopied .python
      (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b) := by
  apply BalanceCanonicalPython.canonical_balance_rep <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hCall : evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩) :
    targetConstruct (balanceProgram .python) (canonicalBalanceSeed .python b) =
      .ok (balanceInvariantPyCopied b) := by
  apply BalanceCanonicalPython.targetConstruct_literal <;> assumption

example (b : Int) : BalanceRep .python b (balanceInvariantPyCopied b) := by
  apply BalanceCanonicalPython.literal_balance_rep <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hCall : evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩) :
    ∃ m, targetConstruct (balanceProgram .python) (canonicalBalanceSeed .python b) = .ok m ∧
      BalanceRep .python b m := by
  apply BalanceCanonicalPython.targetConstruct_balance_rep <;> assumption

example (b : Int) :
    (balanceInvariantPyFinal b).nextObject = 100 ∧
    (balanceInvariantPyReset b).nextObject = 101 ∧
    (balanceInvariantPyCopied b).nextObject = 102 ∧
    (balanceInvariantPyCopied b).checker.context = 79 ∧
    (balanceInvariantPyCopied b).checker.history = 100 ∧
    (balanceInvariantPyCopied b).checker.constructorSeed = some 101 ∧
    (balanceInvariantPyCopied b).nextCell = 144 ∧
    (balanceInvariantPyCopied b).nextClosure = 26 := by
  apply BalanceCanonicalPython.canonical_allocations <;> assumption

example (b : Int) :
    (balanceInvariantPyCopied b).frames = (balanceInvariantPyInput b).frames ∧
    (balanceInvariantPyCopied b).globals = (balanceInvariantPyFinal b).globals ∧
    (balanceInvariantPyCopied b).cells = (balanceInvariantPyBound b).1.cells ∧
    (balanceInvariantPyCopied b).closures = (balanceInvariantPyFinal b).closures ∧
    (balanceInvariantPyCopied b).classMethods = (balanceInvariantPyFinal b).classMethods := by
  apply BalanceCanonicalPython.canonical_bindings <;> assumption

example : tokenMatchAt "balance >= 0" 0 = some ⟨"balance", 0, 7, []⟩ := by
  apply BalanceInvariantLexemes.token0 <;> assumption

example : tokenMatchAt "balance >= 0" 7 = some ⟨" ", 7, 8, []⟩ := by
  apply BalanceInvariantLexemes.token7 <;> assumption

example : tokenMatchAt "balance >= 0" 8 = some ⟨">=", 8, 10, []⟩ := by
  apply BalanceInvariantLexemes.token8 <;> assumption

example : tokenMatchAt "balance >= 0" 10 = some ⟨" ", 10, 11, []⟩ := by
  apply BalanceInvariantLexemes.token10 <;> assumption

example : tokenMatchAt "balance >= 0" 11 = some ⟨"0", 11, 12, []⟩ := by
  apply BalanceInvariantLexemes.token11 <;> assumption

example : identifierFullMatch "balance" = true := by
  apply BalanceInvariantLexemes.nameBalance <;> assumption

example : identifierFullMatch "0" = false := by
  apply BalanceInvariantLexemes.nameZero <;> assumption

example (m : TargetMachine) : hostCall .python m .stringIsSpace
    (some (.string "balance")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
  apply BalanceInvariantLexemes.spaceBalance <;> assumption

example (m : TargetMachine) : hostCall .python m .stringIsSpace
    (some (.string ">=")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
  apply BalanceInvariantLexemes.spaceOperator <;> assumption

example (m : TargetMachine) : hostCall .python m .stringIsSpace
    (some (.string "0")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
  apply BalanceInvariantLexemes.spaceZero <;> assumption

example (m : TargetMachine) : hostCall .python m .stringIsSpace
    (some (.string " ")) [] = .ok ⟨m, .ok (.bool true)⟩ := by
  apply BalanceInvariantLexemes.spaceSpace <;> assumption

example (m : TargetMachine) : hostCall .python m .stringIsDigit
    (some (.string "b")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
  apply BalanceInvariantLexemes.digitBalance <;> assumption

example (m : TargetMachine) : hostCall .python m .stringIsDigit
    (some (.string "0")) [] = .ok ⟨m, .ok (.bool true)⟩ := by
  apply BalanceInvariantLexemes.digitZero <;> assumption

example (m : TargetMachine) : hostCall .python m .stringStartsWith
    (some (.string "balance")) [.string "'"] = .ok ⟨m, .ok (.bool false)⟩ := by
  apply BalanceInvariantLexemes.startsBalance <;> assumption

example (m : TargetMachine) : hostCall .python m .stringStartsWith
    (some (.string "0")) [.string "'"] = .ok ⟨m, .ok (.bool false)⟩ := by
  apply BalanceInvariantLexemes.startsZero <;> assumption

example (m : TargetMachine) : hostCall .python m .float none
    [.string "0"] = .ok ⟨m, .ok (.number .pyFloat 0)⟩ := by
  apply BalanceInvariantLexemes.floatZero <;> assumption

example (n : Nat) (hb : n ≤ 9007199254740991) :
    evalExpr 74 (balanceProgram .python) (balanceInvariantPyInput (Int.ofNat n))
      balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal (Int.ofNat n), .ok .null⟩ := by
  apply balanceInvariant_py_call_nat <;> assumption

example (b : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    evalExpr 74 (balanceProgram .python)
      (balanceInvariantPyInput b) balanceInvariantPyInputFrame (resetInvariantCall .python) =
      .ok ⟨balanceInvariantPyFinal b, .ok .null⟩ := by
  apply BalanceCanonicalPython.Unconditional.canonical_call <;> assumption

example (b : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    execStmt 89 (balanceProgram .python)
      (balanceResetOriginalEntry .python b).1 (balanceResetOriginalEntry .python b).2
      (balanceStoredReset .python).2.body =
      .ok ⟨balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79,
        (balanceResetAfterInvariant .python b (balanceInvariantPyFinal b)).2, .normal⟩ := by
  apply BalanceCanonicalPython.Unconditional.canonical_reset <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    execStmt 99 (balanceProgram .python)
      (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      (balanceStoredConstructor .python).2.body =
      .ok ⟨balanceConstructorCopied .python
          (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b,
        (balanceConstructorBodyEntry .python b).2, .normal⟩ := by
  apply BalanceCanonicalPython.Unconditional.canonical_constructor <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram .python) (canonicalBalanceSeed .python b) =
      .ok (balanceConstructorCopied .python
        (balanceResetCanonicalFinal .python b (balanceInvariantPyFinal b) 79) b) := by
  apply BalanceCanonicalPython.Unconditional.targetConstruct_sound <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram .python) (canonicalBalanceSeed .python b) =
      .ok (balanceInvariantPyCopied b) := by
  apply BalanceCanonicalPython.Unconditional.targetConstruct_literal <;> assumption

example (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    ∃ m, targetConstruct (balanceProgram .python) (canonicalBalanceSeed .python b) = .ok m ∧
      BalanceRep .python b m := by
  apply BalanceCanonicalPython.Unconditional.targetConstruct_balance_rep <;> assumption

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    BalanceResetInvariantEvidence lang b (balanceCanonicalInvariantFinal lang b)
      (balanceCanonicalCandidate lang) (if lang == .ts then 80 else 74) := by
  apply balanceReset_canonical_invariant_evidence <;> assumption

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    evalExpr (if lang == .ts then 80 else 74) (balanceProgram lang)
      (balanceResetPostBounds lang b).1 (balanceResetPostBounds lang b).2
      (resetInvariantCall lang) =
      .ok ⟨balanceCanonicalInvariantFinal lang b, .ok (resetValidationResult lang)⟩ := by
  apply resetInvariant_canonical_execute <;> assumption

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    execStmt (if lang == .ts then 96 else 89) (balanceProgram lang)
      (balanceResetOriginalEntry lang b).1 (balanceResetOriginalEntry lang b).2
      (balanceStoredReset lang).2.body =
      .ok ⟨balanceCanonicalResetFinal lang b,
        (balanceResetAfterInvariant lang b (balanceCanonicalInvariantFinal lang b)).2,
        .normal⟩ := by
  apply balanceReset_canonical_execute <;> assumption

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    execStmt 99 (balanceProgram lang)
      (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (balanceStoredConstructor lang).2.body =
      .ok ⟨balanceConstructorCopied lang (balanceCanonicalResetFinal lang b) b,
        (balanceConstructorBodyEntry lang b).2, .normal⟩ := by
  apply balanceConstructor_canonical_execute <;> assumption

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) =
      .ok (balanceCanonicalConstructed lang b) := by
  apply targetConstruct_sound <;> assumption

example (lang : TargetLang) (b : Int) :
    BalanceRep lang b (balanceCanonicalConstructed lang b) := by
  apply balanceCanonicalConstructed_rep <;> assumption

example (lang : TargetLang) (b : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    ∃ m, targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) = .ok m ∧
      BalanceRep lang b m := by
  apply targetConstruct_balance_rep <;> assumption

example {ε α β : Type} {err : ε → β} {ok : α → β}
    {x y : Except ε α} (h : x = y) :
    @Except.rec ε α (fun _ => β) err ok x =
      @Except.rec ε α (fun _ => β) err ok y :=
  BalanceInvariantCertificate.exceptRec_congr h

-- Both closed endpoints exercise the unconditional common interface.
example (lang : TargetLang) :
    evalExpr (if lang == .ts then 80 else 74) (balanceProgram lang)
      (balanceResetPostBounds lang 0).1 (balanceResetPostBounds lang 0).2
      (resetInvariantCall lang) =
      .ok ⟨balanceCanonicalInvariantFinal lang 0, .ok (resetValidationResult lang)⟩ :=
  resetInvariant_canonical_execute lang 0 (by decide)

example (lang : TargetLang) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang Harmonia.Applications.Kadmos.S) =
      .ok (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S) :=
  targetConstruct_sound lang Harmonia.Applications.Kadmos.S (by decide)

#print axioms resetInvariant_canonical_execute
#print axioms balanceReset_canonical_execute
#print axioms balanceConstructor_canonical_execute
#print axioms targetConstruct_sound
#print axioms targetConstruct_balance_rep

end Batch16CanonicalContracts
