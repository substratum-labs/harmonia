import HarmoniaTests.AuditPolicy
import Harmonia.Applications.Kadmos.Generated.BalanceStepSimulation
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

-- Batch 17: every new public canonical DEBIT contract, checked directly.

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsDigit
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "e"))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.digitEvent

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsDigit
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "0"))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.true))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.digitZero

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.float
      (@Option.none Harmonia.Applications.Kadmos.Generated.TargetValue)
      (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "0")
        (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue)))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.number
            Harmonia.Applications.Kadmos.Generated.NumberTag.pyFloat (@OfNat.ofNat Int 0 (@instOfNat 0))))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.floatZero

example : (@Eq Bool (Harmonia.Applications.Kadmos.Generated.identifierFullMatch "amount") Bool.true) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.nameAmount

example : (@Eq Bool (Harmonia.Applications.Kadmos.Generated.identifierFullMatch "event") Bool.true) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.nameEvent

example : (@Eq Bool (Harmonia.Applications.Kadmos.Generated.identifierFullMatch "0") Bool.false) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.nameZero

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsSpace
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "amount"))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.spaceAmount

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsSpace
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "."))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.spaceDot

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsSpace
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "event"))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.spaceEvent

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsSpace
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string ">"))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.spaceOperator

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsSpace
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string " "))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.true))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.spaceSpace

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringIsSpace
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "0"))
      (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.spaceZero

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringStartsWith
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "event"))
      (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "'")
        (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue)))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.startsEvent

example : (∀ (m : Harmonia.Applications.Kadmos.Generated.TargetMachine),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.hostCall Harmonia.Applications.Kadmos.Generated.TargetLang.python m
      Harmonia.Applications.Kadmos.Generated.BuiltinId.stringStartsWith
      (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "0"))
      (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "'")
        (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue)))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk m
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.startsZero

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 0 (instOfNatNat 0)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk "event" (@OfNat.ofNat Nat 0 (instOfNatNat 0))
      (@OfNat.ofNat Nat 5 (instOfNatNat 5)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token0

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 12 (instOfNatNat 12)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk " " (@OfNat.ofNat Nat 12 (instOfNatNat 12))
      (@OfNat.ofNat Nat 13 (instOfNatNat 13)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token12

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 13 (instOfNatNat 13)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk ">" (@OfNat.ofNat Nat 13 (instOfNatNat 13))
      (@OfNat.ofNat Nat 14 (instOfNatNat 14)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token13

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 14 (instOfNatNat 14)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk " " (@OfNat.ofNat Nat 14 (instOfNatNat 14))
      (@OfNat.ofNat Nat 15 (instOfNatNat 15)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token14

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 15 (instOfNatNat 15)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk "0" (@OfNat.ofNat Nat 15 (instOfNatNat 15))
      (@OfNat.ofNat Nat 16 (instOfNatNat 16)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token15

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 5 (instOfNatNat 5)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk "." (@OfNat.ofNat Nat 5 (instOfNatNat 5))
      (@OfNat.ofNat Nat 6 (instOfNatNat 6)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token5

example : (@Eq (Option Harmonia.Applications.Kadmos.Generated.MatchValue)
  (Harmonia.Applications.Kadmos.Generated.tokenMatchAt "event.amount > 0" (@OfNat.ofNat Nat 6 (instOfNatNat 6)))
  (@Option.some Harmonia.Applications.Kadmos.Generated.MatchValue
    (Harmonia.Applications.Kadmos.Generated.MatchValue.mk "amount" (@OfNat.ofNat Nat 6 (instOfNatNat 6))
      (@OfNat.ofNat Nat 12 (instOfNatNat 12)) (@List.nil (Option String))))) :=
  @Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes.token6

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b : Int),
  @Eq Harmonia.Applications.Kadmos.Generated.TargetStmt
    (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalUnbound lang b).body
    (Harmonia.Applications.Kadmos.Generated.balanceSourceBody
      (Harmonia.Applications.Kadmos.Generated.balanceProgram lang) "WorldChecker.step")) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_body

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int) (k : Nat),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.evalExpr
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat 5 (instOfNatNat 5)))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
      (Harmonia.Applications.Kadmos.Generated.debitCallExpression lang))
    (@Bind.bind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
      (@Monad.toBind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
        (@Except.instMonad Harmonia.Applications.Kadmos.Generated.TargetError))
      Harmonia.Applications.Kadmos.Generated.StmtOutcome Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.execStmt
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat 4 (instOfNatNat 4)))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalBound lang b n))
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalBound lang b n))
        (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalUnbound lang b).body)
      fun result => Harmonia.Applications.Kadmos.Generated.closureResult lang result)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_call_open

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetClosure)
    (Harmonia.Applications.Kadmos.Generated.closureAt
      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
      (@ite Harmonia.Applications.Kadmos.Generated.ClosureRef
        (@Eq Bool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (instDecidableEqBool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 11 (instOfNatNat 11))
        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 19 (instOfNatNat 19))))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetClosure
      (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalUnbound lang b))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_closure

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @LE.le Int Int.instLEInt n (@OfNat.ofNat Int 0 (@instOfNat 0)) →
      @Eq
        (Option
          (Except Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue))
        (@Option.map Harmonia.Applications.Kadmos.Generated.ExprOutcome
          (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
          Harmonia.Applications.Kadmos.Generated.ExprOutcome.result
          (@Except.toOption Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.ExprOutcome
            (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun lang b n)))
        (@Option.some
          (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue
            (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_guard_nonpositive

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @Eq
      (Option
        (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue))
      (@Option.map Harmonia.Applications.Kadmos.Generated.ExprOutcome
        (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
        Harmonia.Applications.Kadmos.Generated.ExprOutcome.result
        (@Except.toOption Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.ExprOutcome
          (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun lang b n)))
      (@Option.some
        (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool
            (@Decidable.decide (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
              (Int.decLt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_guard_value

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b : Int),
  @Eq (Option Harmonia.Applications.Kadmos.Generated.ClosureRef)
    (@List.lookup String Harmonia.Applications.Kadmos.Generated.ClosureRef
      (@instBEqOfDecidableEq String instDecidableEqString) "step"
      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b).classMethods)
    (@Option.some Harmonia.Applications.Kadmos.Generated.ClosureRef
      (@ite Harmonia.Applications.Kadmos.Generated.ClosureRef
        (@Eq Bool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (instDecidableEqBool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 11 (instOfNatNat 11))
        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 19 (instOfNatNat 19))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_method

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
      (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
        (Harmonia.Applications.Kadmos.Generated.debitCallExpression lang))
      (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixContinuation lang b n)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_prefix_continuation

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    And
      (@Eq
        (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
        (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixRun lang b n)
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.StmtOutcome
          (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
            (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
            (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
            Harmonia.Applications.Kadmos.Generated.ControlResult.normal)))
      (And
        (@Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
          (Harmonia.Applications.Kadmos.Generated.balanceView lang
            (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n)))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.BalanceView
            (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
              (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
              (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.true)))
        (And
          (@Eq
            (Except Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetValue)
            (Harmonia.Applications.Kadmos.Generated.localValue
              (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                Harmonia.Applications.Kadmos.Generated.TargetFrame
                (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
              (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                Harmonia.Applications.Kadmos.Generated.TargetFrame
                (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
              (@ite String
                (@Eq Bool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                (instDecidableEqBool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                "safePayload" "payload"))
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetValue
              (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
                  (@Eq Bool
                    (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                      (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                        Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                      lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                    Bool.true)
                  (instDecidableEqBool
                    (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                      (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                        Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                      lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                    Bool.true)
                  (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 53 (instOfNatNat 53))
                  (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 114 (instOfNatNat 114))))))
          (@Eq
            (Except Harmonia.Applications.Kadmos.Generated.TargetError
              (Option Harmonia.Applications.Kadmos.Generated.Descriptor))
            (Harmonia.Applications.Kadmos.Generated.readOwn
              (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                Harmonia.Applications.Kadmos.Generated.TargetFrame
                (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
              (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
                (@Eq Bool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                (instDecidableEqBool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 53 (instOfNatNat 53))
                (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 114 (instOfNatNat 114)))
              "amount")
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
              (Option Harmonia.Applications.Kadmos.Generated.Descriptor)
              (@Option.some Harmonia.Applications.Kadmos.Generated.Descriptor
                (Harmonia.Applications.Kadmos.Generated.Descriptor.mk
                  (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
                    (Harmonia.Applications.Kadmos.Generated.TargetValue.number
                      (@ite Harmonia.Applications.Kadmos.Generated.NumberTag
                        (@Eq Bool
                          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                          Bool.true)
                        (instDecidableEqBool
                          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                          Bool.true)
                        Harmonia.Applications.Kadmos.Generated.NumberTag.jsNumber
                        Harmonia.Applications.Kadmos.Generated.NumberTag.pyFloat)
                      n))
                  (@Option.none Harmonia.Applications.Kadmos.Generated.ClosureRef)
                  (@Option.none Harmonia.Applications.Kadmos.Generated.ClosureRef) Bool.true Bool.true Bool.true))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_prefix_contract

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
      (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixRun lang b n)
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
        (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
          (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame
            (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
          (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame
            (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n))
          Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_prefix_execute

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
      (Harmonia.Applications.Kadmos.Generated.debitCallExpression lang))
    (@Bind.bind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
      (@Monad.toBind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
        (@Except.instMonad Harmonia.Applications.Kadmos.Generated.TargetError))
      Harmonia.Applications.Kadmos.Generated.StmtOutcome Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.execStmt
        (@ite Nat
          (@Eq Bool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (instDecidableEqBool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (@OfNat.ofNat Nat 93 (instOfNatNat 93)) (@OfNat.ofNat Nat 92 (instOfNatNat 92)))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalSnapshots lang b n))
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalSnapshots lang b n))
        (Harmonia.Applications.Kadmos.Generated.dropStmts
          (@ite Nat
            (@Eq Bool
              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
              Bool.true)
            (@OfNat.ofNat Nat 4 (instOfNatNat 4)) (@OfNat.ofNat Nat 5 (instOfNatNat 5)))
          (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshots lang)))
      fun body => Harmonia.Applications.Kadmos.Generated.closureResult lang body)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_snapshot_continuation

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry lang
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b) n))
      (Harmonia.Applications.Kadmos.Generated.debitCallExpression lang))
    (@Bind.bind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
      (@Monad.toBind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
        (@Except.instMonad Harmonia.Applications.Kadmos.Generated.TargetError))
      Harmonia.Applications.Kadmos.Generated.StmtOutcome Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.execStmt (@OfNat.ofNat Nat 97 (instOfNatNat 97))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshotStart lang b n))
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshotStart lang b n))
        (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshots lang))
      fun body => Harmonia.Applications.Kadmos.Generated.closureResult lang body)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_snapshots_entry

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshotRun lang b n)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
      (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalSnapshots lang b n))
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalSnapshots lang b n))
        Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_snapshots_execute

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b : Int),
  @Eq Harmonia.Applications.Kadmos.Generated.TargetStmt
    (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalUnbound lang b).body
    (@Prod.snd Harmonia.Applications.Kadmos.Generated.ClosureRef Harmonia.Applications.Kadmos.Generated.TargetClosure
        (Harmonia.Applications.Kadmos.Generated.balanceStoredStep lang)).body) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_stored

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang),
  @Eq Harmonia.Applications.Kadmos.Generated.TargetStmt
    (Harmonia.Applications.Kadmos.Generated.balanceStepProtected lang).cleanup
    ((Harmonia.Applications.Kadmos.Generated.TargetStmt.assign
          (Harmonia.Applications.Kadmos.Generated.AssignTarget.property
            (Harmonia.Applications.Kadmos.Generated.resetReceiver lang)
            (@ite String
              (@Eq Bool
                (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                  (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                    Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                  lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                Bool.true)
              (instDecidableEqBool
                (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                  (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                    Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                  lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                Bool.true)
              "#busy" "_busy"))
          (Harmonia.Applications.Kadmos.Generated.TargetExpr.bool Bool.false)).sequence
      Harmonia.Applications.Kadmos.Generated.TargetStmt.empty)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_cleanup_shape

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF lang
    (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_WF

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq Bool
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine)
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang (@OfNat.ofNat Int 0 (@instOfNat 0))
          (@OfNat.ofNat Int 0 (@instOfNat 0))).machine)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_WF_footprint

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang),
  Harmonia.Applications.Kadmos.Generated.HeapWF lang
    (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang (@OfNat.ofNat Int 0 (@instOfNat 0))
        (@OfNat.ofNat Int 0 (@instOfNat 0))).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_WF_zero

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String) (@Option.some String "GUARD_FAILED"))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_code

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_frame

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_preserves_view

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.false "Ready"
        (@List.cons (Prod String Int) (@Prod.mk String Int "balance" b) (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_guardRejected_projection

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  let p := Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n;
  @Eq
    (Except Harmonia.Applications.Kadmos.Generated.TargetError
      (Option Harmonia.Applications.Kadmos.Generated.Descriptor))
    (Harmonia.Applications.Kadmos.Generated.readOwn
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        p)
      (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
        (@Eq Bool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (instDecidableEqBool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 53 (instOfNatNat 53))
        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 114 (instOfNatNat 114)))
      "amount")
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
      (Option Harmonia.Applications.Kadmos.Generated.Descriptor)
      (@Option.some Harmonia.Applications.Kadmos.Generated.Descriptor
        (Harmonia.Applications.Kadmos.Generated.Descriptor.mk
          (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
            (Harmonia.Applications.Kadmos.Generated.TargetValue.number
              (@ite Harmonia.Applications.Kadmos.Generated.NumberTag
                (@Eq Bool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                (instDecidableEqBool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                Harmonia.Applications.Kadmos.Generated.NumberTag.jsNumber
                Harmonia.Applications.Kadmos.Generated.NumberTag.pyFloat)
              n))
          (@Option.none Harmonia.Applications.Kadmos.Generated.ClosureRef)
          (@Option.none Harmonia.Applications.Kadmos.Generated.ClosureRef) Bool.true Bool.true Bool.true)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_payload_amount

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  let p := Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n;
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue)
    (Harmonia.Applications.Kadmos.Generated.localValue
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        p)
      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        p)
      (@ite String
        (@Eq Bool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (instDecidableEqBool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        "safePayload" "payload"))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue
      (Harmonia.Applications.Kadmos.Generated.TargetValue.object
        (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
          (@Eq Bool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (instDecidableEqBool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 53 (instOfNatNat 53))
          (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 114 (instOfNatNat 114)))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_payload_local

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  let p := Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n;
  And
    (@Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue)
      (Harmonia.Applications.Kadmos.Generated.localValue
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame p)
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame p)
        (@ite String
          (@Eq Bool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (instDecidableEqBool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          "snapshotState" "previous"))
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "Ready")))
    (And
      (@Eq
        (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue)
        (Harmonia.Applications.Kadmos.Generated.localValue
          (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame p)
          (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame p)
          (@ite String
            (@Eq Bool
              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
              Bool.true)
            "snapshotAction" "action"))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.string "DEBIT")))
      (And
        (@Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue)
          (Harmonia.Applications.Kadmos.Generated.localValue
            (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame p)
            (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame p)
            (@ite String
              (@Eq Bool
                (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                  (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                    Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                  lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                Bool.true)
              (instDecidableEqBool
                (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                  (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                    Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                  lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                Bool.true)
              "snapshotDirective" "proposed"))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue.null))
        (And
          (@Eq
            (Except Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetValue)
            (Harmonia.Applications.Kadmos.Generated.localValue
              (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                Harmonia.Applications.Kadmos.Generated.TargetFrame p)
              (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                Harmonia.Applications.Kadmos.Generated.TargetFrame p)
              (@ite String
                (@Eq Bool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                (instDecidableEqBool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                "descDirective" "has_proposed"))
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetValue
              (@ite Harmonia.Applications.Kadmos.Generated.TargetValue
                (@Eq Bool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                (instDecidableEqBool
                  (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                    (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                      Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                    lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                  Bool.true)
                Harmonia.Applications.Kadmos.Generated.TargetValue.undefined
                (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.false))))
          (And
            (@Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.TargetValue)
              (Harmonia.Applications.Kadmos.Generated.localValue
                (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                  Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                  Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                "rollback")
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.TargetValue
                (Harmonia.Applications.Kadmos.Generated.TargetValue.closure
                  (@ite Harmonia.Applications.Kadmos.Generated.ClosureRef
                    (@Eq Bool
                      (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                        (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                          Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                        lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                      Bool.true)
                    (instDecidableEqBool
                      (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                        (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                          Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                        lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                      Bool.true)
                    (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 20 (instOfNatNat 20))
                    (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 27 (instOfNatNat 27))))))
            (And
              (@Eq
                (Except Harmonia.Applications.Kadmos.Generated.TargetError
                  Harmonia.Applications.Kadmos.Generated.TargetValue)
                (Harmonia.Applications.Kadmos.Generated.localValue
                  (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                    Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                  (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                    Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                  (@ite String
                    (@Eq Bool
                      (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                        (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                          Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                        lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                      Bool.true)
                    (instDecidableEqBool
                      (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                        (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                          Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                        lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                      Bool.true)
                    "rejectRequest" "security_reject"))
                (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                  Harmonia.Applications.Kadmos.Generated.TargetValue
                  (Harmonia.Applications.Kadmos.Generated.TargetValue.closure
                    (@ite Harmonia.Applications.Kadmos.Generated.ClosureRef
                      (@Eq Bool
                        (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                          (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                            Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                          lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                        Bool.true)
                      (instDecidableEqBool
                        (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                          (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                            Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                          lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                        Bool.true)
                      (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 21 (instOfNatNat 21))
                      (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 28 (instOfNatNat 28))))))
              (And
                (@Eq
                  (Except Harmonia.Applications.Kadmos.Generated.TargetError
                    Harmonia.Applications.Kadmos.Generated.TargetValue)
                  (Harmonia.Applications.Kadmos.Generated.localValue
                    (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                      Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                    (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                      Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                    "reject")
                  (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                    Harmonia.Applications.Kadmos.Generated.TargetValue
                    (Harmonia.Applications.Kadmos.Generated.TargetValue.closure
                      (@ite Harmonia.Applications.Kadmos.Generated.ClosureRef
                        (@Eq Bool
                          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                          Bool.true)
                        (instDecidableEqBool
                          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                          Bool.true)
                        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 22 (instOfNatNat 22))
                        (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 30 (instOfNatNat 30))))))
                (And
                  (@Eq
                    (Except Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.TargetValue)
                    (Harmonia.Applications.Kadmos.Generated.localValue
                      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                        Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                        Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                      "transition")
                    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.TargetValue
                      (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                        (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
                          (@Eq Bool
                            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                            Bool.true)
                          (instDecidableEqBool
                            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                            Bool.true)
                          (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 14 (instOfNatNat 14))
                          (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 61 (instOfNatNat 61))))))
                  (And
                    (@Eq
                      (Except Harmonia.Applications.Kadmos.Generated.TargetError
                        Harmonia.Applications.Kadmos.Generated.TargetValue)
                      (Harmonia.Applications.Kadmos.Generated.localValue
                        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                          Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                          Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                        (@ite String
                          (@Eq Bool
                            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                            Bool.true)
                          (instDecidableEqBool
                            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                            Bool.true)
                          "env" "environment"))
                      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                        Harmonia.Applications.Kadmos.Generated.TargetValue
                        (Harmonia.Applications.Kadmos.Generated.TargetValue.closure
                          (@ite Harmonia.Applications.Kadmos.Generated.ClosureRef
                            (@Eq Bool
                              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                              Bool.true)
                            (instDecidableEqBool
                              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                              Bool.true)
                            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 24 (instOfNatNat 24))
                            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 31 (instOfNatNat 31))))))
                    (And
                      (@Eq
                        (Except Harmonia.Applications.Kadmos.Generated.TargetError
                          (Option Harmonia.Applications.Kadmos.Generated.Descriptor))
                        (Harmonia.Applications.Kadmos.Generated.readOwn
                          (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                            Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                          (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
                            (@Eq Bool
                              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                              Bool.true)
                            (instDecidableEqBool
                              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                              Bool.true)
                            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 57 (instOfNatNat 57))
                            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 122 (instOfNatNat 122)))
                          "proposedDirective")
                        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                          (Option Harmonia.Applications.Kadmos.Generated.Descriptor)
                          (@Option.none Harmonia.Applications.Kadmos.Generated.Descriptor)))
                      (@Eq
                        (Except Harmonia.Applications.Kadmos.Generated.TargetError
                          (Option Harmonia.Applications.Kadmos.Generated.Descriptor))
                        (Harmonia.Applications.Kadmos.Generated.readOwn
                          (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                            Harmonia.Applications.Kadmos.Generated.TargetFrame p)
                          (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
                            (@Eq Bool
                              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                              Bool.true)
                            (instDecidableEqBool
                              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                              Bool.true)
                            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 57 (instOfNatNat 57))
                            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 122 (instOfNatNat 122)))
                          "eventPayload")
                        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                          (Option Harmonia.Applications.Kadmos.Generated.Descriptor)
                          (@Option.some Harmonia.Applications.Kadmos.Generated.Descriptor
                            (Harmonia.Applications.Kadmos.Generated.Descriptor.mk
                              (@Option.some Harmonia.Applications.Kadmos.Generated.TargetValue
                                (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                                  (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
                                    (@Eq Bool
                                      (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                        (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                          Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                        lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                                      Bool.true)
                                    (instDecidableEqBool
                                      (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                                        (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                                          Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                                        lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
                                      Bool.true)
                                    (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 53 (instOfNatNat 53))
                                    (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 114
                                      (instOfNatNat 114)))))
                              (@Option.none Harmonia.Applications.Kadmos.Generated.ClosureRef)
                              (@Option.none Harmonia.Applications.Kadmos.Generated.ClosureRef) Bool.true Bool.true
                              Bool.true)))))))))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_prefix_admitted

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang),
  @Eq Bool
    (Harmonia.Applications.Kadmos.Generated.stepPrefixShape
      (@ite Nat
        (@Eq Bool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (instDecidableEqBool
          (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
            (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
              Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
            lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          Bool.true)
        (@OfNat.ofNat Nat 18 (instOfNatNat 18)) (@OfNat.ofNat Nat 21 (instOfNatNat 21)))
      (Harmonia.Applications.Kadmos.Generated.balanceStepProtected lang).body)
    Bool.true) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_prefix_shape

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalPrefix lang b n)))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.true))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_prefix_view

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun Harmonia.Applications.Kadmos.Generated.TargetLang.python
      b n)
    (@Bind.bind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
      (@Monad.toBind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
        (@Except.instMonad Harmonia.Applications.Kadmos.Generated.TargetError))
      Harmonia.Applications.Kadmos.Generated.StmtOutcome Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.execStmt (@OfNat.ofNat Nat 59 (instOfNatNat 59))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
        (Harmonia.Applications.Kadmos.Generated.balanceStep_py_tokenized_machine b n)
        Harmonia.Applications.Kadmos.Generated.balanceStep_py_tokenized_frame
        (Harmonia.Applications.Kadmos.Generated.dropStmts (@OfNat.ofNat Nat 5 (instOfNatNat 5))
          (Harmonia.Applications.Kadmos.Generated.balanceSourceBody
            (Harmonia.Applications.Kadmos.Generated.balanceProgram
              Harmonia.Applications.Kadmos.Generated.TargetLang.python)
            "module.evaluate_world")))
      fun out =>
      Harmonia.Applications.Kadmos.Generated.closureResult Harmonia.Applications.Kadmos.Generated.TargetLang.python out)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_after_tokens

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ArgsOutcome)
    (Harmonia.Applications.Kadmos.Generated.evalArgValues (@OfNat.ofNat Nat 64 (instOfNatNat 64))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefix b n)
      Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefixFrame
      Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_args)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ArgsOutcome
      (Harmonia.Applications.Kadmos.Generated.ArgsOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_argument_machine b n)
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          (List Harmonia.Applications.Kadmos.Generated.TargetValue)
          (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
            (Harmonia.Applications.Kadmos.Generated.TargetValue.string "event.amount > 0")
            (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
              (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 124 (instOfNatNat 124)))
              (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_arguments

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BindOutcome)
    (Harmonia.Applications.Kadmos.Generated.bindCallParams (@OfNat.ofNat Nat 64 (instOfNatNat 64))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_argument_machine b n)
      (Harmonia.Applications.Kadmos.Generated.closureFrame
        Harmonia.Applications.Kadmos.Generated.balanceStep_py_evaluate_closure)
      Harmonia.Applications.Kadmos.Generated.balanceStep_py_evaluate_closure.params
      Harmonia.Applications.Kadmos.Generated.balanceStep_py_evaluate_closure.pythonDefaults
      (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.string "event.amount > 0")
        (@List.cons Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.object
            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 124 (instOfNatNat 124)))
          (@List.nil Harmonia.Applications.Kadmos.Generated.TargetValue))))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BindOutcome
      (Harmonia.Applications.Kadmos.Generated.BindOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_body_machine b n)
        Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_body_frame
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue Unit Unit.unit)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_bind

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun Harmonia.Applications.Kadmos.Generated.TargetLang.python
      b n)
    (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 65 (instOfNatNat 65))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefix b n)
      Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefixFrame
      Harmonia.Applications.Kadmos.Generated.balanceStepPyGuardSyntax)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_call

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetClosure)
    (Harmonia.Applications.Kadmos.Generated.closureAt
      (Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_argument_machine b n)
      (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ClosureRef 5 (instOfNatNat 5)))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetClosure
      Harmonia.Applications.Kadmos.Generated.balanceStep_py_evaluate_closure)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_closure

example : (∀ (b n : Int),
  @LE.le Nat instLENat n.natAbs (@OfNat.ofNat Nat 9007199254740991 (instOfNatNat 9007199254740991)) →
    @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun
        Harmonia.Applications.Kadmos.Generated.TargetLang.python b n)
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
        (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
          (Harmonia.Applications.Kadmos.Generated.balanceStepPyGuard b n)
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue
            (Harmonia.Applications.Kadmos.Generated.TargetValue.bool
              (@Decidable.decide (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
                (Int.decLt (@OfNat.ofNat Int 0 (@instOfNat 0)) n))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_execute

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun Harmonia.Applications.Kadmos.Generated.TargetLang.python
      b n)
    (@Bind.bind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
      (@Monad.toBind (Except Harmonia.Applications.Kadmos.Generated.TargetError)
        (@Except.instMonad Harmonia.Applications.Kadmos.Generated.TargetError))
      Harmonia.Applications.Kadmos.Generated.StmtOutcome Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.execStmt (@OfNat.ofNat Nat 64 (instOfNatNat 64))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
        (Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_body_machine b n)
        Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_body_frame
        (Harmonia.Applications.Kadmos.Generated.balanceSourceBody
          (Harmonia.Applications.Kadmos.Generated.balanceProgram
            Harmonia.Applications.Kadmos.Generated.TargetLang.python)
          "module.evaluate_world"))
      fun out =>
      Harmonia.Applications.Kadmos.Generated.closureResult Harmonia.Applications.Kadmos.Generated.TargetLang.python out)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_open

example : (∀ (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @LE.le Int Int.instLEInt n (@OfNat.ofNat Int 0 (@instOfNat 0)) →
      @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
        (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
          (Harmonia.Applications.Kadmos.Generated.balanceProgram
            Harmonia.Applications.Kadmos.Generated.TargetLang.python)
          (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame
            (Harmonia.Applications.Kadmos.Generated.debitCallEntry
              Harmonia.Applications.Kadmos.Generated.TargetLang.python
              (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
              n))
          (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame
            (Harmonia.Applications.Kadmos.Generated.debitCallEntry
              Harmonia.Applications.Kadmos.Generated.TargetLang.python
              (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
              n))
          (Harmonia.Applications.Kadmos.Generated.debitCallExpression
            Harmonia.Applications.Kadmos.Generated.TargetLang.python))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.ExprOutcome
          (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
            (Harmonia.Applications.Kadmos.Generated.balanceStepPyRejected b n)
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
              Harmonia.Applications.Kadmos.Generated.TargetValue
              (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 142 (instOfNatNat 142))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_reject_execute

example : (@Eq Harmonia.Applications.Kadmos.Generated.TargetExpr
  (Harmonia.Applications.Kadmos.Generated.balanceStepGuardExpression
    Harmonia.Applications.Kadmos.Generated.TargetLang.python)
  Harmonia.Applications.Kadmos.Generated.balanceStepPyGuardSyntax) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_source

example : (∀ (b n : Int),
  @LE.le Nat instLENat n.natAbs (@OfNat.ofNat Nat 9007199254740991 (instOfNatNat 9007199254740991)) →
    @Eq
      (Option
        (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue))
      (@Option.map Harmonia.Applications.Kadmos.Generated.ExprOutcome
        (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
        Harmonia.Applications.Kadmos.Generated.ExprOutcome.result
        (@Except.toOption Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.ExprOutcome
          (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun
            Harmonia.Applications.Kadmos.Generated.TargetLang.python b n)))
      (@Option.some
        (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool
            (@Decidable.decide (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
              (Int.decLt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_value

example : (∀ (b : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry Harmonia.Applications.Kadmos.Generated.TargetLang.python
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
            Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
          (@OfNat.ofNat Int 0 (@instOfNat 0))))
      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry Harmonia.Applications.Kadmos.Generated.TargetLang.python
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
            Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
          (@OfNat.ofNat Int 0 (@instOfNat 0))))
      (Harmonia.Applications.Kadmos.Generated.debitCallExpression
        Harmonia.Applications.Kadmos.Generated.TargetLang.python))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStepPyRejected b (@OfNat.ofNat Int 0 (@instOfNat 0)))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.object
            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 142 (instOfNatNat 142))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_zero_execute

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixRun
      Harmonia.Applications.Kadmos.Generated.TargetLang.python b n)
    (Harmonia.Applications.Kadmos.Generated.execStmt (@OfNat.ofNat Nat 90 (instOfNatNat 90))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (Harmonia.Applications.Kadmos.Generated.balanceStepPySnapshots b n)
      Harmonia.Applications.Kadmos.Generated.balanceStepPySnapshotsFrame
      Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefixSyntax)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_prefix_entry

example : (∀ (b n : Int),
  @LE.le Nat instLENat n.natAbs (@OfNat.ofNat Nat 9007199254740991 (instOfNatNat 9007199254740991)) →
    @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
      (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixRun
        Harmonia.Applications.Kadmos.Generated.TargetLang.python b n)
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
        (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
          (Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefix b n)
          Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefixFrame
          Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_prefix_execute

example : (@Eq Harmonia.Applications.Kadmos.Generated.TargetStmt
  (Harmonia.Applications.Kadmos.Generated.takeStepStmts (@OfNat.ofNat Nat 21 (instOfNatNat 21))
    (Harmonia.Applications.Kadmos.Generated.balanceStepProtected
        Harmonia.Applications.Kadmos.Generated.TargetLang.python).body)
  Harmonia.Applications.Kadmos.Generated.balanceStepPyPrefixSyntax) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_prefix_source

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshotRun
      Harmonia.Applications.Kadmos.Generated.TargetLang.python b n)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
      (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStepPySnapshots b n)
        Harmonia.Applications.Kadmos.Generated.balanceStepPySnapshotsFrame
        Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_snapshots_execute

example : (@Eq Bool
  (Harmonia.Applications.Kadmos.Generated.stepPrefixShape (@OfNat.ofNat Nat 5 (instOfNatNat 5))
    (Harmonia.Applications.Kadmos.Generated.balanceSourceBody
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      "module.evaluate_world"))
  Bool.true) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_token_prefix_shape

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
    (Harmonia.Applications.Kadmos.Generated.execStmt (@OfNat.ofNat Nat 64 (instOfNatNat 64))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_body_machine b n)
      Harmonia.Applications.Kadmos.Generated.balanceStep_py_guard_body_frame
      (Harmonia.Applications.Kadmos.Generated.takeStepStmts (@OfNat.ofNat Nat 5 (instOfNatNat 5))
        (Harmonia.Applications.Kadmos.Generated.balanceSourceBody
          (Harmonia.Applications.Kadmos.Generated.balanceProgram
            Harmonia.Applications.Kadmos.Generated.TargetLang.python)
          "module.evaluate_world")))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
      (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStep_py_tokenized_machine b n)
        Harmonia.Applications.Kadmos.Generated.balanceStep_py_tokenized_frame
        Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_tokenization

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  let p := Harmonia.Applications.Kadmos.Generated.balanceStepCanonicalSnapshots lang b n;
  And
    (@Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Int)
      (Harmonia.Applications.Kadmos.Generated.balanceContextValue lang
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame p)
        (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
          (@Eq Bool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (instDecidableEqBool
            (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
              (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
              lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            Bool.true)
          (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 48 (instOfNatNat 48))
          (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 104 (instOfNatNat 104))))
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Int b))
    (And
      (@Eq
        (Except Harmonia.Applications.Kadmos.Generated.TargetError
          (List Harmonia.Applications.Kadmos.Generated.BalanceRecord))
        (Harmonia.Applications.Kadmos.Generated.decodeBalanceHistory lang
          (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
            Harmonia.Applications.Kadmos.Generated.TargetFrame p)
          (@ite Harmonia.Applications.Kadmos.Generated.ObjRef
            (@Eq Bool
              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq Harmonia.Applications.Kadmos.Generated.TargetLang
                (@instBEqOfDecidableEq Harmonia.Applications.Kadmos.Generated.TargetLang
                  Harmonia.Applications.Kadmos.Generated.instDecidableEqTargetLang)
                lang Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
              Bool.true)
            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 49 (instOfNatNat 49))
            (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 105 (instOfNatNat 105))))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          (List Harmonia.Applications.Kadmos.Generated.BalanceRecord)
          (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)))
      (@Eq Harmonia.Applications.Kadmos.Generated.TargetLang lang
          Harmonia.Applications.Kadmos.Generated.TargetLang.python →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetValue)
          (Harmonia.Applications.Kadmos.Generated.localValue
            (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame p)
            (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame p)
            "previous_undo")
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue.null)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_snapshot_values

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang),
  @Eq Harmonia.Applications.Kadmos.Generated.TargetStmt
    (@Prod.snd Harmonia.Applications.Kadmos.Generated.ClosureRef Harmonia.Applications.Kadmos.Generated.TargetClosure
        (Harmonia.Applications.Kadmos.Generated.balanceStoredStep lang)).body
    (Harmonia.Applications.Kadmos.Generated.balanceSourceBody
      (Harmonia.Applications.Kadmos.Generated.balanceProgram lang) "WorldChecker.step")) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_stored_source

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun Harmonia.Applications.Kadmos.Generated.TargetLang.ts b
      n)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStepTsGuard b n)
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
          Harmonia.Applications.Kadmos.Generated.TargetValue
          (Harmonia.Applications.Kadmos.Generated.TargetValue.bool
            (@Decidable.decide (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
              (Int.decLt (@OfNat.ofNat Int 0 (@instOfNat 0)) n))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_guard_execute

example : (∀ (b n : Int),
  @LE.le Int Int.instLEInt n (@OfNat.ofNat Int 0 (@instOfNat 0)) →
    @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
      (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
        (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
        (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.debitCallEntry Harmonia.Applications.Kadmos.Generated.TargetLang.ts
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
            n))
        (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
          Harmonia.Applications.Kadmos.Generated.TargetFrame
          (Harmonia.Applications.Kadmos.Generated.debitCallEntry Harmonia.Applications.Kadmos.Generated.TargetLang.ts
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
            n))
        (Harmonia.Applications.Kadmos.Generated.debitCallExpression
          Harmonia.Applications.Kadmos.Generated.TargetLang.ts))
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome
        (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
          (Harmonia.Applications.Kadmos.Generated.balanceStepTsRejected b n)
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue
            (Harmonia.Applications.Kadmos.Generated.TargetValue.object
              (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 71 (instOfNatNat 71))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_guard_reject_execute

example : (@Eq Harmonia.Applications.Kadmos.Generated.TargetExpr
  (Harmonia.Applications.Kadmos.Generated.balanceStepGuardExpression
    Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
  Harmonia.Applications.Kadmos.Generated.balanceStepTsGuardSyntax) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_guard_source

example : (∀ (b n : Int),
  @Eq
    (Option
      (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue))
    (@Option.map Harmonia.Applications.Kadmos.Generated.ExprOutcome
      (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
      Harmonia.Applications.Kadmos.Generated.ExprOutcome.result
      (@Except.toOption Harmonia.Applications.Kadmos.Generated.TargetError
        Harmonia.Applications.Kadmos.Generated.ExprOutcome
        (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun Harmonia.Applications.Kadmos.Generated.TargetLang.ts
          b n)))
    (@Option.some
      (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
      (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue
        (Harmonia.Applications.Kadmos.Generated.TargetValue.bool
          (@Decidable.decide (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
            (Int.decLt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_guard_value

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
    (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
      (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry Harmonia.Applications.Kadmos.Generated.TargetLang.ts
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
            Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
          n))
      (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine Harmonia.Applications.Kadmos.Generated.TargetFrame
        (Harmonia.Applications.Kadmos.Generated.debitCallEntry Harmonia.Applications.Kadmos.Generated.TargetLang.ts
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
            Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
          n))
      (Harmonia.Applications.Kadmos.Generated.debitCallExpression Harmonia.Applications.Kadmos.Generated.TargetLang.ts))
    (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixContinuation
      Harmonia.Applications.Kadmos.Generated.TargetLang.ts b n)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_prefix_continuation

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepPrefixRun Harmonia.Applications.Kadmos.Generated.TargetLang.ts b
      n)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
      (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStepTsPrefix b n)
        Harmonia.Applications.Kadmos.Generated.balanceStepTsPrefixFrame
        Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_prefix_execute

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
    (Harmonia.Applications.Kadmos.Generated.balanceStepSnapshotRun Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      b n)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome
      (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk
        (Harmonia.Applications.Kadmos.Generated.balanceStepTsSnapshots b n)
        Harmonia.Applications.Kadmos.Generated.balanceStepTsSnapshotsFrame
        Harmonia.Applications.Kadmos.Generated.ControlResult.normal))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_snapshots_execute

example : (∀ (n k : Nat) (program : Harmonia.Applications.Kadmos.Generated.TargetProgram)
  (m : Harmonia.Applications.Kadmos.Generated.TargetMachine) (f : Harmonia.Applications.Kadmos.Generated.TargetFrame)
  (s : Harmonia.Applications.Kadmos.Generated.TargetStmt) (final : Harmonia.Applications.Kadmos.Generated.TargetMachine)
  (ff : Harmonia.Applications.Kadmos.Generated.TargetFrame),
  @Eq Bool (Harmonia.Applications.Kadmos.Generated.stepPrefixShape n s) Bool.true →
    @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
        (Harmonia.Applications.Kadmos.Generated.execStmt
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k n)
            (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
          program m f (Harmonia.Applications.Kadmos.Generated.takeStepStmts n s))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.StmtOutcome
          (Harmonia.Applications.Kadmos.Generated.StmtOutcome.mk final ff
            Harmonia.Applications.Kadmos.Generated.ControlResult.normal)) →
      @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.StmtOutcome)
        (Harmonia.Applications.Kadmos.Generated.execStmt
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k n)
            (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
          program m f s)
        (Harmonia.Applications.Kadmos.Generated.execStmt
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat 1 (instOfNatNat 1))) program final ff
          (Harmonia.Applications.Kadmos.Generated.dropStmts n s))) :=
  @Harmonia.Applications.Kadmos.Generated.execStepPrefix_normal

example : (∀ {n : Nat} {s : Harmonia.Applications.Kadmos.Generated.TargetStmt},
  @Eq Bool (Harmonia.Applications.Kadmos.Generated.snapshotTryCheck n s) Bool.true →
    @Eq Bool (Harmonia.Applications.Kadmos.Generated.stepPrefixShape n s) Bool.true) :=
  @Harmonia.Applications.Kadmos.Generated.stepPrefixShape_of_snapshot

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LE.le Int Int.instLEInt n (@OfNat.ofNat Int 0 (@instOfNat 0)) →
        And
          (@Eq
            (Except Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetOutcome)
            (Harmonia.Applications.Kadmos.Generated.targetStep
              (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
              (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
              (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest lang n))
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetOutcome
              (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n)))
          (And
            (@Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.Normalized)
              (Harmonia.Applications.Kadmos.Generated.targetProjection lang
                (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.Normalized
                (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.false "Ready"
                  (@List.cons (Prod String Int) (@Prod.mk String Int "balance" b) (@List.nil (Prod String Int)))
                  (@Option.none String))))
            (And
              (@Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
                (Harmonia.Applications.Kadmos.Generated.targetViolationCode
                  (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n))
                (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String)
                  (@Option.some String "GUARD_FAILED")))
              (And
                (Harmonia.Applications.Kadmos.Generated.HeapWF lang
                  (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine)
                (And
                  (@Eq
                    (Except Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.BalanceView)
                    (Harmonia.Applications.Kadmos.Generated.balanceView lang
                      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine)
                    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.BalanceView
                      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
                        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
                        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.false)))
                  (@Eq
                    (Except Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.BalanceView)
                    (Harmonia.Applications.Kadmos.Generated.balanceView lang
                      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n).machine)
                    (Harmonia.Applications.Kadmos.Generated.balanceView lang
                      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)))))))) :=
  @Harmonia.Applications.Kadmos.Generated.step_guard_reject

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @LE.le Int Int.instLEInt n (@OfNat.ofNat Int 0 (@instOfNat 0)) →
      @Eq
        (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetOutcome)
        (Harmonia.Applications.Kadmos.Generated.targetStep (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
          (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest lang n))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.TargetOutcome
          (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected lang b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_guard_reject

example : (∀ (b : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetOutcome)
    (Harmonia.Applications.Kadmos.Generated.targetStep
      (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.python)
      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
        Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
      (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest
        Harmonia.Applications.Kadmos.Generated.TargetLang.python (@OfNat.ofNat Int 0 (@instOfNat 0))))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetOutcome
      (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected
        Harmonia.Applications.Kadmos.Generated.TargetLang.python b (@OfNat.ofNat Int 0 (@instOfNat 0))))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_py_guard_zero

example : (∀ (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @LE.le Int Int.instLEInt n (@OfNat.ofNat Int 0 (@instOfNat 0)) →
      @Eq
        (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.TargetOutcome)
        (Harmonia.Applications.Kadmos.Generated.targetStep
          (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
          (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
            Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
          (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest
            Harmonia.Applications.Kadmos.Generated.TargetLang.ts n))
        (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
          Harmonia.Applications.Kadmos.Generated.TargetOutcome
          (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRejected
            Harmonia.Applications.Kadmos.Generated.TargetLang.ts b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_ts_guard_reject

namespace Batch17Endpoints
open Harmonia.Applications.Kadmos.Generated

-- The full rejection bundle at every balance/rejected-amount endpoint.
example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang 0)
   (canonicalDebitRequest lang (-Harmonia.Applications.Kadmos.S)) = .ok (balanceStepGuardRejected lang 0 (-Harmonia.Applications.Kadmos.S)) ∧
 targetProjection lang (balanceStepGuardRejected lang 0 (-Harmonia.Applications.Kadmos.S)) =
   .ok ⟨false, "Ready", [("balance", 0)], none⟩ ∧
 targetViolationCode (balanceStepGuardRejected lang 0 (-Harmonia.Applications.Kadmos.S)) = .ok (some "GUARD_FAILED") ∧
 HeapWF lang (balanceStepGuardRejected lang 0 (-Harmonia.Applications.Kadmos.S)).machine ∧
 balanceView lang (balanceStepGuardRejected lang 0 (-Harmonia.Applications.Kadmos.S)).machine =
   .ok ⟨"Ready", 0, [], none, 0, false⟩ ∧
 balanceView lang (balanceStepGuardRejected lang 0 (-Harmonia.Applications.Kadmos.S)).machine =
   balanceView lang (balanceCanonicalConstructed lang 0) :=
 step_guard_reject lang 0 (-Harmonia.Applications.Kadmos.S) (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang 0)
   (canonicalDebitRequest lang 0) = .ok (balanceStepGuardRejected lang 0 0) ∧
 targetProjection lang (balanceStepGuardRejected lang 0 0) =
   .ok ⟨false, "Ready", [("balance", 0)], none⟩ ∧
 targetViolationCode (balanceStepGuardRejected lang 0 0) = .ok (some "GUARD_FAILED") ∧
 HeapWF lang (balanceStepGuardRejected lang 0 0).machine ∧
 balanceView lang (balanceStepGuardRejected lang 0 0).machine =
   .ok ⟨"Ready", 0, [], none, 0, false⟩ ∧
 balanceView lang (balanceStepGuardRejected lang 0 0).machine =
   balanceView lang (balanceCanonicalConstructed lang 0) :=
 step_guard_reject lang 0 0 (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S)
   (canonicalDebitRequest lang (-Harmonia.Applications.Kadmos.S)) = .ok (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)) ∧
 targetProjection lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)) =
   .ok ⟨false, "Ready", [("balance", Harmonia.Applications.Kadmos.S)], none⟩ ∧
 targetViolationCode (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)) = .ok (some "GUARD_FAILED") ∧
 HeapWF lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)).machine ∧
 balanceView lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)).machine =
   .ok ⟨"Ready", Harmonia.Applications.Kadmos.S, [], none, Harmonia.Applications.Kadmos.S, false⟩ ∧
 balanceView lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)).machine =
   balanceView lang (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S) :=
 step_guard_reject lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S) (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S)
   (canonicalDebitRequest lang 0) = .ok (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S 0) ∧
 targetProjection lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S 0) =
   .ok ⟨false, "Ready", [("balance", Harmonia.Applications.Kadmos.S)], none⟩ ∧
 targetViolationCode (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S 0) = .ok (some "GUARD_FAILED") ∧
 HeapWF lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S 0).machine ∧
 balanceView lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S 0).machine =
   .ok ⟨"Ready", Harmonia.Applications.Kadmos.S, [], none, Harmonia.Applications.Kadmos.S, false⟩ ∧
 balanceView lang (balanceStepGuardRejected lang Harmonia.Applications.Kadmos.S 0).machine =
   balanceView lang (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S) :=
 step_guard_reject lang Harmonia.Applications.Kadmos.S 0 (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 balanceStepPrefixRun lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S) =
   .ok ⟨(balanceStepCanonicalPrefix lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)).1,
        (balanceStepCanonicalPrefix lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)).2, .normal⟩ :=
 balanceStep_canonical_prefix_execute lang _ _ (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang Harmonia.Applications.Kadmos.S (-Harmonia.Applications.Kadmos.S)).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < ((-Harmonia.Applications.Kadmos.S) : Int))))) :=
 balanceStep_canonical_guard_value lang _ _ (by decide)

example (lang : TargetLang) :
 balanceStepPrefixRun lang Harmonia.Applications.Kadmos.S 0 =
   .ok ⟨(balanceStepCanonicalPrefix lang Harmonia.Applications.Kadmos.S 0).1,
        (balanceStepCanonicalPrefix lang Harmonia.Applications.Kadmos.S 0).2, .normal⟩ :=
 balanceStep_canonical_prefix_execute lang _ _ (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang Harmonia.Applications.Kadmos.S 0).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < (0 : Int))))) :=
 balanceStep_canonical_guard_value lang _ _ (by decide)

example (lang : TargetLang) :
 balanceStepPrefixRun lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S =
   .ok ⟨(balanceStepCanonicalPrefix lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S).1,
        (balanceStepCanonicalPrefix lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S).2, .normal⟩ :=
 balanceStep_canonical_prefix_execute lang _ _ (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < (Harmonia.Applications.Kadmos.S : Int))))) :=
 balanceStep_canonical_guard_value lang _ _ (by decide)

example (lang : TargetLang) :
 balanceStepPrefixRun lang 0 (-Harmonia.Applications.Kadmos.S) =
   .ok ⟨(balanceStepCanonicalPrefix lang 0 (-Harmonia.Applications.Kadmos.S)).1,
        (balanceStepCanonicalPrefix lang 0 (-Harmonia.Applications.Kadmos.S)).2, .normal⟩ :=
 balanceStep_canonical_prefix_execute lang _ _ (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang 0 (-Harmonia.Applications.Kadmos.S)).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < ((-Harmonia.Applications.Kadmos.S) : Int))))) :=
 balanceStep_canonical_guard_value lang _ _ (by decide)

example (lang : TargetLang) :
 balanceStepPrefixRun lang 0 0 =
   .ok ⟨(balanceStepCanonicalPrefix lang 0 0).1,
        (balanceStepCanonicalPrefix lang 0 0).2, .normal⟩ :=
 balanceStep_canonical_prefix_execute lang _ _ (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang 0 0).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < (0 : Int))))) :=
 balanceStep_canonical_guard_value lang _ _ (by decide)

example (lang : TargetLang) :
 balanceStepPrefixRun lang 0 Harmonia.Applications.Kadmos.S =
   .ok ⟨(balanceStepCanonicalPrefix lang 0 Harmonia.Applications.Kadmos.S).1,
        (balanceStepCanonicalPrefix lang 0 Harmonia.Applications.Kadmos.S).2, .normal⟩ :=
 balanceStep_canonical_prefix_execute lang _ _ (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang 0 Harmonia.Applications.Kadmos.S).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < (Harmonia.Applications.Kadmos.S : Int))))) :=
 balanceStep_canonical_guard_value lang _ _ (by decide)

end Batch17Endpoints

-- Batch 18: strict declaration audit and visible axiom dependencies.
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_WF
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_WF
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_code
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_code
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_frame
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_frame
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_projection
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_projection
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_WF
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_WF
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_code
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_code
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_frame
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_frame
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_preserves_view
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_preserves_view
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_projection
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_projection
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_guard_positive
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_guard_positive
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accept_execute
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accept_execute
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF_footprint
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF_footprint
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF_zero
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF_zero
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_code
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_code
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_frame
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_frame
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_projection
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_projection
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF_footprint
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF_footprint
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF_zero
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF_zero
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_code
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_code
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_frame
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_frame
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_projection
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_projection
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_py_bounds_reject_execute
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_py_bounds_reject_execute
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accept_execute
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accept_execute
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF_footprint
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF_footprint
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF_zero
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF_zero
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_code
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_code
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_frame
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_frame
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_projection
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_projection
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF_footprint
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF_footprint
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF_zero
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF_zero
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_code
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_code
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_frame
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_frame
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_projection
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_projection
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.balanceStep_ts_bounds_reject_execute
#print axioms Harmonia.Applications.Kadmos.Generated.balanceStep_ts_bounds_reject_execute
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.step_accept
#print axioms Harmonia.Applications.Kadmos.Generated.step_accept
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.step_bounds_reject
#print axioms Harmonia.Applications.Kadmos.Generated.step_bounds_reject
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.targetStep_accept
#print axioms Harmonia.Applications.Kadmos.Generated.targetStep_accept
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.targetStep_bounds_reject
#print axioms Harmonia.Applications.Kadmos.Generated.targetStep_bounds_reject
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.targetStep_py_accept
#print axioms Harmonia.Applications.Kadmos.Generated.targetStep_py_accept
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.targetStep_py_bounds_reject
#print axioms Harmonia.Applications.Kadmos.Generated.targetStep_py_bounds_reject
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.targetStep_ts_accept
#print axioms Harmonia.Applications.Kadmos.Generated.targetStep_ts_accept
#audit_kadmos_generated_declaration Harmonia.Applications.Kadmos.Generated.targetStep_ts_bounds_reject
#print axioms Harmonia.Applications.Kadmos.Generated.targetStep_ts_bounds_reject

-- Batch 18: every new public canonical DEBIT contract, checked directly.

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF lang
    (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_WF

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String) (@Option.none String))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_code

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready"
        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n)
        (@List.cons Harmonia.Applications.Kadmos.Generated.BalanceRecord
          (Harmonia.Applications.Kadmos.Generated.expectedRecord lang n)
          (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord))
        (@Option.some Harmonia.Applications.Kadmos.Generated.BalanceSaved
          (Harmonia.Applications.Kadmos.Generated.BalanceSaved.mk "Ready" b
            (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)))
        b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_frame

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.true "Ready"
        (@List.cons (Prod String Int)
          (@Prod.mk String Int "balance" (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n))
          (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_accepted_projection

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF lang
    (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_WF

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String)
      (@Option.some String "INVALID_BOUNDS"))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_code

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_frame

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n).machine)
    (Harmonia.Applications.Kadmos.Generated.balanceView lang
      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_preserves_view

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection lang
      (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.false "Ready"
        (@List.cons (Prod String Int) (@Prod.mk String Int "balance" b) (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_boundsRejected_projection

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt Harmonia.Applications.Kadmos.S) n)
      (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
    @LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n →
      @Eq
        (Option
          (Except Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue))
        (@Option.map Harmonia.Applications.Kadmos.Generated.ExprOutcome
          (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
          Harmonia.Applications.Kadmos.Generated.ExprOutcome.result
          (@Except.toOption Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.ExprOutcome
            (Harmonia.Applications.Kadmos.Generated.balanceStepGuardRun lang b n)))
        (@Option.some
          (Except Harmonia.Applications.Kadmos.Generated.TargetValue Harmonia.Applications.Kadmos.Generated.TargetValue)
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
            Harmonia.Applications.Kadmos.Generated.TargetValue
            (Harmonia.Applications.Kadmos.Generated.TargetValue.bool Bool.true)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_canonical_guard_positive

example : (∀ (b n : Int),
  @LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b →
    @LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S →
      @LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n →
        @LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S →
          @LE.le Int Int.instLEInt n b →
            @Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.ExprOutcome)
              (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
                (Harmonia.Applications.Kadmos.Generated.balanceProgram
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python)
                (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                  Harmonia.Applications.Kadmos.Generated.TargetFrame
                  (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                    Harmonia.Applications.Kadmos.Generated.TargetLang.python
                    (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                      Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
                    n))
                (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                  Harmonia.Applications.Kadmos.Generated.TargetFrame
                  (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                    Harmonia.Applications.Kadmos.Generated.TargetLang.python
                    (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                      Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
                    n))
                (Harmonia.Applications.Kadmos.Generated.debitCallExpression
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.ExprOutcome
                (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
                  (Harmonia.Applications.Kadmos.Generated.balanceStepPyAccepted b n)
                  (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
                    Harmonia.Applications.Kadmos.Generated.TargetValue
                    (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                      (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 167 (instOfNatNat 167))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accept_execute

example : (∀ (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.python
    (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF

example : (∀ (b n : Int),
  @Eq Bool
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome b n).machine)
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
          (@OfNat.ofNat Int 0 (@instOfNat 0))).machine)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF_footprint

example : (Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.python
  (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
      (@OfNat.ofNat Int 0 (@instOfNat 0))).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_WF_zero

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String) (@Option.none String))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_code

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready"
        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n)
        (@List.cons Harmonia.Applications.Kadmos.Generated.BalanceRecord
          (Harmonia.Applications.Kadmos.Generated.expectedRecord
            Harmonia.Applications.Kadmos.Generated.TargetLang.python n)
          (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord))
        (@Option.some Harmonia.Applications.Kadmos.Generated.BalanceSaved
          (Harmonia.Applications.Kadmos.Generated.BalanceSaved.mk "Ready" b
            (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)))
        b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_frame

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.true "Ready"
        (@List.cons (Prod String Int)
          (@Prod.mk String Int "balance" (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n))
          (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_accepted_projection

example : (∀ (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.python
    (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF

example : (∀ (b n : Int),
  @Eq Bool
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome b n).machine)
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
          (@OfNat.ofNat Int 0 (@instOfNat 0))).machine)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF_footprint

example : (Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.python
  (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
      (@OfNat.ofNat Int 0 (@instOfNat 0))).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_WF_zero

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String)
      (@Option.some String "INVALID_BOUNDS"))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_code

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_frame

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection Harmonia.Applications.Kadmos.Generated.TargetLang.python
      (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.false "Ready"
        (@List.cons (Prod String Int) (@Prod.mk String Int "balance" b) (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_boundsRejected_projection

example : (∀ (b n : Int),
  @LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b →
    @LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S →
      @LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n →
        @LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S →
          @LT.lt Int Int.instLTInt b n →
            @Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.ExprOutcome)
              (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
                (Harmonia.Applications.Kadmos.Generated.balanceProgram
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python)
                (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
                  Harmonia.Applications.Kadmos.Generated.TargetFrame
                  (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                    Harmonia.Applications.Kadmos.Generated.TargetLang.python
                    (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                      Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
                    n))
                (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
                  Harmonia.Applications.Kadmos.Generated.TargetFrame
                  (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                    Harmonia.Applications.Kadmos.Generated.TargetLang.python
                    (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                      Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
                    n))
                (Harmonia.Applications.Kadmos.Generated.debitCallExpression
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.ExprOutcome
                (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
                  (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejected b n)
                  (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
                    Harmonia.Applications.Kadmos.Generated.TargetValue
                    (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                      (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 157 (instOfNatNat 157))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_py_bounds_reject_execute

example : (∀ (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LE.le Int Int.instLEInt n b →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
          (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
            (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                Harmonia.Applications.Kadmos.Generated.TargetLang.ts
                (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                  Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
                n))
            (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                Harmonia.Applications.Kadmos.Generated.TargetLang.ts
                (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                  Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
                n))
            (Harmonia.Applications.Kadmos.Generated.debitCallExpression
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.ExprOutcome
            (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
              (Harmonia.Applications.Kadmos.Generated.balanceStepTsAccepted b n)
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
                Harmonia.Applications.Kadmos.Generated.TargetValue
                (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                  (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 95 (instOfNatNat 95))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accept_execute

example : (∀ (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.ts
    (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF

example : (∀ (b n : Int),
  @Eq Bool
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome b n).machine)
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
          (@OfNat.ofNat Int 0 (@instOfNat 0))).machine)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF_footprint

example : (Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.ts
  (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
      (@OfNat.ofNat Int 0 (@instOfNat 0))).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_WF_zero

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String) (@Option.none String))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_code

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready"
        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n)
        (@List.cons Harmonia.Applications.Kadmos.Generated.BalanceRecord
          (Harmonia.Applications.Kadmos.Generated.expectedRecord Harmonia.Applications.Kadmos.Generated.TargetLang.ts n)
          (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord))
        (@Option.some Harmonia.Applications.Kadmos.Generated.BalanceSaved
          (Harmonia.Applications.Kadmos.Generated.BalanceSaved.mk "Ready" b
            (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)))
        b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_frame

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.true "Ready"
        (@List.cons (Prod String Int)
          (@Prod.mk String Int "balance" (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n))
          (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_accepted_projection

example : (∀ (b n : Int),
  Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.ts
    (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome b n).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF

example : (∀ (b n : Int),
  @Eq Bool
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome b n).machine)
    (Harmonia.Applications.Kadmos.Generated.heapWFCheck Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
          (@OfNat.ofNat Int 0 (@instOfNat 0))).machine)) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF_footprint

example : (Harmonia.Applications.Kadmos.Generated.HeapWF Harmonia.Applications.Kadmos.Generated.TargetLang.ts
  (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome (@OfNat.ofNat Int 0 (@instOfNat 0))
      (@OfNat.ofNat Int 0 (@instOfNat 0))).machine) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_WF_zero

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
    (Harmonia.Applications.Kadmos.Generated.targetViolationCode
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String)
      (@Option.some String "INVALID_BOUNDS"))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_code

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView)
    (Harmonia.Applications.Kadmos.Generated.balanceView Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome b n).machine)
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.BalanceView
      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.false))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_frame

example : (∀ (b n : Int),
  @Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized)
    (Harmonia.Applications.Kadmos.Generated.targetProjection Harmonia.Applications.Kadmos.Generated.TargetLang.ts
      (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome b n))
    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.Normalized
      (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.false "Ready"
        (@List.cons (Prod String Int) (@Prod.mk String Int "balance" b) (@List.nil (Prod String Int)))
        (@Option.none String)))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_boundsRejected_projection

example : (∀ (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LT.lt Int Int.instLTInt b n →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError Harmonia.Applications.Kadmos.Generated.ExprOutcome)
          (Harmonia.Applications.Kadmos.Generated.evalExpr (@OfNat.ofNat Nat 100 (instOfNatNat 100))
            (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            (@Prod.fst Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                Harmonia.Applications.Kadmos.Generated.TargetLang.ts
                (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                  Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
                n))
            (@Prod.snd Harmonia.Applications.Kadmos.Generated.TargetMachine
              Harmonia.Applications.Kadmos.Generated.TargetFrame
              (Harmonia.Applications.Kadmos.Generated.debitCallEntry
                Harmonia.Applications.Kadmos.Generated.TargetLang.ts
                (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                  Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
                n))
            (Harmonia.Applications.Kadmos.Generated.debitCallExpression
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.ExprOutcome
            (Harmonia.Applications.Kadmos.Generated.ExprOutcome.mk
              (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejected b n)
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetValue
                Harmonia.Applications.Kadmos.Generated.TargetValue
                (Harmonia.Applications.Kadmos.Generated.TargetValue.object
                  (@OfNat.ofNat Harmonia.Applications.Kadmos.Generated.ObjRef 86 (instOfNatNat 86))))))) :=
  @Harmonia.Applications.Kadmos.Generated.balanceStep_ts_bounds_reject_execute

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LE.le Int Int.instLEInt n b →
        And
          (@Eq
            (Except Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetOutcome)
            (Harmonia.Applications.Kadmos.Generated.targetStep
              (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
              (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
              (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest lang n))
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetOutcome
              (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n)))
          (And
            (@Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.Normalized)
              (Harmonia.Applications.Kadmos.Generated.targetProjection lang
                (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.Normalized
                (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.true "Ready"
                  (@List.cons (Prod String Int)
                    (@Prod.mk String Int "balance" (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n))
                    (@List.nil (Prod String Int)))
                  (@Option.none String))))
            (And
              (@Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
                (Harmonia.Applications.Kadmos.Generated.targetViolationCode
                  (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n))
                (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String) (@Option.none String)))
              (And
                (Harmonia.Applications.Kadmos.Generated.HeapWF lang
                  (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n).machine)
                (@Eq
                  (Except Harmonia.Applications.Kadmos.Generated.TargetError
                    Harmonia.Applications.Kadmos.Generated.BalanceView)
                  (Harmonia.Applications.Kadmos.Generated.balanceView lang
                    (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n).machine)
                  (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                    Harmonia.Applications.Kadmos.Generated.BalanceView
                    (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready"
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b n)
                      (@List.cons Harmonia.Applications.Kadmos.Generated.BalanceRecord
                        (Harmonia.Applications.Kadmos.Generated.expectedRecord lang n)
                        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord))
                      (@Option.some Harmonia.Applications.Kadmos.Generated.BalanceSaved
                        (Harmonia.Applications.Kadmos.Generated.BalanceSaved.mk "Ready" b
                          (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)))
                      b Bool.false))))))) :=
  @Harmonia.Applications.Kadmos.Generated.step_accept

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LT.lt Int Int.instLTInt b n →
        And
          (@Eq
            (Except Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetOutcome)
            (Harmonia.Applications.Kadmos.Generated.targetStep
              (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
              (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
              (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest lang n))
            (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
              Harmonia.Applications.Kadmos.Generated.TargetOutcome
              (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n)))
          (And
            (@Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.Normalized)
              (Harmonia.Applications.Kadmos.Generated.targetProjection lang
                (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.Normalized
                (Harmonia.Applications.Kadmos.Generated.Normalized.mk Bool.false "Ready"
                  (@List.cons (Prod String Int) (@Prod.mk String Int "balance" b) (@List.nil (Prod String Int)))
                  (@Option.none String))))
            (And
              (@Eq (Except Harmonia.Applications.Kadmos.Generated.TargetError (Option String))
                (Harmonia.Applications.Kadmos.Generated.targetViolationCode
                  (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n))
                (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError (Option String)
                  (@Option.some String "INVALID_BOUNDS")))
              (And
                (Harmonia.Applications.Kadmos.Generated.HeapWF lang
                  (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n).machine)
                (And
                  (@Eq
                    (Except Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.BalanceView)
                    (Harmonia.Applications.Kadmos.Generated.balanceView lang
                      (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n).machine)
                    (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.BalanceView
                      (Harmonia.Applications.Kadmos.Generated.BalanceView.mk "Ready" b
                        (@List.nil Harmonia.Applications.Kadmos.Generated.BalanceRecord)
                        (@Option.none Harmonia.Applications.Kadmos.Generated.BalanceSaved) b Bool.false)))
                  (@Eq
                    (Except Harmonia.Applications.Kadmos.Generated.TargetError
                      Harmonia.Applications.Kadmos.Generated.BalanceView)
                    (Harmonia.Applications.Kadmos.Generated.balanceView lang
                      (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n).machine)
                    (Harmonia.Applications.Kadmos.Generated.balanceView lang
                      (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)))))))) :=
  @Harmonia.Applications.Kadmos.Generated.step_bounds_reject

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LE.le Int Int.instLEInt n b →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome)
          (Harmonia.Applications.Kadmos.Generated.targetStep
            (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
            (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest lang n))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome
            (Harmonia.Applications.Kadmos.Generated.balanceStepAccepted lang b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_accept

example : (∀ (lang : Harmonia.Applications.Kadmos.Generated.TargetLang) (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LT.lt Int Int.instLTInt b n →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome)
          (Harmonia.Applications.Kadmos.Generated.targetStep
            (Harmonia.Applications.Kadmos.Generated.balanceProgram lang)
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed lang b)
            (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest lang n))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome
            (Harmonia.Applications.Kadmos.Generated.balanceStepBoundsRejected lang b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_bounds_reject

example : (∀ (b n : Int),
  @LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b →
    @LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S →
      @LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n →
        @LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S →
          @LE.le Int Int.instLEInt n b →
            @Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.TargetOutcome)
              (Harmonia.Applications.Kadmos.Generated.targetStep
                (Harmonia.Applications.Kadmos.Generated.balanceProgram
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python)
                (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
                (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python n))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.TargetOutcome
                (Harmonia.Applications.Kadmos.Generated.balanceStepPyAcceptedOutcome b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_py_accept

example : (∀ (b n : Int),
  @LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b →
    @LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S →
      @LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n →
        @LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S →
          @LT.lt Int Int.instLTInt b n →
            @Eq
              (Except Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.TargetOutcome)
              (Harmonia.Applications.Kadmos.Generated.targetStep
                (Harmonia.Applications.Kadmos.Generated.balanceProgram
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python)
                (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python b)
                (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest
                  Harmonia.Applications.Kadmos.Generated.TargetLang.python n))
              (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
                Harmonia.Applications.Kadmos.Generated.TargetOutcome
                (Harmonia.Applications.Kadmos.Generated.balanceStepPyBoundsRejectedOutcome b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_py_bounds_reject

example : (∀ (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LE.le Int Int.instLEInt n b →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome)
          (Harmonia.Applications.Kadmos.Generated.targetStep
            (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
            (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts n))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome
            (Harmonia.Applications.Kadmos.Generated.balanceStepTsAcceptedOutcome b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_ts_accept

example : (∀ (b n : Int),
  And (@LE.le Int Int.instLEInt (@OfNat.ofNat Int 0 (@instOfNat 0)) b)
      (@LE.le Int Int.instLEInt b Harmonia.Applications.Kadmos.S) →
    And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int 0 (@instOfNat 0)) n)
        (@LE.le Int Int.instLEInt n Harmonia.Applications.Kadmos.S) →
      @LT.lt Int Int.instLTInt b n →
        @Eq
          (Except Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome)
          (Harmonia.Applications.Kadmos.Generated.targetStep
            (Harmonia.Applications.Kadmos.Generated.balanceProgram Harmonia.Applications.Kadmos.Generated.TargetLang.ts)
            (Harmonia.Applications.Kadmos.Generated.balanceCanonicalConstructed
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts b)
            (Harmonia.Applications.Kadmos.Generated.canonicalDebitRequest
              Harmonia.Applications.Kadmos.Generated.TargetLang.ts n))
          (@Except.ok Harmonia.Applications.Kadmos.Generated.TargetError
            Harmonia.Applications.Kadmos.Generated.TargetOutcome
            (Harmonia.Applications.Kadmos.Generated.balanceStepTsBoundsRejectedOutcome b n))) :=
  @Harmonia.Applications.Kadmos.Generated.targetStep_ts_bounds_reject

namespace Batch18Endpoints
open Harmonia.Applications.Kadmos.Generated

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang 0)
   (canonicalDebitRequest lang 1) = .ok (balanceStepBoundsRejected lang 0 1) ∧
 targetProjection lang (balanceStepBoundsRejected lang 0 1) =
   .ok ⟨false, "Ready", [("balance", 0)], none⟩ ∧
 targetViolationCode (balanceStepBoundsRejected lang 0 1) = .ok (some "INVALID_BOUNDS") ∧
 HeapWF lang (balanceStepBoundsRejected lang 0 1).machine ∧
 balanceView lang (balanceStepBoundsRejected lang 0 1).machine =
   .ok ⟨"Ready", 0, [], none, 0, false⟩ ∧
 balanceView lang (balanceStepBoundsRejected lang 0 1).machine =
   balanceView lang (balanceCanonicalConstructed lang 0) :=
 step_bounds_reject lang 0 1 (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang 0)
   (canonicalDebitRequest lang Harmonia.Applications.Kadmos.S) = .ok (balanceStepBoundsRejected lang 0 Harmonia.Applications.Kadmos.S) ∧
 targetProjection lang (balanceStepBoundsRejected lang 0 Harmonia.Applications.Kadmos.S) =
   .ok ⟨false, "Ready", [("balance", 0)], none⟩ ∧
 targetViolationCode (balanceStepBoundsRejected lang 0 Harmonia.Applications.Kadmos.S) = .ok (some "INVALID_BOUNDS") ∧
 HeapWF lang (balanceStepBoundsRejected lang 0 Harmonia.Applications.Kadmos.S).machine ∧
 balanceView lang (balanceStepBoundsRejected lang 0 Harmonia.Applications.Kadmos.S).machine =
   .ok ⟨"Ready", 0, [], none, 0, false⟩ ∧
 balanceView lang (balanceStepBoundsRejected lang 0 Harmonia.Applications.Kadmos.S).machine =
   balanceView lang (balanceCanonicalConstructed lang 0) :=
 step_bounds_reject lang 0 Harmonia.Applications.Kadmos.S (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang (Harmonia.Applications.Kadmos.S - 1))
   (canonicalDebitRequest lang Harmonia.Applications.Kadmos.S) = .ok (balanceStepBoundsRejected lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S) ∧
 targetProjection lang (balanceStepBoundsRejected lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S) =
   .ok ⟨false, "Ready", [("balance", (Harmonia.Applications.Kadmos.S - 1))], none⟩ ∧
 targetViolationCode (balanceStepBoundsRejected lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S) = .ok (some "INVALID_BOUNDS") ∧
 HeapWF lang (balanceStepBoundsRejected lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S).machine ∧
 balanceView lang (balanceStepBoundsRejected lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S).machine =
   .ok ⟨"Ready", (Harmonia.Applications.Kadmos.S - 1), [], none, (Harmonia.Applications.Kadmos.S - 1), false⟩ ∧
 balanceView lang (balanceStepBoundsRejected lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S).machine =
   balanceView lang (balanceCanonicalConstructed lang (Harmonia.Applications.Kadmos.S - 1)) :=
 step_bounds_reject lang (Harmonia.Applications.Kadmos.S - 1) Harmonia.Applications.Kadmos.S (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang 1)
   (canonicalDebitRequest lang 1) = .ok (balanceStepAccepted lang 1 1) ∧
 targetProjection lang (balanceStepAccepted lang 1 1) =
   .ok ⟨true, "Ready", [("balance", 1 - 1)], none⟩ ∧
 targetViolationCode (balanceStepAccepted lang 1 1) = .ok none ∧
 HeapWF lang (balanceStepAccepted lang 1 1).machine ∧
 balanceView lang (balanceStepAccepted lang 1 1).machine =
   .ok ⟨"Ready", 1 - 1, [expectedRecord lang 1], some ⟨"Ready", 1, []⟩, 1, false⟩ :=
 step_accept lang 1 1 (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S)
   (canonicalDebitRequest lang 1) = .ok (balanceStepAccepted lang Harmonia.Applications.Kadmos.S 1) ∧
 targetProjection lang (balanceStepAccepted lang Harmonia.Applications.Kadmos.S 1) =
   .ok ⟨true, "Ready", [("balance", Harmonia.Applications.Kadmos.S - 1)], none⟩ ∧
 targetViolationCode (balanceStepAccepted lang Harmonia.Applications.Kadmos.S 1) = .ok none ∧
 HeapWF lang (balanceStepAccepted lang Harmonia.Applications.Kadmos.S 1).machine ∧
 balanceView lang (balanceStepAccepted lang Harmonia.Applications.Kadmos.S 1).machine =
   .ok ⟨"Ready", Harmonia.Applications.Kadmos.S - 1, [expectedRecord lang 1], some ⟨"Ready", Harmonia.Applications.Kadmos.S, []⟩, Harmonia.Applications.Kadmos.S, false⟩ :=
 step_accept lang Harmonia.Applications.Kadmos.S 1 (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang Harmonia.Applications.Kadmos.S)
   (canonicalDebitRequest lang Harmonia.Applications.Kadmos.S) = .ok (balanceStepAccepted lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S) ∧
 targetProjection lang (balanceStepAccepted lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S) =
   .ok ⟨true, "Ready", [("balance", Harmonia.Applications.Kadmos.S - Harmonia.Applications.Kadmos.S)], none⟩ ∧
 targetViolationCode (balanceStepAccepted lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S) = .ok none ∧
 HeapWF lang (balanceStepAccepted lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S).machine ∧
 balanceView lang (balanceStepAccepted lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S).machine =
   .ok ⟨"Ready", Harmonia.Applications.Kadmos.S - Harmonia.Applications.Kadmos.S, [expectedRecord lang Harmonia.Applications.Kadmos.S], some ⟨"Ready", Harmonia.Applications.Kadmos.S, []⟩, Harmonia.Applications.Kadmos.S, false⟩ :=
 step_accept lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S (by decide) (by decide) (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang 0 1).toOption.map ExprOutcome.result =
   some (.ok (.bool true)) :=
 balanceStep_canonical_guard_positive lang 0 1 (by decide) (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang 0 Harmonia.Applications.Kadmos.S).toOption.map ExprOutcome.result =
   some (.ok (.bool true)) :=
 balanceStep_canonical_guard_positive lang 0 Harmonia.Applications.Kadmos.S (by decide) (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang Harmonia.Applications.Kadmos.S 1).toOption.map ExprOutcome.result =
   some (.ok (.bool true)) :=
 balanceStep_canonical_guard_positive lang Harmonia.Applications.Kadmos.S 1 (by decide) (by decide)

example (lang : TargetLang) :
 (balanceStepGuardRun lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S).toOption.map ExprOutcome.result =
   some (.ok (.bool true)) :=
 balanceStep_canonical_guard_positive lang Harmonia.Applications.Kadmos.S Harmonia.Applications.Kadmos.S (by decide) (by decide)

end Batch18Endpoints
