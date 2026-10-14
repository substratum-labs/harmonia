import HarmoniaTests.KadmosGeneratedK02ConstructorProofTS
import HarmoniaTests.KadmosGeneratedK02ConstructorProofPython

open Harmonia.Applications.Kadmos.Generated

-- Boundary facts are split by language to bound physical kernel memory.
-- Universal targetConstruct_sound remains a separate open proof obligation.
#print axioms balanceRepCheck_sound
#print axioms checkedConstructor_witness

-- Universal input-allocation obligation, separate from constructor execution.
theorem kadmos_generated_seed_all_balances {lang m b}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    allocateSeed m (canonicalBalanceSeed lang b) =
      .ok ((allocObject m (balanceHeapObject lang m b)).1,
        .object (allocObject m (balanceHeapObject lang m b)).2) :=
  allocateSeed_balance (balance_natAbs hb)

-- Clone host depth is separate from the entrypoint's recursion depth.
theorem kadmos_generated_clone_balance_all {lang m b ref k}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m b))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    cloneValue (k + 2) m (.object ref) =
      .ok ((allocObject m (balanceHeapObject lang m b)).1, .object m.nextObject) :=
  cloneValue_balance ho hf

theorem kadmos_generated_clone_from_rep {lang b m}
    (h : BalanceRep lang b m) :
    cloneValue 2048 m (.object m.checker.context) =
      .ok ((allocObject m (balanceHeapObject lang m b)).1, .object m.nextObject) :=
  cloneValue_balance h.context h.heapWF.object_fresh

-- The scalar child really consumes a separate host-depth edge.
set_option maxRecDepth 4096 in
theorem kadmos_generated_clone_balance_depth_one {lang m b ref}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m b)) :
    cloneValue 1 m (.object ref) = .error .exhaustedFuel := by
  cases lang <;>
    simp [cloneValue, ho, balanceHeapObject, balanceDataDescriptor, integerValue,
      Bind.bind, Pure.pure, Except.bind, Except.pure, List.forIn_cons, List.forIn_nil]

#print axioms allocateSeed_balance
#print axioms cloneValue_balance
#print axioms HeapWF.object_fresh
#print axioms signed_natAbs

-- Canonical production programs must be exactly the actual-source ASTs.
theorem kadmos_generated_balanceProgram_ts :
    balanceProgram .ts = HarmoniaTests.KadmosGeneratedK02ClosedPrograms.balanceTsProgram := by
  exact balanceProgram_of_parse
    HarmoniaTests.KadmosGeneratedK02ClosedPrograms.balanceTsProgram_source

theorem kadmos_generated_balanceProgram_python :
    balanceProgram .python = HarmoniaTests.KadmosGeneratedK02ClosedPrograms.balancePyProgram := by
  exact balanceProgram_of_parse
    HarmoniaTests.KadmosGeneratedK02ClosedPrograms.balancePyProgram_source

#print axioms kadmos_generated_balanceProgram_ts
#print axioms kadmos_generated_balanceProgram_python

-- Seed-independent closed execution, followed by symbolic allocation.
-- These phase facts do not claim the remaining constructor call is total.
#print axioms targetConstructWithFuel_of_prepared
#print axioms targetConstructFromPrepared_of_seed
#print axioms balancePreparation_total
#print axioms balancePreparation_success
#print axioms balanceProgram_lang
#print axioms targetConstruct_balance_prepared
#print axioms targetConstruct_balance_call

example (lang : TargetLang) {b : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) =
      targetConstructorCall 100 (balanceProgram lang)
        (allocObject (balancePreparation lang).1
          (balanceHeapObject lang (balancePreparation lang).1 b)).1
        (balancePreparation lang).2
        (.object (balancePreparation lang).1.nextObject) :=
  targetConstruct_balance_call lang hb

#print axioms balancePreparation_heapWF
#print axioms balancePreparation_frameWF

-- Method provenance comes from the executed canonical module/class prefix.
theorem kadmos_generated_prepared_constructor_lookup (lang : TargetLang) :
    (balanceConstructorLookup lang).isSome = true :=
  balanceConstructorLookup_total lang

theorem kadmos_generated_prepared_constructor_shape (lang : TargetLang) :
    readCheckerField (balancePreparation lang).1 (balanceConstructorName lang) =
      .error (.unboundLocal (balanceConstructorName lang)) ∧
    (balanceStoredConstructor lang).2.params =
      [⟨balanceConstructorParam lang, some .null⟩] ∧
    (balanceStoredConstructor lang).2.qualifiedName =
      "WorldChecker." ++ balanceConstructorName lang :=
  balanceStoredConstructor_shape lang

#print axioms kadmos_generated_prepared_constructor_lookup
#print axioms kadmos_generated_prepared_constructor_shape

-- Every bounded seed reaches this actual stored body at depth 99.
-- The equation does not assume or conclude body/constructor success.
theorem kadmos_generated_constructor_body_all_balances (lang : TargetLang) {b : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) = (do
      let body ← execStmt 99 (balanceProgram lang)
        (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
        (balanceStoredConstructor lang).2.body
      let result ← closureResult lang body
      match result.result with
      | .ok _ => pure result.machine
      | .error e => throw (.sourceException e)) :=
  targetConstruct_balance_body lang hb

#print axioms kadmos_generated_constructor_body_all_balances

-- Complete small constructor ASTs are source-bound; this does not claim the
-- generated reset/helpers or the post-construction representation are proved.
example (lang : TargetLang) :
    (balanceStoredConstructor lang).2.body = balanceConstructorBodyTemplate lang :=
  balanceConstructorBody_shape lang

example (lang : TargetLang) (b : Int) :
    localValue (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (balanceConstructorParam lang) = .ok (.object (balancePreparation lang).1.nextObject) :=
  balanceConstructorBodyEntry_argument lang b

example (lang : TargetLang) (b : Int) :
    objectAt (balanceConstructorBodyEntry lang b).1 (balancePreparation lang).1.nextObject =
      .ok (balanceHeapObject lang (balancePreparation lang).1 b) :=
  balanceConstructorBodyEntry_object lang b

example {lang m f} (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    execStmt 99 (balanceProgram lang) m f (balanceStoredReset lang).2.body =
      execStmt 97 (balanceProgram lang) (balanceSetBusy m true) f
        (restStmt (restStmt (balanceStoredReset lang).2.body)) :=
  balanceReset_idle_entry hr hi (by decide)

#print axioms balanceConstructorBody_shape
#print axioms balanceConstructor_ts_reset_eq
#print axioms balanceConstructor_python_guard_eq
#print axioms balanceConstructor_python_after_guard
#print axioms balanceReset_idle_entry
#print axioms evalReceiverObjectCall_eq
#print axioms balanceStoredReset_lookup

-- Canonical entry excludes shadowing of the two Python type-check hosts.
example (b : Int) :
    localValue (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      "type" = .ok (.builtin .type) ∧
    localValue (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      "dict" = .ok (.builtin .dict) :=
  balanceConstructorBodyEntry_python_types b

example (lang : TargetLang) (b : Int) :
    readCheckerField (balanceConstructorBodyEntry lang b).1 "reset" =
      .error (.unboundLocal "reset") ∧
    (balanceConstructorBodyEntry lang b).1.classMethods.lookup "reset" =
      some (balanceStoredReset lang).1 ∧
    closureAt (balanceConstructorBodyEntry lang b).1 (balanceStoredReset lang).1 =
      .ok (balanceStoredReset lang).2 :=
  balanceConstructorBodyEntry_reset_store lang b

#print axioms balanceConstructor_python_canonical_after_guard
#print axioms balanceConstructor_reset_call_eq_body
#print axioms balanceResetBodyEntry_snapshots
#print axioms balanceConstructor_ts_snapshots_eq

-- Six-write regression: missing or reordered allocations/field writes change
-- this physical result for an arbitrary starting heap and initial state.
example (m : TargetMachine) (initial : String) :
    let final := balancePythonInitialized m initial
    final.nextObject = m.nextObject + 2 ∧
    final.checker.constructorSeed = none ∧ final.checker.state = initial ∧
    final.checker.context = m.nextObject ∧ final.checker.history = m.nextObject + 1 ∧
    final.checker.busy = false ∧ final.checker.undo = none := by
  simp [balancePythonInitialized, allocObject]

example (m : TargetMachine) (initial : String) (name : String) (ref : ClosureRef) :
    (balancePythonInitialized m initial).classMethods.lookup name = m.classMethods.lookup name ∧
    closureAt (balancePythonInitialized m initial) ref = closureAt m ref := ⟨rfl, rfl⟩

example (b : Int) :
    execStmt 99 (balanceProgram .python)
      (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      (balanceStoredConstructor .python).2.body =
      execStmt 92 (balanceProgram .python)
        (balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready")
        (balanceConstructorBodyEntry .python b).2 balancePythonAfterInit :=
  balanceConstructor_python_canonical_initialized b

example (lang : TargetLang) :
    snapshotTryCheck 4 (restStmt (restStmt (balanceStoredReset lang).2.body)) = true :=
  balanceReset_snapshot_shape lang

example (lang : TargetLang) :
    snapshotTryCheck (if lang == .ts then 4 else 5)
      (restStmt (balanceStepAfterBusy lang)) = true :=
  balanceStep_snapshot_shape lang

#print axioms balanceConstructor_python_initialized
#print axioms balanceConstructorBodyEntry_python_initial
#print axioms balanceConstructor_python_canonical_initialized
#print axioms balancePythonInitialized_preserves_bindings
#print axioms balanceConstructor_python_reset_call_eq_body
#print axioms balanceConstructor_python_snapshots_eq
#print axioms balanceReset_snapshots_eq
#print axioms balanceStep_snapshots_eq
#print axioms balanceReset_protected_shape
#print axioms balanceStep_protected_shape
#print axioms execTryCatchFinally_eq

-- The actual suffix copies the canonical context to a fresh seed. Full reset
-- execution must establish these physical receiver/host/context reads.
example {m f b} (hr : f.receiver = some m.checkerRef)
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .python m b)) :
    execStmt 6 (balanceProgram .python) m f (restStmt balancePythonAfterInit) =
      .ok ⟨balancePythonSeedCopied m b, f, .normal⟩ :=
  balanceConstructor_python_seed_copy hr hd ho (by decide)

#print axioms hostDict_balance
#print axioms balancePython_context_copy
#print axioms balanceConstructor_python_seed_copy
#print axioms balancePythonSeedCopied_preserves_bindings

#check balanceReset_snapshot_execute
#check balanceConstructor_ts_seed_copy
#check balanceReset_cleanup_execute

-- These source projections retain the live rollback body and all protected
-- code. A seed snapshot is not present in the pinned reset sources.
example (lang : TargetLang) :
    firstStmt (dropStmts 3 (balanceResetSnapshots lang)) =
      .defineFunction "rollback" [] (balanceResetRollback lang) :=
  (balanceReset_snapshot_heads lang).2.2.2

-- Receiver binding is derived from the opaque allocation recipe.
example (lang : TargetLang) (b : Int) :
    (balanceResetBodyEntry lang b).2.receiver = some (balanceResetBodyEntry lang b).1.checkerRef :=
  balanceResetBodyEntry_receiver lang b

example {m f b} (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .ts m b))
    (hn : m.checker.context ≠ m.nextObject)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    execStmt 6 (balanceProgram .ts) m f (restStmt (balanceConstructorBodyTemplate .ts)) =
      .ok ⟨balanceTsSeedCopied m b, f, .normal⟩ :=
  balanceConstructor_ts_seed_copy (k := 0) hr ho hn hf

-- Fresh copying preserves the symbolic numeric descriptor and publishes the
-- copied seed address, rather than reusing the context address.
example {m f b} (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .ts m b))
    (hn : m.checker.context ≠ m.nextObject)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    evalExpr 4 (balanceProgram .ts) m f (resetContextCopy .ts) =
      .ok ⟨(allocObject m (balanceHeapObject .ts m b)).1, .ok (.object m.nextObject)⟩ :=
  balanceTs_context_copy (k := 0) hr ho hn hf

example {m f} (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.context = .ok (literalObject .python m))
    (hn : m.checker.context ≠ m.nextObject)
    (hd : localValue m f "dict" = .ok (.builtin .dict)) :
    evalExpr 4 (balanceProgram .python) m f (resetContextCopy .python) =
      .ok ⟨(allocObject m (literalObject .python m)).1, .ok (.object m.nextObject)⟩ :=
  resetEmptyContext_copy (k := 0) hr ho hn (fun _ => hd)

example {lang m f} (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.history = .ok (emptyBalanceHistory lang m))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (hc : SnapshotCloneRead lang m f) :
    evalExpr 4 (balanceProgram lang) m f (resetHistoryCopy lang) =
      .ok ⟨(allocObject m (emptyBalanceHistory lang m)).1, .ok (.object m.nextObject)⟩ :=
  resetHistory_copy (k := 0) hr ho hf hc

example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) :
    execStmt 2 (balanceProgram lang) m f
      (firstStmt (dropStmts 3 (balanceResetSnapshots lang))) =
      .ok ⟨(snapshotRollbackInstalled lang m f (balanceResetRollback lang)).1,
        (snapshotRollbackInstalled lang m f (balanceResetRollback lang)).2, .normal⟩ := by
  rw [(balanceReset_snapshot_heads lang).2.2.2]
  exact execSnapshotRollback lang m f _ 0

#print axioms balanceReset_snapshot_heads_check
#print axioms balanceReset_snapshot_execute
#print axioms balanceConstructor_ts_seed_copy
#print axioms balanceReset_state_snapshot_execute
#print axioms execDefineFunction_empty

example {lang m f} (hr : f.receiver = some m.checkerRef)
    (hn : lang = .python → snapshotAddress m f (snapshotName lang 0) = none) :
    execStmt 3 (balanceProgram lang) m f (firstStmt (balanceResetSnapshots lang)) =
      .ok ⟨(resetSnapshotState lang m f).1, (resetSnapshotState lang m f).2, .normal⟩ :=
  balanceReset_state_snapshot_execute (k := 0) hr hn

-- The installed source closure is callable through its freshly written cell,
-- and retains snapshot addresses rather than copied snapshot values.
example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) (body : TargetStmt) :
    localValue (snapshotRollbackInstalled lang m f body).1
      (snapshotRollbackInstalled lang m f body).2 "rollback" = .ok (.closure m.nextClosure) := by
  cases lang <;> simp [snapshotRollbackInstalled, functionInstalled, localValue,
    allocCell, allocClosure, readCell, List.lookup]

#check balanceReset_candidate_ts_execute
#check balanceReset_candidate_python_execute

example (lang : TargetLang) :
    firstStmt (balanceResetProtected lang).body =
      snapshotBindStmt lang "candidate" (resetCandidateExpr lang) :=
  balanceReset_candidate_shape lang

example {m f ref source} (hd : localValue m f "dict" = .ok (.builtin .dict))
    (hl : localValue m f "_DEFAULTS" = .ok (.object ref))
    (ho : objectAt m ref = .ok source) (hk : source.kind = .mappingProxy)
    (hown : source.own = [("balance", balanceDataDescriptor .python 100)])
    (hn : snapshotAddress m f "candidate" = none) :
    execStmt 4 (balanceProgram .python) m f (firstStmt (balanceResetProtected .python).body) =
      .ok ⟨(snapshotBound .python (allocObject m (balanceHeapObject .python m 100)).1 f "candidate" (.object m.nextObject)).1,
        (snapshotBound .python (allocObject m (balanceHeapObject .python m 100)).1 f "candidate" (.object m.nextObject)).2, .normal⟩ :=
  balanceReset_candidate_python_execute (k := 0) hd hl ho hk hown hn

#print axioms balanceReset_candidate_shape
#print axioms balanceReset_candidate_ts_execute
#print axioms balanceReset_candidate_python_execute

-- One less statement budget fails at the argument spine before any defaults
-- object read or allocation. This tests actual execution, not just ranks.
example {m f} (hd : localValue m f "dict" = .ok (.builtin .dict)) :
    evalExpr 2 (balanceProgram .python) m f (resetCandidateExpr .python) =
      .error .exhaustedFuel := by
  change evalExpr 2 _ _ _ (.call (.local "dict") (.sequence (.local "_DEFAULTS") .empty)) = _
  simp [evalExpr, evalArgValues, hd, Bind.bind, Pure.pure, Except.bind, Except.pure]
  rfl

-- Physical premises are discharged from constructor provenance for arbitrary
-- inputs. Bounds are needed later by validation, not by snapshots/default copy.
example (lang : TargetLang) (b : Int) : balanceResetPhysicalCheck lang b :=
  balanceResetPhysicalCheck_all lang b

example (lang : TargetLang) (b : Int) : balanceResetCandidatePhysicalCheck lang b :=
  balanceResetCandidatePhysicalCheck_all lang b

example (lang : TargetLang) (b : Int) :
    localValue (balanceResetCandidateEntry lang b).1 (balanceResetCandidateEntry lang b).2
      (balanceConstructorParam lang) = .ok (.object (balancePreparation lang).1.nextObject) :=
  balanceResetCandidateEntry_parameter lang b

example (lang : TargetLang) (b : Int) :
    let e := balanceCanonicalResetEntry lang b
    execStmt 94 (balanceProgram lang) e.1 e.2 (balanceResetSnapshots lang) =
      execStmt 90 (balanceProgram lang)
        (balanceCanonicalResetStage lang b 3).1 (balanceCanonicalResetStage lang b 3).2
        (dropStmts 4 (balanceResetSnapshots lang)) :=
  balanceReset_canonical_snapshot_execute lang b 86

example (lang : TargetLang) (b : Int) :
    let e := balanceCanonicalResetStage lang b 3
    execStmt 8 (balanceProgram lang) e.1 e.2 (firstStmt (balanceResetProtected lang).body) =
      .ok ⟨(balanceResetCandidateEntry lang b).1, (balanceResetCandidateEntry lang b).2, .normal⟩ :=
  balanceReset_canonical_candidate_execute lang b 4

-- Python chooses the supplied object at the next real source statement.
example (b : Int) :
    let e := balanceResetCandidateEntry .python b
    execStmt 8 (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 1) =
      .ok ⟨(balanceResetMiddleEntry .python b).1, (balanceResetMiddleEntry .python b).2, .normal⟩ :=
  balanceReset_python_canonical_ctx_execute b 4

#print axioms balanceResetPhysicalCheck_all
#print axioms balanceReset_canonical_snapshot_execute
#print axioms balanceReset_canonical_candidate_execute
#print axioms balanceResetCandidateEntry_parameter
#print axioms balanceReset_python_canonical_ctx_execute
#print axioms balanceConstructor_canonical_snapshots_eq

-- Bounded inputs enter the actual targetConstruct API, not merely a manually
-- supplied reset frame. The residual try/catch/finally and seed-copy stay live.
theorem kadmos_generated_constructor_snapshot_continuation (lang : TargetLang) {b : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) = (do
      let body ← (do
        let resetBody ← execStmt (if lang == .ts then 90 else 83) (balanceProgram lang)
          (balanceCanonicalResetStage lang b 3).1 (balanceCanonicalResetStage lang b 3).2
          (dropStmts 4 (balanceResetSnapshots lang))
        balanceConstructorResetContinuation lang b resetBody)
      let result ← closureResult lang body
      match result.result with
      | .ok _ => pure result.machine
      | .error e => throw (.sourceException e)) := by
  rw [targetConstruct_balance_body lang hb, balanceConstructor_canonical_snapshots_eq lang b]
  rfl

#print axioms kadmos_generated_constructor_snapshot_continuation

-- Source-selected writes retain casts/conversions rather than replacing the
-- real source loop with an invented assignment.
example (lang : TargetLang) :
    balanceResetOverlayWrite lang =
      .assign (.index (.local "candidate") (.local "name")) (resetOverlayValue lang) :=
  balanceReset_overlay_write_shape lang

example (lang : TargetLang) {m ref old b}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old)) :
    writeOwn m ref "balance" (integerValue lang b) =
      .ok (balanceOverlayUpdated lang m ref b) :=
  writeOwn_balance_existing ho

#print axioms balanceReset_overlay_write_ts_execute
#print axioms balanceReset_overlay_write_python_execute
#print axioms writeOwn_balance_existing

example (lang : TargetLang) {m ref old b}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old)) :
    objectAt (balanceOverlayUpdated lang m ref b) ref = .ok (balanceHeapObject lang m b) :=
  balanceOverlayUpdated_objectAt ho
