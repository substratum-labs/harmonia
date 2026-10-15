import HarmoniaTests.KadmosGeneratedK02ConstructorProofTS
import HarmoniaTests.KadmosGeneratedK02ConstructorProofPython

open Harmonia.Applications.Kadmos.Generated

-- Boundary facts are split by language to bound physical kernel memory.
-- Canonical bounded execution contracts are checked below; general step
-- correspondence remains a separate proof obligation.
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

-- Direct regression for the previously compiled but uninvoked guard theorem.
example {m f ref object k}
    (hp : localValue m f "ctx" = .ok (.object ref))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m ref = .ok object) (hk : object.kind = .pythonDict) :
    execStmt (k + 6) (balanceProgram .python) m f
      (ifYesStmt (balanceResetMiddleStmt .python 2)) =
    execStmt (k + 5) (balanceProgram .python) m f
      (restStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) :=
  balanceReset_python_plain_guard_skip hp ht hd ho hk

-- Canonical read congruence and direct discharge of the Python plain-dict guard.
example (lang : TargetLang) (b : Int) (name : String) :
    localValue (balanceResetMiddleEntry lang b).1 (balanceResetMiddleEntry lang b).2 name =
      localValue (balanceResetMiddleEntry lang 0).1 (balanceResetMiddleEntry lang 0).2 name :=
  balanceResetMiddleEntry_localValue lang b name

example (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    execStmt (k + 6) (balanceProgram .python) e.1 e.2
      (ifYesStmt (balanceResetMiddleStmt .python 2)) =
    execStmt (k + 5) (balanceProgram .python) e.1 e.2
      (restStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) :=
  balanceReset_python_canonical_plain_guard_skip b k

#print axioms resetBinding_localValue_congr
#print axioms balanceResetMiddleEntry_localValue
#print axioms balanceResetMiddlePythonCheck_zero
#print axioms balanceResetMiddleEntry_python_seed
#print axioms balanceReset_python_canonical_plain_guard_skip

-- Enumeration does not impose the safe-integer restriction on the payload.
example (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    evalExpr (k + 5) (balanceProgram .python) e.1 e.2 (resetOverlayIterable .python) =
      .ok ⟨resetIterableMachine .python e.1 b,
        .ok (.object (resetIterableRef .python e.1))⟩ :=
  balanceReset_python_iterable_execute b k

example (lang : TargetLang) (m : TargetMachine) (b : Int) :
    objectAt (resetIterableMachine lang m b) (resetIterableRef lang m) =
      .ok (oneEntryItems lang m) ∧
    objectAt (resetIterableMachine lang m b) m.nextObject =
      .ok (oneEntryPair lang m "balance" (integerValue lang b)) :=
  resetIterableMachine_objects lang m b

#print axioms balanceReset_python_iterable_execute
#print axioms resetIterableMachine_objects

-- The range checks inspect the descriptor after the actual existing-key write.
example {lang m f ref old b}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old))
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    let updated := balanceOverlayUpdated lang m ref b
    resetCandidateBalanceRead updated f = .ok (some (integerValue lang b)) ∧
    binaryValue lang updated .ge (integerValue lang b) (integerValue lang 0) =
      .ok (.ok (.bool true)) ∧
    binaryValue lang updated .le (integerValue lang b) (integerValue lang 9007199254740991) =
      .ok (.ok (.bool true)) :=
  balanceOverlayUpdated_candidate_range hc ho hb

#print axioms balanceOverlayUpdated_candidate_range

example (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) (b : Int) (name : String) :
    localValue (resetIterableMachine lang m b) f name = localValue m f name :=
  resetIterableMachine_localValue lang m f b name

#print axioms resetIterableMachine_localValue

-- A live helper frame proves the numeric premises are attainable for every b.
-- The stored closure below retains the actual pinned _safe_integer source body.
def resetSafeHelperTestFrame : TargetFrame :=
  ⟨"safe-helper-test", [], [("value", 0)], [], none, .normal⟩

def resetSafeHelperTestClosure : TargetClosure :=
  ⟨"safe-helper-test._safe_integer", [⟨"value", none⟩], [none],
    balancePythonSafeIntegerClosure.body, [], none⟩

def resetSafeHelperTestMachine (b : Int) : TargetMachine :=
  { TargetMachine.empty with
    objects := [(1, { literalObject .python TargetMachine.empty with
      own := [("isfinite", ⟨some (.builtin .isFinite), none, none, true, true, true⟩)] })],
    closures := [(0, resetSafeHelperTestClosure)],
    cells := [(0, integerValue .python b), (1, .builtin .type), (2, .builtin .int),
      (3, .builtin .float), (4, .builtin .abs), (5, integerValue .python 9007199254740991),
      (6, .object 1), (7, .closure 0)],
    globals := [("type", 1), ("int", 2), ("float", 3), ("abs", 4), ("_MAX_INTEGER", 5),
      ("math", 6), ("_safe_integer", 7)], nextCell := 8, nextObject := 2, nextClosure := 1 }

def resetSafeHelperTest_physical (b : Int) :
    ResetPythonSafePhysical (resetSafeHelperTestMachine b) resetSafeHelperTestFrame b :=
  ⟨1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def resetSafeHelperTest_call_physical (b : Int) :
    let e := resetPythonSafeCallEntry (resetSafeHelperTestMachine b) resetSafeHelperTestClosure b
    ResetPythonSafePhysical e.1 e.2 b :=
  ⟨1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    execStmt 11 (balanceProgram .python) (resetSafeHelperTestMachine b) resetSafeHelperTestFrame
      balancePythonSafeIntegerClosure.body =
        .ok ⟨resetSafeTupleMachine (resetSafeHelperTestMachine b), resetSafeHelperTestFrame,
          .returned (.bool true)⟩ :=
  balancePythonSafeInteger_body_execute (resetSafeHelperTest_physical b) hb

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr 12 (balanceProgram .python) (resetSafeHelperTestMachine b) resetSafeHelperTestFrame
      resetPythonSafeCall =
        .ok ⟨resetSafeTupleMachine
          (resetPythonSafeCallEntry (resetSafeHelperTestMachine b) resetSafeHelperTestClosure b).1,
          .ok (.bool true)⟩ :=
  balanceReset_safe_integer_call_execute rfl rfl rfl rfl rfl
    (resetSafeHelperTest_call_physical b) hb

-- Acceptance of negative safe integers here is not constructor bounds success.
example :
    execStmt 11 (balanceProgram .python) (resetSafeHelperTestMachine (-9007199254740991))
      resetSafeHelperTestFrame balancePythonSafeIntegerClosure.body =
        .ok ⟨resetSafeTupleMachine (resetSafeHelperTestMachine (-9007199254740991)),
          resetSafeHelperTestFrame, .returned (.bool true)⟩ :=
  balancePythonSafeInteger_body_execute (resetSafeHelperTest_physical _) (by decide)

example :
    execStmt 11 (balanceProgram .python) (resetSafeHelperTestMachine 9007199254740991)
      resetSafeHelperTestFrame balancePythonSafeIntegerClosure.body =
        .ok ⟨resetSafeTupleMachine (resetSafeHelperTestMachine 9007199254740991),
          resetSafeHelperTestFrame, .returned (.bool true)⟩ :=
  balancePythonSafeInteger_body_execute (resetSafeHelperTest_physical _) (by decide)

#print axioms evalTupleTwo_eq
#print axioms resetSafeTuple_execute
#print axioms balanceReset_safe_integer_execute
#print axioms balancePythonSafeInteger_body_shape
#print axioms balancePythonSafeInteger_body_execute
#print axioms balanceReset_safe_integer_call_execute

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr 8 (balanceProgram .python) (resetSafeHelperTestMachine b) resetSafeHelperTestFrame
      (.andThen (.andThen resetPythonSafeFinite resetPythonSafeIntegral) resetPythonSafeBound) =
        .ok ⟨resetSafeHelperTestMachine b, .ok (.bool true)⟩ :=
  balanceReset_safe_integer_numeric_execute rfl rfl rfl rfl rfl rfl hb

#print axioms balanceReset_safe_integer_numeric_execute

-- The canonical candidate read is universal; the following actual method-call
-- regressions are deliberately closed at zero, including the fixed Pratt path.
example (lang : TargetLang) (b : Int) :
    resetCandidateBalanceRead (balanceResetUpdatedCandidateEntry lang b).1
      (balanceResetUpdatedCandidateEntry lang b).2 = .ok (some (integerValue lang b)) :=
  balanceResetUpdatedCandidateEntry_read lang b

example (lang : TargetLang) (invariant : Bool) :
    let e := balanceResetUpdatedCandidateEntry lang 0
    resetHelperSuccessCheck lang
      (evalExpr 100 (balanceProgram lang) e.1 e.2
        (if invariant then resetInvariantCall lang else resetBoundsCall lang)) :=
  balanceReset_helpers_zero_check lang invariant

example (lang : TargetLang) (invariant : Bool) :
    let e := balanceResetUpdatedCandidateEntry lang 0
    ∃ m, evalExpr 100 (balanceProgram lang) e.1 e.2
      (if invariant then resetInvariantCall lang else resetBoundsCall lang) =
        .ok ⟨m, .ok (if lang == .ts then .undefined else .null)⟩ :=
  resetHelperSuccessCheck_sound (balanceReset_helpers_zero_check lang invariant)

example {lang b} (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    let e := balanceResetUpdatedCandidateEntry lang b
    resetCandidateBalanceRead e.1 e.2 = .ok (some (integerValue lang b)) ∧
    binaryValue lang e.1 .ge (integerValue lang b) (integerValue lang 0) = .ok (.ok (.bool true)) ∧
    binaryValue lang e.1 .le (integerValue lang b) (integerValue lang 9007199254740991) =
      .ok (.ok (.bool true)) :=
  balanceResetUpdatedCandidateEntry_range hb

#print axioms balanceResetMiddleEntry_candidate_object
#print axioms balanceResetMiddleEntry_candidate_read
#print axioms balanceResetUpdatedCandidateEntry_read
#print axioms balanceResetUpdatedCandidateEntry_range
#print axioms balanceReset_helpers_zero_check
#print axioms resetHelperSuccessCheck_sound

-- A live frozen context table and the actual source-selected helper body.
-- These all-safe body regressions are separate from canonical constructor execution.
def resetPythonBodyTestMachine (b : Int) : TargetMachine :=
  { resetSafeHelperTestMachine b with
    objects := [(2, { literalObject .python TargetMachine.empty with
        own := [("context", ⟨some (.object 3), none, none, true, true, true⟩)] }),
      (3, ⟨.mappingProxy, none,
        [("balance", ⟨some (.object 4), none, none, true, true, true⟩)], [], [], true, false⟩),
      (4, ⟨.mappingProxy, none,
        [("type", ⟨some (.string "integer"), none, none, true, true, true⟩)], [], [], true, false⟩),
      (5, balanceHeapObject .python TargetMachine.empty 100)] ++ (resetSafeHelperTestMachine b).objects,
    cells := [(8, .string "balance"), (9, .builtin .strType), (10, .object 2), (11, .object 5)] ++
      (resetSafeHelperTestMachine b).cells,
    globals := [("str", 9), ("_WORLD", 10), ("candidate", 11)] ++ (resetSafeHelperTestMachine b).globals,
    nextCell := 12, nextObject := 6 }

def resetPythonBodyTestFrame : TargetFrame :=
  { resetSafeHelperTestFrame with locals := [("name", 8), ("value", 0)] }

def resetPythonBodyTestTyped (b : Int) : TargetMachine :=
  (allocObject (resetPythonBodyTestMachine b) (literalObject .python (resetPythonBodyTestMachine b))).1

def resetPythonBodyTestAfterHelper (b : Int) : TargetMachine :=
  resetSafeTupleMachine (resetPythonSafeCallEntry (resetPythonBodyTestTyped b) resetSafeHelperTestClosure b).1

-- The final machine includes the default-dict, argument-cell and tuple allocations.
theorem resetPythonBodyTest_execute (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    execStmt (k + 20) (balanceProgram .python) (resetPythonBodyTestMachine b) resetPythonBodyTestFrame
      (resetLoopBody (balanceResetOverlayLoop .python)) =
        .ok ⟨balanceOverlayUpdated .python (resetPythonBodyTestAfterHelper b) 5 b,
          resetPythonBodyTestFrame, .normal⟩ := by
  apply balanceReset_python_overlay_body_safe (typed := resetPythonBodyTestTyped b)
    (context := 3) (object := ⟨.mappingProxy, none,
        [("balance", ⟨some (.object 4), none, none, true, true, true⟩)], [], [], true, false⟩)
    (helper := 0) (closure := resetSafeHelperTestClosure)
  · rfl
  · rfl
  · rfl
  · simp only [evalExpr, Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang]; rfl
  · rfl
  · exact .inr rfl
  · rfl
  · simp only [resetPythonOverlayGuardType, evalExpr, evalArgValues, evalObjectFields,
      Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang]; rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [resetPythonOverlayStringTest, evalExpr, Bind.bind, Except.bind,
      Pure.pure, Except.pure, balanceProgram_lang]; rfl
  · rfl
  · exact hb

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    resetOverlaySuccessCheck .python b
      (execStmt 20 (balanceProgram .python) (resetPythonBodyTestMachine b) resetPythonBodyTestFrame
        (resetLoopBody (balanceResetOverlayLoop .python))) := by
  rw [resetPythonBodyTest_execute b hb 0]
  unfold resetOverlaySuccessCheck
  simp only [Except.toOption, Option.map, Option.some.injEq, Prod.mk.injEq]
  exact ⟨True.intro, balanceOverlayUpdated_candidate_read rfl rfl⟩

example : (resetPythonBodyTestAfterHelper 0).nextObject = 8 ∧
    (resetPythonBodyTestAfterHelper 0).nextCell = 13 := ⟨rfl, rfl⟩

#print axioms balanceReset_python_known_key_proxy_execute
#print axioms balanceReset_python_overlay_body_shape
#print axioms balanceReset_python_overlay_body_safe
#print axioms resetPythonBodyTest_execute

-- Run list(dict.items(ctx)) and the one-entry loop, including fresh Python
-- bindings, the helper's allocations and the final candidate descriptor.
def resetPythonLoopTestMachine (b : Int) : TargetMachine :=
  { resetPythonBodyTestMachine b with
    objects := (6, balanceHeapObject .python TargetMachine.empty b) :: (resetPythonBodyTestMachine b).objects,
    cells := [(12, .object 6), (13, .builtin .dict), (14, .builtin .list)] ++
      (resetPythonBodyTestMachine b).cells,
    globals := [("ctx", 12), ("dict", 13), ("list", 14)] ++ (resetPythonBodyTestMachine b).globals,
    nextCell := 15, nextObject := 7 }

def resetPythonLoopTestFrame : TargetFrame :=
  { resetPythonBodyTestFrame with locals := [] }

def resetPythonLoopTestBound (b : Int) : TargetMachine × TargetFrame :=
  resetOverlayPairBinding .python (resetIterableMachine .python (resetPythonLoopTestMachine b) b)
    resetPythonLoopTestFrame (integerValue .python b)

def resetPythonLoopTestTyped (b : Int) : TargetMachine :=
  (allocObject (resetPythonLoopTestBound b).1 (literalObject .python (resetPythonLoopTestBound b).1)).1

def resetPythonLoopTestAfterHelper (b : Int) : TargetMachine :=
  resetSafeTupleMachine (resetPythonSafeCallEntry (resetPythonLoopTestTyped b) resetSafeHelperTestClosure b).1

theorem resetPythonLoopTest_execute (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    execStmt (k + 22) (balanceProgram .python) (resetPythonLoopTestMachine b) resetPythonLoopTestFrame
      (balanceResetOverlayLoop .python) =
        .ok ⟨balanceOverlayUpdated .python (resetPythonLoopTestAfterHelper b) 5 b,
          (resetPythonLoopTestBound b).2, .normal⟩ := by
  have objects := resetIterableMachine_objects .python (resetPythonLoopTestMachine b) b
  apply balanceReset_overlay_loop_execute (k := k + 19)
    (list := oneEntryItems .python (resetPythonLoopTestMachine b))
    (pair := oneEntryPair .python (resetPythonLoopTestMachine b) "balance" (integerValue .python b))
    (pairRef := (resetPythonLoopTestMachine b).nextObject) (value := integerValue .python b)
  · exact balanceReset_python_iterable_of_seed rfl rfl rfl rfl rfl
  · exact objects.1
  · rfl
  · rfl
  · exact objects.2
  · rfl
  · intro _; rfl
  · intro _; rfl
  · apply balanceReset_python_overlay_body_safe (typed := resetPythonLoopTestTyped b)
      (context := 3) (object := ⟨.mappingProxy, none,
        [("balance", ⟨some (.object 4), none, none, true, true, true⟩)], [], [], true, false⟩)
      (helper := 0) (closure := resetSafeHelperTestClosure)
    · exact (resetOverlayPairBinding_reads _ _ _ _).1
    · rfl
    · rfl
    · simp only [evalExpr, Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang]; rfl
    · rfl
    · exact .inr rfl
    · rfl
    · simp only [resetPythonOverlayGuardType, evalExpr, evalArgValues, evalObjectFields,
        Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang]; rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ⟨1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [resetPythonOverlayStringTest, evalExpr, Bind.bind, Except.bind,
        Pure.pure, Except.pure, balanceProgram_lang]; rfl
    · rfl
    · exact hb

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) :
    resetOverlaySuccessCheck .python b
      (execStmt 22 (balanceProgram .python) (resetPythonLoopTestMachine b) resetPythonLoopTestFrame
        (balanceResetOverlayLoop .python)) := by
  rw [resetPythonLoopTest_execute b hb 0]
  unfold resetOverlaySuccessCheck
  simp only [Except.toOption, Option.map, Option.some.injEq, Prod.mk.injEq]
  exact ⟨True.intro, balanceOverlayUpdated_candidate_read rfl rfl⟩

example : (resetPythonLoopTestAfterHelper 0).nextObject = 12 ∧
    (resetPythonLoopTestAfterHelper 0).nextCell = 18 := ⟨rfl, rfl⟩

#print axioms resetPythonLoopTest_execute

-- The fixed canonical environment is independent of the supplied descriptor.
example (b : Int) :
    localValue (balanceResetPythonOverlayBound b).1 (balanceResetPythonOverlayBound b).2 "type" =
      .ok (.builtin .type) :=
  balanceReset_python_canonical_overlay_environment b (entry := ("type", 0, .builtin .type)) (by decide)

example (b : Int) :
    localValue (balanceResetPythonOverlayBound b).1 (balanceResetPythonOverlayBound b).2 "_safe_integer" =
      .ok (.closure 4) :=
  balanceReset_python_canonical_overlay_environment b (entry := ("_safe_integer", 84, .closure 4)) (by decide)

-- The real get/get guard eagerly allocates its default dict, even on a hit.
theorem resetPythonBodyTest_guard_type_execute (b : Int) (k : Nat) :
    evalExpr (k + 8) (balanceProgram .python) (resetPythonBodyTestMachine b) resetPythonBodyTestFrame
      resetPythonOverlayGuardType = .ok ⟨resetPythonBodyTestTyped b, .ok (.bool false)⟩ := by
  apply resetPythonOverlayGuardType_execute (world := 2) (context := 3) (definition := 4)
    (ctx := ⟨.mappingProxy, none,
      [("balance", ⟨some (.object 4), none, none, true, true, true⟩)], [], [], true, false⟩)
    (defn := ⟨.mappingProxy, none,
      [("type", ⟨some (.string "integer"), none, none, true, true, true⟩)], [], [], true, false⟩)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (by decide : (3 : Nat) ≠ 1)
  · exact (by decide : (3 : Nat) ≠ 0)
  · exact (by decide : (4 : Nat) ≠ 1)
  · exact (by decide : (4 : Nat) ≠ 0)
  · exact (by decide : (3 : Nat) ≠ 6)
  · exact (by decide : (4 : Nat) ≠ 6)

#print axioms balanceReset_python_canonical_overlay_environment
#print axioms resetPythonOverlayGuardType_execute
#print axioms resetPythonOverlayStringTest_execute
#print axioms resetPythonBodyTest_guard_type_execute

-- A changed type definition cannot inherit the integer-table conclusion.
def resetPythonBodyTestWrongTypeMachine (b : Int) : TargetMachine :=
  { resetPythonBodyTestMachine b with objects :=
    (4, ⟨.mappingProxy, none,
      [("type", ⟨some (.string "string"), none, none, true, true, true⟩)], [], [], true, false⟩) ::
    (resetPythonBodyTestMachine b).objects }

example (b : Int) (k : Nat) :
    evalExpr (k + 5) (balanceProgram .python) (resetPythonBodyTestWrongTypeMachine b)
      resetPythonBodyTestFrame resetPythonOverlayStringTest =
        .ok ⟨resetPythonBodyTestWrongTypeMachine b, .ok (.bool true)⟩ := by
  simp only [resetPythonOverlayStringTest, evalExpr, Bind.bind, Except.bind,
    Pure.pure, Except.pure, balanceProgram_lang]
  rfl

-- Execute canonical Python statement 2 for every safe signed payload. The
-- real helper argument, fallback dict and tuple allocations remain in final.
example (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    execStmt (k + 25) (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 2) =
      .ok ⟨balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b,
        (balanceResetPythonOverlayBound b).2, .normal⟩ :=
  (balanceReset_python_canonical_overlay_safe b hb k).2

-- Inspect the actual candidate data after the canonical overlay, including
-- negative safe values, separately from later nonnegative bounds validation.
theorem resetPythonCanonicalOverlay_candidate_read (b : Int) :
    resetCandidateBalanceRead
      (balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b)
      (balanceResetPythonOverlayBound b).2 = .ok (some (integerValue .python b)) :=
  balanceOverlayUpdated_candidate_read
    (balanceReset_python_canonical_post_candidate b).1
    (balanceReset_python_canonical_post_candidate b).2

example :
    resetCandidateBalanceRead
      (balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper (-9007199254740991)) 79 (-9007199254740991))
      (balanceResetPythonOverlayBound (-9007199254740991)).2 =
        .ok (some (integerValue .python (-9007199254740991))) :=
  resetPythonCanonicalOverlay_candidate_read (-9007199254740991)

-- Canonical TS Array/nodeTypes reads discharge the first supplied-seed guard;
-- its remaining prototype/descriptor-copy continuation is still explicit.
example (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 7) (balanceProgram .ts) e.1 e.2 (ifNoStmt (balanceResetMiddleStmt .ts 2)) =
      execStmt (k + 6) (balanceProgram .ts) e.1 e.2
        (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) :=
  balanceReset_ts_canonical_plain_guard_skip b k

#print axioms balanceReset_python_canonical_safe_physical
#print axioms balanceReset_python_canonical_helper_closure
#print axioms balanceReset_python_canonical_overlay_safe
#print axioms resetPythonCanonicalOverlay_candidate_read
#print axioms balanceReset_ts_canonical_plain_guard_skip

example :
    let b : Int := -9007199254740991
    let e := balanceResetMiddleEntry .python b
    execStmt 25 (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 2) =
      .ok ⟨balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b,
        (balanceResetPythonOverlayBound b).2, .normal⟩ :=
  (balanceReset_python_canonical_overlay_safe (-9007199254740991) (by decide) 0).2

-- Bounded canonical overlay output feeds the actual primitive bounds checks.
example (b : Int) (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    let final := balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b
    let ff := (balanceResetPythonOverlayBound b).2
    execStmt (k + 25) (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 2) =
      .ok ⟨final, ff, .normal⟩ ∧
    resetCandidateBalanceRead final ff = .ok (some (integerValue .python b)) ∧
    binaryValue .python final .lt (integerValue .python b) (integerValue .python 0) =
      .ok (.ok (.bool false)) ∧
    binaryValue .python final .gt (integerValue .python b) (integerValue .python 9007199254740991) =
      .ok (.ok (.bool false)) :=
  balanceReset_python_canonical_overlay_bounded b hb k

example (lang : TargetLang) (m : TargetMachine) :
    binaryValue lang m .lt (integerValue lang (-1)) (integerValue lang 0) =
      .ok (.ok (.bool true)) ∧
    binaryValue lang m .gt (integerValue lang 9007199254740992)
      (integerValue lang 9007199254740991) = .ok (.ok (.bool true)) := by
  cases lang <;> exact ⟨rfl, rfl⟩

#print axioms resetBoundsCall_eq_body
#print axioms resetInvariantCall_eq_closure
#print axioms balanceReset_validation_bind_skip
#print axioms balanceReset_python_canonical_overlay_bounded

-- The actual TS reset separates supplied-seed descriptor copying (node 2)
-- from the entries overlay (node 3).
example (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    let copied := balanceResetTsDescriptorEntry b
    execStmt (k + 26) (balanceProgram .ts) e.1 e.2 (balanceResetMiddleStmt .ts 2) =
      .ok ⟨copied.1, copied.2, .normal⟩ :=
  balanceReset_ts_canonical_descriptor_copy_safe b k

example (b : Int) (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 27) (balanceProgram .ts) e.1 e.2
      (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts)) =
      .ok ⟨balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b,
        (balanceResetTsDescriptorEntry b).2, .normal⟩ :=
  balanceReset_ts_canonical_overlay_safe b hb k

example (b : Int) :
    resetCandidateBalanceRead
      (balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b)
      (balanceResetTsDescriptorEntry b).2 = .ok (some (integerValue .ts b)) :=
  balanceReset_ts_canonical_overlay_candidate_read b

example :
    let b : Int := -9007199254740991
    let e := balanceResetMiddleEntry .ts b
    execStmt 27 (balanceProgram .ts) e.1 e.2
      (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts)) =
      .ok ⟨balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b,
        (balanceResetTsDescriptorEntry b).2, .normal⟩ :=
  balanceReset_ts_canonical_overlay_safe (-9007199254740991) (by decide) 0

#print axioms balanceReset_ts_canonical_descriptor_copy_safe
#print axioms balanceReset_ts_canonical_overlay_safe
#print axioms balanceReset_ts_canonical_overlay_candidate_read

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
