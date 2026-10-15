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
