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
