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
