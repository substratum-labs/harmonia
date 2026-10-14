import Harmonia.Applications.Kadmos.Generated.BalancePrograms
import Harmonia.Applications.Kadmos.Generated.TargetSimulation
import Harmonia.Applications.Kadmos.Generated.TargetObservation
import Harmonia.Applications.Kadmos.Generated.TargetCertificate

namespace Harmonia.Applications.Kadmos.Generated

/-- Fixed seed-independent preparation of the actual admitted BALANCE AST.
    The fallback is excluded by `balancePreparation_success`. -/
def balancePreparation (lang : TargetLang) : TargetMachine × TargetFrame :=
  (targetPrepareConstructor 100 (balanceProgram lang)).toOption.getD
    (TargetMachine.empty, ⟨"module", [], [], [], none, .normal⟩)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balancePreparation_total (lang : TargetLang) :
    (targetPrepareConstructor 100 (balanceProgram lang)).toOption.isSome = true := by
  cases lang with
  | ts =>
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    decide +kernel
  | python =>
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    decide +kernel

/-- Closed kernel preparation is lifted to an exact executable equality;
    there is no symbolic input in the computation certified above. -/
theorem balancePreparation_success (lang : TargetLang) :
    targetPrepareConstructor 100 (balanceProgram lang) = .ok (balancePreparation lang) := by
  have h := balancePreparation_total lang
  unfold balancePreparation
  cases he : targetPrepareConstructor 100 (balanceProgram lang) with
  | error e => simp [he, Except.toOption] at h
  | ok prepared => rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- The executed fixed prefix has live unique heap addresses and captures.
    This is the physical heap check, not a canonical-globals assumption. -/
theorem balancePreparation_heapWF (lang : TargetLang) :
    HeapWF lang (balancePreparation lang).1 := by
  cases lang with
  | ts =>
    unfold balancePreparation
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    decide +kernel
  | python =>
    unfold balancePreparation
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- The retained module frame refers to the preparation's live cells. -/
theorem balancePreparation_frameWF (lang : TargetLang) :
    FrameWF (balancePreparation lang).1 (balancePreparation lang).2 := by
  unfold FrameWF
  cases lang with
  | ts =>
    unfold balancePreparation
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    decide +kernel
  | python =>
    unfold balancePreparation
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceProgram_lang (lang : TargetLang) : (balanceProgram lang).lang = lang := by
  cases lang with
  | ts =>
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    rfl
  | python =>
    rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
    rfl

/-- The canonical constructor begins at the certified fixed preparation.
    Allocation and actual constructor/helper execution remain on the RHS. -/
theorem targetConstruct_balance_prepared (lang : TargetLang) (b : Int) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) =
      targetConstructFromPrepared 100 (balanceProgram lang)
        (balancePreparation lang).1 (balancePreparation lang).2
        (canonicalBalanceSeed lang b) := by
  apply targetConstructWithFuel_of_prepared
  · simp only [canonicalBalanceSeed, balanceProgram_lang]
  · exact balancePreparation_success lang

/-- Convert the source safe-signed interval to the host's absolute-value
    check. This is symbolic in the amount and uses no enumeration. -/
theorem signed_natAbs {n : Int}
    (h : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
    n.natAbs ≤ 9007199254740991 := by
  cases n <;> simp [Harmonia.Applications.Kadmos.S, Int.natAbs] at * <;> omega

theorem balance_natAbs {b : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    b.natAbs ≤ 9007199254740991 := by
  apply signed_natAbs
  constructor
  · have hs : 0 ≤ Harmonia.Applications.Kadmos.S := by decide
    omega
  · exact hb.2

/-- The accepted effect's intermediate lies in the bounded balance domain. -/
theorem balance_accept_difference_bounds {b n : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : 0 < n ∧ n ≤ b) :
    -Harmonia.Applications.Kadmos.S ≤ b - n ∧
      b - n ≤ Harmonia.Applications.Kadmos.S := by
  have hs : 0 ≤ Harmonia.Applications.Kadmos.S := by decide
  constructor <;> omega

/-- Bounds rejection evaluates a safe negative intermediate, only after
    guard success. No subtraction bound is assumed on the guard-reject path. -/
theorem balance_reject_difference_bounds {b n : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : b < n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
    -Harmonia.Applications.Kadmos.S ≤ b - n ∧
      b - n ≤ Harmonia.Applications.Kadmos.S := by
  constructor <;> omega

/-- Canonical own-data descriptor used by constructor copies in both models. -/
def balanceDataDescriptor (lang : TargetLang) (b : Int) : Descriptor :=
  ⟨some (integerValue lang b), none, none, true, true, true⟩

/-- Relational container shapes refer to the machine's live prototype, rather
    than a particular allocation number. No constructor execution is encoded. -/
def balanceHeapObject (lang : TargetLang) (m : TargetMachine) (b : Int) : HeapObject :=
  ⟨(if lang == .ts then .jsOrdinary else .pythonDict),
    (if lang == .ts then some m.objectPrototype else none),
    [("balance", balanceDataDescriptor lang b)], [], [], false, false⟩

def emptyBalanceHistory (lang : TargetLang) (m : TargetMachine) : HeapObject :=
  ⟨(if lang == .ts then .jsArray else .pythonList),
    (if lang == .ts then some m.objectPrototype else none),
    [], [], [], false, false⟩

/-- Every bounded balance reaches the actual constructor call with a
    canonical allocated seed, after the fixed module/class prefix. -/
theorem targetConstruct_balance_call (lang : TargetLang) {b : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) =
      targetConstructorCall 100 (balanceProgram lang)
        (allocObject (balancePreparation lang).1
          (balanceHeapObject lang (balancePreparation lang).1 b)).1
        (balancePreparation lang).2
        (.object (balancePreparation lang).1.nextObject) := by
  rw [targetConstruct_balance_prepared]
  apply targetConstructFromPrepared_of_seed
  exact allocateSeed_balance (balance_natAbs hb)

/-- These names select actual stored source methods, not ideal constructor bodies. -/
def balanceConstructorName (lang : TargetLang) : String :=
  if lang == .ts then "constructor" else "__init__"

def balanceConstructorParam (lang : TargetLang) : String :=
  if lang == .ts then "initialContext" else "initial_context"

/-- Read constructor provenance from the physically prepared method table. -/
def balanceConstructorLookup (lang : TargetLang) : Option (ClosureRef × TargetClosure) := do
  let ref ← (balancePreparation lang).1.classMethods.lookup (balanceConstructorName lang)
  let closure ← (closureAt (balancePreparation lang).1 ref).toOption
  pure (ref, closure)

/-- The fallback is excluded by the closed preparation lookup certificate. -/
def balanceStoredConstructor (lang : TargetLang) : ClosureRef × TargetClosure :=
  (balanceConstructorLookup lang).getD (0, ⟨"", [], [], .empty, [], none⟩)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceConstructorLookup_total (lang : TargetLang) :
    (balanceConstructorLookup lang).isSome = true := by
  cases lang with
  | ts =>
      unfold balanceConstructorLookup balanceConstructorName balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceConstructorLookup balanceConstructorName balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- Extract exact method-table and closure-store equations without choice. -/
theorem balanceStoredConstructor_lookup (lang : TargetLang) :
    (balancePreparation lang).1.classMethods.lookup (balanceConstructorName lang) =
      some (balanceStoredConstructor lang).1 ∧
    closureAt (balancePreparation lang).1 (balanceStoredConstructor lang).1 =
      .ok (balanceStoredConstructor lang).2 := by
  have ht := balanceConstructorLookup_total lang
  unfold balanceConstructorLookup at ht
  unfold balanceStoredConstructor balanceConstructorLookup
  cases hm : (balancePreparation lang).1.classMethods.lookup (balanceConstructorName lang) with
  | none => simp [hm] at ht
  | some ref =>
      cases hc : closureAt (balancePreparation lang).1 ref with
      | error e => simp [hm, hc, Except.toOption] at ht
      | ok closure => simp [hm, hc, Except.toOption]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Both actual constructors take one supplied seed parameter and are looked
    up as methods, rather than checker data fields. Their bodies stay stored. -/
theorem balanceStoredConstructor_shape (lang : TargetLang) :
    readCheckerField (balancePreparation lang).1 (balanceConstructorName lang) =
      .error (.unboundLocal (balanceConstructorName lang)) ∧
    (balanceStoredConstructor lang).2.params =
      [⟨balanceConstructorParam lang, some .null⟩] ∧
    (balanceStoredConstructor lang).2.qualifiedName =
      "WorldChecker." ++ balanceConstructorName lang := by
  cases lang with
  | ts =>
      unfold balanceStoredConstructor balanceConstructorLookup balanceConstructorName
        balanceConstructorParam balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStoredConstructor balanceConstructorLookup balanceConstructorName
        balanceConstructorParam balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- Physical caller allocation for the canonical seed, before method access. -/
def balanceConstructorArgumentEntry (lang : TargetLang) (b : Int) :
    TargetMachine × TargetFrame :=
  let prepared := balancePreparation lang
  let seeded := (allocObject prepared.1 (balanceHeapObject lang prepared.1 b)).1
  let withArgument := (allocCell seeded (.object prepared.1.nextObject) true).1
  (withArgument, ⟨"construct", [], [("initialContext", seeded.nextCell)],
    prepared.2.locals, some withArgument.checkerRef, .normal⟩)

/-- Method access allocates this receiver-bound source closure. -/
def balanceConstructorBoundEntry (lang : TargetLang) (b : Int) :
    TargetMachine × ClosureRef :=
  let caller := (balanceConstructorArgumentEntry lang b).1
  allocClosure caller { (balanceStoredConstructor lang).2 with receiver := some caller.checkerRef }

/-- One fresh supplied-parameter cell, with the actual stored captures/body. -/
def balanceConstructorBodyEntry (lang : TargetLang) (b : Int) :
    TargetMachine × TargetFrame :=
  let bound := (balanceConstructorBoundEntry lang b).1
  let method := { (balanceStoredConstructor lang).2 with receiver := some bound.checkerRef }
  ((allocCell bound (.object (balancePreparation lang).1.nextObject) true).1,
    { closureFrame method with locals := [(balanceConstructorParam lang, bound.nextCell)] })

/-- Canonical receiver dispatch and argument reads have depth one. The parsed
    constructor body is retained as the remaining executable obligation. -/
theorem balanceConstructorCall_eq_body (lang : TargetLang) (b : Int) :
    evalExpr 100 (balanceProgram lang)
      (balanceConstructorArgumentEntry lang b).1 (balanceConstructorArgumentEntry lang b).2
      (.call (.property (.local (if lang == .ts then "this" else "self"))
        (balanceConstructorName lang)) (.sequence (.local "initialContext") .empty)) = (do
      let body ← execStmt 99 (balanceProgram lang)
        (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
        (balanceStoredConstructor lang).2.body
      closureResult lang body) := by
  let caller := (balanceConstructorArgumentEntry lang b).1
  let frame := (balanceConstructorArgumentEntry lang b).2
  let bound := (balanceConstructorBoundEntry lang b).1
  let method := { (balanceStoredConstructor lang).2 with receiver := some caller.checkerRef }
  have hLookup := balanceStoredConstructor_lookup lang
  have hShape := balanceStoredConstructor_shape lang
  have hr : localValue caller frame (if lang == .ts then "this" else "self") =
      .ok (.object caller.checkerRef) := by
    cases lang <;> rfl
  have hf : readCheckerField caller (balanceConstructorName lang) =
      .error (.unboundLocal (balanceConstructorName lang)) := hShape.1
  have hm : caller.classMethods.lookup (balanceConstructorName lang) =
      some (balanceStoredConstructor lang).1 := hLookup.1
  have hc : closureAt caller (balanceStoredConstructor lang).1 =
      .ok (balanceStoredConstructor lang).2 := hLookup.2
  have hRead : readPropertyValue (balanceProgram lang).lang caller
      (.object caller.checkerRef) (balanceConstructorName lang) =
      .ok ⟨bound, .ok (.closure caller.nextClosure)⟩ := by
    rw [balanceProgram_lang]
    exact readCheckerMethod_bound hf hm hc
  have he : DepthDerivesExpr (balanceProgram lang) caller frame
      (.property (.local (if lang == .ts then "this" else "self")) (balanceConstructorName lang))
      ⟨bound, .ok (.closure caller.nextClosure)⟩ 1 := .property (.localRead hr) hRead
  have hv : localValue bound frame "initialContext" =
      .ok (.object (balancePreparation lang).1.nextObject) := by
    simp [bound, frame, balanceConstructorBoundEntry, balanceConstructorArgumentEntry,
      localValue, readCell, allocClosure, allocCell, List.lookup]
  have ha : DepthDerivesArgs (balanceProgram lang) bound frame
      (.sequence (.local "initialContext") .empty)
      ⟨bound, .ok [.object (balancePreparation lang).1.nextObject]⟩ 1 :=
    .cons (.localRead hv) .empty
  have hStored : closureAt bound caller.nextClosure = .ok method := by
    simp [bound, caller, method, balanceConstructorBoundEntry, closureAt, allocClosure, List.lookup]
  have hp : DepthBindsProvided (balanceProgram lang) bound (closureFrame method)
      method.params method.pythonDefaults [.object (balancePreparation lang).1.nextObject]
      (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2 1 := by
    change DepthBindsProvided (balanceProgram lang) bound (closureFrame method)
      (balanceStoredConstructor lang).2.params method.pythonDefaults _ _ _ 1
    rw [hShape.2.1]
    exact .cons (by simp) .empty
  have h := evalStoredCall_eq he ha hStored hp (k := 99) (by decide) (by decide) (by decide)
  simpa only [balanceProgram_lang] using h

/-- Every bounded seed reaches the actual parsed constructor body at depth 99.
    No premise assumes body success and no post-construction representation
    is concluded until the remaining reset/helper/body execution is proved. -/
theorem targetConstruct_balance_body (lang : TargetLang) {b : Int}
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S) :
    targetConstruct (balanceProgram lang) (canonicalBalanceSeed lang b) = (do
      let body ← execStmt 99 (balanceProgram lang)
        (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
        (balanceStoredConstructor lang).2.body
      let result ← closureResult lang body
      match result.result with
      | .ok _ => pure result.machine
      | .error e => throw (.sourceException e)) := by
  rw [targetConstruct_balance_call lang hb]
  unfold targetConstructorCall
  simp only [balanceProgram_lang]
  change (do
    let result ← evalExpr 100 (balanceProgram lang)
      (balanceConstructorArgumentEntry lang b).1 (balanceConstructorArgumentEntry lang b).2
      (.call (.property (.local (if lang == TargetLang.ts then "this" else "self"))
        (balanceConstructorName lang)) (.sequence (.local "initialContext") .empty))
    match result.result with
    | .ok _ => pure result.machine
    | .error e => throw (TargetError.sourceException e) : Except TargetError TargetMachine) = _
  rw [balanceConstructorCall_eq_body]
  cases hBody : execStmt 99 (balanceProgram lang)
      (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (balanceStoredConstructor lang).2.body <;> rfl

set_option maxRecDepth 4096 in
/-- One-key numeric context cloning needs host budget two, uniformly in b.
    Freshness records the physical frame; this theorem neither runs nor
    assumes correctness of a generated constructor or rollback helper. -/
theorem cloneValue_balance {lang m b ref k}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m b))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    cloneValue (k + 2) m (.object ref) =
      .ok ((allocObject m (balanceHeapObject lang m b)).1, .object m.nextObject) := by
  cases lang <;>
    simp [cloneValue, ho, balanceHeapObject, balanceDataDescriptor, integerValue,
      replaceObject_allocObject hf, Bind.bind, Pure.pure, Except.bind, Except.pure,
      List.forIn_cons, List.forIn_nil]

/-- Post-construction representation. The live context and copied seed have
    exactly one enumerable, mutable own-data field; history is empty/mutable.
    This predicate is a proof obligation, never an assumed constructor result. -/
structure BalanceRep (lang : TargetLang) (b : Int) (machine : TargetMachine) : Prop where
  heapWF : HeapWF lang machine
  ready : machine.checker.state = "Ready"
  context : objectAt machine machine.checker.context = .ok (balanceHeapObject lang machine b)
  history : objectAt machine machine.checker.history = .ok (emptyBalanceHistory lang machine)
  noUndo : machine.checker.undo = none
  idle : machine.checker.busy = false
  seed : ∃ ref, machine.checker.constructorSeed = some ref ∧
    ref ≠ machine.checker.context ∧
    objectAt machine ref = .ok (balanceHeapObject lang machine b)

/-- The representation entails the physical descriptor read, not just an
    equality of pre-normalized balance observations. -/
theorem BalanceRep.read_balance {lang b machine} (h : BalanceRep lang b machine) :
    readOwn machine machine.checker.context "balance" =
      .ok (some (balanceDataDescriptor lang b)) := by
  simp [readOwn, h.context, balanceHeapObject,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem BalanceRep.seed_read_balance {lang b machine} (h : BalanceRep lang b machine) :
    ∃ ref, machine.checker.constructorSeed = some ref ∧
      ref ≠ machine.checker.context ∧
      readOwn machine ref "balance" = .ok (some (balanceDataDescriptor lang b)) := by
  obtain ⟨ref, hRef, hCopy, hObject⟩ := h.seed
  refine ⟨ref, hRef, hCopy, ?_⟩
  simp [readOwn, hObject, balanceHeapObject,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Decidable physical representation check. This checks an actual returned
    heap; it does not construct a machine or assume evaluator termination. -/
def balanceRepCheck (lang : TargetLang) (b : Int) (m : TargetMachine) : Bool :=
  heapWFCheck lang m && decide (m.checker.state = "Ready") &&
    decide (objectAt m m.checker.context = .ok (balanceHeapObject lang m b)) &&
    decide (objectAt m m.checker.history = .ok (emptyBalanceHistory lang m)) &&
    decide (m.checker.undo = none) && decide (m.checker.busy = false) &&
    match m.checker.constructorSeed with
    | none => false
    | some ref => decide (ref ≠ m.checker.context) &&
        decide (objectAt m ref = .ok (balanceHeapObject lang m b))

theorem balanceRepCheck_sound {lang b m} (h : balanceRepCheck lang b m = true) :
    BalanceRep lang b m := by
  unfold balanceRepCheck at h
  cases hs : m.checker.constructorSeed with
  | none => simp [hs] at h
  | some ref =>
      simp only [hs, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hw, hr⟩, hc⟩, hh⟩, hu⟩, hi⟩, hn, hseed⟩ := h
      exact ⟨hw, hr, hc, hh, hu, hi, ref, hs, hn, hseed⟩

/-- A physical BalanceRep also entails successful dereferencing of context.
    No arbitrary target execution outcome appears among the premises. -/
theorem BalanceRep.context_value {lang b m} (h : BalanceRep lang b m) :
    balanceContextValue lang m m.checker.context = .ok b := by
  exact balanceContextValue_canonical h.context

/-- The representation's logical view follows from physical dereferencing,
    including the distinct copied seed. -/
theorem BalanceRep.view {lang b m} (h : BalanceRep lang b m) :
    balanceView lang m = .ok ⟨"Ready", b, [], none, b, false⟩ := by
  obtain ⟨seed, hseedRef, _, hseedObject⟩ := h.seed
  exact balanceView_constructed h.context_value
    (decodeBalanceHistory_empty h.history) hseedRef
    (balanceContextValue_canonical hseedObject) h.noUndo h.ready h.idle

/-- A finite executable-check witness can be lifted to the relational
    representation. This is not universal constructor totality. -/
theorem checkedConstructor_witness {program lang b}
    (h : (targetConstruct program (canonicalBalanceSeed lang b)).toOption.map
      (balanceRepCheck lang b) = some true) :
    ∃ m, targetConstruct program (canonicalBalanceSeed lang b) = .ok m ∧
      BalanceRep lang b m := by
  cases he : targetConstruct program (canonicalBalanceSeed lang b) with
  | error e => simp [he, Except.toOption] at h
  | ok m =>
      simp only [he, Except.toOption, Option.map, Option.some.injEq] at h
      exact ⟨m, rfl, balanceRepCheck_sound h⟩

/-- The actual prepared step closure, retained independently of BalanceRep. -/
def balanceStepLookup (lang : TargetLang) : Option (ClosureRef × TargetClosure) := do
  let ref ← (balancePreparation lang).1.classMethods.lookup "step"
  let closure ← (closureAt (balancePreparation lang).1 ref).toOption
  pure (ref, closure)

def balanceStoredStep (lang : TargetLang) : ClosureRef × TargetClosure :=
  (balanceStepLookup lang).getD (0, ⟨"", [], [], .empty, [], none⟩)

/-- Generic AST selectors preserve all actual branches and sibling nodes. -/
def firstStmt (body : TargetStmt) : TargetStmt :=
  match body with | .sequence first _ => first | _ => .empty

def restStmt (body : TargetStmt) : TargetStmt :=
  match body with | .sequence _ rest => rest | _ => .empty

def ifYesStmt (body : TargetStmt) : TargetStmt :=
  match body with | .ifThenElse _ yes _ => yes | _ => .empty

def stepBusyPrefixCheck (lang : TargetLang) (body : TargetStmt) : Bool :=
  match body with
  | .sequence (.ifThenElse cond _ no) _ =>
      cond == .property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy") && no == .empty
  | _ => false

/-- Structural inversion works on a variable AST, never by reducing a
    computed prepared heap or comparing its large body/remainder. -/
theorem stepBusyPrefixCheck_shape {lang body} (h : stepBusyPrefixCheck lang body = true) :
    body = .sequence (firstStmt body) (restStmt body) ∧
    firstStmt body = .ifThenElse
      (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (ifYesStmt (firstStmt body)) .empty := by
  cases body with
  | sequence first rest =>
      cases first with
      | ifThenElse cond yes no =>
          change ((cond == .property (.local (if lang == .ts then "this" else "self"))
            (if lang == .ts then "#busy" else "_busy")) && (no == .empty)) = true at h
          simp only [Bool.and_eq_true] at h
          have hc := (beq_iff_eq).mp h.1
          have hn := (beq_iff_eq).mp h.2
          subst cond no
          exact ⟨rfl, rfl⟩
      | _ => simp [stepBusyPrefixCheck] at h
  | _ => simp [stepBusyPrefixCheck] at h

def balanceStepBusyPrefix (lang : TargetLang) : TargetStmt :=
  firstStmt (balanceStoredStep lang).2.body

def balanceStepAfterBusy (lang : TargetLang) : TargetStmt :=
  restStmt (balanceStoredStep lang).2.body

def balanceStepBusyThrow (lang : TargetLang) : TargetStmt :=
  ifYesStmt (balanceStepBusyPrefix lang)

/-- Only the reached prefix form is reflected; actual throw/remainder ASTs
    are preserved by the generic structural selectors. -/
def stepLookupBusyPrefixCheck (lang : TargetLang)
    (found : Option (ClosureRef × TargetClosure)) : Bool :=
  match found with
  | none => false
  | some (_, closure) => stepBusyPrefixCheck lang closure.body

/-- Invert a variable lookup so closed reflection only computes the lookup once. -/
theorem stepLookupBusyPrefixCheck_shape {lang found fallback}
    (h : stepLookupBusyPrefixCheck lang found = true) :
    found.isSome = true ∧ stepBusyPrefixCheck lang (found.getD fallback).2.body = true := by
  cases found with
  | none => simp [stepLookupBusyPrefixCheck] at h
  | some value => exact ⟨rfl, h⟩

def balanceStepBusyPrefixCheck (lang : TargetLang) : Bool :=
  stepLookupBusyPrefixCheck lang (balanceStepLookup lang)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceStepBusyPrefixCheck_true (lang : TargetLang) :
    balanceStepBusyPrefixCheck lang = true := by
  cases lang with
  | ts =>
      unfold balanceStepBusyPrefixCheck balanceStepLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStepBusyPrefixCheck balanceStepLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- Exact first-statement shape of both prepared source-bound step methods.
    Structural inversion retains every node of the actual body. Constructor
    preservation of the method store remains a separate obligation. -/
theorem balanceStepBusyPrefix_shape (lang : TargetLang) :
    (balanceStepLookup lang).isSome = true ∧
    (balanceStoredStep lang).2.body =
      .sequence (balanceStepBusyPrefix lang) (balanceStepAfterBusy lang) ∧
    balanceStepBusyPrefix lang =
      .ifThenElse (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (balanceStepBusyThrow lang) .empty := by
  have h := stepLookupBusyPrefixCheck_shape
    (fallback := (0, ⟨"", [], [], .empty, [], none⟩)) (balanceStepBusyPrefixCheck_true lang)
  exact ⟨h.1, stepBusyPrefixCheck_shape h.2⟩

/-- The source step's first busy-check takes its idle branch with rank two.
    The receiver and idle bit are explicit preconditions; no source guard,
    effect, sanitizer or verdict behavior is inferred from this prefix. -/
theorem balanceStep_idle_prefix {lang m f}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    DepthDerivesStmt (balanceProgram lang) m f (balanceStepBusyPrefix lang)
      ⟨m, f, .normal⟩ 2 := by
  rw [(balanceStepBusyPrefix_shape lang).2.2]
  have hLocal : localValue m f (if lang == .ts then "this" else "self") =
      .ok (.object m.checkerRef) := by
    cases lang <;> simp [localValue, hr]
  have hRead : readPropertyValue (balanceProgram lang).lang m (.object m.checkerRef)
      (if lang == .ts then "#busy" else "_busy") = .ok ⟨m, .ok (.bool false)⟩ := by
    cases lang <;>
      simp [readPropertyValue, readCheckerField, hi, Bind.bind, Pure.pure, Except.bind, Except.pure] <;>
      rfl
  have hExpr : DepthDerivesExpr (balanceProgram lang) m f
      (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) ⟨m, .ok (.bool false)⟩ 1 :=
    .property (.localRead hLocal) hRead
  exact .ifFalse hExpr rfl .empty

/-- Safe signed amounts have an exact entry equation even for an arbitrary
    preheap. Actual method provenance and the three step branches remain
    separate obligations; this theorem concludes no successful verdict. -/
theorem targetStep_balance_entry (lang : TargetLang) (m : TargetMachine) {n : Int}
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
    targetStep (balanceProgram lang) m (canonicalDebitRequest lang n) = (do
      let result ← evalExpr 100 (balanceProgram lang)
        (debitCallEntry lang m n).1 (debitCallEntry lang m n).2 (debitCallExpression lang)
      match result.result with
      | .ok verdict => pure ⟨result.machine, verdict⟩
      | .error e => throw (.sourceException e)) :=
  targetStepWithFuel_eq_debitEntry (balanceProgram_lang lang) (signed_natAbs hn)

/-- Explicit structural template for the small constructor, including the
    Python type guard and every initialization statement before reset. -/
def balanceConstructorBodyTemplate (lang : TargetLang) : TargetStmt :=
  let receiver := TargetExpr.local (if lang == .ts then "this" else "self")
  let reset := TargetStmt.doExpr (.call (.property receiver "reset")
    (.sequence (.local (balanceConstructorParam lang)) .empty))
  let copy := if lang == .ts then
      TargetExpr.object (.objectSpread (.property receiver "#context") .empty)
    else .call (.local "dict") (.sequence (.property receiver "__context") .empty)
  let finish := TargetStmt.sequence
    (.assign (.property receiver (if lang == .ts then "#constructorSeed" else "__constructor_seed")) copy)
    .empty
  if lang == .ts then .sequence reset finish else
    .sequence
      (.ifThenElse (.andThen
        (.binary .isNotIdentity (.local "initial_context") .null)
        (.binary .isNotIdentity
          (.call (.local "type") (.sequence (.local "initial_context") .empty))
          (.local "dict")))
        (.sequence (.throwValue (.call (.local "ValueError")
          (.sequence (.string "INVALID_BOUNDS: initial context must be a dict") .empty))) .empty)
        .empty)
      (.sequence (.assign (.property receiver "__constructor_seed") .null)
      (.sequence (.assign (.property receiver "__state") (.local "_INITIAL"))
      (.sequence (.assign (.property receiver "__context") (.object .empty))
      (.sequence (.assign (.property receiver "__history") (.array .empty))
      (.sequence (.assign (.property receiver "_busy") (.bool false))
      (.sequence (.assign (.property receiver "__undo") .null)
      (.sequence reset finish)))))))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Closed kernel reflection is confined to the fixed small constructor AST;
    no execution on a symbolic balance is reduced here. -/
theorem balanceConstructorBody_shape (lang : TargetLang) :
    (balanceStoredConstructor lang).2.body = balanceConstructorBodyTemplate lang := by
  cases lang with
  | ts =>
      unfold balanceStoredConstructor balanceConstructorLookup balanceConstructorName balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStoredConstructor balanceConstructorLookup balanceConstructorName balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- The TS constructor's reset statement is exposed at its exact depth 98.
    Reset success is not a premise; its error/control still selects the suffix. -/
theorem balanceConstructor_ts_reset_eq (b : Int) :
    execStmt 99 (balanceProgram .ts)
      (balanceConstructorBodyEntry .ts b).1 (balanceConstructorBodyEntry .ts b).2
      (balanceStoredConstructor .ts).2.body = (do
      let head ← execStmt 98 (balanceProgram .ts)
        (balanceConstructorBodyEntry .ts b).1 (balanceConstructorBodyEntry .ts b).2
        (.doExpr (.call (.property (.local "this") "reset")
          (.sequence (.local "initialContext") .empty)))
      match head.control with
      | .normal =>
          execStmt 98 (balanceProgram .ts) head.machine head.frame
            (restStmt (balanceConstructorBodyTemplate .ts))
      | _ => pure head) := by
  rw [balanceConstructorBody_shape]
  change execStmt (98 + 1) _ _ _ (.sequence _ _) = _
  exact execSequence_eq _ _ _ _ _ _

/-- The actual reset method in the prepared store, separate from its call
    frame and separate from its remaining generated helper execution. -/
def balanceResetLookup (lang : TargetLang) : Option (ClosureRef × TargetClosure) := do
  let ref ← (balancePreparation lang).1.classMethods.lookup "reset"
  let closure ← (closureAt (balancePreparation lang).1 ref).toOption
  pure (ref, closure)

def balanceStoredReset (lang : TargetLang) : ClosureRef × TargetClosure :=
  (balanceResetLookup lang).getD (0, ⟨"", [], [], .empty, [], none⟩)

/-- Reflect only the idle guard and busy write, retaining the actual throw
    subtree and the entire snapshot/try/helper remainder without comparison. -/
def idleEntryCheck (lang : TargetLang) (body : TargetStmt) : Bool :=
  match body with
  | .sequence (.ifThenElse cond _ .empty)
      (.sequence (.assign (.property receiver name) (.bool true)) _) =>
      let self := TargetExpr.local (if lang == .ts then "this" else "self")
      let busy := if lang == .ts then "#busy" else "_busy"
      cond == .property self busy && receiver == self && name == busy
  | _ => false

theorem idleEntryCheck_shape {lang body} (h : idleEntryCheck lang body = true) :
    body = .sequence (firstStmt body)
      (.sequence (.assign (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (.bool true)) (restStmt (restStmt body))) ∧
    firstStmt body = .ifThenElse
      (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (ifYesStmt (firstStmt body)) .empty := by
  cases body with
  | sequence first rest =>
      cases first with
      | ifThenElse cond yes no =>
          cases no <;> try simp [idleEntryCheck] at h
          cases rest with
          | sequence assignment tail =>
              cases assignment with
              | assign target value =>
                  cases target <;> try simp [idleEntryCheck] at h
                  case property receiver name =>
                    cases value <;> try simp [idleEntryCheck] at h
                    case bool enabled =>
                      cases enabled <;> try simp [idleEntryCheck] at h
                      obtain ⟨⟨hc, hr⟩, hn⟩ := h
                      subst cond receiver name
                      cases lang <;> exact ⟨rfl, rfl⟩
              | _ => simp [idleEntryCheck] at h
          | _ => simp [idleEntryCheck] at h
      | _ => simp [idleEntryCheck] at h
  | _ => simp [idleEntryCheck] at h

def lookupIdleEntryCheck (lang : TargetLang)
    (found : Option (ClosureRef × TargetClosure)) : Bool :=
  match found with
  | some (_, closure) => idleEntryCheck lang closure.body
  | none => false

theorem lookupIdleEntryCheck_shape {lang found fallback}
    (h : lookupIdleEntryCheck lang found = true) :
    found.isSome = true ∧ idleEntryCheck lang (found.getD fallback).2.body = true := by
  cases found with
  | none => simp [lookupIdleEntryCheck] at h
  | some value => exact ⟨rfl, h⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceResetIdleEntryCheck_true (lang : TargetLang) :
    lookupIdleEntryCheck lang (balanceResetLookup lang) = true := by
  cases lang with
  | ts =>
      unfold balanceResetLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceResetLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceStepIdleEntryCheck_true (lang : TargetLang) :
    lookupIdleEntryCheck lang (balanceStepLookup lang) = true := by
  cases lang with
  | ts =>
      unfold balanceStepLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStepLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- Exact reset entry shape with the source throw and later statements retained. -/
theorem balanceReset_idle_shape (lang : TargetLang) :
    (balanceResetLookup lang).isSome = true ∧
    (balanceStoredReset lang).2.body = .sequence (firstStmt (balanceStoredReset lang).2.body)
      (.sequence (.assign (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (.bool true))
        (restStmt (restStmt (balanceStoredReset lang).2.body))) ∧
    firstStmt (balanceStoredReset lang).2.body = .ifThenElse
      (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy"))
      (ifYesStmt (firstStmt (balanceStoredReset lang).2.body)) .empty := by
  have h := lookupIdleEntryCheck_shape
    (fallback := (0, ⟨"", [], [], .empty, [], none⟩)) (balanceResetIdleEntryCheck_true lang)
  exact ⟨h.1, idleEntryCheck_shape h.2⟩

/-- Exact step remainder starts by acquiring the shared busy bit. -/
theorem balanceStep_afterBusy_shape (lang : TargetLang) :
    balanceStepAfterBusy lang =
      .sequence (.assign (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (.bool true))
        (restStmt (balanceStepAfterBusy lang)) := by
  have h := lookupIdleEntryCheck_shape
    (fallback := (0, ⟨"", [], [], .empty, [], none⟩)) (balanceStepIdleEntryCheck_true lang)
  have hb := (idleEntryCheck_shape h.2).1
  have hr := congrArg restStmt hb
  exact hr

/-- Shared reset/step idle guard; the source throw is arbitrary and unreachable. -/
theorem balance_idle_guard {lang m f yes}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) :
    DepthDerivesStmt (balanceProgram lang) m f
      (.ifThenElse (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) yes .empty) ⟨m, f, .normal⟩ 2 := by
  have hLocal : localValue m f (if lang == .ts then "this" else "self") =
      .ok (.object m.checkerRef) := by
    cases lang <;> simp [localValue, hr]
  have hRead : readPropertyValue (balanceProgram lang).lang m (.object m.checkerRef)
      (if lang == .ts then "#busy" else "_busy") = .ok ⟨m, .ok (.bool false)⟩ := by
    cases lang <;>
      simp [readPropertyValue, readCheckerField, hi, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> rfl
  exact .ifFalse (.property (.localRead hLocal) hRead) rfl .empty

def balanceSetBusy (m : TargetMachine) (busy : Bool) : TargetMachine :=
  { m with checker := { m.checker with busy := busy } }

/-- The reached source property assignment changes precisely the busy bit. -/
theorem balance_busy_write {lang m f busy}
    (hr : f.receiver = some m.checkerRef) :
    DepthDerivesStmt (balanceProgram lang) m f
      (.assign (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (.bool busy))
      ⟨balanceSetBusy m busy, f, .normal⟩ 1 := by
  have hLocal : localValue m f (if lang == .ts then "this" else "self") =
      .ok (.object m.checkerRef) := by
    cases lang <;> simp [localValue, hr]
  apply DepthDerivesStmt.assignProperty (.localRead hLocal) (.bool busy)
  cases lang <;> simp [writeCheckerField, balanceSetBusy]

/-- All later reset statements remain at their exact sibling depth. This
    reaches snapshots with busy=true without assuming reset/helper success. -/
theorem balanceReset_idle_entry {lang m f k}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) (hk : 4 ≤ k) :
    execStmt (k + 1) (balanceProgram lang) m f (balanceStoredReset lang).2.body =
      execStmt (k - 1) (balanceProgram lang) (balanceSetBusy m true) f
        (restStmt (restStmt (balanceStoredReset lang).2.body)) := by
  conv => lhs; rw [(balanceReset_idle_shape lang).2.1]
  have hGuard : execStmt k (balanceProgram lang) m f
      (firstStmt (balanceStoredReset lang).2.body) = .ok ⟨m, f, .normal⟩ := by
    rw [(balanceReset_idle_shape lang).2.2]
    exact execStmt_adequate (balance_idle_guard hr hi) (by omega)
  rw [execSequence_of_normal hGuard]
  have hWrite := execStmt_adequate (balance_busy_write (lang := lang) (busy := true) hr)
    (k := k - 1) (by omega)
  have hFuel : k = (k - 1) + 1 := by omega
  conv => lhs; rw [hFuel]
  rw [execSequence_of_normal hWrite]

/-- Actual step entry likewise reaches snapshots, with both prefix edges
    removed and the complete generated remainder retained. -/
theorem balanceStep_idle_entry {lang m f k}
    (hr : f.receiver = some m.checkerRef) (hi : m.checker.busy = false) (hk : 4 ≤ k) :
    execStmt (k + 1) (balanceProgram lang) m f (balanceStoredStep lang).2.body =
      execStmt (k - 1) (balanceProgram lang) (balanceSetBusy m true) f
        (restStmt (balanceStepAfterBusy lang)) := by
  conv => lhs; rw [(balanceStepBusyPrefix_shape lang).2.1]
  conv => lhs; rw [balanceStep_afterBusy_shape]
  rw [execSequence_of_normal (execStmt_adequate (balanceStep_idle_prefix hr hi) (by omega))]
  have hWrite := execStmt_adequate (balance_busy_write (lang := lang) (busy := true) hr)
    (k := k - 1) (by omega)
  have hFuel : k = (k - 1) + 1 := by omega
  conv => lhs; rw [hFuel]
  rw [execSequence_of_normal hWrite]

/-- The Python constructor's guard is executed for an exact dict input.
    Values of the source type/dict bindings are explicit physical reads;
    no bounded numeric input is inspected or enumerated. -/
theorem balanceConstructor_python_guard_eq {m f ref object k}
    (hArg : localValue m f "initial_context" = .ok (.object ref))
    (hType : localValue m f "type" = .ok (.builtin .type))
    (hDict : localValue m f "dict" = .ok (.builtin .dict))
    (hObject : objectAt m ref = .ok object) (hKind : object.kind = .pythonDict)
    (hk : 4 ≤ k) :
    execStmt (k + 2) (balanceProgram .python) m f
      (firstStmt (balanceConstructorBodyTemplate .python)) = .ok ⟨m, f, .normal⟩ := by
  have hl : DepthDerivesExpr (balanceProgram .python) m f
      (.binary .isNotIdentity (.local "initial_context") .null)
      ⟨m, .ok (.bool true)⟩ 1 :=
    .binary (by decide) (.localRead hArg) .null rfl
  have hCall : DepthDerivesExpr (balanceProgram .python) m f
      (.call (.local "type") (.sequence (.local "initial_context") .empty))
      ⟨m, .ok (.builtin .dict)⟩ 2 := by
    apply DepthDerivesExpr.callBuiltin (.localRead hType)
      (.cons (.localRead hArg) .empty) (by decide)
    rw [balanceProgram_lang]
    unfold hostCall
    dsimp only
    rw [hObject]
    simp only [Bind.bind, Pure.pure, Except.bind, Except.pure]
    rw [hKind]
    rfl
  have hr : DepthDerivesExpr (balanceProgram .python) m f
      (.binary .isNotIdentity
        (.call (.local "type") (.sequence (.local "initial_context") .empty))
        (.local "dict")) ⟨m, .ok (.bool false)⟩ 3 :=
    .binary (by decide) hCall (.localRead hDict) rfl
  have he := evalAndThen_of_true (evalExpr_adequate hl (k := k) (by omega))
    (by rfl : sourceTruthy (balanceProgram .python).lang m (.bool true) = .ok true)
    (right := .binary .isNotIdentity
      (.call (.local "type") (.sequence (.local "initial_context") .empty)) (.local "dict"))
  rw [evalExpr_adequate hr (by omega)] at he
  change execStmt ((k + 1) + 1) _ _ _ (.ifThenElse _ _ .empty) = _
  rw [execIf_of_false he (by rfl)]
  exact execStmt_adequate DepthDerivesStmt.empty (by omega)

/-- Exact post-guard equation on the actual Python constructor. Its six
    initialization writes, reset call and seed-copy suffix remain in order. -/
theorem balanceConstructor_python_after_guard {m f ref object}
    (hArg : localValue m f "initial_context" = .ok (.object ref))
    (hType : localValue m f "type" = .ok (.builtin .type))
    (hDict : localValue m f "dict" = .ok (.builtin .dict))
    (hObject : objectAt m ref = .ok object) (hKind : object.kind = .pythonDict) :
    execStmt 99 (balanceProgram .python) m f (balanceStoredConstructor .python).2.body =
      execStmt 98 (balanceProgram .python) m f
        (restStmt (balanceConstructorBodyTemplate .python)) := by
  rw [balanceConstructorBody_shape]
  change execStmt (98 + 1) _ _ _ (.sequence _ _) = _
  exact execSequence_of_normal
    (balanceConstructor_python_guard_eq hArg hType hDict hObject hKind (k := 96) (by decide))

/-- Method binding and supplied object-parameter allocation for a single
    source receiver call. The stored callee body remains an executable AST. -/
theorem evalReceiverObjectCall_eq {lang m f name argName param methodRef method objectRef k}
    (hr : f.receiver = some m.checkerRef)
    (hf : readCheckerField m name = .error (.unboundLocal name))
    (hm : m.classMethods.lookup name = some methodRef)
    (hc : closureAt m methodRef = .ok method)
    (hp : method.params = [⟨param, some .null⟩])
    (ha : localValue m f argName = .ok (.object objectRef)) (hk : 1 < k) :
    let bound := (allocClosure m { method with receiver := some m.checkerRef }).1
    evalExpr (k + 1) (balanceProgram lang) m f
      (.call (.property (.local (if lang == .ts then "this" else "self")) name)
        (.sequence (.local argName) .empty)) = (do
      let body ← execStmt k (balanceProgram lang)
        (allocCell bound (.object objectRef) true).1
        { closureFrame { method with receiver := some m.checkerRef } with
          locals := [(param, bound.nextCell)] } method.body
      closureResult lang body) := by
  let bound := (allocClosure m { method with receiver := some m.checkerRef }).1
  let active := { method with receiver := some m.checkerRef }
  have hLocal : localValue m f (if lang == .ts then "this" else "self") =
      .ok (.object m.checkerRef) := by
    cases lang <;> simp [localValue, hr]
  have hRead : readPropertyValue (balanceProgram lang).lang m (.object m.checkerRef) name =
      .ok ⟨bound, .ok (.closure m.nextClosure)⟩ := by
    rw [balanceProgram_lang]
    exact readCheckerMethod_bound hf hm hc
  have he : DepthDerivesExpr (balanceProgram lang) m f
      (.property (.local (if lang == .ts then "this" else "self")) name)
      ⟨bound, .ok (.closure m.nextClosure)⟩ 1 := .property (.localRead hLocal) hRead
  have hArg : localValue bound f argName = .ok (.object objectRef) := ha
  have hArgs : DepthDerivesArgs (balanceProgram lang) bound f
      (.sequence (.local argName) .empty) ⟨bound, .ok [.object objectRef]⟩ 1 :=
    .cons (.localRead hArg) .empty
  have hStored : closureAt bound m.nextClosure = .ok active := by
    simp [bound, active, closureAt, allocClosure, List.lookup]
  have hBind : DepthBindsProvided (balanceProgram lang) bound (closureFrame active)
      active.params active.pythonDefaults [.object objectRef]
      (allocCell bound (.object objectRef) true).1
      { closureFrame active with locals := [(param, bound.nextCell)] } 1 := by
    change DepthBindsProvided _ _ _ method.params _ _ _ _ _
    rw [hp]
    exact .cons (by simp) .empty
  have h := evalStoredCall_eq he hArgs hStored hBind hk hk hk
  simpa only [balanceProgram_lang] using h

/-- Actual reset provenance follows constructively from its certified lookup. -/
theorem balanceStoredReset_lookup (lang : TargetLang) :
    (balancePreparation lang).1.classMethods.lookup "reset" =
      some (balanceStoredReset lang).1 ∧
    closureAt (balancePreparation lang).1 (balanceStoredReset lang).1 =
      .ok (balanceStoredReset lang).2 := by
  have ht := (balanceReset_idle_shape lang).1
  unfold balanceResetLookup at ht
  unfold balanceStoredReset balanceResetLookup
  cases hm : (balancePreparation lang).1.classMethods.lookup "reset" with
  | none => simp [hm] at ht
  | some ref =>
      cases hc : closureAt (balancePreparation lang).1 ref with
      | error e => simp [hm, hc, Except.toOption] at ht
      | ok closure => simp [hm, hc, Except.toOption]

/-- A receiver-only busy write preserves all method, closure, cell and global
    bindings exactly; later heap/closure mutations need their own proofs. -/
theorem balanceSetBusy_preserves_bindings (m : TargetMachine) (busy : Bool) :
    (balanceSetBusy m busy).classMethods = m.classMethods ∧
    (balanceSetBusy m busy).closures = m.closures ∧
    (balanceSetBusy m busy).globals = m.globals ∧
    (balanceSetBusy m busy).cells = m.cells ∧
    (balanceSetBusy m busy).objects = m.objects :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical constructor parameter read for every symbolic b. -/
theorem balanceConstructorBodyEntry_argument (lang : TargetLang) (b : Int) :
    localValue (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (balanceConstructorParam lang) = .ok (.object (balancePreparation lang).1.nextObject) := by
  apply localValue_fresh_parameter
  · cases lang <;> decide
  · cases lang <;> decide

/-- The allocated input remains the exact one-key object after caller and
    constructor parameter cells plus receiver binding are allocated. -/
theorem balanceConstructorBodyEntry_object (lang : TargetLang) (b : Int) :
    objectAt (balanceConstructorBodyEntry lang b).1 (balancePreparation lang).1.nextObject =
      .ok (balanceHeapObject lang (balancePreparation lang).1 b) := by
  change objectAt (allocCell _ _ _).1 _ = _
  rw [objectAt_allocCell]
  change objectAt (allocClosure _ _).1 _ = _
  rw [objectAt_allocClosure]
  change objectAt (allocCell _ _ _).1 _ = _
  rw [objectAt_allocCell]
  exact objectAt_allocObject_fresh _ _

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Fixed preparation resolves Python's two type-check bindings to actual
    host cells. They are unshadowed in the stored constructor captures. -/
theorem balancePreparation_python_types :
    (balanceStoredConstructor .python).2.captures.lookup "type" = none ∧
    (balanceStoredConstructor .python).2.captures.lookup "dict" = none ∧
    (balancePreparation .python).1.globals.lookup "type" = some 0 ∧
    (balancePreparation .python).1.globals.lookup "dict" = some 1 ∧
    readCell (balancePreparation .python).1 0 = .ok (.builtin .type) ∧
    readCell (balancePreparation .python).1 1 = .ok (.builtin .dict) ∧
    1 < (balancePreparation .python).1.nextCell := by
  unfold balanceStoredConstructor balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- Canonical source builtin reads survive all constructor-entry allocations,
    uniformly in the integer value carried by the input object. -/
theorem balanceConstructorBodyEntry_python_types (b : Int) :
    localValue (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      "type" = .ok (.builtin .type) ∧
    localValue (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      "dict" = .ok (.builtin .dict) := by
  obtain ⟨hct, hcd, hgt, hgd, hvt, hvd, hf⟩ := balancePreparation_python_types
  constructor
  · exact localValue_constructor_global (by decide) (by decide) (by decide)
      hct hgt hvt (Nat.lt_trans (by decide : 0 < 1) hf)
  · exact localValue_constructor_global (by decide) (by decide) (by decide)
      hcd hgd hvd hf

/-- For every b, actual canonical Python construction takes the successful
    type-guard edge at depth 98. Reset and seed-copy success are still open. -/
theorem balanceConstructor_python_canonical_after_guard (b : Int) :
    execStmt 99 (balanceProgram .python)
      (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      (balanceStoredConstructor .python).2.body =
      execStmt 98 (balanceProgram .python)
        (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
        (restStmt (balanceConstructorBodyTemplate .python)) := by
  have hTypes := balanceConstructorBodyEntry_python_types b
  exact balanceConstructor_python_after_guard
    (balanceConstructorBodyEntry_argument .python b) hTypes.1 hTypes.2
    (balanceConstructorBodyEntry_object .python b) rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Actual reset parameters and method freshness in the prepared store. -/
theorem balanceStoredReset_shape (lang : TargetLang) :
    readCheckerField (balancePreparation lang).1 "reset" = .error (.unboundLocal "reset") ∧
    (balanceStoredReset lang).2.params = [⟨balanceConstructorParam lang, some .null⟩] ∧
    (balanceStoredReset lang).1 ≠ (balancePreparation lang).1.nextClosure := by
  cases lang with
  | ts =>
      unfold balanceStoredReset balanceResetLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStoredReset balanceResetLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- Constructor-entry allocations preserve actual reset method provenance.
    The newly bound constructor closure cannot shadow the stored reset ref. -/
theorem balanceConstructorBodyEntry_reset_store (lang : TargetLang) (b : Int) :
    readCheckerField (balanceConstructorBodyEntry lang b).1 "reset" =
      .error (.unboundLocal "reset") ∧
    (balanceConstructorBodyEntry lang b).1.classMethods.lookup "reset" =
      some (balanceStoredReset lang).1 ∧
    closureAt (balanceConstructorBodyEntry lang b).1 (balanceStoredReset lang).1 =
      .ok (balanceStoredReset lang).2 := by
  have hShape := balanceStoredReset_shape lang
  have hLookup := balanceStoredReset_lookup lang
  refine ⟨hShape.1, hLookup.1, ?_⟩
  change closureAt (allocCell _ _ _).1 _ = _
  rw [closureAt_allocCell]
  change closureAt (allocClosure _ _).1 _ = _
  rw [closureAt_allocClosure_other (m := (balanceConstructorArgumentEntry lang b).1) hShape.2.2]
  change closureAt (allocCell _ _ _).1 _ = _
  rw [closureAt_allocCell]
  change closureAt (allocObject _ _).1 _ = _
  rw [closureAt_allocObject]
  exact hLookup.2

/-- Physical reset-call binding from the canonical constructor frame. -/
def balanceResetBodyEntry (lang : TargetLang) (b : Int) : TargetMachine × TargetFrame :=
  let m := (balanceConstructorBodyEntry lang b).1
  let active := { (balanceStoredReset lang).2 with receiver := some m.checkerRef }
  let bound := (allocClosure m active).1
  ((allocCell bound (.object (balancePreparation lang).1.nextObject) true).1,
    { closureFrame active with locals := [(balanceConstructorParam lang, bound.nextCell)] })

/-- All languages' reset calls from the canonical constructor frame enter
    the actual source body at the unchanged callClosure depth k. Python's
    pre-reset initialization writes remain a separate execution obligation. -/
theorem balanceConstructor_reset_call_eq_body (lang : TargetLang) (b : Int) {k : Nat}
    (hk : 1 < k) :
    evalExpr (k + 1) (balanceProgram lang)
      (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (.call (.property (.local (if lang == .ts then "this" else "self")) "reset")
        (.sequence (.local (balanceConstructorParam lang)) .empty)) = (do
      let body ← execStmt k (balanceProgram lang)
        (balanceResetBodyEntry lang b).1 (balanceResetBodyEntry lang b).2
        (balanceStoredReset lang).2.body
      closureResult lang body) := by
  have hStore := balanceConstructorBodyEntry_reset_store lang b
  exact evalReceiverObjectCall_eq rfl hStore.1 hStore.2.1 hStore.2.2
    (balanceStoredReset_shape lang).2.1 (balanceConstructorBodyEntry_argument lang b) hk

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Preparation's busy bit is physically idle, before any symbolic input. -/
theorem balancePreparation_idle (lang : TargetLang) :
    (balancePreparation lang).1.checker.busy = false := by
  cases lang with
  | ts =>
      unfold balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- Canonical reset entry acquires busy and enters the source snapshots.
    This equation is universal in b, but assumes no success of the suffix. -/
theorem balanceResetBodyEntry_snapshots (lang : TargetLang) (b : Int) {k : Nat}
    (hk : 4 ≤ k) :
    execStmt (k + 1) (balanceProgram lang)
      (balanceResetBodyEntry lang b).1 (balanceResetBodyEntry lang b).2
      (balanceStoredReset lang).2.body =
      execStmt (k - 1) (balanceProgram lang)
        (balanceSetBusy (balanceResetBodyEntry lang b).1 true) (balanceResetBodyEntry lang b).2
        (restStmt (restStmt (balanceStoredReset lang).2.body)) :=
  balanceReset_idle_entry rfl (balancePreparation_idle lang) hk

/-- TS constructor execution now enters reset's actual snapshot/remainder
    at depth 94, then joins the real seed-copy suffix if reset returns normally.
    Source exceptions and outer target errors are preserved by the equation. -/
theorem balanceConstructor_ts_snapshots_eq (b : Int) :
    execStmt 99 (balanceProgram .ts)
      (balanceConstructorBodyEntry .ts b).1 (balanceConstructorBodyEntry .ts b).2
      (balanceStoredConstructor .ts).2.body = (do
      let resetBody ← execStmt 94 (balanceProgram .ts)
        (balanceSetBusy (balanceResetBodyEntry .ts b).1 true) (balanceResetBodyEntry .ts b).2
        (restStmt (restStmt (balanceStoredReset .ts).2.body))
      let called ← closureResult .ts resetBody
      let head : StmtOutcome := match called.result with
        | .error e => ⟨called.machine, (balanceConstructorBodyEntry .ts b).2, .raised e⟩
        | .ok _ => ⟨called.machine, (balanceConstructorBodyEntry .ts b).2, .normal⟩
      match head.control with
      | .normal =>
          execStmt 98 (balanceProgram .ts) head.machine head.frame
            (restStmt (balanceConstructorBodyTemplate .ts))
      | _ => pure head) := by
  rw [balanceConstructor_ts_reset_eq, execDoExpr_eq]
  have hCall := balanceConstructor_reset_call_eq_body .ts b (k := 96) (by decide)
  change evalExpr 97 (balanceProgram .ts)
    (balanceConstructorBodyEntry .ts b).1 (balanceConstructorBodyEntry .ts b).2
    (.call (.property (.local "this") "reset") (.sequence (.local "initialContext") .empty)) = _ at hCall
  rw [hCall]
  rw [balanceResetBodyEntry_snapshots .ts b (k := 95) (by decide)]
  simp only [Bind.bind, Except.bind]
  cases h : execStmt 94 (balanceProgram .ts)
      (balanceSetBusy (balanceResetBodyEntry .ts b).1 true) (balanceResetBodyEntry .ts b).2
      (restStmt (restStmt (balanceStoredReset .ts).2.body)) with
  | error e => rfl
  | ok out =>
      dsimp only
      cases hc : closureResult .ts out with
      | error e => rfl
      | ok result =>
          dsimp only
          cases result.result <;> rfl

end Harmonia.Applications.Kadmos.Generated
