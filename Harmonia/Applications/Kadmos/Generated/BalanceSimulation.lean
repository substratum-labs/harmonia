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

/-- The six source initialization writes, including two fresh allocations.
    This is the reached Python pre-reset machine, not a completed constructor. -/
def balancePythonInitialized (m : TargetMachine) (initial : String) : TargetMachine :=
  let seed := { m with checker := { m.checker with constructorSeed := none } }
  let state := { seed with checker := { seed.checker with state := initial } }
  let context := (allocObject state (literalObject .python state)).1
  let context := { context with checker := { context.checker with context := state.nextObject } }
  let history := (allocObject context ⟨.pythonList, none, [], [], [], false, false⟩).1
  { history with checker := { history.checker with history := context.nextObject, busy := false, undo := none } }

/-- Exactly the reset/copy sequence following Python's six initialization writes. -/
def balancePythonAfterInit : TargetStmt :=
  .sequence (.doExpr (.call (.property (.local "self") "reset")
    (.sequence (.local (balanceConstructorParam .python)) .empty)))
    (.sequence (.assign (.property (.local "self") "__constructor_seed")
      (.call (.local "dict") (.sequence (.property (.local "self") "__context") .empty))) .empty)

/-- Symbolic initialization: the only external read is the actual _INITIAL cell.
    Every assignment is executed in source order at its own sequence depth. -/
theorem balanceConstructor_python_initialized {m f initial k}
    (hr : f.receiver = some m.checkerRef)
    (hi : localValue m f "_INITIAL" = .ok (.string initial)) (hk : 10 ≤ k) :
    execStmt k (balanceProgram .python) m f
      (restStmt (balanceConstructorBodyTemplate .python)) =
      execStmt (k - 6) (balanceProgram .python) (balancePythonInitialized m initial) f
        balancePythonAfterInit := by
  let m1 := { m with checker := { m.checker with constructorSeed := none } }
  let m2 := { m1 with checker := { m1.checker with state := initial } }
  let m3a := (allocObject m2 (literalObject .python m2)).1
  let m3 := { m3a with checker := { m3a.checker with context := m2.nextObject } }
  let m4a := (allocObject m3 ⟨.pythonList, none, [], [], [], false, false⟩).1
  let m4 := { m4a with checker := { m4a.checker with history := m3.nextObject } }
  let m5 := balanceSetBusy m4 false
  let m6 := { m5 with checker := { m5.checker with undo := none } }
  have receiver (a : TargetMachine) (ha : a.checkerRef = m.checkerRef) (j : Nat) :
      evalExpr (j + 1) (balanceProgram .python) a f (.local "self") =
        .ok ⟨a, .ok (.object m.checkerRef)⟩ := by
    have h : localValue a f "self" = .ok (.object m.checkerRef) := by
      simp [localValue, hr]
    exact evalExpr_adequate (.localRead h) (by omega)
  have h1 : execStmt (k - 1) (balanceProgram .python) m f
      (.assign (.property (.local "self") "__constructor_seed") .null) =
      .ok ⟨m1, f, .normal⟩ := by
    have hf : k - 1 = (k - 3 + 1) + 1 := by omega
    rw [hf]
    exact execCheckerAssign_of_value (final := m) (receiver m rfl _)
      (evalExpr_adequate DepthDerivesExpr.null (by omega)) (by rfl)
  have h2 : execStmt (k - 2) (balanceProgram .python) m1 f
      (.assign (.property (.local "self") "__state") (.local "_INITIAL")) =
      .ok ⟨m2, f, .normal⟩ := by
    have hf : k - 2 = (k - 4 + 1) + 1 := by omega
    rw [hf]
    have hv : localValue m1 f "_INITIAL" = .ok (.string initial) := hi
    exact execCheckerAssign_of_value (final := m1) (receiver m1 rfl _)
      (evalExpr_adequate (.localRead hv) (by omega)) (by rfl)
  have h3 : execStmt (k - 3) (balanceProgram .python) m2 f
      (.assign (.property (.local "self") "__context") (.object .empty)) =
      .ok ⟨m3, f, .normal⟩ := by
    have hf : k - 3 = (k - 5 + 1) + 1 := by omega
    rw [hf]
    have he := evalExpr_adequate (DepthDerivesExpr.objectEmpty
      (program := balanceProgram .python) (m := m2) (f := f))
      (k := k - 5 + 1) (by omega)
    rw [balanceProgram_lang] at he
    exact execCheckerAssign_of_value (final := m3a) (receiver m2 rfl _) he (by rfl)
  have h4 : execStmt (k - 4) (balanceProgram .python) m3 f
      (.assign (.property (.local "self") "__history") (.array .empty)) =
      .ok ⟨m4, f, .normal⟩ := by
    have hf : k - 4 = (k - 7 + 2) + 1 := by omega
    rw [hf]
    exact execCheckerAssign_of_value (final := m4a) (receiver m3 rfl _)
      (evalPythonEmptyList_eq _ (balanceProgram_lang .python)) (by rfl)
  have h5 : execStmt (k - 5) (balanceProgram .python) m4 f
      (.assign (.property (.local "self") "_busy") (.bool false)) =
      .ok ⟨m5, f, .normal⟩ :=
    execStmt_adequate (balance_busy_write (lang := .python) (busy := false) hr) (by omega)
  have h6 : execStmt (k - 6) (balanceProgram .python) m5 f
      (.assign (.property (.local "self") "__undo") .null) =
      .ok ⟨m6, f, .normal⟩ := by
    have hf : k - 6 = (k - 8 + 1) + 1 := by omega
    rw [hf]
    exact execCheckerAssign_of_value (final := m5) (receiver m5 rfl _)
      (evalExpr_adequate DepthDerivesExpr.null (by omega)) (by rfl)
  change execStmt k _ _ _ (.sequence _ (.sequence _ (.sequence _
    (.sequence _ (.sequence _ (.sequence _ balancePythonAfterInit)))))) = _
  simp only [show (TargetLang.python == .ts) = false by decide,
    Bool.false_eq_true, ↓reduceIte]
  have e1 : k = (k - 1) + 1 := by omega
  conv => lhs; rw [e1]
  rw [execSequence_of_normal h1]
  have e2 : k - 1 = (k - 2) + 1 := by omega
  conv => lhs; rw [e2]
  rw [execSequence_of_normal h2]
  have e3 : k - 2 = (k - 3) + 1 := by omega
  conv => lhs; rw [e3]
  rw [execSequence_of_normal h3]
  have e4 : k - 3 = (k - 4) + 1 := by omega
  conv => lhs; rw [e4]
  rw [execSequence_of_normal h4]
  have e5 : k - 4 = (k - 5) + 1 := by omega
  conv => lhs; rw [e5]
  rw [execSequence_of_normal h5]
  have e6 : k - 5 = (k - 6) + 1 := by omega
  conv => lhs; rw [e6]
  rw [execSequence_of_normal h6]
  exact congrArg (fun machine => execStmt (k - 6) (balanceProgram .python) machine f
    balancePythonAfterInit) (by rfl : m6 = balancePythonInitialized m initial)

/-- Physical captured cell carrying the generated initial state. -/
def balancePythonInitialCell : CellRef :=
  71

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balancePreparation_python_initial :
    (balanceStoredConstructor .python).2.captures.lookup "_INITIAL" = some balancePythonInitialCell ∧
    readCell (balancePreparation .python).1 balancePythonInitialCell = .ok (.string "Ready") ∧
    balancePythonInitialCell < (balancePreparation .python).1.nextCell := by
  unfold balancePythonInitialCell balanceStoredConstructor balanceConstructorLookup
    balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

theorem balanceConstructorBodyEntry_python_initial (b : Int) :
    localValue (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      "_INITIAL" = .ok (.string "Ready") := by
  obtain ⟨hc, hv, hf⟩ := balancePreparation_python_initial
  exact localValue_constructor_capture
    (m := (balancePreparation .python).1) (method := (balanceStoredConstructor .python).2)
    (object := balanceHeapObject .python (balancePreparation .python).1 b)
    (argument := .object (balancePreparation .python).1.nextObject)
    (param := balanceConstructorParam .python) (ref := balancePythonInitialCell)
    (name := "_INITIAL") (value := .string "Ready")
    (by decide) (by decide) (by decide) hc hv hf

theorem balanceConstructorBodyEntry_receiver (lang : TargetLang) (b : Int) :
    (balanceConstructorBodyEntry lang b).2.receiver =
      some (balanceConstructorBodyEntry lang b).1.checkerRef :=
  constructorBody_receiver (balancePreparation lang).1 (balanceStoredConstructor lang).2
    (balanceHeapObject lang (balancePreparation lang).1 b)
    (.object (balancePreparation lang).1.nextObject) (balanceConstructorParam lang)

/-- Canonical Python construction has executed all six writes at depth 92. -/
theorem balanceConstructor_python_canonical_initialized (b : Int) :
    execStmt 99 (balanceProgram .python)
      (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      (balanceStoredConstructor .python).2.body =
      execStmt 92 (balanceProgram .python)
        (balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready")
        (balanceConstructorBodyEntry .python b).2 balancePythonAfterInit :=
  (balanceConstructor_python_canonical_after_guard b).trans
    (balanceConstructor_python_initialized
      (m := (balanceConstructorBodyEntry .python b).1)
      (f := (balanceConstructorBodyEntry .python b).2) (initial := "Ready") (k := 98)
      (balanceConstructorBodyEntry_receiver .python b)
      (balanceConstructorBodyEntry_python_initial b) (by decide))

/-- Initialization changes checker fields and allocates objects only. -/
theorem balancePythonInitialized_preserves_bindings (m : TargetMachine) (initial : String) :
    (balancePythonInitialized m initial).classMethods = m.classMethods ∧
    (balancePythonInitialized m initial).closures = m.closures ∧
    (balancePythonInitialized m initial).globals = m.globals ∧
    (balancePythonInitialized m initial).cells = m.cells ∧
    (balancePythonInitialized m initial).nextClosure = m.nextClosure ∧
    (balancePythonInitialized m initial).nextCell = m.nextCell :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The reached Python reset call binds from the post-initialization heap. -/
def balancePythonResetBodyEntry (b : Int) : TargetMachine × TargetFrame :=
  let m := balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready"
  let active := { (balanceStoredReset .python).2 with receiver := some m.checkerRef }
  let bound := (allocClosure m active).1
  ((allocCell bound (.object (balancePreparation .python).1.nextObject) true).1,
    { closureFrame active with locals := [(balanceConstructorParam .python, bound.nextCell)] })

theorem balancePythonInitialized_reset_field (m : TargetMachine) (initial : String) :
    readCheckerField (balancePythonInitialized m initial) "reset" = readCheckerField m "reset" := by
  rfl

/-- Field-independent reads survive all six writes and both allocations. -/
theorem balancePythonInitialized_localValue (m : TargetMachine) (initial : String)
    (f : TargetFrame) (name : String) :
    localValue (balancePythonInitialized m initial) f name = localValue m f name := rfl

theorem balancePythonInitialized_checkerRef (m : TargetMachine) (initial : String) :
    (balancePythonInitialized m initial).checkerRef = m.checkerRef := rfl

theorem balancePythonInitialized_idle (m : TargetMachine) (initial : String) :
    (balancePythonInitialized m initial).checker.busy = false := rfl

/-- Lift actual stored-method provenance through initialization, before using
    any concrete preparation in definitional equality. -/
theorem balancePythonInitialized_reset_store_of {m initial ref method}
    (hf : readCheckerField m "reset" = .error (.unboundLocal "reset"))
    (hm : m.classMethods.lookup "reset" = some ref)
    (hc : closureAt m ref = .ok method) :
    readCheckerField (balancePythonInitialized m initial) "reset" = .error (.unboundLocal "reset") ∧
    (balancePythonInitialized m initial).classMethods.lookup "reset" = some ref ∧
    closureAt (balancePythonInitialized m initial) ref = .ok method := by
  refine ⟨(balancePythonInitialized_reset_field m initial).trans hf, ?_, ?_⟩
  · exact (congrArg (fun methods => methods.lookup "reset")
      (balancePythonInitialized_preserves_bindings m initial).1).trans hm
  · have he : closureAt (balancePythonInitialized m initial) ref = closureAt m ref := rfl
    exact he.trans hc

theorem balancePythonInitialized_reset_store (b : Int) :
    let m := balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready"
    readCheckerField m "reset" = .error (.unboundLocal "reset") ∧
    m.classMethods.lookup "reset" = some (balanceStoredReset .python).1 ∧
    closureAt m (balanceStoredReset .python).1 = .ok (balanceStoredReset .python).2 := by
  have h := balanceConstructorBodyEntry_reset_store .python b
  exact balancePythonInitialized_reset_store_of h.1 h.2.1 h.2.2

theorem balanceConstructor_python_reset_call_eq_body (b : Int) {k : Nat} (hk : 1 < k) :
    evalExpr (k + 1) (balanceProgram .python)
      (balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready")
      (balanceConstructorBodyEntry .python b).2
      (.call (.property (.local "self") "reset")
        (.sequence (.local (balanceConstructorParam .python)) .empty)) = (do
      let body ← execStmt k (balanceProgram .python)
        (balancePythonResetBodyEntry b).1 (balancePythonResetBodyEntry b).2
        (balanceStoredReset .python).2.body
      closureResult .python body) := by
  have hs := balancePythonInitialized_reset_store b
  have hr := (balanceConstructorBodyEntry_receiver .python b).trans
    (congrArg some (balancePythonInitialized_checkerRef
      (balanceConstructorBodyEntry .python b).1 "Ready").symm)
  have ha := (balancePythonInitialized_localValue (balanceConstructorBodyEntry .python b).1
    "Ready" (balanceConstructorBodyEntry .python b).2 (balanceConstructorParam .python)).trans
      (balanceConstructorBodyEntry_argument .python b)
  exact evalReceiverObjectCall_eq (lang := .python) hr hs.1 hs.2.1 hs.2.2
    (balanceStoredReset_shape .python).2.1 ha hk

theorem balancePythonResetBodyEntry_receiver (b : Int) :
    (balancePythonResetBodyEntry b).2.receiver = some (balancePythonResetBodyEntry b).1.checkerRef :=
  receiverCallBody_receiver
    (balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready")
    (balanceStoredReset .python).2 (.object (balancePreparation .python).1.nextObject)
    (balanceConstructorParam .python)

theorem balancePythonResetBodyEntry_idle (b : Int) :
    (balancePythonResetBodyEntry b).1.checker.busy = false :=
  (receiverCallBody_busy
    (balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready")
    (balanceStoredReset .python).2 (.object (balancePreparation .python).1.nextObject)).trans
      (balancePythonInitialized_idle (balanceConstructorBodyEntry .python b).1 "Ready")

/-- Python reaches reset snapshots at depth 87, then joins the actual copy suffix.
    The reset result and all source/target error outcomes are retained. -/
theorem balanceConstructor_python_snapshots_eq (b : Int) :
    execStmt 99 (balanceProgram .python)
      (balanceConstructorBodyEntry .python b).1 (balanceConstructorBodyEntry .python b).2
      (balanceStoredConstructor .python).2.body = (do
      let resetBody ← execStmt 87 (balanceProgram .python)
        (balanceSetBusy (balancePythonResetBodyEntry b).1 true) (balancePythonResetBodyEntry b).2
        (restStmt (restStmt (balanceStoredReset .python).2.body))
      let called ← closureResult .python resetBody
      let head : StmtOutcome := match called.result with
        | .error e => ⟨called.machine, (balanceConstructorBodyEntry .python b).2, .raised e⟩
        | .ok _ => ⟨called.machine, (balanceConstructorBodyEntry .python b).2, .normal⟩
      match head.control with
      | .normal =>
          execStmt 91 (balanceProgram .python) head.machine head.frame
            (restStmt balancePythonAfterInit)
      | _ => pure head) := by
  have hCall := balanceConstructor_python_reset_call_eq_body b (k := 89) (by decide)
  have hSnapshots : execStmt 89 (balanceProgram .python)
      (balancePythonResetBodyEntry b).1 (balancePythonResetBodyEntry b).2
      (balanceStoredReset .python).2.body =
      execStmt 87 (balanceProgram .python)
        (balanceSetBusy (balancePythonResetBodyEntry b).1 true) (balancePythonResetBodyEntry b).2
        (restStmt (restStmt (balanceStoredReset .python).2.body)) :=
    balanceReset_idle_entry (lang := .python)
      (balancePythonResetBodyEntry_receiver b) (balancePythonResetBodyEntry_idle b)
      (k := 88) (by decide)
  have hCall' := hCall.trans (congrArg (fun execution => do
    let body ← execution
    closureResult .python body) hSnapshots)
  exact (balanceConstructor_python_canonical_initialized b).trans
    (execSequenceDoCall_eq _ hCall')

/-- Drop sequence heads without inspecting generated helper/try bodies. -/
def dropStmts : Nat → TargetStmt → TargetStmt
  | 0, stmt => stmt
  | n + 1, stmt => dropStmts n (restStmt stmt)

/-- Exact snapshot spine ending in the actual try/catch/finally and empty tail.
    No helper subtree is compared, evaluated, replaced or discarded. -/
def snapshotTryCheck : Nat → TargetStmt → Bool
  | 0, .sequence (.tryCatchFinally _ _ _ _ _) .empty => true
  | n + 1, .sequence _ rest => snapshotTryCheck n rest
  | _, _ => false

theorem snapshotTryCheck_sequence {n stmt} (h : snapshotTryCheck (n + 1) stmt = true) :
    stmt = .sequence (firstStmt stmt) (restStmt stmt) ∧
    snapshotTryCheck n (restStmt stmt) = true := by
  cases stmt <;> simp_all [snapshotTryCheck, firstStmt, restStmt]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- The stored reset snapshots have four heads, followed by the actual protected body. -/
theorem balanceReset_snapshot_shape (lang : TargetLang) :
    snapshotTryCheck 4 (restStmt (restStmt (balanceStoredReset lang).2.body)) = true := by
  cases lang with
  | ts =>
      unfold balanceStoredReset balanceResetLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStoredReset balanceResetLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Python step additionally saves undo; the source ordering is retained. -/
theorem balanceStep_snapshot_shape (lang : TargetLang) :
    snapshotTryCheck (if lang == .ts then 4 else 5)
      (restStmt (balanceStepAfterBusy lang)) = true := by
  cases lang with
  | ts =>
      unfold balanceStepAfterBusy balanceStoredStep balanceStepLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
      decide +kernel
  | python =>
      unfold balanceStepAfterBusy balanceStoredStep balanceStepLookup balancePreparation
      rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
      decide +kernel

/-- One actual snapshot sibling at its exact budget, with all exits retained. -/
theorem execSnapshot_eq {n stmt} (h : snapshotTryCheck (n + 1) stmt = true)
    (k : Nat) (program : TargetProgram) (m : TargetMachine) (f : TargetFrame) :
    execStmt (k + 1) program m f stmt = (do
      let head ← execStmt k program m f (firstStmt stmt)
      match head.control with
      | .normal => execStmt k program head.machine head.frame (restStmt stmt)
      | _ => pure head) := by
  conv => lhs; rw [(snapshotTryCheck_sequence h).1]
  exact execSequence_eq _ _ _ _ _ _

theorem balanceReset_snapshots_eq (lang : TargetLang) (k : Nat) (m : TargetMachine)
    (f : TargetFrame) :
    let snapshots := restStmt (restStmt (balanceStoredReset lang).2.body)
    execStmt (k + 1) (balanceProgram lang) m f snapshots = (do
      let head ← execStmt k (balanceProgram lang) m f (firstStmt snapshots)
      match head.control with
      | .normal => execStmt k (balanceProgram lang) head.machine head.frame (restStmt snapshots)
      | _ => pure head) :=
  execSnapshot_eq (balanceReset_snapshot_shape lang) k (balanceProgram lang) m f

theorem balanceStep_snapshots_eq (lang : TargetLang) (k : Nat) (m : TargetMachine)
    (f : TargetFrame) :
    let snapshots := restStmt (balanceStepAfterBusy lang)
    execStmt (k + 1) (balanceProgram lang) m f snapshots = (do
      let head ← execStmt k (balanceProgram lang) m f (firstStmt snapshots)
      match head.control with
      | .normal => execStmt k (balanceProgram lang) head.machine head.frame (restStmt snapshots)
      | _ => pure head) := by
  cases lang with
  | ts => exact execSnapshot_eq (balanceStep_snapshot_shape .ts) k (balanceProgram .ts) m f
  | python => exact execSnapshot_eq (balanceStep_snapshot_shape .python) k (balanceProgram .python) m f

/-- Captured protected syntax, selected without traversing its generated bodies. -/
structure ProtectedSyntax where
  body : TargetStmt
  catchType : Option String
  binder : Option String
  handler : TargetStmt
  cleanup : TargetStmt

def protectedSyntax (stmt : TargetStmt) : ProtectedSyntax :=
  match stmt with
  | .tryCatchFinally body ty binder handler cleanup => ⟨body, ty, binder, handler, cleanup⟩
  | _ => ⟨.empty, none, none, .empty, .empty⟩

def ProtectedSyntax.stmt (p : ProtectedSyntax) : TargetStmt :=
  .tryCatchFinally p.body p.catchType p.binder p.handler p.cleanup

theorem snapshotTryCheck_drop {n stmt} (h : snapshotTryCheck n stmt = true) :
    snapshotTryCheck 0 (dropStmts n stmt) = true := by
  induction n generalizing stmt with
  | zero => exact h
  | succ n ih => exact ih (snapshotTryCheck_sequence h).2

theorem snapshotTryCheck_protected {stmt} (h : snapshotTryCheck 0 stmt = true) :
    stmt = .sequence (protectedSyntax (firstStmt stmt)).stmt .empty := by
  cases stmt <;> simp_all [snapshotTryCheck]
  rename_i head tail
  cases head <;> try simp_all [snapshotTryCheck]
  cases tail <;> simp_all [snapshotTryCheck, firstStmt, protectedSyntax, ProtectedSyntax.stmt]

theorem balanceReset_protected_shape (lang : TargetLang) :
    let tail := dropStmts 4 (restStmt (restStmt (balanceStoredReset lang).2.body))
    tail = .sequence (protectedSyntax (firstStmt tail)).stmt .empty :=
  snapshotTryCheck_protected (snapshotTryCheck_drop (balanceReset_snapshot_shape lang))

theorem balanceStep_protected_shape (lang : TargetLang) :
    let tail := dropStmts (if lang == .ts then 4 else 5) (restStmt (balanceStepAfterBusy lang))
    tail = .sequence (protectedSyntax (firstStmt tail)).stmt .empty :=
  snapshotTryCheck_protected (snapshotTryCheck_drop (balanceStep_snapshot_shape lang))

/-- Snapshot termination selects this actual protected source subtree. -/
theorem execProtectedSyntax_eq (k : Nat) (program : TargetProgram) (m : TargetMachine)
    (f : TargetFrame) (p : ProtectedSyntax) :
    execStmt (k + 1) program m f p.stmt = (do
      let attempted ← execStmt k program m f p.body
      let handled ← match attempted.control with
        | .raised errorValue =>
            if controlCaught p.catchType (.raised errorValue) then do
              let bound := bindCatchFrame attempted.machine attempted.frame p.binder errorValue
              let caught ← execStmt k program bound.1 bound.2 p.handler
              pure { caught with frame := { caught.frame with control := .normal } }
            else pure attempted
        | _ => pure attempted
      let finalized ← execStmt k program handled.machine handled.frame p.cleanup
      match finalized.control with
      | .normal => pure ⟨finalized.machine, finalized.frame, handled.control⟩
      | _ => pure finalized) :=
  execTryCatchFinally_eq k program m f p.body p.catchType p.binder p.handler p.cleanup

/-- Python's real shallow dict host copies the canonical one-field context. -/
theorem hostDict_balance {m b ref}
    (ho : objectAt m ref = .ok (balanceHeapObject .python m b)) :
    hostCall .python m .dict none [.object ref] =
      .ok ⟨(allocObject m (balanceHeapObject .python m b)).1, .ok (.object m.nextObject)⟩ := by
  unfold hostCall
  dsimp only
  rw [ho]
  rfl

/-- Actual dict(self.__context), reused by reset snapshots and the constructor
    seed-copy suffix. It requires physical reads, not a reset-success premise. -/
theorem balancePython_context_copy {m f b}
    (hr : f.receiver = some m.checkerRef)
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .python m b)) :
    DepthDerivesExpr (balanceProgram .python) m f
      (.call (.local "dict") (.sequence (.property (.local "self") "__context") .empty))
      ⟨(allocObject m (balanceHeapObject .python m b)).1, .ok (.object m.nextObject)⟩ 3 := by
  have hs : localValue m f "self" = .ok (.object m.checkerRef) := by
    simp [localValue, hr]
  have hp : readPropertyValue (balanceProgram .python).lang m (.object m.checkerRef)
      "__context" = .ok ⟨m, .ok (.object m.checker.context)⟩ := by
    rw [balanceProgram_lang]
    simp [readPropertyValue, readCheckerField, Bind.bind, Pure.pure, Except.bind, Except.pure]
    rfl
  apply DepthDerivesExpr.callBuiltin (.localRead hd)
    (.cons (.property (.localRead hs) hp) .empty) (by decide)
  rw [balanceProgram_lang]
  exact hostDict_balance ho

/-- Physical final seed copy: fresh dict allocation followed by the source field write. -/
def balancePythonSeedCopied (m : TargetMachine) (b : Int) : TargetMachine :=
  let copied := (allocObject m (balanceHeapObject .python m b)).1
  { copied with checker := { copied.checker with constructorSeed := some m.nextObject } }

/-- Execute the actual post-reset Python seed-copy suffix at every adequate budget.
    Full constructor soundness must establish these receiver/dict/context reads. -/
theorem balanceConstructor_python_seed_copy {m f b k}
    (hr : f.receiver = some m.checkerRef)
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .python m b))
    (hk : 6 ≤ k) :
    execStmt k (balanceProgram .python) m f (restStmt balancePythonAfterInit) =
      .ok ⟨balancePythonSeedCopied m b, f, .normal⟩ := by
  have hs : localValue m f "self" = .ok (.object m.checkerRef) := by
    simp [localValue, hr]
  have hCopy := balancePython_context_copy hr hd ho
  have hWrite : DepthDerivesStmt (balanceProgram .python) m f
      (.assign (.property (.local "self") "__constructor_seed")
        (.call (.local "dict") (.sequence (.property (.local "self") "__context") .empty)))
      ⟨balancePythonSeedCopied m b, f, .normal⟩ 4 :=
    .assignProperty (.localRead hs) hCopy (by
      simp [balancePythonSeedCopied, allocObject, writeCheckerField])
  exact execStmt_adequate (.sequenceNormal hWrite .empty) (by omega)

theorem balancePythonSeedCopied_preserves_bindings (m : TargetMachine) (b : Int) :
    (balancePythonSeedCopied m b).classMethods = m.classMethods ∧
    (balancePythonSeedCopied m b).closures = m.closures ∧
    (balancePythonSeedCopied m b).globals = m.globals ∧
    (balancePythonSeedCopied m b).cells = m.cells ∧
    (balancePythonSeedCopied m b).checker.context = m.checker.context ∧
    (balancePythonSeedCopied m b).checker.history = m.checker.history ∧
    (balancePythonSeedCopied m b).checker.busy = m.checker.busy :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


def balanceResetSnapshots (lang : TargetLang) : TargetStmt :=
  restStmt (restStmt (balanceStoredReset lang).2.body)

def balanceResetProtected (lang : TargetLang) : ProtectedSyntax :=
  protectedSyntax (firstStmt (dropStmts 4 (balanceResetSnapshots lang)))

/-- Counts only sequence constructors; never compares generated helper bodies. -/
def statementSpineCheck : Nat → TargetStmt → Bool
  | 0, .empty => true
  | n + 1, .sequence _ rest => statementSpineCheck n rest
  | _, _ => false

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_body_spine (lang : TargetLang) :
    statementSpineCheck (if lang == .ts then 12 else 11) (balanceResetProtected lang).body = true ∧
    (balanceResetProtected lang).cleanup = .sequence
      (.assign (.property (.local (if lang == .ts then "this" else "self"))
        (if lang == .ts then "#busy" else "_busy")) (.bool false)) .empty := by
  cases lang <;>
    unfold balanceResetProtected balanceResetSnapshots balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem statementSpineCheck_sequence {n stmt} (h : statementSpineCheck (n + 1) stmt = true) :
    stmt = .sequence (firstStmt stmt) (restStmt stmt) ∧
    statementSpineCheck n (restStmt stmt) = true := by
  cases stmt <;> simp_all [statementSpineCheck, firstStmt, restStmt]

theorem balanceReset_cleanup_execute {lang m f k}
    (hr : f.receiver = some m.checkerRef) (hk : 4 ≤ k) :
    execStmt k (balanceProgram lang) m f (balanceResetProtected lang).cleanup =
      .ok ⟨balanceSetBusy m false, f, .normal⟩ := by
  rw [(balanceReset_body_spine lang).2]
  exact execStmt_adequate (.sequenceNormal (balance_busy_write hr) .empty) (by omega)

/-- Spread reads the old live object after allocating its destination. -/
theorem objectAt_allocObject_other {m object ref} (hn : ref ≠ m.nextObject) :
    objectAt (allocObject m object).1 ref = objectAt m ref := by
  simp [objectAt, allocObject, List.lookup, beq_eq_false_iff_ne.mpr hn]

theorem writeOwn_balance_fresh {m b}
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    writeOwn (allocObject m (literalObject .ts m)).1 m.nextObject "balance" (integerValue .ts b) =
      .ok (allocObject m (balanceHeapObject .ts m b)).1 := by
  simp [writeOwn, objectAt_allocObject_fresh, literalObject, balanceHeapObject,
    balanceDataDescriptor, replaceObject_allocObject hf,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem balanceTs_context_copy {m f b k}
    (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .ts m b))
    (hn : m.checker.context ≠ m.nextObject)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    evalExpr (k + 4) (balanceProgram .ts) m f
      (.object (.objectSpread (.property (.local "this") "#context") .empty)) =
      .ok ⟨(allocObject m (balanceHeapObject .ts m b)).1, .ok (.object m.nextObject)⟩ := by
  let fresh := (allocObject m (literalObject .ts m)).1
  have hs : localValue fresh f "this" = .ok (.object m.checkerRef) := by
    simp [localValue, hr, fresh, allocObject]
  have hp : readPropertyValue .ts fresh (.object m.checkerRef) "#context" =
      .ok ⟨fresh, .ok (.object m.checker.context)⟩ := by
    simp [readPropertyValue, readCheckerField, fresh, allocObject,
      Bind.bind, Pure.pure, Except.bind, Except.pure]; rfl
  have he : evalExpr (k + 2) (balanceProgram .ts) fresh f
      (.property (.local "this") "#context") =
      .ok ⟨fresh, .ok (.object m.checker.context)⟩ := by
    exact evalExpr_adequate (.property (.localRead hs) (by rw [balanceProgram_lang]; exact hp)) (by omega)
  have ho' : objectAt fresh m.checker.context = .ok (balanceHeapObject .ts m b) :=
    (objectAt_allocObject_other hn).trans ho
  simp only [evalExpr, balanceProgram_lang]
  change evalObjectFields (k + 3) (balanceProgram .ts) fresh f m.nextObject _ = _
  simp [evalObjectFields, he, ho', balanceHeapObject, balanceDataDescriptor,
    show writeOwn fresh m.nextObject "balance" (integerValue .ts b) =
      .ok (allocObject m (balanceHeapObject .ts m b)).1 from writeOwn_balance_fresh hf,
    List.forIn_cons, List.forIn_nil, Bind.bind, Pure.pure, Except.bind, Except.pure]
  rfl

def balanceTsSeedCopied (m : TargetMachine) (b : Int) : TargetMachine :=
  let copied := (allocObject m (balanceHeapObject .ts m b)).1
  { copied with checker := { copied.checker with constructorSeed := some m.nextObject } }

theorem balanceConstructor_ts_seed_copy {m f b k}
    (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.context = .ok (balanceHeapObject .ts m b))
    (hn : m.checker.context ≠ m.nextObject)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    execStmt (k + 6) (balanceProgram .ts) m f (restStmt (balanceConstructorBodyTemplate .ts)) =
      .ok ⟨balanceTsSeedCopied m b, f, .normal⟩ := by
  have hs : evalExpr (k + 4) (balanceProgram .ts) m f (.local "this") =
      .ok ⟨m, .ok (.object m.checkerRef)⟩ :=
    evalExpr_adequate (.localRead (by simp [localValue, hr])) (by omega)
  have he := balanceTs_context_copy (k := k) hr ho hn hf
  have hw : execStmt (k + 5) (balanceProgram .ts) m f
      (.assign (.property (.local "this") "#constructorSeed")
        (.object (.objectSpread (.property (.local "this") "#context") .empty))) =
      .ok ⟨balanceTsSeedCopied m b, f, .normal⟩ := by
    have hh := execCheckerAssign_of_value (final := (allocObject m (balanceHeapObject .ts m b)).1) hs he (show writeCheckerField
        (allocObject m (balanceHeapObject .ts m b)).1 "#constructorSeed" (.object m.nextObject) =
        .ok (balanceTsSeedCopied m b) from rfl)
    exact hh
  change execStmt ((k + 5) + 1) _ _ _ (.sequence _ .empty) = _
  simp only [show (TargetLang.ts == .ts) = true by decide, ↓reduceIte]
  rw [execSequence_of_normal hw]
  exact execStmt_adequate .empty (by omega)


def snapshotName (lang : TargetLang) (i : Nat) : String :=
  if lang == .ts then if i == 0 then "snapshotState" else if i == 1 then "snapshotContext" else "snapshotHistory"
  else if i == 0 then "snapshot_state" else if i == 1 then "snapshot_context" else "snapshot_history"

def snapshotBindStmt (lang : TargetLang) (name : String) (expr : TargetExpr) : TargetStmt :=
  if lang == .ts then .letLocal name false expr else .assign (.local name) expr

def snapshotBound (lang : TargetLang) (m : TargetMachine) (f : TargetFrame)
    (name : String) (value : TargetValue) : TargetMachine × TargetFrame :=
  ((allocCell m value (lang != .ts)).1, { f with locals := (name, m.nextCell) :: f.locals })

def snapshotAddress (m : TargetMachine) (f : TargetFrame) (name : String) : Option CellRef :=
  (f.locals.lookup name).orElse (fun _ => (f.captures.lookup name).orElse (fun _ => m.globals.lookup name))

theorem execSnapshotBind {lang m f name expr final value k}
    (he : evalExpr k (balanceProgram lang) m f expr = .ok ⟨final, .ok value⟩)
    (hn : lang = .python → snapshotAddress m f name = none) :
    execStmt (k + 1) (balanceProgram lang) m f (snapshotBindStmt lang name expr) =
      .ok ⟨(snapshotBound lang final f name value).1, (snapshotBound lang final f name value).2, .normal⟩ := by
  cases lang with
  | ts => simp [snapshotBindStmt, snapshotBound, execStmt, he, allocCell,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | python =>
      have ha := hn rfl
      unfold snapshotAddress at ha
      simp [snapshotBindStmt, snapshotBound, execStmt, he, balanceProgram_lang, ha, allocCell,
        Bind.bind, Pure.pure, Except.bind, Except.pure]

def resetReceiver (lang : TargetLang) : TargetExpr := .local (if lang == .ts then "this" else "self")
def resetField (lang : TargetLang) (ts py : String) : TargetExpr :=
  .property (resetReceiver lang) (if lang == .ts then ts else py)

def resetContextCopy (lang : TargetLang) : TargetExpr :=
  if lang == .ts then .object (.objectSpread (resetField lang "#context" "__context") .empty)
  else .call (.local "dict") (.sequence (resetField lang "#context" "__context") .empty)

def resetHistoryCopy (lang : TargetLang) : TargetExpr :=
  .call (if lang == .ts then .local "structuredClone" else .property (.local "copy") "deepcopy")
    (.sequence (resetField lang "#history" "__history") .empty)

def functionBody (stmt : TargetStmt) : TargetStmt :=
  match stmt with | .defineFunction _ _ body => body | _ => .empty

def balanceResetRollback (lang : TargetLang) : TargetStmt :=
  functionBody (firstStmt (dropStmts 3 (balanceResetSnapshots lang)))

def resetSnapshotHeadsCheck (lang : TargetLang) (s : TargetStmt) : Bool :=
  match s with
  | .sequence a (.sequence b (.sequence c (.sequence (.defineFunction name params _) _))) =>
      a == snapshotBindStmt lang (snapshotName lang 0) (resetField lang "#state" "__state") &&
      b == snapshotBindStmt lang (snapshotName lang 1) (resetContextCopy lang) &&
      c == snapshotBindStmt lang (snapshotName lang 2) (resetHistoryCopy lang) &&
      name == "rollback" && params.isEmpty
  | _ => false

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_snapshot_heads_check (lang : TargetLang) :
    resetSnapshotHeadsCheck lang (balanceResetSnapshots lang) = true := by
  cases lang <;>
    unfold balanceResetSnapshots balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem resetSnapshotHeadsCheck_sound {lang s} (h : resetSnapshotHeadsCheck lang s = true) :
    firstStmt s = snapshotBindStmt lang (snapshotName lang 0) (resetField lang "#state" "__state") ∧
    firstStmt (dropStmts 1 s) = snapshotBindStmt lang (snapshotName lang 1) (resetContextCopy lang) ∧
    firstStmt (dropStmts 2 s) = snapshotBindStmt lang (snapshotName lang 2) (resetHistoryCopy lang) ∧
    firstStmt (dropStmts 3 s) = .defineFunction "rollback" [] (functionBody (firstStmt (dropStmts 3 s))) := by
  cases s <;> try simp_all [resetSnapshotHeadsCheck]
  rename_i a tail
  cases tail <;> try simp_all [resetSnapshotHeadsCheck]
  rename_i b tail
  cases tail <;> try simp_all [resetSnapshotHeadsCheck]
  rename_i c tail
  cases tail <;> try simp_all [resetSnapshotHeadsCheck]
  rename_i d tail
  cases d <;> try simp_all [resetSnapshotHeadsCheck]
  rename_i name params body
  cases params <;> simp_all [resetSnapshotHeadsCheck, firstStmt, dropStmts, restStmt, functionBody]

theorem balanceReset_snapshot_heads (lang : TargetLang) :
    firstStmt (balanceResetSnapshots lang) = snapshotBindStmt lang (snapshotName lang 0) (resetField lang "#state" "__state") ∧
    firstStmt (dropStmts 1 (balanceResetSnapshots lang)) = snapshotBindStmt lang (snapshotName lang 1) (resetContextCopy lang) ∧
    firstStmt (dropStmts 2 (balanceResetSnapshots lang)) = snapshotBindStmt lang (snapshotName lang 2) (resetHistoryCopy lang) ∧
    firstStmt (dropStmts 3 (balanceResetSnapshots lang)) = .defineFunction "rollback" [] (balanceResetRollback lang) :=
  resetSnapshotHeadsCheck_sound (balanceReset_snapshot_heads_check lang)

theorem resetField_depth {lang m f ts py value}
    (hr : f.receiver = some m.checkerRef)
    (hv : readCheckerField m (if lang == .ts then ts else py) = .ok value) :
    DepthDerivesExpr (balanceProgram lang) m f (resetField lang ts py) ⟨m, .ok value⟩ 1 := by
  have hs : localValue m f (if lang == .ts then "this" else "self") = .ok (.object m.checkerRef) := by
    cases lang <;> simp [localValue, hr]
  apply DepthDerivesExpr.property (.localRead hs)
  rw [balanceProgram_lang]
  cases lang with
  | ts =>
      change readCheckerField m ts = .ok value at hv
      change readPropertyValue .ts m (.object m.checkerRef) ts = _
      simp [readPropertyValue, hv, Bind.bind, Pure.pure, Except.bind, Except.pure]; rfl
  | python =>
      change readCheckerField m py = .ok value at hv
      change readPropertyValue .python m (.object m.checkerRef) py = _
      simp [readPropertyValue, hv, Bind.bind, Pure.pure, Except.bind, Except.pure]; rfl

theorem resetEmptyContext_copy {lang m f k}
    (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.context = .ok (literalObject lang m))
    (hn : m.checker.context ≠ m.nextObject)
    (hd : lang = .python → localValue m f "dict" = .ok (.builtin .dict)) :
    evalExpr (k + 4) (balanceProgram lang) m f (resetContextCopy lang) =
      .ok ⟨(allocObject m (literalObject lang m)).1, .ok (.object m.nextObject)⟩ := by
  cases lang with
  | ts =>
      let fresh := (allocObject m (literalObject .ts m)).1
      have ho' : objectAt fresh m.checker.context = .ok (literalObject .ts m) :=
        (objectAt_allocObject_other hn).trans ho
      have he : evalExpr (k + 2) (balanceProgram .ts) fresh f (resetField .ts "#context" "__context") =
          .ok ⟨fresh, .ok (.object m.checker.context)⟩ :=
        evalExpr_adequate (resetField_depth hr (by rfl)) (by omega)
      simp only [resetContextCopy, show (TargetLang.ts == .ts) = true by decide, ↓reduceIte,
        evalExpr, balanceProgram_lang]
      change evalObjectFields (k + 3) _ fresh _ _ _ = _
      simp [evalObjectFields, he, ho', literalObject, Bind.bind, Pure.pure, Except.bind, Except.pure]
      rfl
  | python =>
      have he : DepthDerivesExpr (balanceProgram .python) m f (resetContextCopy .python)
          ⟨(allocObject m (literalObject .python m)).1, .ok (.object m.nextObject)⟩ 3 := by
        change DepthDerivesExpr (balanceProgram .python) m f
          (.call (.local "dict") (.sequence (resetField .python "#context" "__context") .empty)) _ 3
        have hp := resetField_depth (lang := .python) (ts := "#context") (py := "__context") hr
          (show readCheckerField m "__context" = .ok (.object m.checker.context) from rfl)
        apply DepthDerivesExpr.callBuiltin (.localRead (hd rfl)) (.cons hp .empty) (by decide)
        rw [balanceProgram_lang]
        unfold hostCall
        dsimp only
        rw [ho]
        rfl
      exact evalExpr_adequate he (by omega)

theorem cloneValue_emptyHistory {lang m ref k}
    (ho : objectAt m ref = .ok (emptyBalanceHistory lang m))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    cloneValue (k + 1) m (.object ref) =
      .ok ((allocObject m (emptyBalanceHistory lang m)).1, .object m.nextObject) := by
  cases lang <;> simp [cloneValue, ho, emptyBalanceHistory, replaceObject_allocObject hf,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Closure installation retains the actual body and every captured address.
    Maps deliberately model all matching cells even on malformed input heaps. -/
def snapshotRollbackInstalled (lang : TargetLang) (m : TargetMachine) (f : TargetFrame)
    (body : TargetStmt) : TargetMachine × TargetFrame :=
  functionInstalled lang m f "rollback" body

theorem execSnapshotRollback (lang : TargetLang) (m : TargetMachine) (f : TargetFrame)
    (body : TargetStmt) (k : Nat) :
    execStmt (k + 2) (balanceProgram lang) m f (.defineFunction "rollback" [] body) =
      .ok ⟨(snapshotRollbackInstalled lang m f body).1,
        (snapshotRollbackInstalled lang m f body).2, .normal⟩ := by
  rw [execDefineFunction_empty, balanceProgram_lang]
  rfl


/-- Actual pre-reset context differs by language: TS class defaults, Python's
    newly initialized empty dict. The supplied symbolic seed stays separate. -/
def resetSnapshotContextObject (lang : TargetLang) (m : TargetMachine) : HeapObject :=
  if lang == .ts then balanceHeapObject .ts m 100 else literalObject .python m

def resetSnapshotState (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) : TargetMachine × TargetFrame :=
  snapshotBound lang m f (snapshotName lang 0) (.string m.checker.state)

def resetSnapshotContext (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) : TargetMachine × TargetFrame :=
  let s := resetSnapshotState lang m f
  let copied := (allocObject s.1 (resetSnapshotContextObject lang s.1)).1
  snapshotBound lang copied s.2 (snapshotName lang 1) (.object s.1.nextObject)

def resetSnapshotHistory (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) : TargetMachine × TargetFrame :=
  let s := resetSnapshotContext lang m f
  let copied := (allocObject s.1 (emptyBalanceHistory lang s.1)).1
  snapshotBound lang copied s.2 (snapshotName lang 2) (.object s.1.nextObject)

def resetSnapshotsInstalled (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) : TargetMachine × TargetFrame :=
  let s := resetSnapshotHistory lang m f
  snapshotRollbackInstalled lang s.1 s.2 (balanceResetRollback lang)

/-- Physical host reads at the reached history snapshot, with no executor premise. -/
def SnapshotCloneRead (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) : Prop :=
  if lang == .ts then localValue m f "structuredClone" = .ok (.builtin .structuredClone)
  else ∃ value, localValue m f "copy" = .ok value ∧
    readPropertyValue .python m value "deepcopy" = .ok ⟨m, .ok (.builtin .deepCopy)⟩

theorem resetHistory_callee {lang m f} (hc : SnapshotCloneRead lang m f) :
    DepthDerivesExpr (balanceProgram lang) m f
      (if lang == .ts then .local "structuredClone" else .property (.local "copy") "deepcopy")
      ⟨m, .ok (.builtin (if lang == .ts then .structuredClone else .deepCopy))⟩
      (if lang == .ts then 0 else 1) := by
  cases lang with
  | ts => exact .localRead hc
  | python =>
      obtain ⟨value, hl, hp⟩ := hc
      exact .property (.localRead hl) (by rw [balanceProgram_lang]; exact hp)

theorem resetHistory_copy {lang m f k}
    (hr : f.receiver = some m.checkerRef)
    (ho : objectAt m m.checker.history = .ok (emptyBalanceHistory lang m))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (hc : SnapshotCloneRead lang m f) :
    evalExpr (k + 4) (balanceProgram lang) m f (resetHistoryCopy lang) =
      .ok ⟨(allocObject m (emptyBalanceHistory lang m)).1, .ok (.object m.nextObject)⟩ := by
  have hp := resetField_depth (lang := lang) (ts := "#history") (py := "__history") hr
    (show readCheckerField m (if lang == .ts then "#history" else "__history") =
      .ok (.object m.checker.history) by cases lang <;> rfl)
  have hh : hostCall lang m (if lang == .ts then .structuredClone else .deepCopy) none
      [.object m.checker.history] =
      .ok ⟨(allocObject m (emptyBalanceHistory lang m)).1, .ok (.object m.nextObject)⟩ := by
    have hclone := cloneValue_emptyHistory (k := 2047) ho hf
    cases lang <;>
      simp only [show (TargetLang.ts == .ts) = true by decide,
        show (TargetLang.python == .ts) = false by decide, Bool.false_eq_true, ↓reduceIte] <;>
      unfold hostCall <;> dsimp only <;> rw [hclone] <;> rfl
  have he := DepthDerivesExpr.callBuiltin (resetHistory_callee hc) (.cons hp .empty)
    (by cases lang <;> decide) (by rw [balanceProgram_lang]; exact hh)
  exact evalExpr_adequate he (by cases lang <;> simp <;> omega)

/-- Four source siblings compose at their own predecessor budgets. The
    statement is kept abstract so no stored AST is normalized in composition. -/
theorem execFourSnapshots {program stmt m f m1 f1 m2 f2 m3 f3 m4 f4 k}
    (shape : snapshotTryCheck 4 stmt = true)
    (h1 : execStmt (k + 7) program m f (firstStmt stmt) = .ok ⟨m1, f1, .normal⟩)
    (h2 : execStmt (k + 6) program m1 f1 (firstStmt (dropStmts 1 stmt)) = .ok ⟨m2, f2, .normal⟩)
    (h3 : execStmt (k + 5) program m2 f2 (firstStmt (dropStmts 2 stmt)) = .ok ⟨m3, f3, .normal⟩)
    (h4 : execStmt (k + 4) program m3 f3 (firstStmt (dropStmts 3 stmt)) = .ok ⟨m4, f4, .normal⟩) :
    execStmt (k + 8) program m f stmt = execStmt (k + 4) program m4 f4 (dropStmts 4 stmt) := by
  have normal {n s j a af z zf}
      (hs : snapshotTryCheck (n + 1) s = true)
      (hh : execStmt j program a af (firstStmt s) = .ok ⟨z, zf, .normal⟩) :
      execStmt (j + 1) program a af s = execStmt j program z zf (restStmt s) := by
    conv => lhs; rw [(snapshotTryCheck_sequence hs).1]
    exact execSequence_of_normal hh
  have sh1 := (snapshotTryCheck_sequence shape).2
  have sh2 := (snapshotTryCheck_sequence sh1).2
  have sh3 := (snapshotTryCheck_sequence sh2).2
  calc
    _ = execStmt (k + 7) program m1 f1 (dropStmts 1 stmt) := normal shape h1
    _ = execStmt (k + 6) program m2 f2 (dropStmts 2 stmt) := normal sh1 h2
    _ = execStmt (k + 5) program m3 f3 (dropStmts 3 stmt) := normal sh2 h3
    _ = execStmt (k + 4) program m4 f4 (dropStmts 4 stmt) := normal sh3 h4

/-- Executes all four actual source snapshots from physical reached reads.
    No reset success, try-body result or representation is assumed. -/
theorem balanceReset_snapshot_execute {lang m f k}
    (hr : f.receiver = some m.checkerRef)
    (hcontext : objectAt (resetSnapshotState lang m f).1 m.checker.context =
      .ok (resetSnapshotContextObject lang (resetSnapshotState lang m f).1))
    (hcontextFresh : m.checker.context ≠ (resetSnapshotState lang m f).1.nextObject)
    (hfContext : ∀ e ∈ (resetSnapshotState lang m f).1.objects,
      e.1 ≠ (resetSnapshotState lang m f).1.nextObject)
    (hd : lang = .python → localValue (resetSnapshotState lang m f).1
      (resetSnapshotState lang m f).2 "dict" = .ok (.builtin .dict))
    (hhistory : objectAt (resetSnapshotContext lang m f).1 m.checker.history =
      .ok (emptyBalanceHistory lang (resetSnapshotContext lang m f).1))
    (hfHistory : ∀ e ∈ (resetSnapshotContext lang m f).1.objects,
      e.1 ≠ (resetSnapshotContext lang m f).1.nextObject)
    (hc : SnapshotCloneRead lang (resetSnapshotContext lang m f).1 (resetSnapshotContext lang m f).2)
    (hn0 : lang = .python → snapshotAddress m f (snapshotName lang 0) = none)
    (hn1 : lang = .python → snapshotAddress (resetSnapshotState lang m f).1
      (resetSnapshotState lang m f).2 (snapshotName lang 1) = none)
    (hn2 : lang = .python → snapshotAddress (resetSnapshotContext lang m f).1
      (resetSnapshotContext lang m f).2 (snapshotName lang 2) = none) :
    execStmt (k + 8) (balanceProgram lang) m f (balanceResetSnapshots lang) =
      execStmt (k + 4) (balanceProgram lang) (resetSnapshotsInstalled lang m f).1
        (resetSnapshotsInstalled lang m f).2 (dropStmts 4 (balanceResetSnapshots lang)) := by
  let s1 := resetSnapshotState lang m f
  let s2 := resetSnapshotContext lang m f
  let s3 := resetSnapshotHistory lang m f
  have hs := balanceReset_snapshot_heads lang
  have shape := balanceReset_snapshot_shape lang
  change snapshotTryCheck 4 (balanceResetSnapshots lang) = true at shape
  have hp := resetField_depth (lang := lang) (ts := "#state") (py := "__state") hr
    (show readCheckerField m (if lang == .ts then "#state" else "__state") =
      .ok (.string m.checker.state) by cases lang <;> rfl)
  have h1 : execStmt (k + 7) (balanceProgram lang) m f (firstStmt (balanceResetSnapshots lang)) =
      .ok ⟨s1.1, s1.2, .normal⟩ := by
    rw [hs.1]
    exact execSnapshotBind (evalExpr_adequate hp (by omega)) hn0
  have hcopy : evalExpr (k + 5) (balanceProgram lang) s1.1 s1.2 (resetContextCopy lang) =
      .ok ⟨(allocObject s1.1 (resetSnapshotContextObject lang s1.1)).1,
        .ok (.object s1.1.nextObject)⟩ := by
    have hr1 : s1.2.receiver = some s1.1.checkerRef := hr
    cases lang with
    | ts => exact balanceTs_context_copy (k := k + 1) hr1 hcontext hcontextFresh hfContext
    | python => exact resetEmptyContext_copy (k := k + 1) hr1 hcontext hcontextFresh hd
  have h2 : execStmt (k + 6) (balanceProgram lang) s1.1 s1.2
      (firstStmt (dropStmts 1 (balanceResetSnapshots lang))) = .ok ⟨s2.1, s2.2, .normal⟩ := by
    rw [hs.2.1]
    exact execSnapshotBind hcopy hn1
  have h3 : execStmt (k + 5) (balanceProgram lang) s2.1 s2.2
      (firstStmt (dropStmts 2 (balanceResetSnapshots lang))) = .ok ⟨s3.1, s3.2, .normal⟩ := by
    rw [hs.2.2.1]
    exact execSnapshotBind (resetHistory_copy hr hhistory hfHistory hc) hn2
  have h4 : execStmt (k + 4) (balanceProgram lang) s3.1 s3.2
      (firstStmt (dropStmts 3 (balanceResetSnapshots lang))) =
      .ok ⟨(resetSnapshotsInstalled lang m f).1, (resetSnapshotsInstalled lang m f).2, .normal⟩ := by
    rw [hs.2.2.2]
    exact execSnapshotRollback lang s3.1 s3.2 (balanceResetRollback lang) (k + 2)
  exact execFourSnapshots shape h1 h2 h3 h4

/-- The four publication writes are selected after bounds and invariant checks;
    no successful check is assumed by this structural certificate. -/
def resetPublication (lang : TargetLang) : TargetStmt :=
  dropStmts (if lang == .ts then 8 else 7) (balanceResetProtected lang).body

def resetPublicationTemplate (lang : TargetLang) : TargetStmt :=
  .sequence (.assign (.property (resetReceiver lang) (if lang == .ts then "#state" else "__state"))
    (if lang == .ts then .typeCast (.string "Ready") "WorldState" else .local "_INITIAL"))
  (.sequence (.assign (.property (resetReceiver lang) (if lang == .ts then "#context" else "__context")) (.local "candidate"))
  (.sequence (.assign (.property (resetReceiver lang) (if lang == .ts then "#history" else "__history")) (.array .empty))
  (.sequence (.assign (.property (resetReceiver lang) (if lang == .ts then "#undo" else "__undo")) .null) .empty)))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_publication_shape (lang : TargetLang) :
    resetPublication lang = resetPublicationTemplate lang := by
  cases lang <;> unfold resetPublication balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

/-- Publication allocates fresh empty history while preserving the candidate
    reference and the still-held busy bit; the finally block releases it. -/
def resetPublished (lang : TargetLang) (m : TargetMachine) (candidate : ObjRef) : TargetMachine :=
  let state := { m with checker := { m.checker with state := "Ready", context := candidate } }
  let history := (allocObject state (emptyBalanceHistory lang state)).1
  { history with checker := { history.checker with history := state.nextObject, undo := none } }

theorem evalEmptyHistory (lang : TargetLang) (m : TargetMachine) (f : TargetFrame) (k : Nat) :
    evalExpr (k + 2) (balanceProgram lang) m f (.array .empty) =
      .ok ⟨(allocObject m (emptyBalanceHistory lang m)).1, .ok (.object m.nextObject)⟩ := by
  cases lang with
  | python => exact evalPythonEmptyList _ (balanceProgram_lang .python)
  | ts =>
      -- The public TS empty-array equation is obtained by the same private
      -- collection rule as the Python one.
      exact evalEmptyArray _ (balanceProgram_lang .ts)

theorem balanceReset_publication_execute {lang m f candidate k}
    (hr : f.receiver = some m.checkerRef)
    (hc : localValue m f "candidate" = .ok (.object candidate))
    (hi : lang = .python → localValue m f "_INITIAL" = .ok (.string "Ready")) :
    execStmt (k + 8) (balanceProgram lang) m f (resetPublication lang) =
      .ok ⟨resetPublished lang m candidate, f, .normal⟩ := by
  let m1 := { m with checker := { m.checker with state := "Ready" } }
  let m2 := { m1 with checker := { m1.checker with context := candidate } }
  let m3a := (allocObject m2 (emptyBalanceHistory lang m2)).1
  let m3 := { m3a with checker := { m3a.checker with history := m2.nextObject } }
  let m4 := { m3 with checker := { m3.checker with undo := none } }
  have receiver (a : TargetMachine) (ha : a.checkerRef = m.checkerRef) (j : Nat) :
      evalExpr (j + 1) (balanceProgram lang) a f (resetReceiver lang) =
        .ok ⟨a, .ok (.object m.checkerRef)⟩ := by
    have h : localValue a f (if lang == .ts then "this" else "self") = .ok (.object m.checkerRef) := by
      cases lang <;> simp [localValue, hr]
    exact evalExpr_adequate (.localRead h) (by omega)
  have he : evalExpr (k + 6) (balanceProgram lang) m f
      (if lang == .ts then .typeCast (.string "Ready") "WorldState" else .local "_INITIAL") = .ok ⟨m, .ok (.string "Ready")⟩ := by
    cases lang with
    | ts => simp [evalExpr]; rfl
    | python => exact evalExpr_adequate (.localRead (hi rfl)) (by omega)
  have h1 : execStmt (k + 7) (balanceProgram lang) m f
      (.assign (.property (resetReceiver lang) (if lang == .ts then "#state" else "__state"))
        (if lang == .ts then .typeCast (.string "Ready") "WorldState" else .local "_INITIAL")) = .ok ⟨m1, f, .normal⟩ :=
    execCheckerAssign_of_value (final := m) (receiver m rfl _) he (by cases lang <;> rfl)
  have h2 : execStmt (k + 6) (balanceProgram lang) m1 f
      (.assign (.property (resetReceiver lang) (if lang == .ts then "#context" else "__context")) (.local "candidate")) =
      .ok ⟨m2, f, .normal⟩ :=
    execCheckerAssign_of_value (final := m1) (receiver m1 rfl _)
      (evalExpr_adequate (.localRead hc) (by omega)) (by cases lang <;> rfl)
  have h3 : execStmt (k + 5) (balanceProgram lang) m2 f
      (.assign (.property (resetReceiver lang) (if lang == .ts then "#history" else "__history")) (.array .empty)) =
      .ok ⟨m3, f, .normal⟩ :=
    execCheckerAssign_of_value (final := m3a) (receiver m2 rfl _)
      (evalEmptyHistory lang m2 f (k + 2)) (by cases lang <;> rfl)
  have h4 : execStmt (k + 4) (balanceProgram lang) m3 f
      (.assign (.property (resetReceiver lang) (if lang == .ts then "#undo" else "__undo")) .null) =
      .ok ⟨m4, f, .normal⟩ :=
    execCheckerAssign_of_value (final := m3) (receiver m3 rfl _)
      (evalExpr_adequate DepthDerivesExpr.null (by omega)) (by cases lang <;> rfl)
  rw [balanceReset_publication_shape]
  unfold resetPublicationTemplate
  rw [execSequence_of_normal h1, execSequence_of_normal h2, execSequence_of_normal h3,
    execSequence_of_normal h4]
  exact execStmt_adequate .empty (by omega)



/-- Physical receiver binding, proved by the generic reset allocation recipe. -/
theorem balanceResetBodyEntry_receiver (lang : TargetLang) (b : Int) :
    (balanceResetBodyEntry lang b).2.receiver = some (balanceResetBodyEntry lang b).1.checkerRef :=
  receiverCallBody_receiver (balanceConstructorBodyEntry lang b).1 (balanceStoredReset lang).2
    (.object (balancePreparation lang).1.nextObject) (balanceConstructorParam lang)

/-- The real first state snapshot executes for every symbolic seed. Python's
    fresh local address condition is stated separately from receiver binding. -/
theorem balanceReset_state_snapshot_execute {lang m f k}
    (hr : f.receiver = some m.checkerRef)
    (hn : lang = .python → snapshotAddress m f (snapshotName lang 0) = none) :
    execStmt (k + 3) (balanceProgram lang) m f (firstStmt (balanceResetSnapshots lang)) =
      .ok ⟨(resetSnapshotState lang m f).1, (resetSnapshotState lang m f).2, .normal⟩ := by
  rw [(balanceReset_snapshot_heads lang).1]
  have hp := resetField_depth (lang := lang) (ts := "#state") (py := "__state") hr
    (show readCheckerField m (if lang == .ts then "#state" else "__state") =
      .ok (.string m.checker.state) by cases lang <;> rfl)
  exact execSnapshotBind (evalExpr_adequate hp (by omega)) hn


/-- The first protected statement copies actual captured defaults. -/
def resetCandidateExpr (lang : TargetLang) : TargetExpr :=
  if lang == .ts then .object (.objectSpread (.local "contextDefaults") .empty)
  else .call (.local "dict") (.sequence (.local "_DEFAULTS") .empty)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_candidate_shape (lang : TargetLang) :
    firstStmt (balanceResetProtected lang).body = snapshotBindStmt lang "candidate" (resetCandidateExpr lang) := by
  cases lang <;> unfold balanceResetProtected balanceResetSnapshots balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem balanceTs_local_copy {m f name ref b k}
    (hl : localValue (allocObject m (literalObject .ts m)).1 f name = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b))
    (hn : ref ≠ m.nextObject)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    evalExpr (k + 3) (balanceProgram .ts) m f (.object (.objectSpread (.local name) .empty)) =
      .ok ⟨(allocObject m (balanceHeapObject .ts m b)).1, .ok (.object m.nextObject)⟩ := by
  let fresh := (allocObject m (literalObject .ts m)).1
  have he : evalExpr (k + 1) (balanceProgram .ts) fresh f (.local name) =
      .ok ⟨fresh, .ok (.object ref)⟩ := evalExpr_adequate (.localRead hl) (by omega)
  have ho' : objectAt fresh ref = .ok (balanceHeapObject .ts m b) :=
    (objectAt_allocObject_other hn).trans ho
  simp only [evalExpr, balanceProgram_lang]
  change evalObjectFields (k + 2) (balanceProgram .ts) fresh f m.nextObject _ = _
  simp [evalObjectFields, he, ho', balanceHeapObject, balanceDataDescriptor,
    show writeOwn fresh m.nextObject "balance" (integerValue .ts b) =
      .ok (allocObject m (balanceHeapObject .ts m b)).1 from writeOwn_balance_fresh hf,
    List.forIn_cons, List.forIn_nil, Bind.bind, Pure.pure, Except.bind, Except.pure]
  rfl

theorem balanceReset_candidate_ts_execute {m f ref k}
    (hl : localValue (allocObject m (literalObject .ts m)).1 f "contextDefaults" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m 100))
    (hn : ref ≠ m.nextObject)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject) :
    execStmt (k + 4) (balanceProgram .ts) m f (firstStmt (balanceResetProtected .ts).body) =
      .ok ⟨(snapshotBound .ts (allocObject m (balanceHeapObject .ts m 100)).1 f "candidate" (.object m.nextObject)).1,
        (snapshotBound .ts (allocObject m (balanceHeapObject .ts m 100)).1 f "candidate" (.object m.nextObject)).2, .normal⟩ := by
  rw [balanceReset_candidate_shape]
  exact execSnapshotBind (balanceTs_local_copy hl ho hn hf) (fun h => nomatch h)

/-- Python defaults are a mapping proxy; dict copies its own descriptors
    into a mutable ordinary dict and does not retain the proxy prototype. -/
theorem hostDict_balance_proxy {m b ref source}
    (ho : objectAt m ref = .ok source)
    (hk : source.kind = .mappingProxy)
    (hown : source.own = [("balance", balanceDataDescriptor .python b)]) :
    hostCall .python m .dict none [.object ref] =
      .ok ⟨(allocObject m (balanceHeapObject .python m b)).1, .ok (.object m.nextObject)⟩ := by
  unfold hostCall
  dsimp only
  rw [ho]
  dsimp only [Bind.bind, Except.bind]
  rw [hk]
  change (Except.ok ⟨(allocObject m ⟨.pythonDict, none, source.own, [], [], false, false⟩).1,
    .ok (.object m.nextObject)⟩ : Except TargetError ExprOutcome) = _
  rw [hown]
  rfl

theorem balanceReset_candidate_python_execute {m f ref source k}
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (hl : localValue m f "_DEFAULTS" = .ok (.object ref))
    (ho : objectAt m ref = .ok source)
    (hk : source.kind = .mappingProxy)
    (hown : source.own = [("balance", balanceDataDescriptor .python 100)])
    (hn : snapshotAddress m f "candidate" = none) :
    execStmt (k + 4) (balanceProgram .python) m f (firstStmt (balanceResetProtected .python).body) =
      .ok ⟨(snapshotBound .python (allocObject m (balanceHeapObject .python m 100)).1 f "candidate" (.object m.nextObject)).1,
        (snapshotBound .python (allocObject m (balanceHeapObject .python m 100)).1 f "candidate" (.object m.nextObject)).2, .normal⟩ := by
  have he : DepthDerivesExpr (balanceProgram .python) m f
      (.call (.local "dict") (.sequence (.local "_DEFAULTS") .empty))
      ⟨(allocObject m (balanceHeapObject .python m 100)).1, .ok (.object m.nextObject)⟩ 2 :=
    .callBuiltin (.localRead hd) (.cons (.localRead hl) .empty) (by decide)
      (by rw [balanceProgram_lang]; exact hostDict_balance_proxy ho hk hown)
  rw [balanceReset_candidate_shape]
  exact execSnapshotBind (k := k + 3) (evalExpr_adequate he (k := k + 3) (by omega)) (fun _ => hn)

/-- The original next statement and every exit are retained at the body edge. -/
theorem balanceReset_body_first_eq (lang : TargetLang) (k : Nat) (m : TargetMachine) (f : TargetFrame) :
    execStmt (k + 1) (balanceProgram lang) m f (balanceResetProtected lang).body = (do
      let head ← execStmt k (balanceProgram lang) m f (firstStmt (balanceResetProtected lang).body)
      match head.control with
      | .normal => execStmt k (balanceProgram lang) head.machine head.frame (restStmt (balanceResetProtected lang).body)
      | _ => pure head) := by
  have shape : statementSpineCheck ((if lang == .ts then 11 else 10) + 1) (balanceResetProtected lang).body = true := by
    cases lang with
    | ts => exact (balanceReset_body_spine .ts).1
    | python => exact (balanceReset_body_spine .python).1
  conv => lhs; rw [(statementSpineCheck_sequence shape).1]
  exact execSequence_eq _ _ _ _ _ _

/-- Reached canonical reset entry after busy acquisition. Python includes its
    six constructor initialization writes before reset is called. -/
def balanceCanonicalResetEntry (lang : TargetLang) (b : Int) : TargetMachine × TargetFrame :=
  let entry := if lang == .ts then balanceResetBodyEntry lang b else balancePythonResetBodyEntry b
  (balanceSetBusy entry.1 true, entry.2)

/-- Small physical stages; no source body is executed by this selector.
    Stage 3 is after all snapshots and rollback closure installation. -/
def balanceCanonicalResetStage (lang : TargetLang) (b : Int) (i : Nat) : TargetMachine × TargetFrame :=
  let entry := balanceCanonicalResetEntry lang b
  if i == 0 then entry else if i == 1 then resetSnapshotState lang entry.1 entry.2
  else if i == 2 then resetSnapshotContext lang entry.1 entry.2
  else resetSnapshotsInstalled lang entry.1 entry.2

def balanceCanonicalResetPrefixLength (lang : TargetLang) (i : Nat) : Nat :=
  (if lang == .ts then 0 else 2) + (if i < 2 then 0 else if i == 2 then 1 else 2)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Only the seed object's payload varies. These projection equations discard
    stored code before comparing symbolic inputs; no interpreter/AST reduction
    on the integer is used. -/
theorem balanceCanonicalResetStage_footprint (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) :
    let actual := balanceCanonicalResetStage lang b i
    let base := balanceCanonicalResetStage lang 0 i
    actual.1.objects = List.take (balanceCanonicalResetPrefixLength lang i) base.1.objects ++
      ((balancePreparation lang).1.nextObject, balanceHeapObject lang (balancePreparation lang).1 b) :: (balancePreparation lang).1.objects ∧
    actual.2 = base.2 ∧ actual.1.cells = base.1.cells ∧ actual.1.globals = base.1.globals ∧
    actual.1.nextObject = base.1.nextObject ∧ actual.1.objectPrototype = base.1.objectPrototype ∧
    actual.1.checkerRef = base.1.checkerRef ∧ actual.1.checker = base.1.checker ∧
    actual.1.nextCell = base.1.nextCell := by
  cases lang <;> have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rcases this with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lookup_seed_payload {α : Type} (front tail : List (Nat × α))
    (seed ref : Nat) (x y : α) (hn : ref ≠ seed) :
    (front ++ (seed, x) :: tail).lookup ref = (front ++ (seed, y) :: tail).lookup ref := by
  induction front with
  | nil => simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hn]
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      simp only [List.cons_append, List.lookup_cons]
      rw [ih]

/-- All non-seed heap reads are independent of the symbolic seed value. -/
theorem balanceCanonicalResetStage_objectAt (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) (ref : ObjRef)
    (hn : ref ≠ (balancePreparation lang).1.nextObject) :
    objectAt (balanceCanonicalResetStage lang b i).1 ref =
      objectAt (balanceCanonicalResetStage lang 0 i).1 ref := by
  unfold objectAt
  conv => lhs; rw [(balanceCanonicalResetStage_footprint lang b i hi).1]
  conv => rhs; rw [(balanceCanonicalResetStage_footprint lang 0 i hi).1]
  rw [lookup_seed_payload _ _ _ _ _ (balanceHeapObject lang (balancePreparation lang).1 0) hn]

theorem balanceCanonicalResetStage_localValue (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) (name : String) :
    localValue (balanceCanonicalResetStage lang b i).1 (balanceCanonicalResetStage lang b i).2 name =
      localValue (balanceCanonicalResetStage lang 0 i).1 (balanceCanonicalResetStage lang 0 i).2 name := by
  obtain ⟨_, hf, hc, hg, _, _, _, _⟩ := balanceCanonicalResetStage_footprint lang b i hi
  simp only [localValue, readCell, hf, hc, hg]

theorem balanceCanonicalResetStage_address (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) (name : String) :
    snapshotAddress (balanceCanonicalResetStage lang b i).1 (balanceCanonicalResetStage lang b i).2 name =
      snapshotAddress (balanceCanonicalResetStage lang 0 i).1 (balanceCanonicalResetStage lang 0 i).2 name := by
  obtain ⟨_, hf, _, hg, _, _, _, _⟩ := balanceCanonicalResetStage_footprint lang b i hi
  simp only [snapshotAddress, hf, hg]

theorem balanceCanonicalResetStage_keys (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) :
    (balanceCanonicalResetStage lang b i).1.objects.map Prod.fst =
      (balanceCanonicalResetStage lang 0 i).1.objects.map Prod.fst := by
  conv => lhs; rw [(balanceCanonicalResetStage_footprint lang b i hi).1]
  conv => rhs; rw [(balanceCanonicalResetStage_footprint lang 0 i hi).1]
  simp only [List.map_append, List.map_cons]

/-- The Python copy module has this one physical host descriptor. -/
def balanceCopyModuleObject : HeapObject :=
  ⟨.jsOrdinary, some 0,
    [("deepcopy", ⟨some (.builtin .deepCopy), none, none, true, true, true⟩)], [], [], false, false⟩

theorem balanceCopyModule_read {m : TargetMachine} (hc : (2 == m.checkerRef) = false)
    (ho : objectAt m 2 = .ok balanceCopyModuleObject) :
    readPropertyValue .python m (.object 2) "deepcopy" = .ok ⟨m, .ok (.builtin .deepCopy)⟩ := by
  simp [readPropertyValue, hc, ho, balanceCopyModuleObject, readOwn, List.lookup,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  rfl

/-- Only primitive physical observations occur in this check. In particular,
    no equality compares complete machines or stored source bodies. -/
def balanceResetPhysicalCheck (lang : TargetLang) (b : Int) : Prop :=
  let e := balanceCanonicalResetStage lang b 0
  let s := balanceCanonicalResetStage lang b 1
  let c := balanceCanonicalResetStage lang b 2
  let ready := balanceCanonicalResetStage lang b 3
  objectAt s.1 e.1.checker.context = .ok (resetSnapshotContextObject lang s.1) ∧
  e.1.checker.context ≠ s.1.nextObject ∧
  s.1.objects.all (fun x => x.1 != s.1.nextObject) = true ∧
  (lang = .python → localValue s.1 s.2 "dict" = .ok (.builtin .dict)) ∧
  objectAt c.1 e.1.checker.history = .ok (emptyBalanceHistory lang c.1) ∧
  c.1.objects.all (fun x => x.1 != c.1.nextObject) = true ∧
  (if lang == .ts then localValue c.1 c.2 "structuredClone" = .ok (.builtin .structuredClone)
   else localValue c.1 c.2 "copy" = .ok (.object 2) ∧
     objectAt c.1 2 = .ok balanceCopyModuleObject ∧ (2 == c.1.checkerRef) = false) ∧
  (lang = .python → snapshotAddress e.1 e.2 (snapshotName lang 0) = none) ∧
  (lang = .python → snapshotAddress s.1 s.2 (snapshotName lang 1) = none) ∧
  (lang = .python → snapshotAddress c.1 c.2 (snapshotName lang 2) = none) ∧
  ready.1.objects.all (fun x => x.1 != ready.1.nextObject) = true

instance (lang : TargetLang) (b : Int) : Decidable (balanceResetPhysicalCheck lang b) := by
  unfold balanceResetPhysicalCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceResetPhysicalCheck_zero (lang : TargetLang) :
    balanceResetPhysicalCheck lang 0 := by
  cases lang <;> unfold balanceResetPhysicalCheck balanceCanonicalResetStage
    balanceCanonicalResetEntry balanceResetBodyEntry balancePythonResetBodyEntry
    balanceConstructorBodyEntry balanceConstructorBoundEntry balanceConstructorArgumentEntry
    balanceStoredReset balanceResetLookup balanceStoredConstructor balanceConstructorLookup
    balanceConstructorName balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

/-- A seed address never aliases any constructor snapshot read. -/
def balanceResetNonSeedCheck (lang : TargetLang) : Prop :=
  let e := balanceCanonicalResetStage lang 0 0
  e.1.checker.context ≠ (balancePreparation lang).1.nextObject ∧
  e.1.checker.history ≠ (balancePreparation lang).1.nextObject ∧
  2 ≠ (balancePreparation lang).1.nextObject

instance (lang : TargetLang) : Decidable (balanceResetNonSeedCheck lang) := by
  unfold balanceResetNonSeedCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceResetNonSeedCheck_true (lang : TargetLang) : balanceResetNonSeedCheck lang := by
  cases lang <;> unfold balanceResetNonSeedCheck balanceCanonicalResetStage
    balanceCanonicalResetEntry balanceResetBodyEntry balancePythonResetBodyEntry
    balanceConstructorBodyEntry balanceConstructorBoundEntry balanceConstructorArgumentEntry
    balanceStoredReset balanceResetLookup balanceStoredConstructor balanceConstructorLookup
    balanceConstructorName balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

/-- The freshness predicate inspects addresses, never descriptor payloads. -/
theorem balanceCanonicalResetStage_fresh (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) :
    (balanceCanonicalResetStage lang b i).1.objects.all
      (fun x => x.1 != (balanceCanonicalResetStage lang b i).1.nextObject) =
    (balanceCanonicalResetStage lang 0 i).1.objects.all
      (fun x => x.1 != (balanceCanonicalResetStage lang 0 i).1.nextObject) := by
  have hkeys := balanceCanonicalResetStage_keys lang b i hi
  have hn := (balanceCanonicalResetStage_footprint lang b i hi).2.2.2.2.1
  rw [hn]
  have hm (xs : List (ObjRef × HeapObject)) (n : ObjRef) :
      xs.all (fun x => x.1 != n) = (xs.map Prod.fst).all (fun x => x != n) := by
    simp only [List.all_map]
    rfl
  rw [hm, hm, hkeys]

theorem balanceResetPhysicalCheck_all (lang : TargetLang) (b : Int) :
    balanceResetPhysicalCheck lang b := by
  have h0 := balanceResetPhysicalCheck_zero lang
  have hn := balanceResetNonSeedCheck_true lang
  unfold balanceResetNonSeedCheck at hn
  unfold balanceResetPhysicalCheck at h0 ⊢
  dsimp only at h0 ⊢
  have hc := (balanceCanonicalResetStage_footprint lang b 0 (by decide)).2.2.2.2.2.2.2.1
  have hp1 := (balanceCanonicalResetStage_footprint lang b 1 (by decide)).2.2.2.2.2.1
  have hp2 := (balanceCanonicalResetStage_footprint lang b 2 (by decide)).2.2.2.2.2.1
  rw [balanceCanonicalResetStage_fresh lang b 1 (by decide),
    balanceCanonicalResetStage_fresh lang b 2 (by decide),
    balanceCanonicalResetStage_fresh lang b 3 (by decide)]
  simp only [hc, resetSnapshotContextObject, balanceHeapObject, literalObject,
    emptyBalanceHistory, hp1, hp2,
    balanceCanonicalResetStage_localValue lang b 1 (by decide),
    balanceCanonicalResetStage_localValue lang b 2 (by decide),
    balanceCanonicalResetStage_address lang b 0 (by decide),
    balanceCanonicalResetStage_address lang b 1 (by decide),
    balanceCanonicalResetStage_address lang b 2 (by decide),
    balanceCanonicalResetStage_fresh lang b 1 (by decide),
    balanceCanonicalResetStage_fresh lang b 2 (by decide),
    balanceCanonicalResetStage_fresh lang b 3 (by decide),
    balanceCanonicalResetStage_objectAt lang b 1 (by decide) _ hn.1,
    balanceCanonicalResetStage_objectAt lang b 2 (by decide) _ hn.2.1,
    balanceCanonicalResetStage_objectAt lang b 2 (by decide) _ hn.2.2,
    (balanceCanonicalResetStage_footprint lang b 1 (by decide)).2.2.2.2.1,
    (balanceCanonicalResetStage_footprint lang b 2 (by decide)).2.2.2.2.2.2.1]
  simpa only [resetSnapshotContextObject, balanceHeapObject, literalObject, emptyBalanceHistory] using h0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceCanonicalResetEntry_receiver_zero (lang : TargetLang) :
    (balanceCanonicalResetStage lang 0 0).2.receiver =
      some (balanceCanonicalResetStage lang 0 0).1.checkerRef := by
  cases lang <;> unfold balanceCanonicalResetStage balanceCanonicalResetEntry
    balanceResetBodyEntry balancePythonResetBodyEntry balanceConstructorBodyEntry
    balanceConstructorBoundEntry balanceConstructorArgumentEntry balanceStoredReset
    balanceResetLookup balanceStoredConstructor balanceConstructorLookup balanceConstructorName balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem balanceCanonicalResetEntry_receiver (lang : TargetLang) (b : Int) :
    (balanceCanonicalResetStage lang b 0).2.receiver =
      some (balanceCanonicalResetStage lang b 0).1.checkerRef := by
  rw [(balanceCanonicalResetStage_footprint lang b 0 (by decide)).2.1,
    (balanceCanonicalResetStage_footprint lang b 0 (by decide)).2.2.2.2.2.2.1]
  exact balanceCanonicalResetEntry_receiver_zero lang

theorem objects_all_fresh {m : TargetMachine}
    (h : m.objects.all (fun x => x.1 != m.nextObject) = true) :
    ∀ e ∈ m.objects, e.1 ≠ m.nextObject := by
  intro e he
  simpa using (List.all_eq_true.mp h e he)

theorem snapshotCloneRead_of_physical {lang m f}
    (hc : if lang == .ts then localValue m f "structuredClone" = .ok (.builtin .structuredClone)
      else localValue m f "copy" = .ok (.object 2) ∧
        objectAt m 2 = .ok balanceCopyModuleObject ∧ (2 == m.checkerRef) = false) :
    SnapshotCloneRead lang m f := by
  cases lang with
  | ts => exact hc
  | python => exact ⟨.object 2, hc.1, balanceCopyModule_read hc.2.2 hc.2.1⟩

/-- All snapshot premises are discharged from actual constructor provenance,
    uniformly in b (and hence for every bounded balance). -/
theorem balanceReset_canonical_snapshot_execute (lang : TargetLang) (b : Int) (k : Nat) :
    let e := balanceCanonicalResetEntry lang b
    execStmt (k + 8) (balanceProgram lang) e.1 e.2 (balanceResetSnapshots lang) =
      execStmt (k + 4) (balanceProgram lang)
        (balanceCanonicalResetStage lang b 3).1 (balanceCanonicalResetStage lang b 3).2
        (dropStmts 4 (balanceResetSnapshots lang)) := by
  obtain ⟨hcontext, hn, hf, hd, hhistory, hhf, hc, hn0, hn1, hn2, _⟩ :=
    balanceResetPhysicalCheck_all lang b
  exact balanceReset_snapshot_execute (balanceCanonicalResetEntry_receiver lang b)
    hcontext hn (objects_all_fresh hf) hd hhistory (objects_all_fresh hhf) (snapshotCloneRead_of_physical hc) hn0 hn1 hn2

/-- Fixed source defaults, including Python's real proxy prototype and freeze bit. -/
def balanceResetDefaultsRef (lang : TargetLang) : ObjRef := if lang == .ts then 17 else 68

def balanceResetDefaultsObject (lang : TargetLang) : HeapObject :=
  if lang == .ts then balanceHeapObject .ts (balancePreparation lang).1 100
  else ⟨.mappingProxy, some 67, [("balance", balanceDataDescriptor .python 100)], [], [], true, false⟩

def balanceResetCandidatePhysicalCheck (lang : TargetLang) (b : Int) : Prop :=
  let e := balanceCanonicalResetStage lang b 3
  localValue e.1 e.2 (if lang == .ts then "contextDefaults" else "_DEFAULTS") =
    .ok (.object (balanceResetDefaultsRef lang)) ∧
  objectAt e.1 (balanceResetDefaultsRef lang) = .ok (balanceResetDefaultsObject lang) ∧
  balanceResetDefaultsRef lang ≠ e.1.nextObject ∧
  (lang = .python → localValue e.1 e.2 "dict" = .ok (.builtin .dict)) ∧
  (lang = .python → snapshotAddress e.1 e.2 "candidate" = none)

instance (lang : TargetLang) (b : Int) : Decidable (balanceResetCandidatePhysicalCheck lang b) := by
  unfold balanceResetCandidatePhysicalCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceResetCandidatePhysicalCheck_zero (lang : TargetLang) :
    balanceResetCandidatePhysicalCheck lang 0 ∧
      balanceResetDefaultsRef lang ≠ (balancePreparation lang).1.nextObject ∧
      (balanceCanonicalResetStage lang 0 3).1.objectPrototype = (balancePreparation lang).1.objectPrototype := by
  cases lang <;> unfold balanceResetCandidatePhysicalCheck balanceCanonicalResetStage
    balanceCanonicalResetEntry balanceResetBodyEntry balancePythonResetBodyEntry
    balanceConstructorBodyEntry balanceConstructorBoundEntry balanceConstructorArgumentEntry
    balanceStoredReset balanceResetLookup balanceStoredConstructor balanceConstructorLookup
    balanceConstructorName balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem balanceResetCandidatePhysicalCheck_all (lang : TargetLang) (b : Int) :
    balanceResetCandidatePhysicalCheck lang b := by
  obtain ⟨h0, hn, _⟩ := balanceResetCandidatePhysicalCheck_zero lang
  unfold balanceResetCandidatePhysicalCheck at h0 ⊢
  dsimp only at h0 ⊢
  rw [balanceCanonicalResetStage_localValue lang b 3 (by decide),
    balanceCanonicalResetStage_objectAt lang b 3 (by decide) _ hn,
    (balanceCanonicalResetStage_footprint lang b 3 (by decide)).2.2.2.2.1,
    balanceCanonicalResetStage_localValue lang b 3 (by decide),
    balanceCanonicalResetStage_address lang b 3 (by decide)]
  exact h0

def balanceResetCandidateEntry (lang : TargetLang) (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceCanonicalResetStage lang b 3
  snapshotBound lang (allocObject e.1 (balanceHeapObject lang e.1 100)).1 e.2 "candidate" (.object e.1.nextObject)

theorem localValue_allocObject (m : TargetMachine) (f : TargetFrame) (o : HeapObject) (name : String) :
    localValue (allocObject m o).1 f name = localValue m f name := rfl

theorem balanceReset_candidate_execute {lang m f k}
    (hl : localValue m f (if lang == .ts then "contextDefaults" else "_DEFAULTS") =
      .ok (.object (balanceResetDefaultsRef lang)))
    (ho : objectAt m (balanceResetDefaultsRef lang) = .ok (balanceResetDefaultsObject lang))
    (hn : balanceResetDefaultsRef lang ≠ m.nextObject)
    (hd : lang = .python → localValue m f "dict" = .ok (.builtin .dict))
    (ha : lang = .python → snapshotAddress m f "candidate" = none)
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (hp : m.objectPrototype = (balancePreparation lang).1.objectPrototype) :
    execStmt (k + 4) (balanceProgram lang) m f (firstStmt (balanceResetProtected lang).body) =
      .ok ⟨(snapshotBound lang (allocObject m (balanceHeapObject lang m 100)).1 f "candidate" (.object m.nextObject)).1,
        (snapshotBound lang (allocObject m (balanceHeapObject lang m 100)).1 f "candidate" (.object m.nextObject)).2, .normal⟩ := by
  cases lang with
  | ts =>
      apply balanceReset_candidate_ts_execute (ref := 17)
      · rw [localValue_allocObject]; exact hl
      · simpa only [balanceResetDefaultsRef, balanceResetDefaultsObject, balanceHeapObject, hp] using ho
      · exact hn
      · exact hf
  | python => exact balanceReset_candidate_python_execute (hd rfl) hl ho rfl rfl (ha rfl)

/-- The real defaults copy executes after the canonical snapshots. All physical
    premises have been proved, without a reset-success or representation premise. -/
theorem balanceReset_canonical_candidate_execute (lang : TargetLang) (b : Int) (k : Nat) :
    let e := balanceCanonicalResetStage lang b 3
    execStmt (k + 4) (balanceProgram lang) e.1 e.2
      (firstStmt (balanceResetProtected lang).body) =
      .ok ⟨(balanceResetCandidateEntry lang b).1, (balanceResetCandidateEntry lang b).2, .normal⟩ := by
  obtain ⟨hl, ho, hn, hd, ha⟩ := balanceResetCandidatePhysicalCheck_all lang b
  have hf := objects_all_fresh (balanceResetPhysicalCheck_all lang b).2.2.2.2.2.2.2.2.2.2
  have hp : (balanceCanonicalResetStage lang b 3).1.objectPrototype =
      (balancePreparation lang).1.objectPrototype := by
    rw [(balanceCanonicalResetStage_footprint lang b 3 (by decide)).2.2.2.2.2.1]
    exact (balanceResetCandidatePhysicalCheck_zero lang).2.2
  exact balanceReset_candidate_execute hl ho hn hd ha hf hp

/-- A header deliberately omits branch and loop bodies. Closed certificates
    expose one source node without reducing a symbolic input through its children. -/
inductive ResetMiddleHeader where
  | bind (name : String) (mutable : Bool) (expr : TargetExpr)
  | assign (target : AssignTarget) (expr : TargetExpr)
  | branch (expr : TargetExpr)
  | loop (names : List String) (expr : TargetExpr)
  | other
  deriving DecidableEq, Repr

def resetMiddleHeader : TargetStmt → ResetMiddleHeader
  | .letLocal name mutable expr => .bind name mutable expr
  | .assign target expr => .assign target expr
  | .ifThenElse expr _ _ => .branch expr
  | .forDo names expr _ => .loop names expr
  | _ => .other

def balanceResetMiddleStmt (lang : TargetLang) (i : Nat) : TargetStmt :=
  firstStmt (dropStmts i (balanceResetProtected lang).body)

def resetPythonCtxExpr : TargetExpr :=
  .conditional (.binary .isIdentity (.local "initial_context") .null)
    (resetField .python "#constructorSeed" "__constructor_seed") (.local "initial_context")

def resetSeedPresenceExpr (lang : TargetLang) : TargetExpr :=
  if lang == .ts then
    .orElse (.binary .strictEq (.local "initialContext") .null)
      (.binary .strictEq (.local "initialContext") .undefined)
  else .binary .isNotIdentity (.local "ctx") .null

def resetBoundsCall (lang : TargetLang) : TargetExpr :=
  .call (.property (resetReceiver lang) (if lang == .ts then "checkBounds" else "_bounds"))
    (.sequence (.local "candidate") .empty)

def resetInvariantCall (lang : TargetLang) : TargetExpr :=
  .call (.property (resetReceiver lang) (if lang == .ts then "checkInvariants" else "_invariant"))
    (.sequence (if lang == .ts then .string "Ready" else .local "_INITIAL")
      (.sequence (.local "candidate") .empty))

def resetMiddleExpectedHeaders (lang : TargetLang) : List ResetMiddleHeader :=
  let validation := [
    (if lang == .ts then .bind "invalid" false (resetBoundsCall lang)
     else .assign (.local "invalid") (resetBoundsCall lang)),
    .branch (.local "invalid"),
    (if lang == .ts then .bind "violated" false (resetInvariantCall lang)
     else .assign (.local "violated") (resetInvariantCall lang)),
    .branch (.local "violated")]
  (if lang == .ts then [
    .bind "overrides" true .undefined,
    .branch (resetSeedPresenceExpr lang),
    .loop ["name", "value"] (.call (.property (.local "Object") "entries")
      (.sequence (.local "overrides") .empty))]
   else [.assign (.local "ctx") resetPythonCtxExpr, .branch (resetSeedPresenceExpr lang)]) ++ validation

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
/-- Every middle sibling is selected, including both helper calls and both
    rejection tests. This is source shape, not validation/helper success. -/
theorem balanceReset_middle_shapes (lang : TargetLang) :
    ((List.range (if lang == .ts then 7 else 6)).map
      (fun i => resetMiddleHeader (balanceResetMiddleStmt lang (i + 1)))) =
      resetMiddleExpectedHeaders lang := by
  cases lang <;> unfold balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_middle_entry_shape (lang : TargetLang) :
    balanceResetMiddleStmt lang 1 =
      if lang == .ts then .letLocal "overrides" true .undefined
      else .assign (.local "ctx") resetPythonCtxExpr := by
  cases lang <;> unfold balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

def resetTsOverridesEntry (m : TargetMachine) (f : TargetFrame) : TargetMachine × TargetFrame :=
  ((allocCell m .undefined true).1, { f with locals := ("overrides", m.nextCell) :: f.locals })

theorem balanceReset_ts_overrides_execute (m : TargetMachine) (f : TargetFrame) (k : Nat) :
    execStmt (k + 2) (balanceProgram .ts) m f (balanceResetMiddleStmt .ts 1) =
      .ok ⟨(resetTsOverridesEntry m f).1, (resetTsOverridesEntry m f).2, .normal⟩ := by
  rw [balanceReset_middle_entry_shape]
  exact execStmt_adequate (.letLocal DepthDerivesExpr.undefined) (by omega)

/-- For a supplied object the Python conditional chooses that object, without
    reading the constructor-seed fallback or inspecting any descriptor. -/
theorem resetPythonCtx_execute {m f ref k}
    (hp : localValue m f "initial_context" = .ok (.object ref)) :
    evalExpr (k + 3) (balanceProgram .python) m f resetPythonCtxExpr =
      .ok ⟨m, .ok (.object ref)⟩ := by
  have hb : evalExpr (k + 2) (balanceProgram .python) m f
      (.binary .isIdentity (.local "initial_context") .null) = .ok ⟨m, .ok (.bool false)⟩ :=
    evalExpr_adequate (.binary (by decide) (.localRead hp) .null
      (by rw [balanceProgram_lang]; rfl)) (by omega)
  simp only [resetPythonCtxExpr, evalExpr, hb, balanceProgram_lang,
    sourceTruthy, Bind.bind, Pure.pure, Except.bind, Except.pure]
  simp only [Bool.false_eq_true, if_false, hp]
  rfl

theorem balanceReset_python_ctx_execute {m f ref k}
    (hp : localValue m f "initial_context" = .ok (.object ref))
    (hn : snapshotAddress m f "ctx" = none) :
    execStmt (k + 4) (balanceProgram .python) m f (balanceResetMiddleStmt .python 1) =
      .ok ⟨(snapshotBound .python m f "ctx" (.object ref)).1,
        (snapshotBound .python m f "ctx" (.object ref)).2, .normal⟩ := by
  rw [balanceReset_middle_entry_shape]
  exact execSnapshotBind (lang := .python) (resetPythonCtx_execute hp) (fun _ => hn)

theorem balanceCanonicalResetStage_nextCell (lang : TargetLang) (b : Int)
    (i : Nat) (hi : i ≤ 3) :
    (balanceCanonicalResetStage lang b i).1.nextCell =
      (balanceCanonicalResetStage lang 0 i).1.nextCell :=
  (balanceCanonicalResetStage_footprint lang b i hi).2.2.2.2.2.2.2.2

/-- Compare reads only after projecting away the unused heap/code fields. -/
theorem localValue_fields_congr {m n : TargetMachine} {f g : TargetFrame} {name : String}
    (hf : f = g) (hc : m.cells = n.cells) (hg : m.globals = n.globals) :
    localValue m f name = localValue n g name := by
  unfold localValue readCell
  rw [hf, hc, hg]

theorem snapshotAddress_fields_congr {m n : TargetMachine} {f g : TargetFrame} {name : String}
    (hf : f = g) (hg : m.globals = n.globals) :
    snapshotAddress m f name = snapshotAddress n g name := by
  unfold snapshotAddress
  rw [hf, hg]

theorem candidateBinding_frame_congr {lang m n f g o p}
    (hf : f = g) (hn : m.nextCell = n.nextCell) :
    (snapshotBound lang (allocObject m o).1 f "candidate" (.object m.nextObject)).2 =
      (snapshotBound lang (allocObject n p).1 g "candidate" (.object n.nextObject)).2 := by
  change { f with locals := ("candidate", m.nextCell) :: f.locals } =
    { g with locals := ("candidate", n.nextCell) :: g.locals }
  rw [hf, hn]

theorem candidateBinding_localValue_congr {lang m n f g o p name}
    (hf : f = g) (hc : m.cells = n.cells) (hg : m.globals = n.globals)
    (hn : m.nextCell = n.nextCell) (ho : m.nextObject = n.nextObject) :
    localValue (snapshotBound lang (allocObject m o).1 f "candidate" (.object m.nextObject)).1
      (snapshotBound lang (allocObject m o).1 f "candidate" (.object m.nextObject)).2 name =
    localValue (snapshotBound lang (allocObject n p).1 g "candidate" (.object n.nextObject)).1
      (snapshotBound lang (allocObject n p).1 g "candidate" (.object n.nextObject)).2 name := by
  apply localValue_fields_congr (candidateBinding_frame_congr hf hn)
  · change (m.nextCell, .object m.nextObject) :: m.cells =
      (n.nextCell, .object n.nextObject) :: n.cells
    rw [hn, ho, hc]
  · exact hg

theorem balanceResetCandidateEntry_localValue (lang : TargetLang) (b : Int) (name : String) :
    localValue (balanceResetCandidateEntry lang b).1 (balanceResetCandidateEntry lang b).2 name =
      localValue (balanceResetCandidateEntry lang 0).1 (balanceResetCandidateEntry lang 0).2 name := by
  obtain ⟨_, hf, hc, hg, ho, _, _, _⟩ := balanceCanonicalResetStage_footprint lang b 3 (by decide)
  exact candidateBinding_localValue_congr hf hc hg (balanceCanonicalResetStage_nextCell lang b 3 (by decide)) ho

theorem balanceResetCandidateEntry_address (lang : TargetLang) (b : Int) (name : String) :
    snapshotAddress (balanceResetCandidateEntry lang b).1 (balanceResetCandidateEntry lang b).2 name =
      snapshotAddress (balanceResetCandidateEntry lang 0).1 (balanceResetCandidateEntry lang 0).2 name := by
  obtain ⟨_, hf, _, hg, _, _, _, _⟩ := balanceCanonicalResetStage_footprint lang b 3 (by decide)
  exact snapshotAddress_fields_congr
    (candidateBinding_frame_congr hf (balanceCanonicalResetStage_nextCell lang b 3 (by decide))) hg

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceResetCandidateEntry_parameter_zero (lang : TargetLang) :
    localValue (balanceResetCandidateEntry lang 0).1 (balanceResetCandidateEntry lang 0).2
      (balanceConstructorParam lang) = .ok (.object (balancePreparation lang).1.nextObject) ∧
    (lang = .python → snapshotAddress (balanceResetCandidateEntry lang 0).1
      (balanceResetCandidateEntry lang 0).2 "ctx" = none) := by
  cases lang <;> unfold balanceResetCandidateEntry balanceCanonicalResetStage
    balanceCanonicalResetEntry balanceResetBodyEntry balancePythonResetBodyEntry
    balanceConstructorBodyEntry balanceConstructorBoundEntry balanceConstructorArgumentEntry
    balanceStoredReset balanceResetLookup balanceStoredConstructor balanceConstructorLookup
    balanceConstructorName balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

section CanonicalResetComposition

-- Resource limits only: this section follows the large closed physical
-- certificates. All symbolic steps still use explicit small projections.
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

theorem balanceResetCandidateEntry_parameter (lang : TargetLang) (b : Int) :
    localValue (balanceResetCandidateEntry lang b).1 (balanceResetCandidateEntry lang b).2
      (balanceConstructorParam lang) = .ok (.object (balancePreparation lang).1.nextObject) := by
  rw [balanceResetCandidateEntry_localValue lang b (balanceConstructorParam lang)]
  exact (balanceResetCandidateEntry_parameter_zero lang).1

def balanceResetMiddleEntry (lang : TargetLang) (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceResetCandidateEntry lang b
  if lang == .ts then resetTsOverridesEntry e.1 e.2
  else snapshotBound .python e.1 e.2 "ctx" (.object (balancePreparation lang).1.nextObject)

theorem balanceReset_ts_canonical_overrides_execute (b : Int) (k : Nat) :
    let e := balanceResetCandidateEntry .ts b
    execStmt (k + 2) (balanceProgram .ts) e.1 e.2 (balanceResetMiddleStmt .ts 1) =
      .ok ⟨(balanceResetMiddleEntry .ts b).1, (balanceResetMiddleEntry .ts b).2, .normal⟩ :=
  balanceReset_ts_overrides_execute _ _ _

theorem balanceReset_python_canonical_ctx_execute (b : Int) (k : Nat) :
    let e := balanceResetCandidateEntry .python b
    execStmt (k + 4) (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 1) =
      .ok ⟨(balanceResetMiddleEntry .python b).1, (balanceResetMiddleEntry .python b).2, .normal⟩ := by
  have hp := balanceResetCandidateEntry_parameter .python b
  have ha : snapshotAddress (balanceResetCandidateEntry .python b).1
      (balanceResetCandidateEntry .python b).2 "ctx" = none := by
    rw [balanceResetCandidateEntry_address .python b "ctx"]
    exact (balanceResetCandidateEntry_parameter_zero .python).2 rfl
  exact balanceReset_python_ctx_execute hp ha

/-- The middle prefix leaves the original overlay/validation continuation
    intact. Both normal statements are proved at their actual sibling budgets. -/
theorem balanceReset_canonical_body_prefix_execute (lang : TargetLang) (b : Int) (k : Nat) :
    let e := balanceCanonicalResetStage lang b 3
    execStmt (k + 8) (balanceProgram lang) e.1 e.2 (balanceResetProtected lang).body =
      execStmt (k + 6) (balanceProgram lang)
        (balanceResetMiddleEntry lang b).1 (balanceResetMiddleEntry lang b).2
        (dropStmts 2 (balanceResetProtected lang).body) := by
  dsimp only
  have hs := (balanceReset_body_spine lang).1
  have shape : statementSpineCheck ((if lang == .ts then 10 else 9) + 2)
      (balanceResetProtected lang).body = true := by
    cases lang with
    | ts => exact hs
    | python => exact hs
  have first := statementSpineCheck_sequence shape
  have second := statementSpineCheck_sequence first.2
  have h0 := balanceReset_canonical_candidate_execute lang b (k + 3)
  have h1 : execStmt (k + 6) (balanceProgram lang)
      (balanceResetCandidateEntry lang b).1 (balanceResetCandidateEntry lang b).2
      (balanceResetMiddleStmt lang 1) =
      .ok ⟨(balanceResetMiddleEntry lang b).1, (balanceResetMiddleEntry lang b).2, .normal⟩ := by
    cases lang with
    | ts => exact balanceReset_ts_canonical_overrides_execute b (k + 4)
    | python => exact balanceReset_python_canonical_ctx_execute b (k + 2)
  conv => lhs; rw [first.1]
  rw [execSequence_of_normal h0]
  conv => lhs; rw [second.1]
  exact execSequence_of_normal h1

/-- Caller restoration and the actual post-reset constructor seed-copy suffix
    remain explicit. This continuation does not assert successful reset. -/
def balanceConstructorResetContinuation (lang : TargetLang) (b : Int)
    (resetBody : StmtOutcome) : Except TargetError StmtOutcome := do
  let called ← closureResult lang resetBody
  let head : StmtOutcome := match called.result with
    | .error e => ⟨called.machine, (balanceConstructorBodyEntry lang b).2, .raised e⟩
    | .ok _ => ⟨called.machine, (balanceConstructorBodyEntry lang b).2, .normal⟩
  match head.control with
  | .normal =>
      execStmt (if lang == .ts then 98 else 91) (balanceProgram lang) head.machine head.frame
        (if lang == .ts then restStmt (balanceConstructorBodyTemplate .ts)
         else restStmt balancePythonAfterInit)
  | _ => pure head

/-- Full canonical constructor composition now reaches the protected reset
    subtree after executing the snapshots for every symbolic input. -/
theorem balanceConstructor_canonical_snapshots_eq (lang : TargetLang) (b : Int) :
    execStmt 99 (balanceProgram lang)
      (balanceConstructorBodyEntry lang b).1 (balanceConstructorBodyEntry lang b).2
      (balanceStoredConstructor lang).2.body = (do
      let resetBody ← execStmt (if lang == .ts then 90 else 83) (balanceProgram lang)
        (balanceCanonicalResetStage lang b 3).1 (balanceCanonicalResetStage lang b 3).2
        (dropStmts 4 (balanceResetSnapshots lang))
      balanceConstructorResetContinuation lang b resetBody) := by
  cases lang with
  | ts =>
      have h := balanceReset_canonical_snapshot_execute .ts b 86
      change execStmt 94 (balanceProgram .ts)
        (balanceSetBusy (balanceResetBodyEntry .ts b).1 true) (balanceResetBodyEntry .ts b).2
        (restStmt (restStmt (balanceStoredReset .ts).2.body)) = _ at h
      rw [balanceConstructor_ts_snapshots_eq b, h]
      rfl
  | python =>
      have h := balanceReset_canonical_snapshot_execute .python b 79
      change execStmt 87 (balanceProgram .python)
        (balanceSetBusy (balancePythonResetBodyEntry b).1 true) (balancePythonResetBodyEntry b).2
        (restStmt (restStmt (balanceStoredReset .python).2.body)) = _ at h
      rw [balanceConstructor_python_snapshots_eq b, h]
      rfl

/-- Successful execution of the still-open protected body is followed by the
    actual finally block. This conditional lemma does not supply body success. -/
theorem balanceReset_protected_normal {lang m f final ff k}
    (hb : execStmt (k + 4) (balanceProgram lang) m f (balanceResetProtected lang).body =
      .ok ⟨final, ff, .normal⟩)
    (hr : ff.receiver = some final.checkerRef) :
    execStmt (k + 5) (balanceProgram lang) m f (balanceResetProtected lang).stmt =
      .ok ⟨balanceSetBusy final false, ff, .normal⟩ := by
  rw [execProtectedSyntax_eq (k + 4) (balanceProgram lang) m f (balanceResetProtected lang), hb]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [balanceReset_cleanup_execute (lang := lang) (m := final) (f := ff) (k := k + 4) hr (by omega)]

/-- Canonical snapshots, source try body and finally compose. The sole semantic
    execution premise is the remaining protected body, kept explicit. -/
theorem balanceReset_canonical_snapshots_normal {lang b final ff k}
    (hb : execStmt (k + 4) (balanceProgram lang)
      (balanceCanonicalResetStage lang b 3).1 (balanceCanonicalResetStage lang b 3).2
      (balanceResetProtected lang).body = .ok ⟨final, ff, .normal⟩)
    (hr : ff.receiver = some final.checkerRef) :
    let e := balanceCanonicalResetEntry lang b
    execStmt (k + 10) (balanceProgram lang) e.1 e.2 (balanceResetSnapshots lang) =
      .ok ⟨balanceSetBusy final false, ff, .normal⟩ := by
  dsimp only
  rw [balanceReset_canonical_snapshot_execute lang b (k + 2)]
  have hs : dropStmts 4 (balanceResetSnapshots lang) =
      .sequence (balanceResetProtected lang).stmt .empty := balanceReset_protected_shape lang
  rw [hs, execSequence_of_normal (balanceReset_protected_normal hb hr)]
  exact execStmt_adequate .empty (by omega)

def ifNoStmt : TargetStmt → TargetStmt
  | .ifThenElse _ _ no => no
  | _ => .empty

theorem resetMiddleHeader_branch_shape {stmt expr}
    (h : resetMiddleHeader stmt = .branch expr) :
    stmt = .ifThenElse expr (ifYesStmt stmt) (ifNoStmt stmt) := by
  cases stmt <;> simp_all [resetMiddleHeader, ifYesStmt, ifNoStmt]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_seed_presence_header (lang : TargetLang) :
    resetMiddleHeader (balanceResetMiddleStmt lang 2) = .branch (resetSeedPresenceExpr lang) := by
  cases lang <;> unfold balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

/-- Presence testing uses the supplied object's identity, independently of its
    balance descriptor. The branches still contain all actual overlay code. -/
theorem resetSeedPresence_execute {lang m f ref k}
    (hp : localValue m f (if lang == .ts then "initialContext" else "ctx") = .ok (.object ref)) :
    evalExpr (k + 4) (balanceProgram lang) m f (resetSeedPresenceExpr lang) =
      .ok ⟨m, .ok (.bool (lang != .ts))⟩ := by
  cases lang with
  | ts =>
      change localValue m f "initialContext" = .ok (.object ref) at hp
      have hnull : evalExpr (k + 3) (balanceProgram .ts) m f
          (.binary .strictEq (.local "initialContext") .null) = .ok ⟨m, .ok (.bool false)⟩ :=
        evalExpr_adequate (.binary (by decide) (.localRead hp) .null
          (by rw [balanceProgram_lang]; rfl)) (by omega)
      have hundefined : evalExpr (k + 3) (balanceProgram .ts) m f
          (.binary .strictEq (.local "initialContext") .undefined) = .ok ⟨m, .ok (.bool false)⟩ :=
        evalExpr_adequate (.binary (by decide) (.localRead hp) .undefined
          (by rw [balanceProgram_lang]; rfl)) (by omega)
      change evalExpr (k + 4) (balanceProgram .ts) m f
        (.orElse (.binary .strictEq (.local "initialContext") .null)
          (.binary .strictEq (.local "initialContext") .undefined)) = _
      rw [evalExpr, hnull]
      simpa only [Bind.bind, Except.bind, Pure.pure, Except.pure, sourceTruthy,
        Bool.false_eq_true, if_false] using hundefined
  | python =>
      change localValue m f "ctx" = .ok (.object ref) at hp
      exact evalExpr_adequate (.binary (by decide) (.localRead hp) .null
        (by rw [balanceProgram_lang]; rfl)) (by omega)

theorem balanceReset_ts_seed_present {m f ref k}
    (hp : localValue m f "initialContext" = .ok (.object ref)) :
    execStmt (k + 5) (balanceProgram .ts) m f (balanceResetMiddleStmt .ts 2) =
      execStmt (k + 4) (balanceProgram .ts) m f (ifNoStmt (balanceResetMiddleStmt .ts 2)) := by
  conv => lhs; rw [resetMiddleHeader_branch_shape (balanceReset_seed_presence_header .ts)]
  exact execIf_of_false (resetSeedPresence_execute (lang := .ts) hp) rfl

theorem balanceReset_python_seed_present {m f ref k}
    (hp : localValue m f "ctx" = .ok (.object ref)) :
    execStmt (k + 5) (balanceProgram .python) m f (balanceResetMiddleStmt .python 2) =
      execStmt (k + 4) (balanceProgram .python) m f (ifYesStmt (balanceResetMiddleStmt .python 2)) := by
  conv => lhs; rw [resetMiddleHeader_branch_shape (balanceReset_seed_presence_header .python)]
  rw [execStmt, resetSeedPresence_execute (lang := .python) hp]
  rfl

/-- The nested Python plain-dict guard is selected without its throw body. -/
def resetPythonPlainGuardExpr : TargetExpr :=
  .binary .isNotIdentity (.call (.local "type") (.sequence (.local "ctx") .empty)) (.local "dict")

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_python_plain_guard_header :
    resetMiddleHeader (firstStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) =
      .branch resetPythonPlainGuardExpr := by
  unfold balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

theorem resetPythonPlainGuard_execute {m f ref object k}
    (hp : localValue m f "ctx" = .ok (.object ref))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m ref = .ok object) (hk : object.kind = .pythonDict) :
    evalExpr (k + 4) (balanceProgram .python) m f resetPythonPlainGuardExpr =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have htype : DepthDerivesExpr (balanceProgram .python) m f
      (.call (.local "type") (.sequence (.local "ctx") .empty))
      ⟨m, .ok (.builtin .dict)⟩ 2 := by
    apply DepthDerivesExpr.callBuiltin (.localRead ht) (.cons (.localRead hp) .empty) (by decide)
    rw [balanceProgram_lang]
    unfold hostCall
    dsimp only
    rw [ho]
    dsimp only [Bind.bind, Except.bind]
    rw [hk]
    rfl
  exact evalExpr_adequate (.binary (by decide) htype (.localRead hd)
    (by rw [balanceProgram_lang]; rfl)) (by omega)

end CanonicalResetComposition

end Harmonia.Applications.Kadmos.Generated
