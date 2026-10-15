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

/-- Select the actual overlay loop without reducing its body during execution. -/
def resetLoopBody : TargetStmt → TargetStmt
  | .forDo _ _ body => body
  | _ => .empty

def balanceResetOverlayLoop (lang : TargetLang) : TargetStmt :=
  if lang == .ts then balanceResetMiddleStmt .ts 3
  else firstStmt (restStmt (ifYesStmt (balanceResetMiddleStmt .python 2)))

def resetPythonOverlayStringTest : TargetExpr :=
  .binary .eq
    (.index (.index (.index (.local "_WORLD") (.string "context")) (.local "name")) (.string "type"))
    (.string "string")

def resetOverlayValue (lang : TargetLang) : TargetExpr :=
  if lang == .ts then .typeCast (.local "value") "string|number"
  else .conditional resetPythonOverlayStringTest (.local "value")
    (.call (.local "int") (.sequence (.local "value") .empty))

def balanceResetOverlayWrite (lang : TargetLang) : TargetStmt :=
  firstStmt (dropStmts (if lang == .ts then 1 else 2)
    (resetLoopBody (balanceResetOverlayLoop lang)))

/-- Closed source certificates retain the TS cast and Python int conversion. -/
theorem balanceReset_overlay_write_shape (lang : TargetLang) :
    balanceResetOverlayWrite lang =
      .assign (.index (.local "candidate") (.local "name")) (resetOverlayValue lang) := by
  cases lang <;> unfold balanceResetOverlayWrite balanceResetOverlayLoop
    balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem balanceReset_python_plain_guard_shape :
    firstStmt (ifYesStmt (balanceResetMiddleStmt .python 2)) =
      .ifThenElse resetPythonPlainGuardExpr
        (ifYesStmt (firstStmt (ifYesStmt (balanceResetMiddleStmt .python 2)))) .empty ∧
    ifYesStmt (balanceResetMiddleStmt .python 2) =
      .sequence (firstStmt (ifYesStmt (balanceResetMiddleStmt .python 2)))
        (restStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) := by
  unfold balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- Execute the guard statement, including its empty false branch, then expose
    the actual loop continuation at its predecessor sibling budget. -/
theorem balanceReset_python_plain_guard_skip {m f ref object k}
    (hp : localValue m f "ctx" = .ok (.object ref))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (ho : objectAt m ref = .ok object) (hk : object.kind = .pythonDict) :
    execStmt (k + 6) (balanceProgram .python) m f
      (ifYesStmt (balanceResetMiddleStmt .python 2)) =
    execStmt (k + 5) (balanceProgram .python) m f
      (restStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) := by
  have head : execStmt (k + 5) (balanceProgram .python) m f
      (firstStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) = .ok ⟨m, f, .normal⟩ := by
    rw [balanceReset_python_plain_guard_shape.1,
      execIf_of_false (resetPythonPlainGuard_execute hp ht hd ho hk) rfl]
    exact execStmt_adequate .empty (by omega)
  conv => lhs; rw [balanceReset_python_plain_guard_shape.2]
  exact execSequence_of_normal head

/-- Rejection sites are exact source branches with empty false arms. This
    certificate does not assume or establish either validation call result. -/
theorem balanceReset_validation_rejection_shape (lang : TargetLang) (invariant : Bool) :
    let i := if invariant then (if lang == .ts then 7 else 6) else (if lang == .ts then 5 else 4)
    balanceResetMiddleStmt lang i =
      .ifThenElse (.local (if invariant then "violated" else "invalid"))
        (ifYesStmt (balanceResetMiddleStmt lang i)) .empty := by
  cases lang <;> cases invariant <;> unfold balanceResetMiddleStmt
    balanceResetProtected balanceResetSnapshots balanceStoredReset balanceResetLookup balancePreparation
  all_goals first
    | (rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel)
    | (rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel)

theorem balanceReset_validation_rejection_execute {lang m f k} (invariant : Bool)
    (hv : localValue m f (if invariant then "violated" else "invalid") = .ok .null) :
    let i := if invariant then (if lang == .ts then 7 else 6) else (if lang == .ts then 5 else 4)
    execStmt (k + 2) (balanceProgram lang) m f (balanceResetMiddleStmt lang i) =
      .ok ⟨m, f, .normal⟩ := by
  dsimp only
  rw [balanceReset_validation_rejection_shape]
  rw [execIf_of_false (evalExpr_adequate (.localRead hv) (by omega))
    (by cases lang <;> rfl)]
  exact execStmt_adequate .empty (by omega)

/-- TS validation success uses undefined in the emitted source. Its false
    branch has the same no-op behavior as Python's null result. -/
theorem balanceReset_ts_validation_rejection_undefined {m f k} (invariant : Bool)
    (hv : localValue m f (if invariant then "violated" else "invalid") = .ok .undefined) :
    let i := if invariant then 7 else 5
    execStmt (k + 2) (balanceProgram .ts) m f (balanceResetMiddleStmt .ts i) =
      .ok ⟨m, f, .normal⟩ := by
  dsimp only
  have hs := balanceReset_validation_rejection_shape .ts invariant
  change balanceResetMiddleStmt .ts (if invariant then 7 else 5) = _ at hs
  rw [hs]
  rw [execIf_of_false (evalExpr_adequate (.localRead hv) (by omega)) rfl]
  exact execStmt_adequate .empty (by omega)

/-- The candidate update preserves allocation, cells and code, replacing only
    the selected object's own balance descriptor. No freshness assumption is
    needed for an already allocated writable candidate. -/
def balanceOverlayUpdated (lang : TargetLang) (m : TargetMachine) (ref : ObjRef)
    (b : Int) : TargetMachine :=
  { m with objects := m.objects.map fun entry =>
      (entry.1, if entry.1 == ref then balanceHeapObject lang m b else entry.2) }

theorem writeOwn_balance_existing {lang m ref old b}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old)) :
    writeOwn m ref "balance" (integerValue lang b) =
      .ok (balanceOverlayUpdated lang m ref b) := by
  cases lang <;>
    simp [writeOwn, ho, balanceHeapObject, balanceDataDescriptor, replaceObject,
      balanceOverlayUpdated, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem lookup_replace_payload {α : Type} (entries : List (Nat × α)) (ref : Nat) (value : α) :
    (entries.map (fun entry => (entry.1, if entry.1 == ref then value else entry.2))).lookup ref =
      (entries.lookup ref).map (fun _ => value) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, old⟩
      by_cases h : key = ref
      · subst key; simp
      · have heq : (ref == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
        have hkey : (key == ref) = false := beq_eq_false_iff_ne.mpr h
        simp only [List.map_cons, List.lookup_cons, Prod.fst, Prod.snd, heq, hkey, if_false, ih]

/-- The update has a live candidate with exactly the supplied balance. -/
theorem balanceOverlayUpdated_objectAt {lang m ref old b}
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old)) :
    objectAt (balanceOverlayUpdated lang m ref b) ref =
      .ok (balanceHeapObject lang m b) := by
  unfold objectAt at ho ⊢
  change (match (m.objects.map (fun entry =>
    (entry.1, if entry.1 == ref then balanceHeapObject lang m b else entry.2))).lookup ref with
    | some o => Except.ok o | none => Except.error (TargetError.danglingObject ref)) = _
  rw [lookup_replace_payload]
  cases hl : m.objects.lookup ref with
  | none => simp [hl] at ho
  | some value => rfl

/-- Execute TS's selected indexed write for a symbolic integer; the heap write
    is kept explicit so its descriptor/freshness proof can be reused. -/
theorem balanceReset_overlay_write_ts_execute {m final f ref b k}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hv : localValue m f "value" = .ok (integerValue .ts b))
    (hw : writeOwn m ref "balance" (integerValue .ts b) = .ok final) :
    execStmt (k + 3) (balanceProgram .ts) m f (balanceResetOverlayWrite .ts) =
      .ok ⟨final, f, .normal⟩ := by
  rw [balanceReset_overlay_write_shape]
  have value : evalExpr (k + 2) (balanceProgram .ts) m f (resetOverlayValue .ts) =
      .ok ⟨m, .ok (integerValue .ts b)⟩ := by
    change evalExpr (k + 2) _ _ _ (.typeCast (.local "value") "string|number") = _
    rw [evalExpr]
    exact evalExpr_adequate (.localRead hv) (by omega)
  rw [execStmt]
  have c := evalExpr_adequate (program := balanceProgram .ts) (.localRead hc) (k := k + 2) (by omega)
  have n := evalExpr_adequate (program := balanceProgram .ts) (.localRead hn) (k := k + 2) (by omega)
  simp only [c, n, value, hw, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Python's selected write takes the integer arm and calls the real int host.
    The context-definition lookup is explicit, not silently treated as trusted. -/
theorem balanceReset_overlay_write_python_execute {m final f ref b k}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hi : localValue m f "int" = .ok (.builtin .int))
    (ht : evalExpr (k + 5) (balanceProgram .python) m f resetPythonOverlayStringTest =
      .ok ⟨m, .ok (.bool false)⟩)
    (hb : b.natAbs ≤ 9007199254740991)
    (hw : writeOwn m ref "balance" (integerValue .python b) = .ok final) :
    execStmt (k + 7) (balanceProgram .python) m f (balanceResetOverlayWrite .python) =
      .ok ⟨final, f, .normal⟩ := by
  have call : evalExpr (k + 5) (balanceProgram .python) m f
      (.call (.local "int") (.sequence (.local "value") .empty)) =
        .ok ⟨m, .ok (integerValue .python b)⟩ := by
    apply evalExpr_adequate (DepthDerivesExpr.callBuiltin (.localRead hi)
      (.cons (.localRead hv) .empty) (by decide) ?_) (by omega)
    rw [balanceProgram_lang]
    change (if !(decide (b.natAbs ≤ 9007199254740991)) then
      Except.error TargetError.outsideNumericDomain else
      Except.ok (⟨m, .ok (integerValue .python b)⟩ : ExprOutcome)) = _
    simp only [hb, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
  have value : evalExpr (k + 6) (balanceProgram .python) m f (resetOverlayValue .python) =
      .ok ⟨m, .ok (integerValue .python b)⟩ := by
    change evalExpr (k + 6) _ _ _ (.conditional _ _ _) = _
    rw [evalExpr, ht]
    simpa only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      balanceProgram_lang, sourceTruthy, Bool.false_eq_true, if_false] using call
  rw [balanceReset_overlay_write_shape]
  rw [execStmt]
  have c := evalExpr_adequate (program := balanceProgram .python) (.localRead hc) (k := k + 6) (by omega)
  have n := evalExpr_adequate (program := balanceProgram .python) (.localRead hn) (k := k + 6) (by omega)
  simp only [c, n, value, hw, Bind.bind, Except.bind, Pure.pure, Except.pure]


theorem resetBinding_localValue_congr {lang m n f g name boundName value}
    (hf : f = g) (hc : m.cells = n.cells) (hg : m.globals = n.globals)
    (hn : m.nextCell = n.nextCell) :
    localValue (snapshotBound lang m f boundName value).1
      (snapshotBound lang m f boundName value).2 name =
    localValue (snapshotBound lang n g boundName value).1
      (snapshotBound lang n g boundName value).2 name := by
  apply localValue_fields_congr
  · change { f with locals := (boundName, m.nextCell) :: f.locals } =
      { g with locals := (boundName, n.nextCell) :: g.locals }
    rw [hf, hn]
  · change (m.nextCell, value) :: m.cells = (n.nextCell, value) :: n.cells
    rw [hn, hc]
  · exact hg

theorem resetTsOverridesEntry_localValue_congr {m n f g name}
    (hf : f = g) (hc : m.cells = n.cells) (hg : m.globals = n.globals)
    (hn : m.nextCell = n.nextCell) :
    localValue (resetTsOverridesEntry m f).1 (resetTsOverridesEntry m f).2 name =
    localValue (resetTsOverridesEntry n g).1 (resetTsOverridesEntry n g).2 name := by
  apply localValue_fields_congr
  · change { f with locals := ("overrides", m.nextCell) :: f.locals } =
      { g with locals := ("overrides", n.nextCell) :: g.locals }
    rw [hf, hn]
  · change (m.nextCell, TargetValue.undefined) :: m.cells =
      (n.nextCell, TargetValue.undefined) :: n.cells
    rw [hn, hc]
  · exact hg

/-- The middle binding changes only cells and the frame; its reads are
    independent of the seed descriptor's symbolic integer payload. -/
theorem balanceResetMiddleEntry_localValue (lang : TargetLang) (b : Int) (name : String) :
    localValue (balanceResetMiddleEntry lang b).1 (balanceResetMiddleEntry lang b).2 name =
      localValue (balanceResetMiddleEntry lang 0).1 (balanceResetMiddleEntry lang 0).2 name := by
  have hs := balanceCanonicalResetStage_footprint lang b 3 (by decide)
  have hn := balanceCanonicalResetStage_nextCell lang b 3 (by decide)
  have hf : (balanceResetCandidateEntry lang b).2 = (balanceResetCandidateEntry lang 0).2 :=
    candidateBinding_frame_congr hs.2.1 hn
  have hnc : (balanceResetCandidateEntry lang b).1.nextCell =
      (balanceResetCandidateEntry lang 0).1.nextCell := by
    change (balanceCanonicalResetStage lang b 3).1.nextCell + 1 =
      (balanceCanonicalResetStage lang 0 3).1.nextCell + 1
    rw [hn]
  have hc : (balanceResetCandidateEntry lang b).1.cells =
      (balanceResetCandidateEntry lang 0).1.cells := by
    change ((balanceCanonicalResetStage lang b 3).1.nextCell,
        TargetValue.object (balanceCanonicalResetStage lang b 3).1.nextObject) ::
        (balanceCanonicalResetStage lang b 3).1.cells =
      ((balanceCanonicalResetStage lang 0 3).1.nextCell,
        TargetValue.object (balanceCanonicalResetStage lang 0 3).1.nextObject) ::
        (balanceCanonicalResetStage lang 0 3).1.cells
    rw [hn, hs.2.2.2.2.1, hs.2.2.1]
  have hg : (balanceResetCandidateEntry lang b).1.globals =
      (balanceResetCandidateEntry lang 0).1.globals := hs.2.2.2.1
  cases lang with
  | ts => exact resetTsOverridesEntry_localValue_congr hf hc hg hnc
  | python => exact resetBinding_localValue_congr hf hc hg hnc

def resetOverlayIterable (lang : TargetLang) : TargetExpr :=
  if lang == .ts then .call (.property (.local "Object") "entries")
    (.sequence (.local "overrides") .empty)
  else .call (.local "list") (.sequence
    (.call (.property (.local "dict") "items") (.sequence (.local "ctx") .empty)) .empty)

theorem balanceReset_overlay_loop_shape (lang : TargetLang) :
    balanceResetOverlayLoop lang =
      .forDo ["name", "value"] (resetOverlayIterable lang)
        (resetLoopBody (balanceResetOverlayLoop lang)) := by
  cases lang <;> unfold balanceResetOverlayLoop balanceResetMiddleStmt balanceResetProtected
    balanceResetSnapshots balanceStoredReset balanceResetLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

/-- Exact heap after descriptor enumeration and the Python list copy. -/
def resetIterableMachine (lang : TargetLang) (m : TargetMachine) (b : Int) : TargetMachine :=
  let entries := oneEntryMachine lang m "balance" (integerValue lang b)
  if lang == .ts then entries
  else (allocObject entries (oneEntryItems .python m)).1

def resetIterableRef (lang : TargetLang) (m : TargetMachine) : ObjRef :=
  m.nextObject + (if lang == .ts then 1 else 2)

/-- All iterable/pair heap premises of the one-entry loop, for either language
    and every payload. No freshness assumption about the old heap is needed. -/
theorem resetIterableMachine_objects (lang : TargetLang) (m : TargetMachine) (b : Int) :
    objectAt (resetIterableMachine lang m b) (resetIterableRef lang m) =
      .ok (oneEntryItems lang m) ∧
    objectAt (resetIterableMachine lang m b) m.nextObject =
      .ok (oneEntryPair lang m "balance" (integerValue lang b)) := by
  have h1 : m.nextObject ≠ m.nextObject + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  have h2 : m.nextObject ≠ m.nextObject + 2 :=
    Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
  cases lang <;> simp [resetIterableMachine, resetIterableRef, oneEntryMachine,
    oneEntryItems, oneEntryPair, objectAt, allocObject, List.lookup, beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, Nat.add_assoc]

theorem resetIterableMachine_localValue (lang : TargetLang) (m : TargetMachine)
    (f : TargetFrame) (b : Int) (name : String) :
    localValue (resetIterableMachine lang m b) f name = localValue m f name := by
  apply localValue_fields_congr rfl
  · cases lang <;> rfl
  · cases lang <;> rfl

/-- Object.entries enumerates the actual overrides object. Its provenance
    after the TS descriptor-copy arm is a separate obligation. -/
theorem balanceReset_ts_iterable_execute {m f ref object b k}
    (hc : readPropertyValue .ts m (.object object) "entries" =
      .ok ⟨m, .ok (.builtin .objectEntries)⟩)
    (hg : localValue m f "Object" = .ok (.object object))
    (hr : localValue m f "overrides" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b)) :
    evalExpr (k + 4) (balanceProgram .ts) m f (resetOverlayIterable .ts) =
      .ok ⟨resetIterableMachine .ts m b, .ok (.object (resetIterableRef .ts m))⟩ := by
  have he : DepthDerivesExpr (balanceProgram .ts) m f
      (.property (.local "Object") "entries") ⟨m, .ok (.builtin .objectEntries)⟩ 1 :=
    .property (.localRead hg) (by simpa only [balanceProgram_lang] using hc)
  have hh := hostEntries_one (lang := TargetLang.ts) ho (by rfl)
  have h := evalExpr_adequate
    (.callBuiltin he (.cons (.localRead hr) .empty) (by decide)
      (by simpa only [balanceProgram_lang] using hh)) (k := k + 4) (by omega)
  simpa only [resetOverlayIterable, resetIterableMachine, resetIterableRef,
    balanceDataDescriptor, balanceHeapObject, ↓reduceIte, Nat.add_comm] using h

/-- Python evaluates list(dict.items(ctx)), including its extra list object,
    without inspecting or constraining the numeric payload. -/
theorem balanceReset_python_iterable_of_seed {m f ref object b k}
    (hd : localValue m f "dict" = .ok (.builtin .dict))
    (hl : localValue m f "list" = .ok (.builtin .list))
    (hr : localValue m f "ctx" = .ok (.object ref))
    (ho : objectAt m ref = .ok object)
    (hp : object.own = [("balance", balanceDataDescriptor .python b)]) :
    evalExpr (k + 5) (balanceProgram .python) m f (resetOverlayIterable .python) =
      .ok ⟨resetIterableMachine .python m b,
        .ok (.object (resetIterableRef .python m))⟩ := by
  have he : DepthDerivesExpr (balanceProgram .python) m f
      (.property (.local "dict") "items") ⟨m, .ok (.builtin .dictItems)⟩ 1 :=
    .property (.localRead hd) (by rw [balanceProgram_lang]; rfl)
  have hh := hostEntries_one (lang := TargetLang.python) ho hp
  have hi := evalExpr_adequate
    (.callBuiltin he (.cons (.localRead hr) .empty) (by decide)
      (by simpa only [balanceProgram_lang] using hh)) (k := k + 3) (by omega)
  have ha : objectAt (oneEntryMachine .python m "balance" (integerValue .python b))
      (m.nextObject + 1) = .ok (oneEntryItems .python m) := by
    simpa only [oneEntryMachine, allocObject] using
      objectAt_allocObject_fresh (allocObject m
        (oneEntryPair .python m "balance" (integerValue .python b))).1 (oneEntryItems .python m)
  have h := evalList_copy hl hi ha (.inl (by rfl))
  simpa only [resetOverlayIterable, resetIterableMachine, resetIterableRef,
    oneEntryMachine, oneEntryItems, allocObject, ↓reduceIte, Nat.add_assoc] using h

/-- The first Python overlay guard requires a string key. The second guard
    owns the known-key test in the pinned source's context definition table. -/
def resetPythonOverlayNameTest : TargetExpr :=
  .binary .isNotIdentity (.call (.local "type") (.sequence (.local "name") .empty)) (.local "str")

def resetPythonOverlayKnownKeyTest : TargetExpr :=
  .binary .notInObject (.local "name") (.index (.local "_WORLD") (.string "context"))

theorem resetPythonOverlayName_execute {m f k}
    (hn : localValue m f "name" = .ok (.string "balance"))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hs : localValue m f "str" = .ok (.builtin .strType)) :
    evalExpr (k + 4) (balanceProgram .python) m f resetPythonOverlayNameTest =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have hc : DepthDerivesExpr (balanceProgram .python) m f
      (.call (.local "type") (.sequence (.local "name") .empty))
      ⟨m, .ok (.builtin .strType)⟩ 2 :=
    .callBuiltin (.localRead ht) (.cons (.localRead hn) .empty) (by decide) (by rfl)
  exact evalExpr_adequate (.binary (by decide) hc (.localRead hs) (by rfl)) (by omega)

/-- This small membership fact does not evaluate the unused rejection arm. -/
theorem balanceReset_python_known_key_execute {m f ref object k}
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hc : evalExpr (k + 3) (balanceProgram .python) m f
      (.index (.local "_WORLD") (.string "context")) = .ok ⟨m, .ok (.object ref)⟩)
    (ho : objectAt m ref = .ok object) (hk : object.kind = .pythonDict)
    (hp : (object.own.lookup "balance").isSome = true) :
    evalExpr (k + 4) (balanceProgram .python) m f resetPythonOverlayKnownKeyTest =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have hname := evalExpr_adequate (program := balanceProgram .python)
    (.localRead hn) (k := k + 3) (by omega)
  change evalExpr (k + 4) _ _ _ (.binary .notInObject _ _) = _
  rw [evalExpr, hname]
  simp only [Bind.bind, Except.bind]
  rw [hc]
  simp only [Bind.bind, Except.bind]
  rw [balanceProgram_lang]
  simp only [binaryValue, ho, hk, hp, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-- Frozen canonical context tables use the same own-key membership rule. -/
theorem balanceReset_python_known_key_proxy_execute {m f ref object k}
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hc : evalExpr (k + 3) (balanceProgram .python) m f
      (.index (.local "_WORLD") (.string "context")) = .ok ⟨m, .ok (.object ref)⟩)
    (ho : objectAt m ref = .ok object) (hk : object.kind = .mappingProxy)
    (hp : (object.own.lookup "balance").isSome = true) :
    evalExpr (k + 4) (balanceProgram .python) m f resetPythonOverlayKnownKeyTest =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have hname := evalExpr_adequate (program := balanceProgram .python)
    (.localRead hn) (k := k + 3) (by omega)
  change evalExpr (k + 4) _ _ _ (.binary .notInObject _ _) = _
  rw [evalExpr, hname]
  simp only [Bind.bind, Except.bind]
  rw [hc]
  simp only [Bind.bind, Except.bind]
  rw [balanceProgram_lang]
  simp only [binaryValue, ho, hk, hp, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-- Closed facts inspect addresses and builtin locals, not a symbolic seed. -/
def balanceResetMiddlePythonCheck : Prop :=
  let e := balanceResetMiddleEntry .python 0
  let stage := balanceCanonicalResetStage .python 0 3
  let seed := (balancePreparation .python).1.nextObject
  localValue e.1 e.2 "ctx" = .ok (.object seed) ∧
  localValue e.1 e.2 "type" = .ok (.builtin .type) ∧
  localValue e.1 e.2 "dict" = .ok (.builtin .dict) ∧
  stage.1.nextObject ≠ seed ∧
  (List.take (balanceCanonicalResetPrefixLength .python 3) stage.1.objects).lookup seed = none

instance : Decidable balanceResetMiddlePythonCheck := by
  unfold balanceResetMiddlePythonCheck
  infer_instance

theorem balanceResetMiddlePythonCheck_zero : balanceResetMiddlePythonCheck := by
  unfold balanceResetMiddlePythonCheck balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- The supplied seed survives snapshot, candidate allocation, and ctx binding.
    Only its payload varies; address separation is certified at zero. -/
theorem balanceResetMiddleEntry_python_seed (b : Int) :
    objectAt (balanceResetMiddleEntry .python b).1 (balancePreparation .python).1.nextObject =
      .ok (balanceHeapObject .python (balancePreparation .python).1 b) := by
  have h := balanceResetMiddlePythonCheck_zero
  unfold balanceResetMiddlePythonCheck at h
  dsimp only at h
  have footprint := balanceCanonicalResetStage_footprint .python b 3 (by decide)
  change (match (((balanceCanonicalResetStage .python b 3).1.nextObject,
      balanceHeapObject .python (balanceCanonicalResetStage .python b 3).1 100) ::
      (balanceCanonicalResetStage .python b 3).1.objects).lookup
      (balancePreparation .python).1.nextObject with
      | some o => Except.ok o | none => Except.error _) = _
  rw [footprint.1, footprint.2.2.2.2.1]
  simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm h.2.2.2.1), if_false,
    List.lookup_append, h.2.2.2.2, Option.or, beq_self_eq_true, if_true]

/-- Seed-independent builtin reads are checked once at the closed entry. -/
theorem balanceResetMiddle_python_list :
    localValue (balanceResetMiddleEntry .python 0).1
      (balanceResetMiddleEntry .python 0).2 "list" = .ok (.builtin .list) := by
  unfold balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- Complete canonical Python iterable evaluation for every integer seed.
    The bounded-domain premise is needed by the later body, not enumeration. -/
theorem balanceReset_python_iterable_execute (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    evalExpr (k + 5) (balanceProgram .python) e.1 e.2 (resetOverlayIterable .python) =
      .ok ⟨resetIterableMachine .python e.1 b,
        .ok (.object (resetIterableRef .python e.1))⟩ := by
  have h := balanceResetMiddlePythonCheck_zero
  unfold balanceResetMiddlePythonCheck at h
  dsimp only at h
  apply balanceReset_python_iterable_of_seed
  · rw [balanceResetMiddleEntry_localValue .python b "dict"]; exact h.2.2.1
  · rw [balanceResetMiddleEntry_localValue .python b "list"]
    exact balanceResetMiddle_python_list
  · rw [balanceResetMiddleEntry_localValue .python b "ctx"]; exact h.1
  · exact balanceResetMiddleEntry_python_seed b
  · rfl

/-- Directly discharge all five plain-dict premises at the canonical entry. -/
theorem balanceReset_python_canonical_plain_guard_skip (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    execStmt (k + 6) (balanceProgram .python) e.1 e.2
      (ifYesStmt (balanceResetMiddleStmt .python 2)) =
    execStmt (k + 5) (balanceProgram .python) e.1 e.2
      (restStmt (ifYesStmt (balanceResetMiddleStmt .python 2))) := by
  have h := balanceResetMiddlePythonCheck_zero
  unfold balanceResetMiddlePythonCheck at h
  dsimp only at h
  apply balanceReset_python_plain_guard_skip
  · rw [balanceResetMiddleEntry_localValue .python b "ctx"]; exact h.1
  · rw [balanceResetMiddleEntry_localValue .python b "type"]; exact h.2.1
  · rw [balanceResetMiddleEntry_localValue .python b "dict"]; exact h.2.2.1
  · exact balanceResetMiddleEntry_python_seed b
  · rfl
/-- The Python middle frame is independent of the supplied descriptor value. -/
theorem balanceResetMiddleEntry_python_frame (b : Int) :
    (balanceResetMiddleEntry .python b).2 = (balanceResetMiddleEntry .python 0).2 := by
  have hs := balanceCanonicalResetStage_footprint .python b 3 (by decide)
  have hn := balanceCanonicalResetStage_nextCell .python b 3 (by decide)
  have hf : (balanceResetCandidateEntry .python b).2 =
      (balanceResetCandidateEntry .python 0).2 := candidateBinding_frame_congr hs.2.1 hn
  change { (balanceResetCandidateEntry .python b).2 with
      locals := ("ctx", (balanceResetCandidateEntry .python b).1.nextCell) ::
        (balanceResetCandidateEntry .python b).2.locals } =
    { (balanceResetCandidateEntry .python 0).2 with
      locals := ("ctx", (balanceResetCandidateEntry .python 0).1.nextCell) ::
        (balanceResetCandidateEntry .python 0).2.locals }
  have hc : (balanceResetCandidateEntry .python b).1.nextCell =
      (balanceResetCandidateEntry .python 0).1.nextCell := by
    change (balanceCanonicalResetStage .python b 3).1.nextCell + 1 =
      (balanceCanonicalResetStage .python 0 3).1.nextCell + 1
    rw [hn]
  rw [hf, hc]

theorem balanceResetMiddle_python_pair_fresh :
    (balanceResetMiddleEntry .python 0).2.locals.lookup "name" = none ∧
    (balanceResetMiddleEntry .python 0).2.locals.lookup "value" = none := by
  unfold balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- The physical two-cell binding used by one fresh overlay iteration. -/
def resetOverlayPairBinding (lang : TargetLang) (m : TargetMachine) (f : TargetFrame)
    (value : TargetValue) : TargetMachine × TargetFrame :=
  forPairBound lang m f (.string "balance") value

/-- The actual destructuring reads expose the key and arbitrary value. -/
theorem resetOverlayPairBinding_reads (lang : TargetLang) (m : TargetMachine)
    (f : TargetFrame) (value : TargetValue) :
    let bound := resetOverlayPairBinding lang m f value
    localValue bound.1 bound.2 "name" = .ok (.string "balance") ∧
    localValue bound.1 bound.2 "value" = .ok value := by
  have hn : m.nextCell ≠ m.nextCell + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  simp [resetOverlayPairBinding, forPairBound, allocCell, localValue,
    readCell, List.lookup, beq_eq_false_iff_ne.mpr hn]

/-- Execute the source-selected one-entry overlay loop, including its real
    destructuring, body depth, empty iterator tail, and language frame behavior.
    Iterable and body premises are explicit, not canonical execution claims. -/
theorem balanceReset_overlay_loop_execute {lang m source final f ff listRef pairRef list pair value k}
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
      .ok ⟨final, (if lang == .ts then f else ff), .normal⟩ := by
  rw [balanceReset_overlay_loop_shape]
  have h := execForDo_one_pair he hl
    (by rw [balanceProgram_lang]; exact hk) hi hp hv
    (by rw [balanceProgram_lang]; exact hn)
    (by rw [balanceProgram_lang]; exact hf)
    (by rw [balanceProgram_lang]; exact hb)
  simpa only [balanceProgram_lang] using h

/-- Canonical Python loop execution with every iterable, pair and freshness
    premise discharged for all b. Only execution of the source body remains. -/
theorem balanceReset_python_canonical_loop_execute {b k final ff}
    (hb : let e := balanceResetMiddleEntry .python b
      execStmt (k + 4) (balanceProgram .python)
        (resetOverlayPairBinding .python (resetIterableMachine .python e.1 b)
          e.2 (integerValue .python b)).1
        (resetOverlayPairBinding .python (resetIterableMachine .python e.1 b)
          e.2 (integerValue .python b)).2
        (resetLoopBody (balanceResetOverlayLoop .python)) = .ok ⟨final, ff, .normal⟩) :
    let e := balanceResetMiddleEntry .python b
    execStmt (k + 6) (balanceProgram .python) e.1 e.2 (balanceResetOverlayLoop .python) =
      .ok ⟨final, ff, .normal⟩ := by
  let e := balanceResetMiddleEntry .python b
  have ho := resetIterableMachine_objects .python e.1 b
  apply balanceReset_overlay_loop_execute (k := k + 3)
    (list := oneEntryItems .python e.1)
    (pair := oneEntryPair .python e.1 "balance" (integerValue .python b))
    (pairRef := e.1.nextObject) (value := integerValue .python b)
  · exact balanceReset_python_iterable_execute b k
  · exact ho.1
  · rfl
  · rfl
  · exact ho.2
  · rfl
  · intro _; rw [balanceResetMiddleEntry_python_frame b]
    exact balanceResetMiddle_python_pair_fresh.1
  · intro _; rw [balanceResetMiddleEntry_python_frame b]
    exact balanceResetMiddle_python_pair_fresh.2
  · exact hb

/-- Project only the candidate's data descriptor after a loop. -/
def resetCandidateBalanceRead (m : TargetMachine) (f : TargetFrame) :
    Except TargetError (Option TargetValue) := do
  let value ← localValue m f "candidate"
  match value with
  | .object ref =>
      let object ← objectAt m ref
      match object.own.lookup "balance" with
      | some descriptor => pure descriptor.value
      | none => throw .badDescriptor
  | _ => throw .badDescriptor

/-- Universal range predicates on the actual updated candidate descriptor.
    These are primitive evaluations, not execution of the bounds/invariant
    methods or of the generated Pratt evaluator. -/
theorem balanceOverlayUpdated_candidate_range {lang m f ref old b}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old))
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    let updated := balanceOverlayUpdated lang m ref b
    resetCandidateBalanceRead updated f = .ok (some (integerValue lang b)) ∧
    binaryValue lang updated .ge (integerValue lang b) (integerValue lang 0) =
      .ok (.ok (.bool true)) ∧
    binaryValue lang updated .le (integerValue lang b) (integerValue lang 9007199254740991) =
      .ok (.ok (.bool true)) := by
  have hr : localValue (balanceOverlayUpdated lang m ref b) f "candidate" =
      .ok (.object ref) := (localValue_fields_congr rfl rfl rfl).trans hc
  have hp := balanceOverlayUpdated_objectAt ho (b := b)
  refine ⟨?_, ?_, ?_⟩
  · simp [resetCandidateBalanceRead, hr, hp, balanceHeapObject, balanceDataDescriptor,
      List.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases lang <;>
      change Except.ok (Except.ok (TargetValue.bool (decide (0 ≤ b)))) = _ <;>
      simp only [hb.1, decide_true]
  · cases lang <;>
      change Except.ok (Except.ok (TargetValue.bool (decide (b ≤ 9007199254740991)))) = _ <;>
      simp only [hb.2, decide_true]

/-- A decidable closed check of execution control and candidate data. -/
def resetOverlaySuccessCheck (lang : TargetLang) (b : Int)
    (result : Except TargetError StmtOutcome) : Prop :=
  result.toOption.map (fun out => (out.control, resetCandidateBalanceRead out.machine out.frame)) =
    some (.normal, .ok (some (integerValue lang b)))

instance (lang : TargetLang) (b : Int) (result : Except TargetError StmtOutcome) :
    Decidable (resetOverlaySuccessCheck lang b result) := by
  unfold resetOverlaySuccessCheck
  infer_instance

theorem resetOverlaySuccessCheck_sound {lang b result}
    (h : resetOverlaySuccessCheck lang b result) :
    ∃ m f, result = .ok ⟨m, f, .normal⟩ ∧
      resetCandidateBalanceRead m f = .ok (some (integerValue lang b)) := by
  cases result with
  | error e => simp [resetOverlaySuccessCheck, Except.toOption] at h
  | ok out =>
      cases out with
      | mk m f control =>
          simp only [resetOverlaySuccessCheck, Except.toOption, Option.map,
            Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨m, f, congrArg (fun c => Except.ok (StmtOutcome.mk m f c)) h.1, h.2⟩

/-- Closed zero regression of the complete Python one-entry overlay, including
    its source guards, safe-integer helper, int conversion, and forDo tail.
    This is deliberately separate from the universal constructor obligation. -/
theorem balanceReset_python_overlay_zero_check :
    let e := balanceResetMiddleEntry .python 0
    resetOverlaySuccessCheck .python 0
      (execStmt 40 (balanceProgram .python) e.1 e.2 (balanceResetOverlayLoop .python)) := by
  unfold balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
    balanceResetOverlayLoop balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- The complete TS supplied-seed arm includes descriptor copying. This closed
    check then runs the actual Object.entries overlay and inspects its write. -/
theorem balanceReset_ts_overlay_zero_check :
    let e := balanceResetMiddleEntry .ts 0
    resetOverlaySuccessCheck .ts 0
      (execStmt 40 (balanceProgram .ts) e.1 e.2
        (.sequence (ifNoStmt (balanceResetMiddleStmt .ts 2)) (balanceResetOverlayLoop .ts))) := by
  unfold balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
    balanceResetOverlayLoop balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  decide +kernel


def resetTsOverlayHasOwn : TargetExpr :=
  .call (.property (.local "Object") "hasOwn")
    (.sequence (.property (.local "world") "context") (.sequence (.local "name") .empty))
def resetTsOverlayStringTest : TargetExpr :=
  .binary .strictEq
    (.property (.nonNull (.index (.local "contextDefinitions") (.local "name"))) "type")
    (.string "string")
def resetTsOverlayNumberTest : TargetExpr :=
  .binary .strictEq (.unary .typeof (.local "value")) (.string "number")
def resetTsOverlaySafeCall : TargetExpr :=
  .call (.property (.local "Number") "isSafeInteger") (.sequence (.local "value") .empty)
def resetTsOverlayGuard : TargetExpr :=
  .orElse (.unary .not resetTsOverlayHasOwn)
    (.unary .not (.conditional resetTsOverlayStringTest
      (.binary .strictEq (.unary .typeof (.local "value")) (.string "string"))
      (.andThen resetTsOverlayNumberTest resetTsOverlaySafeCall)))

theorem balanceReset_ts_overlay_body_shape :
    resetLoopBody (balanceResetOverlayLoop .ts) =
      .sequence (.ifThenElse resetTsOverlayGuard
        (ifYesStmt (firstStmt (resetLoopBody (balanceResetOverlayLoop .ts)))) .empty)
        (.sequence (balanceResetOverlayWrite .ts) .empty) := by
  unfold balanceResetOverlayWrite balanceResetOverlayLoop
    balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
    balanceStoredReset balanceResetLookup balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  decide +kernel

theorem resetTsOverlaySafeCall_execute {m f b number k}
    (hv : localValue m f "value" = .ok (integerValue .ts b))
    (hn : localValue m f "Number" = .ok (.object number))
    (hp : readPropertyValue .ts m (.object number) "isSafeInteger" =
      .ok ⟨m, .ok (.builtin .jsIsSafeInteger)⟩)
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 3) (balanceProgram .ts) m f resetTsOverlaySafeCall =
      .ok ⟨m, .ok (.bool true)⟩ := by
  apply evalExpr_adequate (.callBuiltin (.property (.localRead hn)
    (by simpa only [balanceProgram_lang] using hp))
    (.cons (.localRead hv) .empty) (by decide) ?_) (by omega)
  rw [balanceProgram_lang]
  change Except.ok (⟨m, .ok (.bool (decide (b.natAbs ≤ 9007199254740991)))⟩ : ExprOutcome) = _
  simp only [hb, decide_true]

theorem resetTsOverlayNumberTest_execute {m f b k}
    (hv : localValue m f "value" = .ok (integerValue .ts b)) :
    evalExpr (k + 3) (balanceProgram .ts) m f resetTsOverlayNumberTest =
      .ok ⟨m, .ok (.bool true)⟩ := by
  have hv' := evalExpr_adequate (program := balanceProgram .ts) (.localRead hv)
    (k := k + 1) (by omega)
  have ht : evalExpr (k + 2) (balanceProgram .ts) m f
      (.unary .typeof (.local "value")) = .ok ⟨m, .ok (.string "number")⟩ := by
    rw [evalExpr, hv']; rfl
  unfold resetTsOverlayNumberTest
  rw [evalExpr, ht]
  simp only [Bind.bind, Except.bind]
  rw [evalExpr_adequate (DepthDerivesExpr.string "number") (by omega)]
  rw [balanceProgram_lang]; rfl

-- Physical table reads, rather than successful expression execution, are premises.
theorem resetTsOverlayGuard_execute {m f b object world context definitions definition number k}
    (hv : localValue m f "value" = .ok (integerValue .ts b))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hObject : localValue m f "Object" = .ok (.object object))
    (hHas : readPropertyValue .ts m (.object object) "hasOwn" =
      .ok ⟨m, .ok (.builtin .objectHasOwn)⟩)
    (hWorld : localValue m f "world" = .ok (.object world))
    (hContext : readPropertyValue .ts m (.object world) "context" =
      .ok ⟨m, .ok (.object context)⟩)
    (hOwn : ∃ descriptor, readOwn m context "balance" = .ok (some descriptor))
    (hDefs : localValue m f "contextDefinitions" = .ok (.object definitions))
    (hDef : readPropertyValue .ts m (.object definitions) "balance" =
      .ok ⟨m, .ok (.object definition)⟩)
    (hType : readPropertyValue .ts m (.object definition) "type" =
      .ok ⟨m, .ok (.string "integer")⟩)
    (hNumber : localValue m f "Number" = .ok (.object number))
    (hSafe : readPropertyValue .ts m (.object number) "isSafeInteger" =
      .ok ⟨m, .ok (.builtin .jsIsSafeInteger)⟩)
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 8) (balanceProgram .ts) m f resetTsOverlayGuard =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have has : evalExpr (k + 6) (balanceProgram .ts) m f resetTsOverlayHasOwn =
      .ok ⟨m, .ok (.bool true)⟩ := by
    apply evalExpr_adequate (.callBuiltin
      (.property (.localRead hObject) (by simpa only [balanceProgram_lang] using hHas))
      (.cons (.property (.localRead hWorld) (by simpa only [balanceProgram_lang] using hContext))
        (.cons (.localRead hn) .empty)) (by decide) ?_) (by omega)
    rw [balanceProgram_lang]
    unfold hostCall
    change (do let own ← readOwn m context "balance"; pure (⟨m, .ok (.bool own.isSome)⟩ : ExprOutcome)) = _
    obtain ⟨descriptor, hd⟩ := hOwn
    rw [hd]; rfl
  have st : evalExpr (k + 5) (balanceProgram .ts) m f resetTsOverlayStringTest =
      .ok ⟨m, .ok (.bool false)⟩ := by
    have idx : evalExpr (k + 2) (balanceProgram .ts) m f
        (.index (.local "contextDefinitions") (.local "name")) =
          .ok ⟨m, .ok (.object definition)⟩ := by
      rw [evalExpr, evalExpr_adequate (.localRead hDefs) (by omega)]
      simp only [Bind.bind, Except.bind]
      rw [evalExpr_adequate (.localRead hn) (by omega)]
      simpa only [Bind.bind, Except.bind, balanceProgram_lang] using hDef
    have non : evalExpr (k + 3) (balanceProgram .ts) m f
        (.nonNull (.index (.local "contextDefinitions") (.local "name"))) =
          .ok ⟨m, .ok (.object definition)⟩ := by
      rw [evalExpr, idx]
    have prop : evalExpr (k + 4) (balanceProgram .ts) m f
        (.property (.nonNull (.index (.local "contextDefinitions") (.local "name"))) "type") =
          .ok ⟨m, .ok (.string "integer")⟩ := by
      rw [evalExpr, non]
      simpa only [Bind.bind, Except.bind, balanceProgram_lang] using hType
    unfold resetTsOverlayStringTest
    rw [evalExpr, prop]
    simp only [Bind.bind, Except.bind]
    rw [evalExpr_adequate (DepthDerivesExpr.string "string") (by omega)]
    rw [balanceProgram_lang]; rfl
  have num := resetTsOverlayNumberTest_execute (k := k + 1) hv
  have safe := resetTsOverlaySafeCall_execute (k := k + 1) hv hNumber hSafe hb
  have and : evalExpr (k + 5) (balanceProgram .ts) m f
      (.andThen resetTsOverlayNumberTest resetTsOverlaySafeCall) =
        .ok ⟨m, .ok (.bool true)⟩ := by
    rw [evalExpr, num]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
      Bool.true_eq, if_true] using safe
  have cond : evalExpr (k + 6) (balanceProgram .ts) m f
      (.conditional resetTsOverlayStringTest
        (.binary .strictEq (.unary .typeof (.local "value")) (.string "string"))
        (.andThen resetTsOverlayNumberTest resetTsOverlaySafeCall)) =
        .ok ⟨m, .ok (.bool true)⟩ := by
    rw [evalExpr, st]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
      Bool.false_eq_true, if_false] using and
  unfold resetTsOverlayGuard
  have notHas : evalExpr (k + 7) (balanceProgram .ts) m f
      (.unary .not resetTsOverlayHasOwn) = .ok ⟨m, .ok (.bool false)⟩ := by
    rw [evalExpr, has]; rfl
  have notCond : evalExpr (k + 7) (balanceProgram .ts) m f
      (.unary .not (.conditional resetTsOverlayStringTest
        (.binary .strictEq (.unary .typeof (.local "value")) (.string "string"))
        (.andThen resetTsOverlayNumberTest resetTsOverlaySafeCall))) =
          .ok ⟨m, .ok (.bool false)⟩ := by
    rw [evalExpr, cond]; rfl
  rw [evalExpr, notHas]
  simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
    Bool.false_eq_true, if_false] using notCond

/-- Physical environment required by the pinned TS overlay guard. These fields
    describe heap/local lookups, not execution of the guard or loop body. -/
structure ResetTsOverlayPhysical (m : TargetMachine) (f : TargetFrame) (b : Int) where
  object : ObjRef
  world : ObjRef
  context : ObjRef
  definitions : ObjRef
  definition : ObjRef
  number : ObjRef
  valueRead : localValue m f "value" = .ok (integerValue .ts b)
  nameRead : localValue m f "name" = .ok (.string "balance")
  objectRead : localValue m f "Object" = .ok (.object object)
  hasOwnRead : readPropertyValue .ts m (.object object) "hasOwn" =
    .ok ⟨m, .ok (.builtin .objectHasOwn)⟩
  worldRead : localValue m f "world" = .ok (.object world)
  contextRead : readPropertyValue .ts m (.object world) "context" =
    .ok ⟨m, .ok (.object context)⟩
  ownRead : ∃ descriptor, readOwn m context "balance" = .ok (some descriptor)
  definitionsRead : localValue m f "contextDefinitions" = .ok (.object definitions)
  definitionRead : readPropertyValue .ts m (.object definitions) "balance" =
    .ok ⟨m, .ok (.object definition)⟩
  typeRead : readPropertyValue .ts m (.object definition) "type" =
    .ok ⟨m, .ok (.string "integer")⟩
  numberRead : localValue m f "Number" = .ok (.object number)
  safeRead : readPropertyValue .ts m (.object number) "isSafeInteger" =
    .ok ⟨m, .ok (.builtin .jsIsSafeInteger)⟩

/-- Complete execution of the actual TS overlay body for any safe signed b.
    Table/builtin premises are physical lookups; no body-success premise remains.
    Negative safe values pass this body and are rejected later by bounds. -/
theorem balanceReset_ts_overlay_body_safe {m f ref old b k}
    (h : ResetTsOverlayPhysical m f b)
    (hc : localValue m f "candidate" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m old))
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 10) (balanceProgram .ts) m f
      (resetLoopBody (balanceResetOverlayLoop .ts)) =
        .ok ⟨balanceOverlayUpdated .ts m ref b, f, .normal⟩ := by
  have guard := resetTsOverlayGuard_execute (k := k) h.valueRead h.nameRead
    h.objectRead h.hasOwnRead h.worldRead h.contextRead h.ownRead
    h.definitionsRead h.definitionRead h.typeRead h.numberRead h.safeRead hb
  have head : execStmt (k + 9) (balanceProgram .ts) m f
      (.ifThenElse resetTsOverlayGuard
        (ifYesStmt (firstStmt (resetLoopBody (balanceResetOverlayLoop .ts)))) .empty) =
        .ok ⟨m, f, .normal⟩ := by
    rw [execIf_of_false guard rfl]
    exact execStmt_adequate .empty (by omega)
  rw [balanceReset_ts_overlay_body_shape, execSequence_of_normal head]
  rw [execSequence_of_normal (balanceReset_overlay_write_ts_execute
    (k := k + 5) hc h.nameRead h.valueRead (writeOwn_balance_existing ho))]
  exact execStmt_adequate .empty (by omega)

/-- The generic one-entry TS loop retains the explicit iterable-evaluation
    premise `he` alongside physical iterable/table facts. Guard, cast, write and
    iterator-tail execution are discharged; `balanceReset_ts_seed_loop_safe`
    also discharges iterable evaluation from physical seed/builtin lookups. -/
theorem balanceReset_ts_overlay_loop_safe
    {m source f listRef pairRef list pair ref old b k}
    (he : evalExpr (k + 11) (balanceProgram .ts) m f (resetOverlayIterable .ts) =
      .ok ⟨source, .ok (.object listRef)⟩)
    (hl : objectAt source listRef = .ok list)
    (hk : list.kind = .jsArray) (hi : list.items = [.object pairRef])
    (hp : objectAt source pairRef = .ok pair)
    (hv : pair.items = [.string "balance", integerValue .ts b])
    (h : let bound := resetOverlayPairBinding .ts source f (integerValue .ts b)
      ResetTsOverlayPhysical bound.1 bound.2 b)
    (hc : let bound := resetOverlayPairBinding .ts source f (integerValue .ts b)
      localValue bound.1 bound.2 "candidate" = .ok (.object ref))
    (ho : let bound := resetOverlayPairBinding .ts source f (integerValue .ts b)
      objectAt bound.1 ref = .ok (balanceHeapObject .ts bound.1 old))
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 12) (balanceProgram .ts) m f (balanceResetOverlayLoop .ts) =
      .ok ⟨balanceOverlayUpdated .ts
        (resetOverlayPairBinding .ts source f (integerValue .ts b)).1 ref b, f, .normal⟩ := by
  apply balanceReset_overlay_loop_execute (k := k + 9) he hl hk hi hp hv
  · intro hlang; cases hlang
  · intro hlang; cases hlang
  · exact balanceReset_ts_overlay_body_safe h hc ho hb
def resetSafeTupleObject (items : List TargetValue) : HeapObject :=
  ⟨.pythonTuple, none, [], items, [], false, false⟩
def resetSafeTupleStage (m : TargetMachine) (items : List TargetValue) : TargetMachine :=
  { (allocObject m (resetSafeTupleObject [])).1 with objects :=
    ((allocObject m (resetSafeTupleObject [])).1.objects.map fun e =>
      (e.1, if e.1 == m.nextObject then resetSafeTupleObject items else e.2)) }
def resetSafeTupleMachine (m : TargetMachine) : TargetMachine :=
  { resetSafeTupleStage m [.builtin .int] with objects :=
    ((resetSafeTupleStage m [.builtin .int]).objects.map fun e =>
      (e.1, if e.1 == m.nextObject then resetSafeTupleObject [.builtin .int, .builtin .float] else e.2)) }

theorem resetSafeTuple_execute {m f k}
    (hi : localValue m f "int" = .ok (.builtin .int))
    (hf : localValue m f "float" = .ok (.builtin .float)) :
    evalExpr (k + 4) (balanceProgram .python) m f
      (.tuple (.sequence (.local "int") (.sequence (.local "float") .empty))) =
      .ok ⟨resetSafeTupleMachine m, .ok (.object m.nextObject)⟩ := by
  let m0 := (allocObject m (resetSafeTupleObject [])).1
  let m1 := resetSafeTupleStage m [.builtin .int]
  have hi0 : localValue m0 f "int" = .ok (.builtin .int) := hi
  have hf1 : localValue m1 f "float" = .ok (.builtin .float) := hf
  have ho0 : objectAt m0 m.nextObject = .ok (resetSafeTupleObject []) :=
    objectAt_allocObject_fresh m (resetSafeTupleObject [])
  have ho1 : objectAt m1 m.nextObject = .ok (resetSafeTupleObject [.builtin .int]) := by
    simp [m1, resetSafeTupleStage, allocObject, objectAt, List.lookup]
  rw [evalTupleTwo_eq (balanceProgram_lang .python)]
  change (do
    let v1 ← evalExpr (k + 2) (balanceProgram .python) m0 f (.local "int")
    match v1.result with
    | .error e => pure (⟨v1.machine, .error e⟩ : ExprOutcome)
    | .ok value1 => do
      let o1 ← objectAt v1.machine m.nextObject
      let n1 ← replaceObject v1.machine m.nextObject {o1 with items := o1.items ++ [value1]}
      let v2 ← evalExpr (k + 1) (balanceProgram .python) n1 f (.local "float")
      match v2.result with
      | .error e => pure (⟨v2.machine, .error e⟩ : ExprOutcome)
      | .ok value2 => do
        let o2 ← objectAt v2.machine m.nextObject
        let n2 ← replaceObject v2.machine m.nextObject {o2 with items := o2.items ++ [value2]}
        pure (⟨n2, .ok (.object m.nextObject)⟩ : ExprOutcome)) = _
  rw [evalExpr_adequate (.localRead hi0) (by omega)]
  simp only [Bind.bind, Except.bind]
  rw [ho0]
  simp only [replaceObject, ho0, Bind.bind, Except.bind, Pure.pure, Except.pure]
  change (do
    let v2 ← evalExpr (k + 1) (balanceProgram .python) m1 f (.local "float")
    match v2.result with
    | .error e => pure (⟨v2.machine, .error e⟩ : ExprOutcome)
    | .ok value2 => do
      let o2 ← objectAt v2.machine m.nextObject
      let n2 ← replaceObject v2.machine m.nextObject {o2 with items := o2.items ++ [value2]}
      pure (⟨n2, .ok (.object m.nextObject)⟩ : ExprOutcome)) = _
  rw [evalExpr_adequate (.localRead hf1) (by omega)]
  simp only [Bind.bind, Except.bind]
  rw [ho1]
  simp only [replaceObject, ho1, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl
def resetPythonSafeFloat : TargetExpr :=
  .call (.local "float") (.sequence (.local "value") .empty)
def resetPythonSafeFinite : TargetExpr :=
  .call (.property (.local "math") "isfinite") (.sequence (.local "value") .empty)
def resetPythonSafeIntegral : TargetExpr :=
  .call (.property resetPythonSafeFloat "is_integer") .empty
def resetPythonSafeAbs : TargetExpr :=
  .call (.local "abs") (.sequence resetPythonSafeFloat .empty)
def resetPythonSafeBound : TargetExpr :=
  .binary .le resetPythonSafeAbs (.local "_MAX_INTEGER")

theorem resetPythonSafeFloat_execute {m f b k}
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hf : localValue m f "float" = .ok (.builtin .float))
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 3) (balanceProgram .python) m f resetPythonSafeFloat =
      .ok ⟨m, .ok (.number .pyFloat b)⟩ := by
  exact evalExpr_adequate (.callBuiltin (.localRead hf)
    (.cons (.localRead hv) .empty) (by decide)
    (by simpa only [balanceProgram_lang, integerValue] using host_float_exact m b hb)) (by omega)

theorem resetPythonSafeIntegral_execute {m f b k}
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hf : localValue m f "float" = .ok (.builtin .float))
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 5) (balanceProgram .python) m f resetPythonSafeIntegral =
      .ok ⟨m, .ok (.bool true)⟩ := by
  have hfloat : DepthDerivesExpr (balanceProgram .python) m f resetPythonSafeFloat
      ⟨m, .ok (.number .pyFloat b)⟩ 2 :=
    .callBuiltin (.localRead hf) (.cons (.localRead hv) .empty) (by decide)
      (by simpa only [balanceProgram_lang, integerValue] using host_float_exact m b hb)
  exact evalExpr_adequate (.callBoundBuiltin
    (.property hfloat (by rw [balanceProgram_lang]; rfl)) .empty (by decide)
    (by rw [balanceProgram_lang]; rfl)) (by omega)

theorem resetPythonSafeAbs_execute {m f b k}
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hf : localValue m f "float" = .ok (.builtin .float))
    (ha : localValue m f "abs" = .ok (.builtin .abs))
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 5) (balanceProgram .python) m f resetPythonSafeAbs =
      .ok ⟨m, .ok (.number .pyFloat (Int.ofNat b.natAbs))⟩ := by
  have hfloat : DepthDerivesExpr (balanceProgram .python) m f resetPythonSafeFloat
      ⟨m, .ok (.number .pyFloat b)⟩ 2 :=
    .callBuiltin (.localRead hf) (.cons (.localRead hv) .empty) (by decide)
      (by simpa only [balanceProgram_lang, integerValue] using host_float_exact m b hb)
  exact evalExpr_adequate (.callBuiltin (.localRead ha) (.cons hfloat .empty)
    (by decide) (by rw [balanceProgram_lang]; rfl)) (by omega)

theorem resetPythonSafeBound_execute {m f b k}
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hf : localValue m f "float" = .ok (.builtin .float))
    (ha : localValue m f "abs" = .ok (.builtin .abs))
    (hm : localValue m f "_MAX_INTEGER" = .ok (integerValue .python 9007199254740991))
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 6) (balanceProgram .python) m f resetPythonSafeBound =
      .ok ⟨m, .ok (.bool true)⟩ := by
  have hAbs := resetPythonSafeAbs_execute (k := k) hv hf ha hb
  unfold resetPythonSafeBound
  rw [evalExpr, hAbs]
  simp only [Bind.bind, Except.bind]
  rw [evalExpr_adequate (.localRead hm) (by omega), balanceProgram_lang]
  have hb' : Int.ofNat b.natAbs ≤ (9007199254740991 : Int) := Int.ofNat_le.mpr hb
  change Except.ok (⟨m, .ok (.bool (decide (Int.ofNat b.natAbs ≤ (9007199254740991 : Int))))⟩ : ExprOutcome) = _
  simp only [hb', decide_true]

/-- All numeric clauses of the source _safe_integer helper, with the actual
    float conversion and receiver-bound is_integer call retained. -/
theorem balanceReset_safe_integer_numeric_execute {m f b math k}
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hf : localValue m f "float" = .ok (.builtin .float))
    (ha : localValue m f "abs" = .ok (.builtin .abs))
    (hm : localValue m f "_MAX_INTEGER" = .ok (integerValue .python 9007199254740991))
    (hMath : localValue m f "math" = .ok (.object math))
    (hFinite : readPropertyValue .python m (.object math) "isfinite" =
      .ok ⟨m, .ok (.builtin .isFinite)⟩)
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 8) (balanceProgram .python) m f
      (.andThen (.andThen resetPythonSafeFinite resetPythonSafeIntegral) resetPythonSafeBound) =
        .ok ⟨m, .ok (.bool true)⟩ := by
  have finite : evalExpr (k + 6) (balanceProgram .python) m f resetPythonSafeFinite =
      .ok ⟨m, .ok (.bool true)⟩ := by
    exact evalExpr_adequate (.callBuiltin (.property (.localRead hMath)
      (by simpa only [balanceProgram_lang] using hFinite))
      (.cons (.localRead hv) .empty) (by decide)
      (by rw [balanceProgram_lang]; rfl)) (by omega)
  have integral := resetPythonSafeIntegral_execute (k := k + 1) hv hf hb
  have bound := resetPythonSafeBound_execute (k := k + 1) hv hf ha hm hb
  have and : evalExpr (k + 7) (balanceProgram .python) m f
      (.andThen resetPythonSafeFinite resetPythonSafeIntegral) =
        .ok ⟨m, .ok (.bool true)⟩ := by
    rw [evalExpr, finite]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
      Bool.true_eq, if_true] using integral
  rw [evalExpr, and]
  simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
    Bool.true_eq, if_true] using bound

def resetPythonSafePrefix : TargetExpr :=
  .binary .inObject (.call (.local "type") (.sequence (.local "value") .empty))
    (.tuple (.sequence (.local "int") (.sequence (.local "float") .empty)))
def resetPythonSafeExpr : TargetExpr :=
  .andThen (.andThen (.andThen resetPythonSafePrefix resetPythonSafeFinite)
    resetPythonSafeIntegral) resetPythonSafeBound

theorem resetPythonSafePrefix_execute {m f b k}
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hi : localValue m f "int" = .ok (.builtin .int))
    (hf : localValue m f "float" = .ok (.builtin .float)) :
    evalExpr (k + 5) (balanceProgram .python) m f resetPythonSafePrefix =
      .ok ⟨resetSafeTupleMachine m, .ok (.bool true)⟩ := by
  have typeCall : evalExpr (k + 4) (balanceProgram .python) m f
      (.call (.local "type") (.sequence (.local "value") .empty)) =
        .ok ⟨m, .ok (.builtin .int)⟩ := by
    exact evalExpr_adequate (.callBuiltin (.localRead ht)
      (.cons (.localRead hv) .empty) (by decide)
      (by rw [balanceProgram_lang]; rfl)) (by omega)
  unfold resetPythonSafePrefix
  rw [evalExpr, typeCall]
  simp only [Bind.bind, Except.bind]
  rw [resetSafeTuple_execute hi hf, balanceProgram_lang]
  have ho : objectAt (resetSafeTupleMachine m) m.nextObject =
      .ok (resetSafeTupleObject [.builtin .int, .builtin .float]) := by
    simp [resetSafeTupleMachine, resetSafeTupleStage, allocObject, objectAt, List.lookup]
  simp [binaryValue, ho, resetSafeTupleObject, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- Physical lookups needed by the Python source helper. Its type tuple really
    allocates; the math property is read in that resulting heap. -/
structure ResetPythonSafePhysical (m : TargetMachine) (f : TargetFrame) (b : Int) where
  math : ObjRef
  valueRead : localValue m f "value" = .ok (integerValue .python b)
  typeRead : localValue m f "type" = .ok (.builtin .type)
  intRead : localValue m f "int" = .ok (.builtin .int)
  floatRead : localValue m f "float" = .ok (.builtin .float)
  absRead : localValue m f "abs" = .ok (.builtin .abs)
  maxRead : localValue m f "_MAX_INTEGER" = .ok (integerValue .python 9007199254740991)
  mathRead : localValue m f "math" = .ok (.object math)
  finiteRead : readPropertyValue .python (resetSafeTupleMachine m) (.object math) "isfinite" =
    .ok ⟨resetSafeTupleMachine m, .ok (.builtin .isFinite)⟩

/-- Execute the complete source helper expression, not just a host surrogate.
    All safe signed balances are accepted and the actual tuple allocation remains. -/
theorem balanceReset_safe_integer_execute {m f b k}
    (h : ResetPythonSafePhysical m f b)
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 9) (balanceProgram .python) m f resetPythonSafeExpr =
      .ok ⟨resetSafeTupleMachine m, .ok (.bool true)⟩ := by
  let n := resetSafeTupleMachine m
  have hv : localValue n f "value" = .ok (integerValue .python b) := h.valueRead
  have hf : localValue n f "float" = .ok (.builtin .float) := h.floatRead
  have ha : localValue n f "abs" = .ok (.builtin .abs) := h.absRead
  have hm : localValue n f "_MAX_INTEGER" = .ok (integerValue .python 9007199254740991) := h.maxRead
  have hMath : localValue n f "math" = .ok (.object h.math) := h.mathRead
  have hPrefix := resetPythonSafePrefix_execute (k := k + 1)
    h.valueRead h.typeRead h.intRead h.floatRead
  have finite : evalExpr (k + 6) (balanceProgram .python) n f resetPythonSafeFinite =
      .ok ⟨n, .ok (.bool true)⟩ := by
    exact evalExpr_adequate (.callBuiltin (.property (.localRead hMath)
      (by simpa only [balanceProgram_lang] using h.finiteRead))
      (.cons (.localRead hv) .empty) (by decide)
      (by rw [balanceProgram_lang]; rfl)) (by omega)
  have integral := resetPythonSafeIntegral_execute (k := k + 2) hv hf hb
  have bound := resetPythonSafeBound_execute (k := k + 2) hv hf ha hm hb
  have first : evalExpr (k + 7) (balanceProgram .python) m f
      (.andThen resetPythonSafePrefix resetPythonSafeFinite) = .ok ⟨n, .ok (.bool true)⟩ := by
    rw [evalExpr, hPrefix]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
      Bool.true_eq, if_true] using finite
  have second : evalExpr (k + 8) (balanceProgram .python) m f
      (.andThen (.andThen resetPythonSafePrefix resetPythonSafeFinite) resetPythonSafeIntegral) =
        .ok ⟨n, .ok (.bool true)⟩ := by
    rw [evalExpr, first]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
      Bool.true_eq, if_true] using integral
  unfold resetPythonSafeExpr
  rw [evalExpr, second]
  simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang,
    Bool.true_eq, if_true] using bound

/-- The selected helper is the closure installed by the actual Python module. -/
def balancePythonSafeIntegerClosure : TargetClosure :=
  ((do
    let value ← localValue (balancePreparation .python).1 (balancePreparation .python).2 "_safe_integer"
    match value with
    | .closure ref => closureAt (balancePreparation .python).1 ref
    | _ => throw TargetError.badDescriptor) : Except TargetError TargetClosure).toOption.getD
      ⟨"missing", [], [], .empty, [], none⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balancePythonSafeInteger_body_shape :
    balancePythonSafeIntegerClosure.body = .sequence (.returnValue resetPythonSafeExpr) .empty := by
  unfold balancePythonSafeIntegerClosure balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- Execute the real source-selected return and its sequence control, for all
    safe signed values, with physical helper-frame premises only. -/
theorem balancePythonSafeInteger_body_execute {m f b k}
    (h : ResetPythonSafePhysical m f b)
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 11) (balanceProgram .python) m f balancePythonSafeIntegerClosure.body =
      .ok ⟨resetSafeTupleMachine m, f, .returned (.bool true)⟩ := by
  rw [balancePythonSafeInteger_body_shape, execStmt, execStmt,
    balanceReset_safe_integer_execute h hb]
  rfl

/-- The physical argument cell and fresh helper frame used by _safe_integer. -/
def resetPythonSafeCallEntry (m : TargetMachine) (closure : TargetClosure) (b : Int) :
    TargetMachine × TargetFrame :=
  ((allocCell m (integerValue .python b) true).1,
    { closureFrame closure with locals := [("value", m.nextCell)] })

def resetPythonSafeCall : TargetExpr :=
  .call (.local "_safe_integer") (.sequence (.local "value") .empty)

/-- Execute the actual stored Python helper through parameter binding, its
    source body, and return translation. No helper-success premise is required. -/
theorem balanceReset_safe_integer_call_execute {m f ref closure b k}
    (hr : localValue m f "_safe_integer" = .ok (.closure ref))
    (hv : localValue m f "value" = .ok (integerValue .python b))
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = [⟨"value", none⟩])
    (hs : closure.body = balancePythonSafeIntegerClosure.body)
    (h : let e := resetPythonSafeCallEntry m closure b
      ResetPythonSafePhysical e.1 e.2 b)
    (hb : b.natAbs ≤ 9007199254740991) :
    evalExpr (k + 12) (balanceProgram .python) m f resetPythonSafeCall =
      .ok ⟨resetSafeTupleMachine (resetPythonSafeCallEntry m closure b).1, .ok (.bool true)⟩ := by
  have bindings : DepthBindsProvided (balanceProgram .python) m (closureFrame closure)
      closure.params closure.pythonDefaults [integerValue .python b]
      (resetPythonSafeCallEntry m closure b).1 (resetPythonSafeCallEntry m closure b).2 1 := by
    rw [hp]
    apply DepthBindsProvided.cons (rank := 0)
    · rw [balanceProgram_lang]; rfl
    · exact .empty
  unfold resetPythonSafeCall
  rw [evalStoredCall_eq (.localRead hr) (.cons (.localRead hv) .empty) hc bindings
    (by omega) (by omega) (by omega), hs]
  rw [balancePythonSafeInteger_body_execute h hb]
  rfl


/-- The updated candidate contains exactly b even when it is safe and negative.
    This is a descriptor read, separate from later nonnegative validation. -/
theorem balanceOverlayUpdated_candidate_read {lang m f ref old b}
    (hc : localValue m f "candidate" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject lang m old)) :
    resetCandidateBalanceRead (balanceOverlayUpdated lang m ref b) f =
      .ok (some (integerValue lang b)) := by
  have hr : localValue (balanceOverlayUpdated lang m ref b) f "candidate" =
      .ok (.object ref) := (localValue_fields_congr rfl rfl rfl).trans hc
  have hp := balanceOverlayUpdated_objectAt ho (b := b)
  simp [resetCandidateBalanceRead, hr, hp, balanceHeapObject, balanceDataDescriptor,
    List.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Complete body control and descriptor-data postcondition for every safe
    signed TS value. This does not claim constructor validation success. -/
theorem balanceReset_ts_overlay_body_success {m f ref old b k}
    (h : ResetTsOverlayPhysical m f b)
    (hc : localValue m f "candidate" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m old))
    (hb : b.natAbs ≤ 9007199254740991) :
    resetOverlaySuccessCheck .ts b
      (execStmt (k + 10) (balanceProgram .ts) m f (resetLoopBody (balanceResetOverlayLoop .ts))) := by
  rw [balanceReset_ts_overlay_body_safe h hc ho hb]
  unfold resetOverlaySuccessCheck
  simp only [Except.toOption, Option.map, Option.some.injEq, Prod.mk.injEq]
  exact ⟨True.intro, balanceOverlayUpdated_candidate_read hc ho⟩



/-- Supply Object.entries from physical lookups as well as discharging the body.
    This is universal for safe b on a supplied one-key overrides object; the
    preceding TS descriptor-copy false arm remains a separate obligation. -/
theorem balanceReset_ts_seed_loop_safe {m f seed object ref old b k}
    (hEntries : readPropertyValue .ts m (.object object) "entries" =
      .ok ⟨m, .ok (.builtin .objectEntries)⟩)
    (hObject : localValue m f "Object" = .ok (.object object))
    (hSeed : localValue m f "overrides" = .ok (.object seed))
    (hoSeed : objectAt m seed = .ok (balanceHeapObject .ts m b))
    (h : let bound := resetOverlayPairBinding .ts (resetIterableMachine .ts m b) f (integerValue .ts b)
      ResetTsOverlayPhysical bound.1 bound.2 b)
    (hc : let bound := resetOverlayPairBinding .ts (resetIterableMachine .ts m b) f (integerValue .ts b)
      localValue bound.1 bound.2 "candidate" = .ok (.object ref))
    (ho : let bound := resetOverlayPairBinding .ts (resetIterableMachine .ts m b) f (integerValue .ts b)
      objectAt bound.1 ref = .ok (balanceHeapObject .ts bound.1 old))
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 12) (balanceProgram .ts) m f (balanceResetOverlayLoop .ts) =
      .ok ⟨balanceOverlayUpdated .ts
        (resetOverlayPairBinding .ts (resetIterableMachine .ts m b) f (integerValue .ts b)).1 ref b,
        f, .normal⟩ := by
  have objects := resetIterableMachine_objects .ts m b
  exact balanceReset_ts_overlay_loop_safe
    (balanceReset_ts_iterable_execute (k := k + 7) hEntries hObject hSeed hoSeed)
    objects.1 rfl rfl objects.2 rfl h hc ho hb

def resetCandidateMiddleModel (lang : TargetLang) (stage : TargetMachine × TargetFrame) (seed : ObjRef) :
    TargetMachine × TargetFrame :=
  let e := snapshotBound lang (allocObject stage.1 (balanceHeapObject lang stage.1 100)).1
    stage.2 "candidate" (.object stage.1.nextObject)
  if lang == .ts then resetTsOverridesEntry e.1 e.2
  else snapshotBound .python e.1 e.2 "ctx" (.object seed)

theorem resetCandidateMiddleModel_object (lang : TargetLang) (stage : TargetMachine × TargetFrame) (seed : ObjRef) :
    objectAt (resetCandidateMiddleModel lang stage seed).1 stage.1.nextObject =
      .ok (balanceHeapObject lang (resetCandidateMiddleModel lang stage seed).1 100) := by
  cases lang <;>
    simp only [resetCandidateMiddleModel, resetTsOverridesEntry, snapshotBound,
      Bool.false_eq_true, if_false, if_true, Prod.fst, objectAt_allocCell]
  all_goals exact objectAt_allocObject_fresh _ _

theorem balanceResetMiddleEntry_model (lang : TargetLang) (b : Int) :
    balanceResetMiddleEntry lang b = resetCandidateMiddleModel lang
      (balanceCanonicalResetStage lang b 3) (balancePreparation lang).1.nextObject := rfl

theorem balanceResetMiddleEntry_candidate_object (lang : TargetLang) (b : Int) :
    objectAt (balanceResetMiddleEntry lang b).1 (balanceCanonicalResetStage lang b 3).1.nextObject =
      .ok (balanceHeapObject lang (balanceResetMiddleEntry lang b).1 100) := by
  rw [balanceResetMiddleEntry_model]
  exact resetCandidateMiddleModel_object lang (balanceCanonicalResetStage lang b 3)
    (balancePreparation lang).1.nextObject
def balanceResetMiddleCandidateCheck (lang : TargetLang) : Prop :=
  localValue (balanceResetMiddleEntry lang 0).1 (balanceResetMiddleEntry lang 0).2 "candidate" =
    .ok (.object (balanceCanonicalResetStage lang 0 3).1.nextObject)

instance (lang : TargetLang) : Decidable (balanceResetMiddleCandidateCheck lang) := by
  unfold balanceResetMiddleCandidateCheck
  infer_instance

theorem balanceResetMiddleCandidateCheck_zero (lang : TargetLang) : balanceResetMiddleCandidateCheck lang := by
  cases lang <;>
    unfold balanceResetMiddleCandidateCheck balanceResetMiddleEntry balanceResetCandidateEntry
      balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
      balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
      balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
      balanceConstructorLookup balanceConstructorName balancePreparation
  all_goals first
    | (rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel)
    | (rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel)

theorem balanceResetMiddleEntry_candidate_read (lang : TargetLang) (b : Int) :
    localValue (balanceResetMiddleEntry lang b).1 (balanceResetMiddleEntry lang b).2 "candidate" =
      .ok (.object (balanceCanonicalResetStage lang b 3).1.nextObject) := by
  rw [balanceResetMiddleEntry_localValue,
    (balanceCanonicalResetStage_footprint lang b 3 (by decide)).2.2.2.2.1]
  exact balanceResetMiddleCandidateCheck_zero lang
/-- A candidate update at the physical middle entry. This selector is a heap
    construction, not a claim that reset/overlay execution has reached it. -/
def balanceResetUpdatedCandidateEntry (lang : TargetLang) (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceResetMiddleEntry lang b
  (balanceOverlayUpdated lang e.1 (balanceCanonicalResetStage lang b 3).1.nextObject b, e.2)

/-- Only the helper return is projected. Helper allocation remains inside the
    interpreter result; an arbitrary final machine is not assumed unchanged. -/
def resetHelperSuccessCheck (lang : TargetLang) (result : Except TargetError ExprOutcome) : Prop :=
  (result.toOption.bind fun out => out.result.toOption) =
    some (if lang == .ts then TargetValue.undefined else TargetValue.null)

instance (lang : TargetLang) (result : Except TargetError ExprOutcome) :
    Decidable (resetHelperSuccessCheck lang result) := by
  unfold resetHelperSuccessCheck
  infer_instance

theorem resetHelperSuccessCheck_sound {lang result}
    (h : resetHelperSuccessCheck lang result) :
    ∃ m, result = .ok ⟨m, .ok (if lang == .ts then .undefined else .null)⟩ := by
  cases result with
  | error e => simp [resetHelperSuccessCheck, Except.toOption] at h
  | ok out =>
    rcases out with ⟨m, returned⟩
    cases returned with
    | error e => simp [resetHelperSuccessCheck, Except.toOption] at h
    | ok value =>
      simp only [resetHelperSuccessCheck, Except.toOption, Option.bind,
        Option.some.injEq] at h
      subst value
      exact ⟨m, rfl⟩

/-- Closed certificates of the actual bounds and invariant method calls on an
    updated zero candidate. The invariant call runs the emitted Pratt parser
    on the fixed balance >= 0 string. Neither call is yet universal in b. -/
theorem balanceReset_helpers_zero_check (lang : TargetLang) (invariant : Bool) :
    let e := balanceResetUpdatedCandidateEntry lang 0
    resetHelperSuccessCheck lang
      (evalExpr 100 (balanceProgram lang) e.1 e.2
        (if invariant then resetInvariantCall lang else resetBoundsCall lang)) := by
  cases lang <;> cases invariant <;>
    unfold balanceResetUpdatedCandidateEntry balanceResetMiddleEntry balanceResetCandidateEntry
      balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
      balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
      balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
      balanceConstructorLookup balanceConstructorName balancePreparation
  all_goals first
    | (rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel)
    | (rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel)

/-- Canonical candidate binding and existing-key update have the actual data
    descriptor b for every integer. This remains a physical boundary fact. -/
theorem balanceResetUpdatedCandidateEntry_read (lang : TargetLang) (b : Int) :
    resetCandidateBalanceRead (balanceResetUpdatedCandidateEntry lang b).1
      (balanceResetUpdatedCandidateEntry lang b).2 = .ok (some (integerValue lang b)) :=
  balanceOverlayUpdated_candidate_read (balanceResetMiddleEntry_candidate_read lang b)
    (balanceResetMiddleEntry_candidate_object lang b)

/-- Instantiate the primitive range predicates on the canonical updated heap.
    Execution of the bounds/invariant methods is not inferred from this lemma. -/
theorem balanceResetUpdatedCandidateEntry_range {lang b}
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    let e := balanceResetUpdatedCandidateEntry lang b
    resetCandidateBalanceRead e.1 e.2 = .ok (some (integerValue lang b)) ∧
    binaryValue lang e.1 .ge (integerValue lang b) (integerValue lang 0) = .ok (.ok (.bool true)) ∧
    binaryValue lang e.1 .le (integerValue lang b) (integerValue lang 9007199254740991) =
      .ok (.ok (.bool true)) :=
  balanceOverlayUpdated_candidate_range (balanceResetMiddleEntry_candidate_read lang b)
    (balanceResetMiddleEntry_candidate_object lang b) hb


def resetPythonOverlayGuardType : TargetExpr :=
  .binary .eq
    (.call (.property (.call (.property (.index (.local "_WORLD") (.string "context")) "get")
      (.sequence (.local "name") (.sequence (.object .empty) .empty))) "get")
      (.sequence (.string "type") .empty)) (.string "string")

def resetPythonOverlayGuard : TargetExpr :=
  .orElse resetPythonOverlayKnownKeyTest
    (.conditional resetPythonOverlayGuardType
      (.binary .isNotIdentity (.call (.local "type") (.sequence (.local "value") .empty)) (.local "str"))
      (.unary .not resetPythonSafeCall))

theorem balanceReset_python_overlay_body_shape :
  resetLoopBody (balanceResetOverlayLoop .python) =
    .sequence (.ifThenElse resetPythonOverlayNameTest
      (ifYesStmt (firstStmt (resetLoopBody (balanceResetOverlayLoop .python)))) .empty)
      (.sequence (.ifThenElse resetPythonOverlayGuard
        (ifYesStmt (firstStmt (restStmt (resetLoopBody (balanceResetOverlayLoop .python))))) .empty)
        (.sequence (balanceResetOverlayWrite .python) .empty)) := by
  unfold balanceResetOverlayWrite balanceResetOverlayLoop balanceResetMiddleStmt
    balanceResetProtected balanceResetSnapshots balanceStoredReset balanceResetLookup balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel

/-- Execute every source guard and write, retaining the helper's allocations.
    Definition-table evaluations and physical reads are explicit premises. -/
theorem balanceReset_python_overlay_body_safe {m typed f ref context object helper closure b k}
    (hn : localValue m f "name" = .ok (.string "balance"))
    (ht : localValue m f "type" = .ok (.builtin .type))
    (hs : localValue m f "str" = .ok (.builtin .strType))
    (hc : evalExpr (k + 15) (balanceProgram .python) m f
      (.index (.local "_WORLD") (.string "context")) = .ok ⟨m, .ok (.object context)⟩)
    (ho : objectAt m context = .ok object) (hk : object.kind = .pythonDict ∨ object.kind = .mappingProxy)
    (hp : (object.own.lookup "balance").isSome = true)
    (hType : evalExpr (k + 15) (balanceProgram .python) m f resetPythonOverlayGuardType =
      .ok ⟨typed, .ok (.bool false)⟩)
    (hr : localValue typed f "_safe_integer" = .ok (.closure helper))
    (hv : localValue typed f "value" = .ok (integerValue .python b))
    (hClosure : closureAt typed helper = .ok closure)
    (hParams : closure.params = [⟨"value", none⟩])
    (hBody : closure.body = balancePythonSafeIntegerClosure.body)
    (hSafe : let e := resetPythonSafeCallEntry typed closure b
      ResetPythonSafePhysical e.1 e.2 b)
    (hCandidate : let n := resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1
      localValue n f "candidate" = .ok (.object ref))
    (hName : let n := resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1
      localValue n f "name" = .ok (.string "balance"))
    (hValue : let n := resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1
      localValue n f "value" = .ok (integerValue .python b))
    (hInt : let n := resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1
      localValue n f "int" = .ok (.builtin .int))
    (hWriteType : let n := resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1
      evalExpr (k + 15) (balanceProgram .python) n f resetPythonOverlayStringTest =
        .ok ⟨n, .ok (.bool false)⟩)
    (hObject : let n := resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1
      objectAt n ref = .ok (balanceHeapObject .python n 100))
    (hb : b.natAbs ≤ 9007199254740991) :
    execStmt (k + 20) (balanceProgram .python) m f
      (resetLoopBody (balanceResetOverlayLoop .python)) =
        .ok ⟨balanceOverlayUpdated .python
          (resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1) ref b, f, .normal⟩ := by
  have name := resetPythonOverlayName_execute (k := k + 14) hn ht hs
  have first : execStmt (k + 19) (balanceProgram .python) m f
      (.ifThenElse resetPythonOverlayNameTest
        (ifYesStmt (firstStmt (resetLoopBody (balanceResetOverlayLoop .python)))) .empty) =
        .ok ⟨m, f, .normal⟩ := by
    rw [execIf_of_false name rfl]
    exact execStmt_adequate .empty (by omega)
  have known : evalExpr (k + 16) (balanceProgram .python) m f resetPythonOverlayKnownKeyTest =
      .ok ⟨m, .ok (.bool false)⟩ := by
    rcases hk with hk | hk
    · exact balanceReset_python_known_key_execute hn hc ho hk hp
    · exact balanceReset_python_known_key_proxy_execute hn hc ho hk hp
  have safe := balanceReset_safe_integer_call_execute (k := k + 2) hr hv hClosure hParams hBody hSafe hb
  have neg : evalExpr (k + 15) (balanceProgram .python) typed f (.unary .not resetPythonSafeCall) =
      .ok ⟨resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1, .ok (.bool false)⟩ := by
    rw [evalExpr, safe]; rfl
  have cond : evalExpr (k + 16) (balanceProgram .python) m f
      (.conditional resetPythonOverlayGuardType
        (.binary .isNotIdentity (.call (.local "type") (.sequence (.local "value") .empty)) (.local "str"))
        (.unary .not resetPythonSafeCall)) =
      .ok ⟨resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1, .ok (.bool false)⟩ := by
    rw [evalExpr, hType]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang, Bool.false_eq_true, if_false] using neg
  have guard : evalExpr (k + 17) (balanceProgram .python) m f resetPythonOverlayGuard =
      .ok ⟨resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1, .ok (.bool false)⟩ := by
    unfold resetPythonOverlayGuard
    rw [evalExpr, known]
    simpa only [Bind.bind, Except.bind, sourceTruthy, balanceProgram_lang, Bool.false_eq_true, if_false] using cond
  have second : execStmt (k + 18) (balanceProgram .python) m f
      (.ifThenElse resetPythonOverlayGuard
        (ifYesStmt (firstStmt (restStmt (resetLoopBody (balanceResetOverlayLoop .python))))) .empty) =
      .ok ⟨resetSafeTupleMachine (resetPythonSafeCallEntry typed closure b).1, f, .normal⟩ := by
    rw [execIf_of_false guard rfl]
    exact execStmt_adequate .empty (by omega)
  rw [balanceReset_python_overlay_body_shape, execSequence_of_normal first,
    execSequence_of_normal second,
    execSequence_of_normal (balanceReset_overlay_write_python_execute (k := k + 10)
      hCandidate hName hValue hInt hWriteType hb (writeOwn_balance_existing hObject))]
  exact execStmt_adequate .empty (by omega)

-- Canonical overlay environment and source-selected definition-table discharge.
theorem resetCandidateMiddleModel_cells_congr {lang m n f g seed}
    (hc : m.cells = n.cells) (hn : m.nextCell = n.nextCell)
    (ho : m.nextObject = n.nextObject) :
    (resetCandidateMiddleModel lang (m, f) seed).1.cells =
      (resetCandidateMiddleModel lang (n, g) seed).1.cells := by
  cases lang <;>
    simp only [resetCandidateMiddleModel, snapshotBound, resetTsOverridesEntry,
      allocCell, allocObject, Prod.fst, beq_self_eq_true, Bool.false_eq_true, if_false, if_true]
  all_goals rw [hc, hn, ho]
  all_goals rfl

theorem balanceResetMiddleEntry_cells (lang : TargetLang) (b : Int) :
    (balanceResetMiddleEntry lang b).1.cells = (balanceResetMiddleEntry lang 0).1.cells := by
  rw [balanceResetMiddleEntry_model, balanceResetMiddleEntry_model]
  have h := balanceCanonicalResetStage_footprint lang b 3 (by decide)
  exact resetCandidateMiddleModel_cells_congr h.2.2.1 h.2.2.2.2.2.2.2.2 h.2.2.2.2.1

theorem balanceResetMiddleEntry_nextCell (lang : TargetLang) (b : Int) :
    (balanceResetMiddleEntry lang b).1.nextCell = (balanceResetMiddleEntry lang 0).1.nextCell := by
  cases lang <;> rfl

theorem resetCandidateMiddleModel_address_congr {lang m n f g seed name}
    (hf : f = g) (hg : m.globals = n.globals) (hn : m.nextCell = n.nextCell) :
    snapshotAddress (resetCandidateMiddleModel lang (m, f) seed).1
      (resetCandidateMiddleModel lang (m, f) seed).2 name =
    snapshotAddress (resetCandidateMiddleModel lang (n, g) seed).1
      (resetCandidateMiddleModel lang (n, g) seed).2 name := by
  cases lang <;>
    simp only [resetCandidateMiddleModel, snapshotBound, resetTsOverridesEntry,
      allocCell, allocObject, Prod.fst, Prod.snd, beq_self_eq_true,
      Bool.false_eq_true, if_false, if_true, snapshotAddress]
  all_goals rw [hf, hg, hn]
  all_goals rfl

theorem balanceResetMiddleEntry_address (lang : TargetLang) (b : Int) (name : String) :
    snapshotAddress (balanceResetMiddleEntry lang b).1 (balanceResetMiddleEntry lang b).2 name =
      snapshotAddress (balanceResetMiddleEntry lang 0).1 (balanceResetMiddleEntry lang 0).2 name := by
  rw [balanceResetMiddleEntry_model, balanceResetMiddleEntry_model]
  have h := balanceCanonicalResetStage_footprint lang b 3 (by decide)
  exact resetCandidateMiddleModel_address_congr h.2.1 h.2.2.2.1 h.2.2.2.2.2.2.2.2

theorem localValue_of_snapshotAddress {m f name ref}
    (hn : name ≠ "this" ∧ name ≠ "self")
    (ha : snapshotAddress m f name = some ref) :
    localValue m f name = readCell m ref := by
  unfold snapshotAddress at ha
  simp only [localValue, beq_eq_false_iff_ne.mpr hn.1,
    beq_eq_false_iff_ne.mpr hn.2, Bool.or_false, Bool.false_eq_true, if_false]
  cases hl : f.locals.lookup name <;> simp only [hl, Option.orElse] at ha ⊢
  · cases hc : f.captures.lookup name <;> simp only [hc, Option.orElse] at ha ⊢
    · cases hg : m.globals.lookup name <;> simp_all
    · simp_all
  · simp_all

theorem resetOverlayPairBinding_preserves_local {lang m f value name ref}
    (hn : name ≠ "name" ∧ name ≠ "value" ∧ name ≠ "this" ∧ name ≠ "self")
    (ha : snapshotAddress m f name = some ref)
    (hf : ref < m.nextCell) :
    let bound := resetOverlayPairBinding lang m f value
    localValue bound.1 bound.2 name = localValue m f name := by
  dsimp only
  have a : snapshotAddress (resetOverlayPairBinding lang m f value).1
      (resetOverlayPairBinding lang m f value).2 name = some ref := by
    simpa only [resetOverlayPairBinding, forPairBound, snapshotAddress, allocCell,
      List.lookup_cons, beq_eq_false_iff_ne.mpr hn.1, beq_eq_false_iff_ne.mpr hn.2.1,
      if_false] using ha
  have h1 : ref ≠ m.nextCell := Nat.ne_of_lt hf
  have h2 : ref ≠ m.nextCell + 1 := Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_succ_self _))
  rw [localValue_of_snapshotAddress ⟨hn.2.2.1, hn.2.2.2⟩ a,
    localValue_of_snapshotAddress ⟨hn.2.2.1, hn.2.2.2⟩ ha]
  simp [readCell, resetOverlayPairBinding, forPairBound, allocCell,
    List.lookup, beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2]
/-- An own data lookup in the frozen Python definition tables. -/
theorem resetPythonTable_read {m ref object key value}
    (hr : ref ≠ m.checkerRef) (hproto : ref ≠ m.objectPrototype)
    (hkey : key ≠ "get" ∧ key ≠ "items") (ho : objectAt m ref = .ok object)
    (hk : object.kind = .mappingProxy)
    (hp : object.own.lookup key = some ⟨some value, none, none, true, true, true⟩) :
    readPropertyValue .python m (.object ref) key = .ok ⟨m, .ok value⟩ := by
  simp [readPropertyValue, beq_eq_false_iff_ne.mpr hr, beq_eq_false_iff_ne.mpr hproto,
    beq_eq_false_iff_ne.mpr hkey.1, beq_eq_false_iff_ne.mpr hkey.2, ho, hk,
    readOwn, hp, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem resetPythonWorldContext_execute {m f world context k}
    (hw : localValue m f "_WORLD" = .ok (.object world))
    (hc : readPropertyValue .python m (.object world) "context" = .ok ⟨m, .ok (.object context)⟩) :
    evalExpr (k + 2) (balanceProgram .python) m f
      (.index (.local "_WORLD") (.string "context")) = .ok ⟨m, .ok (.object context)⟩ := by
  rw [evalExpr, evalExpr_adequate (.localRead hw) (by omega)]
  simp only [Bind.bind, Except.bind]
  rw [evalExpr_adequate (.string "context") (by omega), balanceProgram_lang]
  exact hc

theorem resetPythonOverlayStringTest_execute {m f world context definition k}
    (hw : localValue m f "_WORLD" = .ok (.object world))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hc : readPropertyValue .python m (.object world) "context" = .ok ⟨m, .ok (.object context)⟩)
    (hd : readPropertyValue .python m (.object context) "balance" = .ok ⟨m, .ok (.object definition)⟩)
    (ht : readPropertyValue .python m (.object definition) "type" = .ok ⟨m, .ok (.string "integer")⟩) :
    evalExpr (k + 5) (balanceProgram .python) m f resetPythonOverlayStringTest =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have ctx := resetPythonWorldContext_execute (k := k) hw hc
  have defn : evalExpr (k + 3) (balanceProgram .python) m f
      (.index (.index (.local "_WORLD") (.string "context")) (.local "name")) =
        .ok ⟨m, .ok (.object definition)⟩ := by
    rw [evalExpr, ctx]
    simp only [Bind.bind, Except.bind]
    rw [evalExpr_adequate (.localRead hn) (by omega), balanceProgram_lang]
    exact hd
  have typ : evalExpr (k + 4) (balanceProgram .python) m f
      (.index (.index (.index (.local "_WORLD") (.string "context")) (.local "name")) (.string "type")) =
        .ok ⟨m, .ok (.string "integer")⟩ := by
    rw [evalExpr, defn]
    simp only [Bind.bind, Except.bind]
    rw [evalExpr_adequate (.string "type") (by omega), balanceProgram_lang]
    exact ht
  unfold resetPythonOverlayStringTest
  rw [evalExpr, typ]
  simp only [Bind.bind, Except.bind]
  rw [evalExpr_adequate (.string "string") (by omega), balanceProgram_lang]
  rfl

/-- The fallback dictionary in the first get call is evaluated eagerly. -/
def resetPythonOverlayTypedMachine (m : TargetMachine) : TargetMachine :=
  (allocObject m (literalObject .python m)).1

theorem resetPythonTable_get {m ref object}
    (hr : ref ≠ m.checkerRef) (hproto : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok object) (hk : object.kind = .mappingProxy) :
    readPropertyValue .python m (.object ref) "get" =
      .ok ⟨m, .ok (.boundBuiltin .dictGet (.object ref))⟩ := by
  simp [readPropertyValue, beq_eq_false_iff_ne.mpr hr,
    beq_eq_false_iff_ne.mpr hproto, ho, hk,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem resetPythonOverlayGuardType_execute {m f world context definition ctx defn k}
    (hw : localValue m f "_WORLD" = .ok (.object world))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hc : readPropertyValue .python m (.object world) "context" = .ok ⟨m, .ok (.object context)⟩)
    (hctx : objectAt m context = .ok ctx) (hkctx : ctx.kind = .mappingProxy)
    (hpctx : ctx.own.lookup "balance" = some ⟨some (.object definition), none, none, true, true, true⟩)
    (hdef : objectAt m definition = .ok defn) (hkdef : defn.kind = .mappingProxy)
    (hpdef : defn.own.lookup "type" = some ⟨some (.string "integer"), none, none, true, true, true⟩)
    (hctxChecker : context ≠ m.checkerRef) (hctxProto : context ≠ m.objectPrototype)
    (hdefChecker : definition ≠ m.checkerRef) (hdefProto : definition ≠ m.objectPrototype)
    (hctxFresh : context ≠ m.nextObject) (hdefFresh : definition ≠ m.nextObject) :
    evalExpr (k + 8) (balanceProgram .python) m f resetPythonOverlayGuardType =
      .ok ⟨resetPythonOverlayTypedMachine m, .ok (.bool false)⟩ := by
  let n := resetPythonOverlayTypedMachine m
  have hcN : objectAt n context = .ok ctx :=
    (objectAt_allocObject_other hctxFresh).trans hctx
  have hdN : objectAt n definition = .ok defn :=
    (objectAt_allocObject_other hdefFresh).trans hdef
  have ctxEval := resetPythonWorldContext_execute (k := k + 1) hw hc
  have get : evalExpr (k + 4) (balanceProgram .python) m f
      (.property (.index (.local "_WORLD") (.string "context")) "get") =
        .ok ⟨m, .ok (.boundBuiltin .dictGet (.object context))⟩ := by
    rw [evalExpr, ctxEval]
    simpa only [Bind.bind, Except.bind, balanceProgram_lang] using
      resetPythonTable_get hctxChecker hctxProto hctx hkctx
  have args : evalArgValues (k + 4) (balanceProgram .python) m f
      (.sequence (.local "name") (.sequence (.object .empty) .empty)) =
        .ok ⟨n, .ok [.string "balance", .object m.nextObject]⟩ := by
    rw [evalArgValues, evalExpr_adequate (.localRead hn) (by omega)]
    simp only [Bind.bind, Except.bind]
    have empty : evalExpr (k + 2) (balanceProgram .python) m f (.object .empty) =
        .ok ⟨n, .ok (.object m.nextObject)⟩ := by
      simpa only [balanceProgram_lang] using
        (evalExpr_adequate (program := balanceProgram .python)
          (machine := m) (frame := f) .objectEmpty (k := k + 2) (by omega))
    rw [evalArgValues, empty]
    simp only [Bind.bind, Except.bind, evalArgValues, Pure.pure, Except.pure]
  have first : evalExpr (k + 5) (balanceProgram .python) m f
      (.call (.property (.index (.local "_WORLD") (.string "context")) "get")
        (.sequence (.local "name") (.sequence (.object .empty) .empty))) =
          .ok ⟨n, .ok (.object definition)⟩ := by
    rw [evalExpr, get]
    simp only [Bind.bind, Except.bind]
    rw [args]
    simp only [Bind.bind, Except.bind]
    change hostCall (balanceProgram .python).lang n .dictGet (some (.object context))
      [.string "balance", .object m.nextObject] = _
    rw [balanceProgram_lang]
    delta hostCall
    simp only [readOwn, hcN, hpctx, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  have getDef : evalExpr (k + 6) (balanceProgram .python) m f
      (.property (.call (.property (.index (.local "_WORLD") (.string "context")) "get")
        (.sequence (.local "name") (.sequence (.object .empty) .empty))) "get") =
          .ok ⟨n, .ok (.boundBuiltin .dictGet (.object definition))⟩ := by
    rw [evalExpr, first]
    simpa only [Bind.bind, Except.bind, balanceProgram_lang] using
      resetPythonTable_get (m := n) hdefChecker hdefProto hdN hkdef
  have typ : evalExpr (k + 7) (balanceProgram .python) m f
      (.call (.property (.call (.property (.index (.local "_WORLD") (.string "context")) "get")
        (.sequence (.local "name") (.sequence (.object .empty) .empty))) "get")
        (.sequence (.string "type") .empty)) = .ok ⟨n, .ok (.string "integer")⟩ := by
    rw [evalExpr, getDef]
    simp only [Bind.bind, Except.bind]
    rw [evalArgValues, evalExpr_adequate (.string "type") (by omega)]
    simp only [Bind.bind, Except.bind, evalArgValues, Pure.pure, Except.pure]
    change hostCall (balanceProgram .python).lang n .dictGet (some (.object definition))
      [.string "type"] = _
    rw [balanceProgram_lang]
    delta hostCall
    simp only [readOwn, hdN, hpdef, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  unfold resetPythonOverlayGuardType
  rw [evalExpr, typ]
  simp only [Bind.bind, Except.bind]
  rw [evalExpr_adequate (.string "string") (by omega), balanceProgram_lang]
  rfl

/-- Fixed cell addresses in the canonical Python reset frame. -/
def resetPythonCanonicalBindings : List (String × Nat × TargetValue) :=
  [("type", 0, .builtin .type), ("str", 7, .builtin .strType),
    ("_WORLD", 69, .object 63), ("_safe_integer", 84, .closure 4),
    ("int", 6, .builtin .int), ("float", 5, .builtin .float),
    ("abs", 14, .builtin .abs), ("_MAX_INTEGER", 79, integerValue .python 9007199254740991),
    ("math", 21, .object 4), ("candidate", 108, .object 79)]

def resetPythonCanonicalBindingsCheck : Bool :=
  let e := balanceResetMiddleEntry .python 0
  resetPythonCanonicalBindings.all fun entry =>
    decide (snapshotAddress e.1 e.2 entry.1 = some entry.2.1 ∧
      entry.2.1 < e.1.nextCell ∧ localValue e.1 e.2 entry.1 = .ok entry.2.2 ∧
      entry.1 ≠ "name" ∧ entry.1 ≠ "value" ∧ entry.1 ≠ "this" ∧ entry.1 ≠ "self")

set_option maxHeartbeats 10000000 in
theorem resetPythonCanonicalBindingsCheck_true : resetPythonCanonicalBindingsCheck = true := by
  unfold resetPythonCanonicalBindingsCheck balanceResetMiddleEntry balanceResetCandidateEntry
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel



def balanceResetPythonOverlayBound (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceResetMiddleEntry .python b
  resetOverlayPairBinding .python (resetIterableMachine .python e.1 b) e.2 (integerValue .python b)

set_option maxHeartbeats 10000000 in
/-- Every fixed canonical environment read survives iterable allocation and
    fresh pair binding, independently of the symbolic supplied balance. -/
theorem balanceReset_python_canonical_overlay_environment (b : Int) {entry}
    (he : entry ∈ resetPythonCanonicalBindings) :
    localValue (balanceResetPythonOverlayBound b).1 (balanceResetPythonOverlayBound b).2 entry.1 =
      .ok entry.2.2 := by
  have ht := resetPythonCanonicalBindingsCheck_true
  unfold resetPythonCanonicalBindingsCheck at ht
  have h := (List.all_eq_true.mp ht) entry he
  simp only [decide_eq_true_eq] at h
  obtain ⟨ha, hf, hv, hn⟩ := h
  have hab : snapshotAddress (balanceResetMiddleEntry .python b).1
      (balanceResetMiddleEntry .python b).2 entry.1 = some entry.2.1 := by
    rw [balanceResetMiddleEntry_address]; exact ha
  have hfb : entry.2.1 < (balanceResetMiddleEntry .python b).1.nextCell := by
    rw [balanceResetMiddleEntry_nextCell]; exact hf
  have hval : localValue (balanceResetMiddleEntry .python b).1
      (balanceResetMiddleEntry .python b).2 entry.1 = .ok entry.2.2 := by
    rw [balanceResetMiddleEntry_localValue]; exact hv
  unfold balanceResetPythonOverlayBound
  generalize heq : balanceResetMiddleEntry .python b = e at hab hfb hval ⊢
  rw [resetOverlayPairBinding_preserves_local
      (lang := .python) (m := resetIterableMachine .python e.1 b)
      (f := e.2) (value := integerValue .python b) hn hab hfb,
    resetIterableMachine_localValue]
  exact hval




/-- Preserve old heap reads across iterable and fresh pair allocations. -/
theorem resetIterableMachine_objectAt_other {lang m b ref} (hf : ref < m.nextObject) :
    objectAt (resetIterableMachine lang m b) ref = objectAt m ref := by
  have h1 : ref ≠ m.nextObject := Nat.ne_of_lt hf
  have h2 : ref ≠ m.nextObject + 1 := Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_succ_self _))
  have h3 : ref ≠ m.nextObject + 2 := Nat.ne_of_lt
    (Nat.lt_trans hf (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
  cases lang <;> simp only [show (TargetLang.python == .ts) = false from rfl,
    beq_self_eq_true, Bool.false_eq_true, if_false, if_true, Nat.add_assoc, resetIterableMachine, oneEntryMachine, allocObject,
    objectAt, List.lookup_cons, beq_eq_false_iff_ne.mpr h1,
    beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h3]
  all_goals rfl

theorem resetOverlayPairBinding_objectAt (lang m f value ref) :
    objectAt (resetOverlayPairBinding lang m f value).1 ref = objectAt m ref := rfl

theorem resetCandidateMiddleModel_objectAt_other {lang m f seed ref}
    (hf : ref ≠ m.nextObject) :
    objectAt (resetCandidateMiddleModel lang (m, f) seed).1 ref = objectAt m ref := by
  cases lang <;> change objectAt (allocObject m (balanceHeapObject _ m 100)).1 ref = _
  all_goals exact objectAt_allocObject_other hf

theorem balanceResetPythonOverlayBound_objectAt (b : Int) (ref : ObjRef)
    (hf : ref < (balanceCanonicalResetStage .python 0 3).1.nextObject)
    (hs : ref ≠ (balancePreparation .python).1.nextObject) :
    objectAt (balanceResetPythonOverlayBound b).1 ref =
      objectAt (balanceCanonicalResetStage .python 0 3).1 ref := by
  have hstage := balanceCanonicalResetStage_footprint .python b 3 (by decide)
  have hfb : ref < (balanceCanonicalResetStage .python b 3).1.nextObject := by
    rw [hstage.2.2.2.2.1]; exact hf
  have hm : ref < (balanceResetMiddleEntry .python b).1.nextObject := by
    change ref < (balanceCanonicalResetStage .python b 3).1.nextObject + 1
    exact Nat.lt_trans hfb (Nat.lt_succ_self _)
  unfold balanceResetPythonOverlayBound
  rw [resetOverlayPairBinding_objectAt, resetIterableMachine_objectAt_other hm,
    balanceResetMiddleEntry_model, resetCandidateMiddleModel_objectAt_other (Nat.ne_of_lt hfb)]
  exact balanceCanonicalResetStage_objectAt .python b 3 (by decide) ref hs



def resetPythonCanonicalTableObject (ref : ObjRef) : HeapObject :=
  (objectAt (balanceCanonicalResetStage .python 0 3).1 ref).toOption.getD
    (literalObject .python TargetMachine.empty)

def resetPythonCanonicalTablesCheck : Prop :=
  let m := (balanceCanonicalResetStage .python 0 3).1
  m.nextObject = 79 ∧ m.checkerRef = 1 ∧ m.objectPrototype = 0 ∧
  (balancePreparation .python).1.nextObject = 74 ∧
  objectAt m 63 = .ok (resetPythonCanonicalTableObject 63) ∧
  (resetPythonCanonicalTableObject 63).kind = .mappingProxy ∧
  (resetPythonCanonicalTableObject 63).own.lookup "context" =
    some ⟨some (.object 42), none, none, true, true, true⟩ ∧
  objectAt m 42 = .ok (resetPythonCanonicalTableObject 42) ∧
  (resetPythonCanonicalTableObject 42).kind = .mappingProxy ∧
  (resetPythonCanonicalTableObject 42).own.lookup "balance" =
    some ⟨some (.object 41), none, none, true, true, true⟩ ∧
  objectAt m 41 = .ok (resetPythonCanonicalTableObject 41) ∧
  (resetPythonCanonicalTableObject 41).kind = .mappingProxy ∧
  (resetPythonCanonicalTableObject 41).own.lookup "type" =
    some ⟨some (.string "integer"), none, none, true, true, true⟩

instance : Decidable resetPythonCanonicalTablesCheck := by
  unfold resetPythonCanonicalTablesCheck; infer_instance

set_option maxHeartbeats 10000000 in
theorem resetPythonCanonicalTablesCheck_true : resetPythonCanonicalTablesCheck := by
  unfold resetPythonCanonicalTablesCheck resetPythonCanonicalTableObject
    balanceCanonicalResetStage balanceCanonicalResetEntry balanceResetBodyEntry
    balancePythonResetBodyEntry balanceConstructorBodyEntry balanceConstructorBoundEntry
    balanceConstructorArgumentEntry balanceStoredReset balanceResetLookup balanceStoredConstructor
    balanceConstructorLookup balanceConstructorName balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel



set_option maxHeartbeats 10000000 in
/-- Both source-selected Python type-table tests at the canonical loop body
    entry. The first retains the eagerly allocated fallback dictionary. -/
theorem balanceReset_python_canonical_table_tests (b : Int) (k : Nat) :
    let e := balanceResetPythonOverlayBound b
    evalExpr (k + 8) (balanceProgram .python) e.1 e.2 resetPythonOverlayGuardType =
      .ok ⟨resetPythonOverlayTypedMachine e.1, .ok (.bool false)⟩ ∧
    evalExpr (k + 5) (balanceProgram .python) e.1 e.2 resetPythonOverlayStringTest =
      .ok ⟨e.1, .ok (.bool false)⟩ := by
  obtain ⟨hnext, hchecker, hproto, hseed, hw, hwk, hwp, hc, hck, hcp, hd, hdk, hdp⟩ :=
    resetPythonCanonicalTablesCheck_true
  let e := balanceResetPythonOverlayBound b
  have objs (ref : ObjRef) (h : ref = 63 ∨ ref = 42 ∨ ref = 41) :
      objectAt e.1 ref = .ok (resetPythonCanonicalTableObject ref) := by
    rcases h with rfl | rfl | rfl
    all_goals rw [balanceResetPythonOverlayBound_objectAt b _ (by rw [hnext]; decide) (by rw [hseed]; decide)]
    · exact hw
    · exact hc
    · exact hd
  have checker : e.1.checkerRef = 1 := by
    change (balanceCanonicalResetStage .python b 3).1.checkerRef = 1
    rw [(balanceCanonicalResetStage_footprint .python b 3 (by decide)).2.2.2.2.2.2.1]
    exact hchecker
  have proto : e.1.objectPrototype = 0 := by
    change (balanceCanonicalResetStage .python b 3).1.objectPrototype = 0
    rw [(balanceCanonicalResetStage_footprint .python b 3 (by decide)).2.2.2.2.2.1]
    exact hproto
  have next : e.1.nextObject = 83 := by
    change (balanceCanonicalResetStage .python b 3).1.nextObject + 1 + 1 + 1 + 1 = 83
    rw [(balanceCanonicalResetStage_footprint .python b 3 (by decide)).2.2.2.2.1, hnext]
  have world : localValue e.1 e.2 "_WORLD" = .ok (.object 63) :=
    balanceReset_python_canonical_overlay_environment b (entry := ("_WORLD", 69, .object 63)) (by decide)
  have name : localValue e.1 e.2 "name" = .ok (.string "balance") :=
    (resetOverlayPairBinding_reads .python
      (resetIterableMachine .python (balanceResetMiddleEntry .python b).1 b)
      (balanceResetMiddleEntry .python b).2 (integerValue .python b)).1
  have context : readPropertyValue .python e.1 (.object 63) "context" = .ok ⟨e.1, .ok (.object 42)⟩ :=
    resetPythonTable_read (m := e.1) (ref := 63) (key := "context")
      (by rw [checker]; decide) (by rw [proto]; decide) (by decide)
      (objs 63 (.inl rfl)) hwk hwp
  constructor
  · exact resetPythonOverlayGuardType_execute world name context
      (objs 42 (.inr (.inl rfl))) hck hcp (objs 41 (.inr (.inr rfl))) hdk hdp
      (by rw [checker]; decide) (by rw [proto]; decide)
      (by rw [checker]; decide) (by rw [proto]; decide)
      (by rw [next]; decide) (by rw [next]; decide)
  · exact resetPythonOverlayStringTest_execute world name context
      (resetPythonTable_read (m := e.1) (ref := 42) (key := "balance")
        (by rw [checker]; decide) (by rw [proto]; decide) (by decide)
        (objs 42 (.inr (.inl rfl))) hck hcp)
      (resetPythonTable_read (m := e.1) (ref := 41) (key := "type")
        (by rw [checker]; decide) (by rw [proto]; decide) (by decide)
        (objs 41 (.inr (.inr rfl))) hdk hdp)

-- Canonical signed-safe Python overlay: physical helper discharge and composition.

/-- Updating a different heap entry preserves an existing lookup. -/
theorem lookup_replace_payload_other {α : Type} (entries : List (Nat × α))
    {ref target : Nat} (value : α) (hn : ref ≠ target) :
    (entries.map (fun entry => (entry.1, if entry.1 == target then value else entry.2))).lookup ref =
      entries.lookup ref := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, old⟩
    by_cases h : ref = key
    · subst key
      simp [List.lookup_cons, hn, beq_eq_false_iff_ne.mpr hn]
    · simp only [List.map_cons, List.lookup_cons, Prod.fst, Prod.snd,
        beq_eq_false_iff_ne.mpr h, if_false, ih]

theorem resetSafeTupleMachine_objectAt_other {m ref} (hn : ref ≠ m.nextObject) :
    objectAt (resetSafeTupleMachine m) ref = objectAt m ref := by
  unfold objectAt resetSafeTupleMachine resetSafeTupleStage
  simp only [allocObject, Prod.fst]
  rw [lookup_replace_payload_other _ _ hn, lookup_replace_payload_other _ _ hn]
  simp [List.lookup_cons, hn, beq_eq_false_iff_ne.mpr hn]

theorem localValue_allocCell_preserved {m f name ref value}
    (hn : name ≠ "this" ∧ name ≠ "self")
    (ha : snapshotAddress m f name = some ref) (hf : ref < m.nextCell) :
    localValue (allocCell m value true).1 f name = localValue m f name := by
  have hb : snapshotAddress (allocCell m value true).1 f name = some ref := ha
  rw [localValue_of_snapshotAddress hn hb, localValue_of_snapshotAddress hn ha]
  simp [readCell, allocCell, List.lookup_cons, beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hf)]

/-- Physical post-helper machine, retaining the eager default dict and tuple. -/
def balanceResetPythonOverlayAfterHelper (b : Int) : TargetMachine :=
  resetSafeTupleMachine (resetPythonSafeCallEntry
    (resetPythonOverlayTypedMachine (balanceResetPythonOverlayBound b).1)
    balancePythonSafeIntegerClosure b).1

/-- Closed helper binding inventory; no execution result is assumed. -/
def resetPythonCanonicalHelperBindingsCheck : Prop :=
  let m := (balanceCanonicalResetStage .python 0 3).1
  let f := closureFrame balancePythonSafeIntegerClosure
  balancePythonSafeIntegerClosure.params = [⟨"value", none⟩] ∧
  closureAt (balanceResetPythonOverlayBound 0).1 4 = .ok balancePythonSafeIntegerClosure ∧
  m.nextCell = 108 ∧
  (resetPythonCanonicalBindings.take 9).all (fun entry =>
    decide (entry.1 ≠ "value" ∧ entry.1 ≠ "this" ∧ entry.1 ≠ "self" ∧
      snapshotAddress m f entry.1 = some entry.2.1 ∧ entry.2.1 < m.nextCell ∧
      localValue m f entry.1 = .ok entry.2.2)) = true

instance : Decidable resetPythonCanonicalHelperBindingsCheck := by
  unfold resetPythonCanonicalHelperBindingsCheck; infer_instance

set_option maxHeartbeats 10000000 in
theorem resetPythonCanonicalHelperBindingsCheck_true : resetPythonCanonicalHelperBindingsCheck := by
  unfold resetPythonCanonicalHelperBindingsCheck balanceResetPythonOverlayBound
    balanceResetMiddleEntry balanceResetCandidateEntry balanceCanonicalResetStage
    balanceCanonicalResetEntry balanceResetBodyEntry balancePythonResetBodyEntry
    balanceConstructorBodyEntry balanceConstructorBoundEntry balanceConstructorArgumentEntry
    balanceStoredReset balanceResetLookup balanceStoredConstructor balanceConstructorLookup
    balanceConstructorName balancePreparation balancePythonSafeIntegerClosure
  simp only [balancePreparation, balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel


/-- Old lexical cells survive the candidate, context, pair, eager dictionary,
    and helper-argument allocations. The stage and closure are abstract. -/
theorem resetPythonCanonicalHelper_read_generic
    (stage : TargetMachine × TargetFrame) (seed : ObjRef) (b : Int)
    (closure : TargetClosure) (name : String) (ref : CellRef) (value : TargetValue)
    (hn : name ≠ "value" ∧ name ≠ "this" ∧ name ≠ "self")
    (ha : snapshotAddress stage.1 (closureFrame closure) name = some ref)
    (hf : ref < stage.1.nextCell)
    (hv : localValue stage.1 (closureFrame closure) name = .ok value) :
    let original := resetCandidateMiddleModel .python stage seed
    let bound := resetOverlayPairBinding .python
      (resetIterableMachine .python original.1 b) original.2 (.number .pyInt b)
    let call := resetPythonSafeCallEntry (resetPythonOverlayTypedMachine bound.1) closure b
    localValue call.1 call.2 name = .ok value := by
  let original := resetCandidateMiddleModel .python stage seed
  let bound := resetOverlayPairBinding .python
    (resetIterableMachine .python original.1 b) original.2 (.number .pyInt b)
  let call := resetPythonSafeCallEntry (resetPythonOverlayTypedMachine bound.1) closure b
  change localValue call.1 call.2 name = .ok value
  have address : snapshotAddress call.1 call.2 name = some ref := by
    dsimp only [call, resetPythonSafeCallEntry, snapshotAddress, closureFrame]
    simp only [List.lookup_cons, List.lookup_nil, beq_eq_false_iff_ne.mpr hn.1, if_false, Option.orElse]
    have hg : (resetPythonOverlayTypedMachine bound.1).globals = stage.1.globals := by
      simp only [bound, original, resetPythonOverlayTypedMachine, resetOverlayPairBinding,
        forPairBound, resetIterableMachine, oneEntryMachine, resetCandidateMiddleModel,
        snapshotBound, resetTsOverridesEntry, allocCell, allocObject, Prod.fst, Prod.snd,
        beq_self_eq_true, show (TargetLang.python == .ts) = false from rfl, Bool.false_eq_true, if_false, if_true]
    simp only [allocCell, Prod.fst, hg]
    exact ha
  rw [localValue_of_snapshotAddress ⟨hn.2.1, hn.2.2⟩ address]
  rw [localValue_of_snapshotAddress ⟨hn.2.1, hn.2.2⟩ ha] at hv
  have ne (i : Nat) : ref ≠ stage.1.nextCell + i := by
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hf (Nat.le_add_right _ _))
  have read : readCell call.1 ref = readCell stage.1 ref := by
    change (match
      ((stage.1.nextCell + 4, TargetValue.number .pyInt b) ::
       (stage.1.nextCell + 3, TargetValue.number .pyInt b) ::
       (stage.1.nextCell + 2, TargetValue.string "balance") ::
       (stage.1.nextCell + 1, TargetValue.object seed) ::
       (stage.1.nextCell, TargetValue.object stage.1.nextObject) :: stage.1.cells).lookup ref with
      | some found => Except.ok found
      | none => Except.error (TargetError.danglingCell ref)) = _
    simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr (ne 4),
      beq_eq_false_iff_ne.mpr (ne 3), beq_eq_false_iff_ne.mpr (ne 2),
      beq_eq_false_iff_ne.mpr (ne 1),
      beq_eq_false_iff_ne.mpr (show ref ≠ stage.1.nextCell from by simpa using ne 0), if_false]
    rfl
  exact read.trans hv

set_option maxHeartbeats 10000000 in
theorem balanceReset_python_canonical_helper_environment (b : Int) {entry}
    (he : entry ∈ resetPythonCanonicalBindings.take 9) :
    let e := resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine (balanceResetPythonOverlayBound b).1)
      balancePythonSafeIntegerClosure b
    localValue e.1 e.2 entry.1 = .ok entry.2.2 := by
  obtain ⟨_, _, _, check⟩ := resetPythonCanonicalHelperBindingsCheck_true
  have h := List.all_eq_true.mp check entry he
  simp only [decide_eq_true_eq] at h
  obtain ⟨hn, ht, hs, ha, hf, hv⟩ := h
  have foot := balanceCanonicalResetStage_footprint .python b 3 (by decide)
  apply resetPythonCanonicalHelper_read_generic
    (stage := balanceCanonicalResetStage .python b 3)
    (seed := (balancePreparation .python).1.nextObject)
    (b := b) (closure := balancePythonSafeIntegerClosure)
    (name := entry.1) (ref := entry.2.1) (value := entry.2.2)
  · exact ⟨hn, ht, hs⟩
  · simpa only [snapshotAddress, foot.2.2.2.1] using ha
  · rw [foot.2.2.2.2.2.2.2.2]; exact hf
  · exact (localValue_fields_congr rfl foot.2.2.1 foot.2.2.2.1).trans hv

theorem resetOverlayPairBinding_nextObject (lang m f value) :
    (resetOverlayPairBinding lang m f value).1.nextObject = m.nextObject := rfl

theorem resetOverlayPairBinding_nextCell (lang m f value) :
    (resetOverlayPairBinding lang m f value).1.nextCell = m.nextCell + 2 := rfl

theorem resetIterableMachine_nextObject_python (m b) :
    (resetIterableMachine .python m b).nextObject = m.nextObject + 3 := rfl

theorem resetIterableMachine_nextCell (lang m b) :
    (resetIterableMachine lang m b).nextCell = m.nextCell := by cases lang <;> rfl

theorem resetCandidateMiddleModel_nextObject_python (stage seed) :
    (resetCandidateMiddleModel .python stage seed).1.nextObject = stage.1.nextObject + 1 := rfl

theorem resetCandidateMiddleModel_nextCell_python (stage seed) :
    (resetCandidateMiddleModel .python stage seed).1.nextCell = stage.1.nextCell + 2 := rfl

theorem balanceResetPythonOverlayBound_next (b : Int) :
    (balanceResetPythonOverlayBound b).1.nextObject = 83 ∧
    (balanceResetPythonOverlayBound b).1.nextCell = 112 := by
  have ho := (balanceCanonicalResetStage_footprint .python b 3 (by decide)).2.2.2.2.1
  have hc := (balanceCanonicalResetStage_footprint .python b 3 (by decide)).2.2.2.2.2.2.2.2
  unfold balanceResetPythonOverlayBound
  constructor
  · rw [resetOverlayPairBinding_nextObject, resetIterableMachine_nextObject_python,
      balanceResetMiddleEntry_model, resetCandidateMiddleModel_nextObject_python, ho,
      resetPythonCanonicalTablesCheck_true.1]
  · rw [resetOverlayPairBinding_nextCell, resetIterableMachine_nextCell,
      balanceResetMiddleEntry_model, resetCandidateMiddleModel_nextCell_python, hc,
      resetPythonCanonicalHelperBindingsCheck_true.2.2.1]

/-- Helper effects preserve caller cells below the fresh argument address. -/
theorem resetPythonHelperResult_localValue {m f closure b name ref}
    (hn : name ≠ "this" ∧ name ≠ "self")
    (ha : snapshotAddress m f name = some ref) (hf : ref < m.nextCell) :
    localValue (resetSafeTupleMachine (resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine m) closure b).1) f name = localValue m f name := by
  exact localValue_allocCell_preserved (m := resetPythonOverlayTypedMachine m)
    (value := integerValue .python b) hn ha hf

theorem balanceResetPythonOverlayAfterHelper_localValue {b name ref}
    (hn : name ≠ "this" ∧ name ≠ "self")
    (ha : snapshotAddress (balanceResetPythonOverlayBound b).1
      (balanceResetPythonOverlayBound b).2 name = some ref)
    (hf : ref < (balanceResetPythonOverlayBound b).1.nextCell) :
    localValue (balanceResetPythonOverlayAfterHelper b) (balanceResetPythonOverlayBound b).2 name =
      localValue (balanceResetPythonOverlayBound b).1 (balanceResetPythonOverlayBound b).2 name :=
  resetPythonHelperResult_localValue hn ha hf

theorem resetPythonHelperResult_objectAt {m closure b ref} (hf : ref < m.nextObject) :
    objectAt (resetSafeTupleMachine (resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine m) closure b).1) ref = objectAt m ref := by
  rw [resetSafeTupleMachine_objectAt_other (by
    change ref ≠ m.nextObject + 1
    exact Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_succ_self _)))]
  change objectAt (allocObject m (literalObject .python m)).1 ref = _
  exact objectAt_allocObject_other (Nat.ne_of_lt hf)

theorem balanceResetPythonOverlayAfterHelper_objectAt {b ref} (hf : ref < 83) :
    objectAt (balanceResetPythonOverlayAfterHelper b) ref =
      objectAt (balanceResetPythonOverlayBound b).1 ref := by
  apply resetPythonHelperResult_objectAt
  rw [(balanceResetPythonOverlayBound_next b).1]; exact hf

theorem resetOverlayPairBinding_address_other {lang m f value name ref}
    (hn : name ≠ "value" ∧ name ≠ "name") (ha : snapshotAddress m f name = some ref) :
    snapshotAddress (resetOverlayPairBinding lang m f value).1
      (resetOverlayPairBinding lang m f value).2 name = some ref := by
  simpa only [resetOverlayPairBinding, forPairBound, snapshotAddress, allocCell,
    List.lookup_cons, beq_eq_false_iff_ne.mpr hn.1, beq_eq_false_iff_ne.mpr hn.2, if_false] using ha

theorem resetIterableMachine_address (lang m f b name) :
    snapshotAddress (resetIterableMachine lang m b) f name = snapshotAddress m f name := by
  cases lang <;> rfl

/-- Every fixed caller binding survives the canonical helper invocation. -/
theorem balanceResetPythonOverlayAfterHelper_environment (b : Int) {entry}
    (he : entry ∈ resetPythonCanonicalBindings) :
    localValue (balanceResetPythonOverlayAfterHelper b) (balanceResetPythonOverlayBound b).2 entry.1 =
      .ok entry.2.2 := by
  have check := List.all_eq_true.mp resetPythonCanonicalBindingsCheck_true entry he
  simp only [resetPythonCanonicalBindingsCheck, decide_eq_true_eq] at check
  obtain ⟨ha, hf, _, hn, hv, ht, hs⟩ := check
  have hab : snapshotAddress (balanceResetMiddleEntry .python b).1
      (balanceResetMiddleEntry .python b).2 entry.1 = some entry.2.1 := by
    rw [balanceResetMiddleEntry_address]; exact ha
  have hfb : entry.2.1 < (balanceResetMiddleEntry .python b).1.nextCell := by
    rw [balanceResetMiddleEntry_nextCell]; exact hf
  have bound : snapshotAddress (balanceResetPythonOverlayBound b).1
      (balanceResetPythonOverlayBound b).2 entry.1 = some entry.2.1 := by
    apply resetOverlayPairBinding_address_other ⟨hv, hn⟩
    rw [resetIterableMachine_address]; exact hab
  have fresh : entry.2.1 < (balanceResetPythonOverlayBound b).1.nextCell := by
    unfold balanceResetPythonOverlayBound
    rw [resetOverlayPairBinding_nextCell, resetIterableMachine_nextCell]
    exact Nat.lt_trans hfb (Nat.lt_add_of_pos_right (by decide : 0 < 2))
  rw [balanceResetPythonOverlayAfterHelper_localValue ⟨ht, hs⟩ bound fresh]
  exact balanceReset_python_canonical_overlay_environment b he

theorem resetPythonHelperResult_pair_reads (m f closure b) :
    let e := resetOverlayPairBinding .python m f (integerValue .python b)
    let n := resetSafeTupleMachine (resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine e.1) closure b).1
    localValue n e.2 "name" = .ok (.string "balance") ∧
    localValue n e.2 "value" = .ok (integerValue .python b) := by
  let e := resetOverlayPairBinding .python m f (integerValue .python b)
  have name : snapshotAddress e.1 e.2 "name" = some m.nextCell := by
    simp [e, resetOverlayPairBinding, forPairBound, snapshotAddress, allocCell, List.lookup, Option.orElse]
  have value : snapshotAddress e.1 e.2 "value" = some (m.nextCell + 1) := by
    simp [e, resetOverlayPairBinding, forPairBound, snapshotAddress, allocCell, List.lookup, Option.orElse]
  constructor
  · rw [resetPythonHelperResult_localValue (by decide) name (by
      rw [resetOverlayPairBinding_nextCell]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2))]
    exact (resetOverlayPairBinding_reads .python m f (integerValue .python b)).1
  · rw [resetPythonHelperResult_localValue (by decide) value (by
      rw [resetOverlayPairBinding_nextCell]; exact Nat.lt_succ_self _)]
    exact (resetOverlayPairBinding_reads .python m f (integerValue .python b)).2

theorem balanceResetPythonOverlayAfterHelper_pair_reads (b : Int) :
    localValue (balanceResetPythonOverlayAfterHelper b) (balanceResetPythonOverlayBound b).2 "name" =
      .ok (.string "balance") ∧
    localValue (balanceResetPythonOverlayAfterHelper b) (balanceResetPythonOverlayBound b).2 "value" =
      .ok (integerValue .python b) := resetPythonHelperResult_pair_reads _ _ _ _

/-- A data property in an ordinary host module is read without allocation. -/
theorem resetPythonOrdinaryTable_read {m ref object key value}
    (hr : ref ≠ m.checkerRef) (hp : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok object) (hk : object.kind = .jsOrdinary)
    (hv : object.own.lookup key = some ⟨some value, none, none, true, true, true⟩) :
    readPropertyValue .python m (.object ref) key = .ok ⟨m, .ok value⟩ := by
  simp [readPropertyValue, beq_eq_false_iff_ne.mpr hr, beq_eq_false_iff_ne.mpr hp,
    ho, hk, readOwn, hv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

def resetPythonCanonicalMathCheck : Prop :=
  let object := resetPythonCanonicalTableObject 4
  objectAt (balanceCanonicalResetStage .python 0 3).1 4 = .ok object ∧
  object.kind = .jsOrdinary ∧
  object.own.lookup "isfinite" = some ⟨some (.builtin .isFinite), none, none, true, true, true⟩

instance : Decidable resetPythonCanonicalMathCheck := by
  unfold resetPythonCanonicalMathCheck; infer_instance

set_option maxHeartbeats 10000000 in
theorem resetPythonCanonicalMathCheck_true : resetPythonCanonicalMathCheck := by
  simp only [resetPythonCanonicalMathCheck, resetPythonCanonicalTableObject,
    balanceCanonicalResetStage, balanceCanonicalResetEntry, balanceResetBodyEntry,
    balancePythonResetBodyEntry, balanceConstructorBodyEntry, balanceConstructorBoundEntry,
    balanceConstructorArgumentEntry, balanceStoredReset, balanceResetLookup,
    balanceStoredConstructor, balanceConstructorLookup, balanceConstructorName,
    balancePreparation, balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel


theorem resetPythonHelperResult_checkerRef (m closure b) :
    (resetSafeTupleMachine (resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine m) closure b).1).checkerRef = m.checkerRef := rfl

theorem resetPythonHelperResult_objectPrototype (m closure b) :
    (resetSafeTupleMachine (resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine m) closure b).1).objectPrototype = m.objectPrototype := rfl

theorem resetOverlayPairBinding_checkerRef (lang m f value) :
    (resetOverlayPairBinding lang m f value).1.checkerRef = m.checkerRef := rfl

theorem resetOverlayPairBinding_objectPrototype (lang m f value) :
    (resetOverlayPairBinding lang m f value).1.objectPrototype = m.objectPrototype := rfl

theorem resetIterableMachine_checkerRef (lang m b) :
    (resetIterableMachine lang m b).checkerRef = m.checkerRef := by cases lang <;> rfl

theorem resetIterableMachine_objectPrototype (lang m b) :
    (resetIterableMachine lang m b).objectPrototype = m.objectPrototype := by cases lang <;> rfl

theorem resetCandidateMiddleModel_checkerRef_python (stage seed) :
    (resetCandidateMiddleModel .python stage seed).1.checkerRef = stage.1.checkerRef := rfl

theorem resetCandidateMiddleModel_objectPrototype_python (stage seed) :
    (resetCandidateMiddleModel .python stage seed).1.objectPrototype = stage.1.objectPrototype := rfl

theorem balanceResetPythonOverlayAfterHelper_fixed (b : Int) :
    (balanceResetPythonOverlayAfterHelper b).checkerRef = 1 ∧
    (balanceResetPythonOverlayAfterHelper b).objectPrototype = 0 := by
  have h := balanceCanonicalResetStage_footprint .python b 3 (by decide)
  unfold balanceResetPythonOverlayAfterHelper balanceResetPythonOverlayBound
  constructor
  · rw [resetPythonHelperResult_checkerRef, resetOverlayPairBinding_checkerRef,
      resetIterableMachine_checkerRef, balanceResetMiddleEntry_model,
      resetCandidateMiddleModel_checkerRef_python, h.2.2.2.2.2.2.1]
    exact resetPythonCanonicalTablesCheck_true.2.1
  · rw [resetPythonHelperResult_objectPrototype, resetOverlayPairBinding_objectPrototype,
      resetIterableMachine_objectPrototype, balanceResetMiddleEntry_model,
      resetCandidateMiddleModel_objectPrototype_python, h.2.2.2.2.2.1]
    exact resetPythonCanonicalTablesCheck_true.2.2.1

theorem balanceResetPythonOverlayAfterHelper_old_object (b : Int) (ref : ObjRef)
    (hf : ref < 79) (hs : ref ≠ 74) :
    objectAt (balanceResetPythonOverlayAfterHelper b) ref =
      objectAt (balanceCanonicalResetStage .python 0 3).1 ref := by
  rw [balanceResetPythonOverlayAfterHelper_objectAt (Nat.lt_trans hf (by decide : 79 < 83))]
  apply balanceResetPythonOverlayBound_objectAt b ref
  · rw [resetPythonCanonicalTablesCheck_true.1]; exact hf
  · rw [resetPythonCanonicalTablesCheck_true.2.2.2.1]; exact hs

theorem resetPythonSafeCallEntry_value (m : TargetMachine) (closure : TargetClosure) (b : Int) :
    localValue (resetPythonSafeCallEntry m closure b).1
      (resetPythonSafeCallEntry m closure b).2 "value" = .ok (integerValue .python b) := by
  simp [resetPythonSafeCallEntry, localValue, readCell, allocCell, List.lookup]

/-- All physical helper premises at the actual canonical argument frame. -/
def balanceReset_python_canonical_safe_physical (b : Int) :
    let e := resetPythonSafeCallEntry
      (resetPythonOverlayTypedMachine (balanceResetPythonOverlayBound b).1)
      balancePythonSafeIntegerClosure b
    ResetPythonSafePhysical e.1 e.2 b := by
  refine ⟨4, resetPythonSafeCallEntry_value
    (resetPythonOverlayTypedMachine (balanceResetPythonOverlayBound b).1) balancePythonSafeIntegerClosure b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact balanceReset_python_canonical_helper_environment b (entry := ("type", 0, .builtin .type)) (by decide)
  · exact balanceReset_python_canonical_helper_environment b (entry := ("int", 6, .builtin .int)) (by decide)
  · exact balanceReset_python_canonical_helper_environment b (entry := ("float", 5, .builtin .float)) (by decide)
  · exact balanceReset_python_canonical_helper_environment b (entry := ("abs", 14, .builtin .abs)) (by decide)
  · exact balanceReset_python_canonical_helper_environment b
      (entry := ("_MAX_INTEGER", 79, integerValue .python 9007199254740991)) (by decide)
  · exact balanceReset_python_canonical_helper_environment b (entry := ("math", 21, .object 4)) (by decide)
  · obtain ⟨ho, hk, hv⟩ := resetPythonCanonicalMathCheck_true
    exact resetPythonOrdinaryTable_read (m := balanceResetPythonOverlayAfterHelper b) (ref := 4)
      (by rw [(balanceResetPythonOverlayAfterHelper_fixed b).1]; decide)
      (by rw [(balanceResetPythonOverlayAfterHelper_fixed b).2]; decide)
      ((balanceResetPythonOverlayAfterHelper_old_object b 4 (by decide) (by decide)).trans ho) hk hv

theorem balanceReset_python_canonical_post_table_test (b : Int) (k : Nat) :
    evalExpr (k + 5) (balanceProgram .python) (balanceResetPythonOverlayAfterHelper b)
      (balanceResetPythonOverlayBound b).2 resetPythonOverlayStringTest =
        .ok ⟨balanceResetPythonOverlayAfterHelper b, .ok (.bool false)⟩ := by
  obtain ⟨_, _, _, _, hw, hwk, hwp, hc, hck, hcp, hd, hdk, hdp⟩ := resetPythonCanonicalTablesCheck_true
  let n := balanceResetPythonOverlayAfterHelper b
  have objs (ref : ObjRef) (h : ref = 63 ∨ ref = 42 ∨ ref = 41) :
      objectAt n ref = .ok (resetPythonCanonicalTableObject ref) := by
    rcases h with rfl | rfl | rfl
    all_goals rw [balanceResetPythonOverlayAfterHelper_old_object b _ (by decide) (by decide)]
    · exact hw
    · exact hc
    · exact hd
  have checker := (balanceResetPythonOverlayAfterHelper_fixed b).1
  have proto := (balanceResetPythonOverlayAfterHelper_fixed b).2
  apply resetPythonOverlayStringTest_execute (world := 63) (context := 42) (definition := 41)
  · exact balanceResetPythonOverlayAfterHelper_environment b (entry := ("_WORLD", 69, .object 63)) (by decide)
  · exact (balanceResetPythonOverlayAfterHelper_pair_reads b).1
  · exact resetPythonTable_read (m := n) (ref := 63) (by rw [checker]; decide) (by rw [proto]; decide) (by decide)
      (objs 63 (.inl rfl)) hwk hwp
  · exact resetPythonTable_read (m := n) (ref := 42) (by rw [checker]; decide) (by rw [proto]; decide) (by decide)
      (objs 42 (.inr (.inl rfl))) hck hcp
  · exact resetPythonTable_read (m := n) (ref := 41) (by rw [checker]; decide) (by rw [proto]; decide) (by decide)
      (objs 41 (.inr (.inr rfl))) hdk hdp

theorem balanceHeapObject_python_machine (m n : TargetMachine) (b : Int) :
    balanceHeapObject .python m b = balanceHeapObject .python n b := rfl

/-- The existing candidate remains live across every helper allocation. -/
theorem balanceReset_python_canonical_post_candidate (b : Int) :
    localValue (balanceResetPythonOverlayAfterHelper b) (balanceResetPythonOverlayBound b).2 "candidate" =
      .ok (.object 79) ∧
    objectAt (balanceResetPythonOverlayAfterHelper b) 79 =
      .ok (balanceHeapObject .python (balanceResetPythonOverlayAfterHelper b) 100) := by
  constructor
  · exact balanceResetPythonOverlayAfterHelper_environment b (entry := ("candidate", 108, .object 79)) (by decide)
  · have key : (balanceCanonicalResetStage .python b 3).1.nextObject = 79 :=
      (balanceCanonicalResetStage_footprint .python b 3 (by decide)).2.2.2.2.1.trans
        resetPythonCanonicalTablesCheck_true.1
    have hn : (balanceResetMiddleEntry .python b).1.nextObject = 80 := by
      rw [balanceResetMiddleEntry_model, resetCandidateMiddleModel_nextObject_python, key]
    have mid : objectAt (balanceResetMiddleEntry .python b).1 79 =
        .ok (balanceHeapObject .python (balanceResetMiddleEntry .python b).1 100) := by
      simpa only [key] using balanceResetMiddleEntry_candidate_object .python b
    have before : objectAt (balanceResetPythonOverlayBound b).1 79 =
        objectAt (balanceResetMiddleEntry .python b).1 79 := by
      unfold balanceResetPythonOverlayBound
      rw [resetOverlayPairBinding_objectAt,
        resetIterableMachine_objectAt_other (m := (balanceResetMiddleEntry .python b).1)
          (b := b) (ref := 79) (by rw [hn]; decide)]
    exact (balanceResetPythonOverlayAfterHelper_objectAt (b := b) (ref := 79) (by decide)).trans
      (before.trans (mid.trans (congrArg (fun object : HeapObject => (Except.ok object : Except TargetError HeapObject))
        (balanceHeapObject_python_machine (balanceResetMiddleEntry .python b).1
          (balanceResetPythonOverlayAfterHelper b) 100))))

theorem balanceResetPythonOverlayBound_fixed (b : Int) :
    (balanceResetPythonOverlayBound b).1.checkerRef = 1 ∧
    (balanceResetPythonOverlayBound b).1.objectPrototype = 0 := by
  have h := balanceResetPythonOverlayAfterHelper_fixed b
  unfold balanceResetPythonOverlayAfterHelper at h
  rwa [resetPythonHelperResult_checkerRef, resetPythonHelperResult_objectPrototype] at h

theorem resetOverlayPairBinding_closureAt (lang m f value ref) :
    closureAt (resetOverlayPairBinding lang m f value).1 ref = closureAt m ref := rfl

theorem resetIterableMachine_closureAt (lang m b ref) :
    closureAt (resetIterableMachine lang m b) ref = closureAt m ref := by cases lang <;> rfl

theorem resetCandidateMiddleModel_closureAt_python (stage seed ref) :
    closureAt (resetCandidateMiddleModel .python stage seed).1 ref = closureAt stage.1 ref := rfl


theorem allocCell_nextClosure (m value mutable) :
    (allocCell m value mutable).1.nextClosure = m.nextClosure := rfl

theorem allocObject_nextClosure (m object) :
    (allocObject m object).1.nextClosure = m.nextClosure := rfl

theorem allocClosure_nextClosure (m closure) :
    (allocClosure m closure).1.nextClosure = m.nextClosure + 1 := rfl

/-- Closure lookup does not depend on the new function's body when its fresh
    closure address differs from the queried old address. -/
theorem functionInstalled_closureAt_other {lang : TargetLang}
    {m : TargetMachine} {f : TargetFrame} {name : String} {body : TargetStmt} {ref : ClosureRef}
    (hn : ref ≠ m.nextClosure) :
    closureAt (functionInstalled lang m f name body).1 ref = closureAt m ref := by
  let installed : TargetClosure := ⟨f.qualifiedName ++ "." ++ name, [], [], body,
    (name, m.nextCell) :: f.locals ++ f.captures, f.receiver⟩
  cases lang <;>
    change (match ((m.nextClosure, installed) :: m.closures).lookup ref with
      | some closure => Except.ok closure
      | none => Except.error (TargetError.danglingClosure ref)) = _
  all_goals simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hn, if_false]
  all_goals rfl

theorem resetSnapshotHistory_closureAt (lang m f ref) :
    closureAt (resetSnapshotHistory lang m f).1 ref = closureAt m ref := rfl

theorem resetSnapshotHistory_nextClosure (lang m f) :
    (resetSnapshotHistory lang m f).1.nextClosure = m.nextClosure := rfl

theorem resetSnapshotsInstalled_closureAt_other {lang m f ref}
    (hn : ref ≠ m.nextClosure) :
    closureAt (resetSnapshotsInstalled lang m f).1 ref = closureAt m ref := by
  unfold resetSnapshotsInstalled snapshotRollbackInstalled
  rw [functionInstalled_closureAt_other
    (m := (resetSnapshotHistory lang m f).1)
    (by rw [resetSnapshotHistory_nextClosure]; exact hn)]
  exact resetSnapshotHistory_closureAt lang m f ref

theorem balanceConstructorArgumentEntry_closureAt (lang b ref) :
    closureAt (balanceConstructorArgumentEntry lang b).1 ref =
      closureAt (balancePreparation lang).1 ref := by
  unfold balanceConstructorArgumentEntry
  rw [closureAt_allocCell, closureAt_allocObject]

theorem balanceConstructorArgumentEntry_nextClosure (lang b) :
    (balanceConstructorArgumentEntry lang b).1.nextClosure =
      (balancePreparation lang).1.nextClosure := by
  unfold balanceConstructorArgumentEntry
  rw [allocCell_nextClosure, allocObject_nextClosure]

theorem balanceConstructorBodyEntry_nextClosure (lang b) :
    (balanceConstructorBodyEntry lang b).1.nextClosure =
      (balancePreparation lang).1.nextClosure + 1 := by
  unfold balanceConstructorBodyEntry balanceConstructorBoundEntry
  rw [allocCell_nextClosure, allocClosure_nextClosure, balanceConstructorArgumentEntry_nextClosure]

theorem balanceConstructorBodyEntry_closureAt_other {lang b ref}
    (hn : ref ≠ (balancePreparation lang).1.nextClosure) :
    closureAt (balanceConstructorBodyEntry lang b).1 ref =
      closureAt (balancePreparation lang).1 ref := by
  unfold balanceConstructorBodyEntry balanceConstructorBoundEntry
  rw [closureAt_allocCell, closureAt_allocClosure_other
    (m := (balanceConstructorArgumentEntry lang b).1)
    (by rw [balanceConstructorArgumentEntry_nextClosure]; exact hn)]
  exact balanceConstructorArgumentEntry_closureAt lang b ref

theorem balancePythonInitialized_closureAt (m initial ref) :
    closureAt (balancePythonInitialized m initial) ref = closureAt m ref := by
  unfold closureAt
  rw [(balancePythonInitialized_preserves_bindings m initial).2.1]

theorem balancePythonResetBodyEntry_nextClosure (b) :
    (balancePythonResetBodyEntry b).1.nextClosure =
      (balancePreparation .python).1.nextClosure + 1 + 1 := by
  unfold balancePythonResetBodyEntry
  rw [allocCell_nextClosure, allocClosure_nextClosure,
    (balancePythonInitialized_preserves_bindings _ _).2.2.2.2.1,
    balanceConstructorBodyEntry_nextClosure]

theorem balancePythonResetBodyEntry_closureAt_other {b ref}
    (h0 : ref ≠ (balancePreparation .python).1.nextClosure)
    (h1 : ref ≠ (balancePreparation .python).1.nextClosure + 1) :
    closureAt (balancePythonResetBodyEntry b).1 ref =
      closureAt (balancePreparation .python).1 ref := by
  unfold balancePythonResetBodyEntry
  rw [closureAt_allocCell, closureAt_allocClosure_other
    (m := balancePythonInitialized (balanceConstructorBodyEntry .python b).1 "Ready")
    (by
      rw [(balancePythonInitialized_preserves_bindings
        (balanceConstructorBodyEntry .python b).1 "Ready").2.2.2.2.1,
        balanceConstructorBodyEntry_nextClosure]
      exact h1)]
  rw [balancePythonInitialized_closureAt]
  exact balanceConstructorBodyEntry_closureAt_other (lang := .python) (b := b) (ref := ref) h0

theorem balanceSetBusy_closureAt (m busy ref) :
    closureAt (balanceSetBusy m busy) ref = closureAt m ref := rfl

theorem balanceSetBusy_nextClosure (m busy) :
    (balanceSetBusy m busy).nextClosure = m.nextClosure := rfl

theorem balanceCanonicalResetStage_python3_eq (b : Int) :
    balanceCanonicalResetStage .python b 3 =
      resetSnapshotsInstalled .python (balanceCanonicalResetEntry .python b).1
        (balanceCanonicalResetEntry .python b).2 := rfl

theorem balanceCanonicalResetEntry_python_eq (b : Int) :
    balanceCanonicalResetEntry .python b =
      (balanceSetBusy (balancePythonResetBodyEntry b).1 true,
        (balancePythonResetBodyEntry b).2) := rfl

theorem balanceCanonicalResetStage_python_closureAt_other {b ref}
    (h0 : ref ≠ (balancePreparation .python).1.nextClosure)
    (h1 : ref ≠ (balancePreparation .python).1.nextClosure + 1)
    (h2 : ref ≠ (balancePreparation .python).1.nextClosure + 1 + 1) :
    closureAt (balanceCanonicalResetStage .python b 3).1 ref =
      closureAt (balancePreparation .python).1 ref := by
  rw [balanceCanonicalResetStage_python3_eq, resetSnapshotsInstalled_closureAt_other]
  · rw [balanceCanonicalResetEntry_python_eq, balanceSetBusy_closureAt]
    exact balancePythonResetBodyEntry_closureAt_other (b := b) (ref := ref) h0 h1
  · rw [balanceCanonicalResetEntry_python_eq, balanceSetBusy_nextClosure,
      balancePythonResetBodyEntry_nextClosure]
    exact h2

set_option maxHeartbeats 10000000 in
theorem balancePythonSafeInteger_fresh_closures : 4 < (balancePreparation .python).1.nextClosure := by
  unfold balancePreparation
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
  decide +kernel


theorem balanceResetPythonOverlayBound_closureAt (b : Int) (ref : ClosureRef) :
    closureAt (balanceResetPythonOverlayBound b).1 ref =
      closureAt (balanceCanonicalResetStage .python b 3).1 ref := by
  unfold balanceResetPythonOverlayBound
  rw [resetOverlayPairBinding_closureAt, resetIterableMachine_closureAt,
    balanceResetMiddleEntry_model, resetCandidateMiddleModel_closureAt_python]



def balancePythonPrepared : TargetMachine × TargetFrame :=
  (targetPrepareConstructor 100 BalancePrograms.balancePyProgram).toOption.getD
    (TargetMachine.empty, ⟨"module", [], [], [], none, .normal⟩)

theorem balancePreparation_python_eq : balancePreparation .python = balancePythonPrepared := by
  unfold balancePreparation balancePythonPrepared
  rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]

theorem balancePythonSafeInteger_preparation_closure :
    closureAt (balancePreparation .python).1 4 = .ok balancePythonSafeIntegerClosure := by
  unfold balancePythonSafeIntegerClosure
  simp only [balancePreparation_python_eq]
  decide +kernel

theorem resetPythonOverlayTypedMachine_closureAt (m ref) :
    closureAt (resetPythonOverlayTypedMachine m) ref = closureAt m ref := rfl


theorem resetClosureFresh_inequalities {ref fresh : Nat} (hf : ref < fresh) :
    ref ≠ fresh ∧ ref ≠ fresh + 1 ∧ ref ≠ fresh + 1 + 1 := by
  have h1 : ref < fresh + 1 := Nat.lt_of_lt_of_le hf (Nat.le_succ fresh)
  have h2 : ref < fresh + 1 + 1 := Nat.lt_of_lt_of_le h1 (Nat.le_succ (fresh + 1))
  exact ⟨Nat.ne_of_lt hf, Nat.ne_of_lt h1, Nat.ne_of_lt h2⟩

theorem balanceReset_python_canonical_helper_closure (b : Int) :
    closureAt (resetPythonOverlayTypedMachine (balanceResetPythonOverlayBound b).1) 4 =
      .ok balancePythonSafeIntegerClosure := by
  have h := resetClosureFresh_inequalities balancePythonSafeInteger_fresh_closures
  calc
    closureAt (resetPythonOverlayTypedMachine (balanceResetPythonOverlayBound b).1) 4 =
        closureAt (balanceResetPythonOverlayBound b).1 4 :=
      resetPythonOverlayTypedMachine_closureAt (balanceResetPythonOverlayBound b).1 4
    _ = closureAt (balanceCanonicalResetStage .python b 3).1 4 :=
      balanceResetPythonOverlayBound_closureAt b 4
    _ = closureAt (balancePreparation .python).1 4 :=
      balanceCanonicalResetStage_python_closureAt_other (b := b) (ref := 4) h.1 h.2.1 h.2.2
    _ = .ok balancePythonSafeIntegerClosure := balancePythonSafeInteger_preparation_closure
theorem resetPythonOverlayTypedMachine_localValue (m f name) :
    localValue (resetPythonOverlayTypedMachine m) f name = localValue m f name := rfl

/-- Execute the complete canonical Python overlay body for every safe signed
    payload. All table, closure, helper-frame and post-allocation reads are discharged. -/
theorem balanceReset_python_canonical_overlay_body_safe (b : Int)
    (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetPythonOverlayBound b
    execStmt (k + 20) (balanceProgram .python) e.1 e.2
      (resetLoopBody (balanceResetOverlayLoop .python)) =
        .ok ⟨balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b, e.2, .normal⟩ := by
  let e := balanceResetPythonOverlayBound b
  have reads := resetOverlayPairBinding_reads .python
    (resetIterableMachine .python (balanceResetMiddleEntry .python b).1 b)
    (balanceResetMiddleEntry .python b).2 (integerValue .python b)
  obtain ⟨hnext, hchecker, hproto, hseed, hw, hwk, hwp, hc, hck, hcp, hd, hdk, hdp⟩ :=
    resetPythonCanonicalTablesCheck_true
  have obj42 : objectAt e.1 42 = .ok (resetPythonCanonicalTableObject 42) :=
    (balanceResetPythonOverlayBound_objectAt b 42 (by rw [hnext]; decide) (by rw [hseed]; decide)).trans hc
  have obj63 : objectAt e.1 63 = .ok (resetPythonCanonicalTableObject 63) :=
    (balanceResetPythonOverlayBound_objectAt b 63 (by rw [hnext]; decide) (by rw [hseed]; decide)).trans hw
  have context : readPropertyValue .python e.1 (.object 63) "context" =
      .ok ⟨e.1, .ok (.object 42)⟩ :=
    resetPythonTable_read (m := e.1) (ref := 63) (by rw [(balanceResetPythonOverlayBound_fixed b).1]; decide)
      (by rw [(balanceResetPythonOverlayBound_fixed b).2]; decide) (by decide) obj63 hwk hwp
  apply balanceReset_python_overlay_body_safe (m := e.1) (f := e.2) (ref := 79) (b := b) (k := k) (typed := resetPythonOverlayTypedMachine e.1)
    (context := 42) (object := resetPythonCanonicalTableObject 42)
    (helper := 4) (closure := balancePythonSafeIntegerClosure)
  · exact reads.1
  · exact balanceReset_python_canonical_overlay_environment b (entry := ("type", 0, .builtin .type)) (by decide)
  · exact balanceReset_python_canonical_overlay_environment b (entry := ("str", 7, .builtin .strType)) (by decide)
  · exact resetPythonWorldContext_execute
      (balanceReset_python_canonical_overlay_environment b (entry := ("_WORLD", 69, .object 63)) (by decide)) context
  · exact obj42
  · exact .inr hck
  · rw [hcp]; rfl
  · exact (balanceReset_python_canonical_table_tests b (k + 7)).1
  · exact (resetPythonOverlayTypedMachine_localValue e.1 e.2 "_safe_integer").trans
      (balanceReset_python_canonical_overlay_environment b (entry := ("_safe_integer", 84, .closure 4)) (by decide))
  · exact (resetPythonOverlayTypedMachine_localValue e.1 e.2 "value").trans reads.2
  · exact balanceReset_python_canonical_helper_closure b
  · exact resetPythonCanonicalHelperBindingsCheck_true.1
  · rfl
  · exact balanceReset_python_canonical_safe_physical b
  · exact (balanceReset_python_canonical_post_candidate b).1
  · exact (balanceResetPythonOverlayAfterHelper_pair_reads b).1
  · exact (balanceResetPythonOverlayAfterHelper_pair_reads b).2
  · exact balanceResetPythonOverlayAfterHelper_environment b (entry := ("int", 6, .builtin .int)) (by decide)
  · exact balanceReset_python_canonical_post_table_test b (k + 10)
  · exact (balanceReset_python_canonical_post_candidate b).2
  · exact hb

set_option maxHeartbeats 10000000 in
theorem balanceReset_python_overlay_tail_shape :
    restStmt (ifYesStmt (balanceResetMiddleStmt .python 2)) =
      .sequence (balanceResetOverlayLoop .python) .empty := by
  unfold balanceResetOverlayLoop balanceResetMiddleStmt balanceResetProtected
    balanceResetSnapshots balanceStoredReset balanceResetLookup
  simp only [balancePreparation_python_eq]
  decide +kernel

/-- Unconditional canonical Python loop and complete statement-2 execution.
    Negative safe values are written here; later bounds validation is separate. -/
theorem balanceReset_python_canonical_overlay_safe (b : Int)
    (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    let final := balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b
    execStmt (k + 22) (balanceProgram .python) e.1 e.2 (balanceResetOverlayLoop .python) =
      .ok ⟨final, (balanceResetPythonOverlayBound b).2, .normal⟩ ∧
    execStmt (k + 25) (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 2) =
      .ok ⟨final, (balanceResetPythonOverlayBound b).2, .normal⟩ := by
  have loop := balanceReset_python_canonical_loop_execute (b := b) (k := k + 16)
    (final := balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b)
    (ff := (balanceResetPythonOverlayBound b).2)
    (balanceReset_python_canonical_overlay_body_safe b hb k)
  constructor
  · exact loop
  · have ctx : localValue (balanceResetMiddleEntry .python b).1 (balanceResetMiddleEntry .python b).2 "ctx" =
        .ok (.object (balancePreparation .python).1.nextObject) := by
      exact (balanceResetMiddleEntry_localValue .python b "ctx").trans balanceResetMiddlePythonCheck_zero.1
    rw [balanceReset_python_seed_present (k := k + 20) ctx,
      balanceReset_python_canonical_plain_guard_skip b (k + 18),
      balanceReset_python_overlay_tail_shape, execSequence_of_normal loop]
    exact execStmt_adequate .empty (by omega)



-- Supplied-seed TS first guard; descriptor-copy continuation remains separate.

def balanceTsPrepared : TargetMachine × TargetFrame :=
  (targetPrepareConstructor 100 BalancePrograms.balanceTsProgram).toOption.getD
    (TargetMachine.empty, ⟨"module", [], [], [], none, .normal⟩)

theorem balancePreparation_ts_eq : balancePreparation .ts = balanceTsPrepared := by
  unfold balancePreparation balanceTsPrepared
  rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]

/-- The first supplied-seed TS guard reads only object kind and proxy status. -/
def resetTsPlainGuardExpr : TargetExpr :=
  .orElse
    (.orElse (.binary .strictNe (.unary .typeof (.local "initialContext")) (.string "object"))
      (.call (.property (.local "Array") "isArray") (.sequence (.local "initialContext") .empty)))
    (.call (.property (.local "nodeTypes") "isProxy") (.sequence (.local "initialContext") .empty))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_ts_plain_guard_shape :
    firstStmt (ifNoStmt (balanceResetMiddleStmt .ts 2)) =
      .ifThenElse resetTsPlainGuardExpr
        (ifYesStmt (firstStmt (ifNoStmt (balanceResetMiddleStmt .ts 2)))) .empty ∧
    ifNoStmt (balanceResetMiddleStmt .ts 2) =
      .sequence (firstStmt (ifNoStmt (balanceResetMiddleStmt .ts 2)))
        (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) := by
  simp only [balanceResetMiddleStmt, balanceResetProtected, balanceResetSnapshots,
    balanceStoredReset, balanceResetLookup, balancePreparation_ts_eq]
  decide +kernel

theorem resetTsPlainGuard_execute {m f ref object array node k}
    (hp : localValue m f "initialContext" = .ok (.object ref))
    (ha : localValue m f "Array" = .ok (.object array))
    (haRead : readPropertyValue .ts m (.object array) "isArray" =
      .ok ⟨m, .ok (.builtin .arrayIsArray)⟩)
    (hn : localValue m f "nodeTypes" = .ok (.object node))
    (hnRead : readPropertyValue .ts m (.object node) "isProxy" =
      .ok ⟨m, .ok (.builtin .nodeIsProxy)⟩)
    (ho : objectAt m ref = .ok object) (hk : object.kind ≠ .jsArray)
    (hproxy : object.proxy = false) :
    evalExpr (k + 5) (balanceProgram .ts) m f resetTsPlainGuardExpr =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have typ : evalExpr (k + 3) (balanceProgram .ts) m f
      (.binary .strictNe (.unary .typeof (.local "initialContext")) (.string "object")) =
      .ok ⟨m, .ok (.bool false)⟩ := by
    have inner : evalExpr (k + 2) (balanceProgram .ts) m f
        (.unary .typeof (.local "initialContext")) = .ok ⟨m, .ok (.string "object")⟩ := by
      rw [evalExpr, evalExpr_adequate (.localRead hp) (by omega)]; rfl
    rw [evalExpr, inner]
    simp only [Bind.bind, Except.bind]
    rw [evalExpr_adequate (.string "object") (by omega), balanceProgram_lang]; rfl
  have arr : evalExpr (k + 3) (balanceProgram .ts) m f
      (.call (.property (.local "Array") "isArray") (.sequence (.local "initialContext") .empty)) =
      .ok ⟨m, .ok (.bool false)⟩ := by
    apply evalExpr_adequate (.callBuiltin (.property (.localRead ha)
      (by simpa only [balanceProgram_lang] using haRead))
      (.cons (.localRead hp) .empty) (by decide) ?_) (by omega)
    rw [balanceProgram_lang]
    change (do let current ← objectAt m ref
               pure (⟨m, .ok (.bool (current.kind == ObjectKind.jsArray))⟩ : ExprOutcome)) = _
    rw [ho]
    simp only [Bind.bind, Except.bind, beq_eq_false_iff_ne.mpr hk]
    rfl
  have proxy : evalExpr (k + 4) (balanceProgram .ts) m f
      (.call (.property (.local "nodeTypes") "isProxy") (.sequence (.local "initialContext") .empty)) =
      .ok ⟨m, .ok (.bool false)⟩ := by
    apply evalExpr_adequate (.callBuiltin (.property (.localRead hn)
      (by simpa only [balanceProgram_lang] using hnRead))
      (.cons (.localRead hp) .empty) (by decide) ?_) (by omega)
    rw [balanceProgram_lang]
    change (do let current ← objectAt m ref
               pure (⟨m, .ok (.bool current.proxy)⟩ : ExprOutcome)) = _
    rw [ho]
    simp only [Bind.bind, Except.bind, hproxy]
    rfl
  have first : evalExpr (k + 4) (balanceProgram .ts) m f
      (.orElse (.binary .strictNe (.unary .typeof (.local "initialContext")) (.string "object"))
        (.call (.property (.local "Array") "isArray") (.sequence (.local "initialContext") .empty))) =
      .ok ⟨m, .ok (.bool false)⟩ := by
    rw [evalExpr, typ]
    simpa only [Bind.bind, Except.bind, sourceTruthy, Bool.false_eq_true, if_false] using arr
  unfold resetTsPlainGuardExpr
  rw [evalExpr, first]
  simpa only [Bind.bind, Except.bind, sourceTruthy, Bool.false_eq_true, if_false] using proxy

theorem balanceReset_ts_plain_guard_skip {m f ref object array node k}
    (hp : localValue m f "initialContext" = .ok (.object ref))
    (ha : localValue m f "Array" = .ok (.object array))
    (haRead : readPropertyValue .ts m (.object array) "isArray" =
      .ok ⟨m, .ok (.builtin .arrayIsArray)⟩)
    (hn : localValue m f "nodeTypes" = .ok (.object node))
    (hnRead : readPropertyValue .ts m (.object node) "isProxy" =
      .ok ⟨m, .ok (.builtin .nodeIsProxy)⟩)
    (ho : objectAt m ref = .ok object) (hk : object.kind ≠ .jsArray)
    (hproxy : object.proxy = false) :
    execStmt (k + 7) (balanceProgram .ts) m f
      (ifNoStmt (balanceResetMiddleStmt .ts 2)) =
    execStmt (k + 6) (balanceProgram .ts) m f
      (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) := by
  have head : execStmt (k + 6) (balanceProgram .ts) m f
      (firstStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) = .ok ⟨m, f, .normal⟩ := by
    rw [balanceReset_ts_plain_guard_shape.1,
      execIf_of_false (resetTsPlainGuard_execute hp ha haRead hn hnRead ho hk hproxy) rfl]
    exact execStmt_adequate .empty (by omega)
  conv => lhs; rw [balanceReset_ts_plain_guard_shape.2]
  exact execSequence_of_normal head

def resetTsPlainArrayHost : HeapObject :=
  ⟨.jsOrdinary, some 0,
    [("isArray", ⟨some (.builtin .arrayIsArray), none, none, true, true, true⟩)],
    [], [], false, false⟩

def resetTsPlainNodeHost : HeapObject :=
  ⟨.jsOrdinary, some 0,
    [("isProxy", ⟨some (.builtin .nodeIsProxy), none, none, true, true, true⟩)],
    [], [], false, false⟩

def resetTsCanonicalPlainFixedCheck : Prop :=
  let stage := (balanceCanonicalResetStage .ts 0 3).1
  let e := balanceResetMiddleEntry .ts 0
  let seed := (balancePreparation .ts).1.nextObject
  stage.checkerRef = 1 ∧ stage.objectPrototype = 0 ∧
  stage.nextObject ≠ seed ∧
  (List.take (balanceCanonicalResetPrefixLength .ts 3) stage.objects).lookup seed = none ∧
  localValue e.1 e.2 "initialContext" = .ok (.object seed) ∧
  localValue e.1 e.2 "Array" = .ok (.object 4) ∧
  localValue e.1 e.2 "nodeTypes" = .ok (.object 6) ∧
  4 < stage.nextObject ∧ 6 < stage.nextObject ∧ 4 ≠ seed ∧ 6 ≠ seed ∧
  objectAt stage 4 = .ok resetTsPlainArrayHost ∧
  objectAt stage 6 = .ok resetTsPlainNodeHost

instance : Decidable resetTsCanonicalPlainFixedCheck := by
  unfold resetTsCanonicalPlainFixedCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem resetTsCanonicalPlainFixedCheck_true : resetTsCanonicalPlainFixedCheck := by
  simp only [resetTsCanonicalPlainFixedCheck,
    balanceResetMiddleEntry, balanceResetCandidateEntry,
    balanceCanonicalResetStage, balanceCanonicalResetEntry, balanceResetBodyEntry,
    balancePythonResetBodyEntry, balanceConstructorBodyEntry, balanceConstructorBoundEntry,
    balanceConstructorArgumentEntry, balanceStoredReset, balanceResetLookup, balanceStoredConstructor,
    balanceConstructorLookup, balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel

theorem balanceResetMiddleEntry_ts_seed_fixed (b : Int) :
    objectAt (balanceResetMiddleEntry .ts b).1 (balancePreparation .ts).1.nextObject =
      .ok (balanceHeapObject .ts (balancePreparation .ts).1 b) := by
  obtain ⟨_, _, hne, hfront, _⟩ := resetTsCanonicalPlainFixedCheck_true
  have footprint := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  change (match (((balanceCanonicalResetStage .ts b 3).1.nextObject,
      balanceHeapObject .ts (balanceCanonicalResetStage .ts b 3).1 100) ::
      (balanceCanonicalResetStage .ts b 3).1.objects).lookup
      (balancePreparation .ts).1.nextObject with
      | some o => Except.ok o | none => Except.error _) = _
  rw [footprint.1, footprint.2.2.2.2.1]
  simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hne), if_false,
    List.lookup_append, hfront, Option.or, beq_self_eq_true, if_true]

theorem resetTsPlainArrayHost_read {m : TargetMachine}
    (hc : m.checkerRef = 1) (hp : m.objectPrototype = 0)
    (ho : objectAt m 4 = .ok resetTsPlainArrayHost) :
    readPropertyValue .ts m (.object 4) "isArray" = .ok ⟨m, .ok (.builtin .arrayIsArray)⟩ := by
  simp [readPropertyValue, hc, hp, ho, resetTsPlainArrayHost,
    readOwn, List.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem resetTsPlainNodeHost_read {m : TargetMachine}
    (hc : m.checkerRef = 1) (hp : m.objectPrototype = 0)
    (ho : objectAt m 6 = .ok resetTsPlainNodeHost) :
    readPropertyValue .ts m (.object 6) "isProxy" = .ok ⟨m, .ok (.builtin .nodeIsProxy)⟩ := by
  simp [readPropertyValue, hc, hp, ho, resetTsPlainNodeHost,
    readOwn, List.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem balanceReset_ts_canonical_plain_guard_skip (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 7) (balanceProgram .ts) e.1 e.2
      (ifNoStmt (balanceResetMiddleStmt .ts 2)) =
    execStmt (k + 6) (balanceProgram .ts) e.1 e.2
      (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) := by
  obtain ⟨hc, hp, _, _, hseed, harr, hnode, h4, h6, hn4, hn6, ho4, ho6⟩ :=
    resetTsCanonicalPlainFixedCheck_true
  let e := balanceResetMiddleEntry .ts b
  have footprint := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  have checker : e.1.checkerRef = 1 := by
    change (balanceCanonicalResetStage .ts b 3).1.checkerRef = 1
    rw [footprint.2.2.2.2.2.2.1]; exact hc
  have proto : e.1.objectPrototype = 0 := by
    change (balanceCanonicalResetStage .ts b 3).1.objectPrototype = 0
    rw [footprint.2.2.2.2.2.1]; exact hp
  have objectOther (ref : ObjRef)
      (hf : ref < (balanceCanonicalResetStage .ts 0 3).1.nextObject)
      (hs : ref ≠ (balancePreparation .ts).1.nextObject) :
      objectAt e.1 ref = objectAt (balanceCanonicalResetStage .ts 0 3).1 ref := by
    change objectAt (balanceResetMiddleEntry .ts b).1 ref = _
    rw [balanceResetMiddleEntry_model, resetCandidateMiddleModel_objectAt_other]
    · exact balanceCanonicalResetStage_objectAt .ts b 3 (by decide) ref hs
    · rw [footprint.2.2.2.2.1]; exact Nat.ne_of_lt hf
  have arrayObject : objectAt e.1 4 = .ok resetTsPlainArrayHost :=
    (objectOther 4 h4 hn4).trans ho4
  have nodeObject : objectAt e.1 6 = .ok resetTsPlainNodeHost :=
    (objectOther 6 h6 hn6).trans ho6
  apply balanceReset_ts_plain_guard_skip
    (ref := (balancePreparation .ts).1.nextObject)
    (object := balanceHeapObject .ts (balancePreparation .ts).1 b)
    (array := 4) (node := 6)
  · exact (balanceResetMiddleEntry_localValue .ts b "initialContext").trans hseed
  · exact (balanceResetMiddleEntry_localValue .ts b "Array").trans harr
  · exact resetTsPlainArrayHost_read checker proto arrayObject
  · exact (balanceResetMiddleEntry_localValue .ts b "nodeTypes").trans hnode
  · exact resetTsPlainNodeHost_read checker proto nodeObject
  · exact balanceResetMiddleEntry_ts_seed_fixed b
  · exact (by decide : ObjectKind.jsOrdinary ≠ ObjectKind.jsArray)
  · rfl


section Batch14CanonicalTsOverlay
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000


def resetTsDescriptorObject (m : TargetMachine) (b : Int) : HeapObject :=
  ⟨.jsOrdinary, some m.objectPrototype,
    [("value", ⟨some (integerValue .ts b), none, none, true, true, true⟩),
     ("get", ⟨some .undefined, none, none, true, true, true⟩),
     ("set", ⟨some .undefined, none, none, true, true, true⟩),
     ("enumerable", ⟨some (.bool true), none, none, true, true, true⟩),
     ("writable", ⟨some (.bool true), none, none, true, true, true⟩),
     ("configurable", ⟨some (.bool true), none, none, true, true, true⟩)],
    [], [], false, false⟩

def resetTsDescriptorMap (m : TargetMachine) : HeapObject :=
  ⟨.jsOrdinary, some m.objectPrototype,
    [("balance", ⟨some (.object (m.nextObject + 1)), none, none, true, true, true⟩)],
    [], [], false, false⟩

def resetTsDescriptorsMachine (m : TargetMachine) (b : Int) : TargetMachine :=
  let blank : HeapObject := ⟨.jsOrdinary, some m.objectPrototype, [], [], [], false, false⟩
  let entry := (allocObject (allocObject m blank).1 (resetTsDescriptorObject m b)).1
  { entry with objects := entry.objects.map (fun pair =>
    (pair.1, if pair.1 == m.nextObject then resetTsDescriptorMap m else pair.2)) }

set_option maxHeartbeats 10000000 in
theorem resetTsDescriptors_execute {m ref b}
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b)) :
    hostCall .ts m .objectOwnDescriptors none [.object ref] =
      .ok ⟨resetTsDescriptorsMachine m b, .ok (.object m.nextObject)⟩ := by
  change (do
    let obj ← objectAt m ref
    let (withResult, resultRef) := allocObject m
      (⟨.jsOrdinary, some m.objectPrototype, [], [], [], false, false⟩ : HeapObject)
    let mut current := withResult
    for (key, descriptor) in obj.own do
      let (withEntry, entryRef) := allocObject current
        (⟨.jsOrdinary, some current.objectPrototype,
          [("value", ⟨some (descriptor.value.getD .undefined), none, none, true, true, true⟩),
           ("get", ⟨some (descriptor.get.map TargetValue.closure |>.getD .undefined), none, none, true, true, true⟩),
           ("set", ⟨some (descriptor.set.map TargetValue.closure |>.getD .undefined), none, none, true, true, true⟩),
           ("enumerable", ⟨some (.bool descriptor.enumerable), none, none, true, true, true⟩),
           ("writable", ⟨some (.bool descriptor.writable), none, none, true, true, true⟩),
           ("configurable", ⟨some (.bool descriptor.configurable), none, none, true, true, true⟩)],
          [], [], false, false⟩ : HeapObject)
      current ← writeOwn withEntry resultRef key (.object entryRef)
    pure (⟨current, .ok (.object resultRef)⟩ : ExprOutcome)) = _
  rw [ho]
  have h : m.nextObject + 1 ≠ m.nextObject := Nat.ne_of_gt (Nat.lt_succ_self _)
  simp only [balanceHeapObject, balanceDataDescriptor, resetTsDescriptorsMachine,
    resetTsDescriptorObject, resetTsDescriptorMap, allocObject, writeOwn, objectAt,
    replaceObject, List.lookup, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h),
    List.forIn_cons, List.forIn_nil, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.lookup_cons, List.map_cons, List.map_nil, List.append_nil, beq_self_eq_true,
    Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, Option.getD, Option.map_none,
    List.lookup_nil, Bool.false_or, Bool.or_false, Bool.not_false, Bool.not_true,
    or_false, false_or, reduceCtorEq, List.any_nil,
    Option.isNone, String.reduceBEq, dite_false, dite_true]
  rfl


def resetTsDescriptorPairBound (m : TargetMachine) (f : TargetFrame)
    (descriptor : TargetValue) : TargetMachine × TargetFrame :=
  let named := allocCell m (.string "balance") false
  let valued := allocCell named.1 descriptor false
  (valued.1, { f with locals := ("descriptor", named.1.nextCell) :: ("name", m.nextCell) :: f.locals })

def resetTsDefineLiteral (m : TargetMachine) (b : Int) : HeapObject :=
  ⟨.jsOrdinary, some m.objectPrototype,
    [("value", ⟨some (integerValue .ts b), none, none, true, true, true⟩),
     ("enumerable", ⟨some (.bool true), none, none, true, true, true⟩),
     ("writable", ⟨some (.bool true), none, none, true, true, true⟩),
     ("configurable", ⟨some (.bool true), none, none, true, true, true⟩)], [], [], false, false⟩

/-- Physical allocation/cell-write model for the supplied-seed TS descriptor copy. -/
def resetTsDescriptorCopyModel (m : TargetMachine) (f : TargetFrame) (b : Int)
    (overridesCell : CellRef) : TargetMachine × TargetFrame :=
  let proto := snapshotBound .ts m f "proto" (.object m.objectPrototype)
  let descriptors := resetTsDescriptorsMachine proto.1 b
  let bound := snapshotBound .ts descriptors proto.2 "descriptors" (.object m.nextObject)
  let overrides := allocObject bound.1
    (⟨.jsOrdinary, some m.objectPrototype, [], [], [], false, false⟩ : HeapObject)
  let written := { overrides.1 with cells := overrides.1.cells.map (fun pair =>
    (pair.1, if pair.1 == overridesCell then TargetValue.object overrides.2 else pair.2)) }
  let iterated := oneEntryMachine .ts written "balance" (.object (m.nextObject + 1))
  let pair := resetTsDescriptorPairBound iterated bound.2 (.object (m.nextObject + 1))
  let literal := (allocObject pair.1 (resetTsDefineLiteral pair.1 b)).1
  let final := { literal with objects := literal.objects.map (fun entry =>
    (entry.1, if entry.1 == overrides.2 then balanceHeapObject .ts m b else entry.2)) }
  (final, bound.2)



def resetTsOwnDescriptorsExpr : TargetExpr :=
  .call (.property (.local "Object") "getOwnPropertyDescriptors")
    (.sequence (.local "initialContext") .empty)

theorem resetTsOwnDescriptorsExpr_execute {m f ref object b k}
    (hg : localValue m f "Object" = .ok (.object object))
    (hc : readPropertyValue .ts m (.object object) "getOwnPropertyDescriptors" =
      .ok ⟨m, .ok (.builtin .objectOwnDescriptors)⟩)
    (hr : localValue m f "initialContext" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b)) :
    evalExpr (k + 4) (balanceProgram .ts) m f resetTsOwnDescriptorsExpr =
      .ok ⟨resetTsDescriptorsMachine m b, .ok (.object m.nextObject)⟩ := by
  apply evalExpr_adequate (.callBuiltin (.property (.localRead hg)
    (by simpa only [balanceProgram_lang] using hc))
    (.cons (.localRead hr) .empty) (by decide) ?_) (by omega)
  simpa only [balanceProgram_lang] using resetTsDescriptors_execute ho


def resetTsProtoExpr : TargetExpr :=
  .call (.property (.local "Object") "getPrototypeOf")
    (.sequence (.local "initialContext") .empty)

theorem resetTsProtoExpr_execute {m f ref object b k}
    (hg : localValue m f "Object" = .ok (.object object))
    (hc : readPropertyValue .ts m (.object object) "getPrototypeOf" =
      .ok ⟨m, .ok (.builtin .objectGetPrototypeOf)⟩)
    (hr : localValue m f "initialContext" = .ok (.object ref))
    (ho : objectAt m ref = .ok (balanceHeapObject .ts m b)) :
    evalExpr (k + 4) (balanceProgram .ts) m f resetTsProtoExpr =
      .ok ⟨m, .ok (.object m.objectPrototype)⟩ := by
  apply evalExpr_adequate (.callBuiltin (.property (.localRead hg)
    (by simpa only [balanceProgram_lang] using hc))
    (.cons (.localRead hr) .empty) (by decide) ?_) (by omega)
  rw [balanceProgram_lang]
  change (do let object ← objectAt m ref
             pure (⟨m, .ok (object.prototype.map TargetValue.object |>.getD .null)⟩ : ExprOutcome)) = _
  rw [ho]
  rfl

def resetTsProtoGuard : TargetExpr :=
  .andThen
    (.binary .strictNe (.local "proto") (.property (.local "Object") "prototype"))
    (.binary .strictNe (.local "proto") .null)

theorem resetTsProtoGuard_execute {m f object k}
    (hg : localValue m f "Object" = .ok (.object object))
    (hc : readPropertyValue .ts m (.object object) "prototype" =
      .ok ⟨m, .ok (.object m.objectPrototype)⟩)
    (hp : localValue m f "proto" = .ok (.object m.objectPrototype)) :
    evalExpr (k + 4) (balanceProgram .ts) m f resetTsProtoGuard =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have left : DepthDerivesExpr (balanceProgram .ts) m f
      (.binary .strictNe (.local "proto") (.property (.local "Object") "prototype"))
      ⟨m, .ok (.bool false)⟩ 2 :=
    .binary (by decide) (.localRead hp) (.property (.localRead hg)
      (by simpa only [balanceProgram_lang] using hc)) (by
        simp [balanceProgram_lang, binaryValue])
  change evalExpr (k + 4) _ _ _ (.andThen _ _) = _
  rw [evalExpr, evalExpr_adequate left (by omega)]
  rfl


set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_ts_descriptor_prefix_shape :
    firstStmt (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) =
      .letLocal "proto" false resetTsProtoExpr ∧
    firstStmt (restStmt (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2)))) =
      .ifThenElse resetTsProtoGuard
        (ifYesStmt (firstStmt (restStmt (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2)))))) .empty ∧
    firstStmt (restStmt (restStmt (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))))) =
      .letLocal "descriptors" false resetTsOwnDescriptorsExpr := by
  simp only [balanceResetMiddleStmt, balanceResetProtected, balanceResetSnapshots,
    balanceStoredReset, balanceResetLookup, balancePreparation_ts_eq]
  decide +kernel


theorem resetTsLiteral_writeOwn {m object key value}
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (hk : object.own.lookup key = none) (hfr : object.frozen = false)
    (hkind : object.kind ≠ .mappingProxy) :
    writeOwn (allocObject m object).1 m.nextObject key value =
      .ok (allocObject m {object with own := object.own ++
        [(key, ⟨some value, none, none, true, true, true⟩)]}).1 := by
  simp [writeOwn, objectAt_allocObject_fresh, hk, hfr,
    beq_eq_false_iff_ne.mpr hkind, replaceObject_allocObject hf,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

def resetTsDefineFields : TargetExpr :=
  .objectEntry "value" (.property (.local "descriptor") "value")
    (.objectEntry "enumerable" (.bool true)
      (.objectEntry "writable" (.bool true) (.objectEntry "configurable" (.bool true) .empty)))

theorem resetTsDefineLiteral_execute {m f b k}
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (he : DepthDerivesExpr (balanceProgram .ts) (allocObject m (literalObject .ts m)).1 f
      (.property (.local "descriptor") "value")
      ⟨(allocObject m (literalObject .ts m)).1, .ok (integerValue .ts b)⟩ 1) :
    evalExpr (k + 6) (balanceProgram .ts) m f (.object resetTsDefineFields) =
      .ok ⟨(allocObject m (resetTsDefineLiteral m b)).1, .ok (.object m.nextObject)⟩ := by
  apply evalExpr_adequate (.objectFields (rank := 4) ?_) (by omega)
  rw [balanceProgram_lang]
  unfold resetTsDefineFields
  apply DepthDerivesFields.entry (rf := 3) he (resetTsLiteral_writeOwn hf rfl rfl (by simp [literalObject]))
  apply DepthDerivesFields.entry (rf := 2) (.bool true) (resetTsLiteral_writeOwn hf rfl rfl (by simp [literalObject]))
  apply DepthDerivesFields.entry (rf := 1) (.bool true) (resetTsLiteral_writeOwn hf rfl rfl (by simp [literalObject]))
  apply DepthDerivesFields.entry (rf := 0) (.bool true) (resetTsLiteral_writeOwn hf rfl rfl (by simp [literalObject]))
  exact .empty


theorem resetTsDefineProperty_execute {m target descriptor b}
    (ht : objectAt m target = .ok (literalObject .ts m))
    (hd : objectAt m descriptor = .ok (resetTsDefineLiteral m b)) :
    hostCall .ts m .objectDefineProperty none [.object target, .string "balance", .object descriptor] =
      .ok ⟨{ m with objects := m.objects.map (fun entry =>
        (entry.1, if entry.1 == target then balanceHeapObject .ts m b else entry.2)) },
        .ok (.object target)⟩ := by
  change (do
    let object ← objectAt m target
    if object.frozen then pure (⟨m, .error (.exception "TypeError" "frozen target")⟩ : ExprOutcome) else do
      let valueDescriptor ← readOwn m descriptor "value"
      let value ← match valueDescriptor with
        | some entry => match entry.value with
          | some v => .ok v
          | none => .error .badDescriptor
        | none => .error .badDescriptor
      let flag (name : String) : Except TargetError Bool := do
        match ← readOwn m descriptor name with
        | some entry => match entry.value with
          | some (TargetValue.bool b) => pure b
          | _ => throw TargetError.badDescriptor
        | none => pure false
      let newDescriptor : Descriptor :=
        ⟨some value, none, none, ← flag "enumerable", ← flag "writable", ← flag "configurable"⟩
      let own := if object.own.any (fun (entry : String × Descriptor) => entry.1 == "balance") then
        object.own.map (fun (entry : String × Descriptor) => if entry.1 == "balance" then ("balance", newDescriptor) else entry)
        else object.own ++ [("balance", newDescriptor)]
      let updated ← replaceObject m target {object with own := own}
      pure (⟨updated, .ok (.object target)⟩ : ExprOutcome)) = _
  simp [ht, hd, literalObject, resetTsDefineLiteral, balanceHeapObject,
    balanceDataDescriptor, readOwn, replaceObject,
    Bind.bind, Except.bind, Pure.pure, Except.pure, List.lookup]


def resetTsDescriptorDataGuard : TargetExpr :=
  .unary .not (.binary .inObject (.string "value") (.local "descriptor"))

theorem resetTsDescriptorDataGuard_execute {m f descriptor b k}
    (hr : localValue m f "descriptor" = .ok (.object descriptor))
    (ho : objectAt m descriptor = .ok (resetTsDescriptorObject m b)) :
    evalExpr (k + 3) (balanceProgram .ts) m f resetTsDescriptorDataGuard =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have inner : DepthDerivesExpr (balanceProgram .ts) m f
      (.binary .inObject (.string "value") (.local "descriptor"))
      ⟨m, .ok (.bool true)⟩ 1 :=
    .binary (by decide) (.string "value") (.localRead hr) (by
      simp [balanceProgram_lang, binaryValue, ho, resetTsDescriptorObject,
        Bind.bind, Except.bind, Pure.pure, Except.pure, List.lookup])
  change evalExpr (k + 3) _ _ _ (.unary .not _) = _
  rw [evalExpr, evalExpr_adequate inner (by omega)]
  rfl

def resetTsDefineExpr : TargetExpr :=
  .call (.property (.local "Object") "defineProperty")
    (.sequence (.local "overrides") (.sequence (.local "name")
      (.sequence (.object resetTsDefineFields) .empty)))

theorem resetTsDefineExpr_execute {m f object target b k}
    (hg : localValue m f "Object" = .ok (.object object))
    (hc : readPropertyValue .ts m (.object object) "defineProperty" =
      .ok ⟨m, .ok (.builtin .objectDefineProperty)⟩)
    (ht : localValue m f "overrides" = .ok (.object target))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (he : DepthDerivesExpr (balanceProgram .ts) (allocObject m (literalObject .ts m)).1 f
      (.property (.local "descriptor") "value")
      ⟨(allocObject m (literalObject .ts m)).1, .ok (integerValue .ts b)⟩ 1)
    (ho : objectAt (allocObject m (resetTsDefineLiteral m b)).1 target =
      .ok (literalObject .ts (allocObject m (resetTsDefineLiteral m b)).1)) :
    evalExpr (k + 10) (balanceProgram .ts) m f resetTsDefineExpr =
      .ok ⟨{ (allocObject m (resetTsDefineLiteral m b)).1 with
        objects := (allocObject m (resetTsDefineLiteral m b)).1.objects.map (fun entry =>
          (entry.1, if entry.1 == target then balanceHeapObject .ts m b else entry.2)) },
        .ok (.object target)⟩ := by
  have hcallee : evalExpr (k + 9) (balanceProgram .ts) m f
      (.property (.local "Object") "defineProperty") =
      .ok ⟨m, .ok (.builtin .objectDefineProperty)⟩ :=
    evalExpr_adequate (.property (.localRead hg) (by simpa only [balanceProgram_lang] using hc)) (by omega)
  have hov : evalExpr (k + 8) (balanceProgram .ts) m f (.local "overrides") =
      .ok ⟨m, .ok (.object target)⟩ := evalExpr_adequate (.localRead ht) (by omega)
  have hname : evalExpr (k + 7) (balanceProgram .ts) m f (.local "name") =
      .ok ⟨m, .ok (.string "balance")⟩ := evalExpr_adequate (.localRead hn) (by omega)
  have hhost := resetTsDefineProperty_execute ho (b := b)
    (by exact objectAt_allocObject_fresh _ _)
  change evalExpr (k + 10) _ _ _ (.call _ _) = _
  rw [evalExpr, hcallee]
  simp only [Bind.bind, Except.bind]
  rw [evalArgValues]
  simp only [hov, Bind.bind, Except.bind]
  rw [evalArgValues]
  simp only [hname, Bind.bind, Except.bind]
  rw [evalArgValues, resetTsDefineLiteral_execute hf he]
  simp only [Bind.bind, Except.bind]
  rw [evalArgValues]
  simpa only [balanceProgram_lang, Bind.bind, Except.bind, Pure.pure, Except.pure] using hhost


def resetTsDescriptorCopyBody (bad : TargetStmt) : TargetStmt :=
  .sequence (.ifThenElse resetTsDescriptorDataGuard bad .empty)
    (.sequence (.doExpr resetTsDefineExpr) .empty)

theorem resetTsDescriptorCopyBody_execute {m f object target descriptor b k bad}
    (hg : localValue m f "Object" = .ok (.object object))
    (hc : readPropertyValue .ts m (.object object) "defineProperty" =
      .ok ⟨m, .ok (.builtin .objectDefineProperty)⟩)
    (ht : localValue m f "overrides" = .ok (.object target))
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hr : localValue m f "descriptor" = .ok (.object descriptor))
    (hd : objectAt m descriptor = .ok (resetTsDescriptorObject m b))
    (hf : ∀ e ∈ m.objects, e.1 ≠ m.nextObject)
    (he : DepthDerivesExpr (balanceProgram .ts) (allocObject m (literalObject .ts m)).1 f
      (.property (.local "descriptor") "value")
      ⟨(allocObject m (literalObject .ts m)).1, .ok (integerValue .ts b)⟩ 1)
    (ho : objectAt (allocObject m (resetTsDefineLiteral m b)).1 target =
      .ok (literalObject .ts (allocObject m (resetTsDefineLiteral m b)).1)) :
    execStmt (k + 14) (balanceProgram .ts) m f (resetTsDescriptorCopyBody bad) =
      .ok ⟨{ (allocObject m (resetTsDefineLiteral m b)).1 with
        objects := (allocObject m (resetTsDefineLiteral m b)).1.objects.map (fun entry =>
          (entry.1, if entry.1 == target then balanceHeapObject .ts m b else entry.2)) }, f, .normal⟩ := by
  have hguard : execStmt (k + 13) (balanceProgram .ts) m f
      (.ifThenElse resetTsDescriptorDataGuard bad .empty) = .ok ⟨m, f, .normal⟩ := by
    rw [execIf_of_false (resetTsDescriptorDataGuard_execute (k := k + 9) hr hd) rfl]
    exact execStmt_adequate .empty (by omega)
  have hcall : execStmt (k + 12) (balanceProgram .ts) m f (.doExpr resetTsDefineExpr) =
      .ok ⟨{ (allocObject m (resetTsDefineLiteral m b)).1 with
        objects := (allocObject m (resetTsDefineLiteral m b)).1.objects.map (fun entry =>
          (entry.1, if entry.1 == target then balanceHeapObject .ts m b else entry.2)) }, f, .normal⟩ := by
    rw [execStmt, resetTsDefineExpr_execute (k := k + 1) hg hc ht hn hf he ho]
    rfl
  unfold resetTsDescriptorCopyBody
  rw [execSequence_of_normal hguard, execSequence_of_normal hcall]
  exact execStmt_adequate .empty (by omega)


def resetTsCopyProtoEntry (m : TargetMachine) (f : TargetFrame) : TargetMachine × TargetFrame :=
  snapshotBound .ts m f "proto" (.object m.objectPrototype)

def resetTsCopyDescriptorEntry (m : TargetMachine) (f : TargetFrame) (b : Int) :
    TargetMachine × TargetFrame :=
  let p := resetTsCopyProtoEntry m f
  snapshotBound .ts (resetTsDescriptorsMachine p.1 b) p.2 "descriptors" (.object m.nextObject)

def resetTsCopyOverridesEntry (m : TargetMachine) (f : TargetFrame) (b : Int) (cell : CellRef) :
    TargetMachine × TargetFrame :=
  let d := resetTsCopyDescriptorEntry m f b
  let overrides := allocObject d.1 (literalObject .ts d.1)
  ({ overrides.1 with cells := overrides.1.cells.map (fun pair =>
    (pair.1, if pair.1 == cell then TargetValue.object overrides.2 else pair.2)) }, d.2)

def resetTsCopyIterationEntry (m : TargetMachine) (f : TargetFrame) (b : Int) (cell : CellRef) :
    TargetMachine × TargetFrame :=
  let o := resetTsCopyOverridesEntry m f b cell
  (oneEntryMachine .ts o.1 "balance" (.object (m.nextObject + 1)), o.2)

def resetTsCopyBoundEntry (m : TargetMachine) (f : TargetFrame) (b : Int) (cell : CellRef) :
    TargetMachine × TargetFrame :=
  let i := resetTsCopyIterationEntry m f b cell
  resetTsDescriptorPairBound i.1 i.2 (.object (m.nextObject + 1))

def resetTsCopyPlainError : TargetStmt :=
  .throwValue (.newExpr (.call (.local "Error")
    (.sequence (.string "INVALID_BOUNDS: initial context must be a plain object") .empty)))

def resetTsCopyAccessorError : TargetStmt :=
  .throwValue (.newExpr (.call (.local "Error")
    (.sequence (.string "INVALID_BOUNDS: accessor") .empty)))

def resetTsDescriptorContinuation : TargetStmt :=
  .sequence (.letLocal "proto" false resetTsProtoExpr)
    (.sequence (.ifThenElse resetTsProtoGuard resetTsCopyPlainError .empty)
      (.sequence (.letLocal "descriptors" false resetTsOwnDescriptorsExpr)
        (.sequence (.assign (.local "overrides") (.object .empty))
          (.sequence (.forDo ["name", "descriptor"]
            (.call (.property (.local "Object") "entries")
              (.sequence (.local "descriptors") .empty))
            (resetTsDescriptorCopyBody resetTsCopyAccessorError)) .empty))))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_ts_descriptor_continuation_shape :
    restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2)) = resetTsDescriptorContinuation := by
  simp only [balanceResetMiddleStmt, balanceResetProtected, balanceResetSnapshots,
    balanceStoredReset, balanceResetLookup, balancePreparation_ts_eq]
  decide +kernel


structure ResetTsDescriptorCopyPhysical (m : TargetMachine) (f : TargetFrame) (b : Int) (cell : CellRef) : Prop where
  proto : ∀ k, evalExpr (k + 4) (balanceProgram .ts) m f resetTsProtoExpr =
    .ok ⟨m, .ok (.object m.objectPrototype)⟩
  guard : ∀ k, let p := resetTsCopyProtoEntry m f
    evalExpr (k + 4) (balanceProgram .ts) p.1 p.2 resetTsProtoGuard = .ok ⟨p.1, .ok (.bool false)⟩
  descriptors : ∀ k, let p := resetTsCopyProtoEntry m f
    evalExpr (k + 4) (balanceProgram .ts) p.1 p.2 resetTsOwnDescriptorsExpr =
      .ok ⟨resetTsDescriptorsMachine p.1 b, .ok (.object m.nextObject)⟩
  address : let d := resetTsCopyDescriptorEntry m f b
    snapshotAddress d.1 d.2 "overrides" = some cell
  write : let d := resetTsCopyDescriptorEntry m f b
    let allocated := (allocObject d.1 (literalObject .ts d.1)).1
    writeCell allocated cell (.object d.1.nextObject) =
      .ok (resetTsCopyOverridesEntry m f b cell).1
  entries : ∀ k, let o := resetTsCopyOverridesEntry m f b cell
    evalExpr (k + 4) (balanceProgram .ts) o.1 o.2
      (.call (.property (.local "Object") "entries") (.sequence (.local "descriptors") .empty)) =
      .ok ⟨(resetTsCopyIterationEntry m f b cell).1, .ok (.object (o.1.nextObject + 1))⟩
  list : let o := resetTsCopyOverridesEntry m f b cell
    let i := resetTsCopyIterationEntry m f b cell
    objectAt i.1 (o.1.nextObject + 1) = .ok (oneEntryItems .ts o.1)
  pair : let o := resetTsCopyOverridesEntry m f b cell
    let i := resetTsCopyIterationEntry m f b cell
    objectAt i.1 o.1.nextObject = .ok (oneEntryPair .ts o.1 "balance" (.object (m.nextObject + 1)))
  body : ∀ k, let e := resetTsCopyBoundEntry m f b cell
    execStmt (k + 14) (balanceProgram .ts) e.1 e.2 (resetTsDescriptorCopyBody resetTsCopyAccessorError) =
      .ok ⟨(resetTsDescriptorCopyModel m f b cell).1, e.2, .normal⟩

/-- Exact real-AST continuation, with the closed host/heap obligations isolated. -/
theorem resetTsDescriptorContinuation_execute {m f b cell k}
    (h : ResetTsDescriptorCopyPhysical m f b cell) :
    execStmt (k + 24) (balanceProgram .ts) m f
      (restStmt (ifNoStmt (balanceResetMiddleStmt .ts 2))) =
      .ok ⟨(resetTsDescriptorCopyModel m f b cell).1,
        (resetTsDescriptorCopyModel m f b cell).2, .normal⟩ := by
  let p := resetTsCopyProtoEntry m f
  let d := resetTsCopyDescriptorEntry m f b
  let o := resetTsCopyOverridesEntry m f b cell
  let i := resetTsCopyIterationEntry m f b cell
  let bound := resetTsCopyBoundEntry m f b cell
  have proto : execStmt (k + 23) (balanceProgram .ts) m f (.letLocal "proto" false resetTsProtoExpr) =
      .ok ⟨p.1, p.2, .normal⟩ := by
    exact execSnapshotBind (lang := .ts) (name := "proto") (h.proto (k + 18)) (by intro h; cases h)
  have guard : execStmt (k + 22) (balanceProgram .ts) p.1 p.2
      (.ifThenElse resetTsProtoGuard resetTsCopyPlainError .empty) = .ok ⟨p.1, p.2, .normal⟩ := by
    rw [execIf_of_false (h.guard (k + 17)) rfl]
    exact execStmt_adequate .empty (by omega)
  have descriptors : execStmt (k + 21) (balanceProgram .ts) p.1 p.2
      (.letLocal "descriptors" false resetTsOwnDescriptorsExpr) = .ok ⟨d.1, d.2, .normal⟩ := by
    exact execSnapshotBind (lang := .ts) (name := "descriptors") (h.descriptors (k + 16)) (by intro h; cases h)
  have assigned : execStmt (k + 20) (balanceProgram .ts) d.1 d.2
      (.assign (.local "overrides") (.object .empty)) = .ok ⟨o.1, o.2, .normal⟩ := by
    exact execStmt_adequate (.assignLocal (.objectEmpty)
      h.address (by simpa only [balanceProgram_lang] using h.write)) (by omega)
  have loop : execStmt (k + 19) (balanceProgram .ts) o.1 o.2
      (.forDo ["name", "descriptor"]
        (.call (.property (.local "Object") "entries") (.sequence (.local "descriptors") .empty))
        (resetTsDescriptorCopyBody resetTsCopyAccessorError)) =
      .ok ⟨(resetTsDescriptorCopyModel m f b cell).1, o.2, .normal⟩ := by
    apply execForDo_ts_one_pair (list := oneEntryItems .ts o.1)
      (pair := oneEntryPair .ts o.1 "balance" (.object (m.nextObject + 1)))
      (left := .string "balance") (right := .object (m.nextObject + 1))
      (balanceProgram_lang .ts) (h.entries (k + 14)) h.list rfl rfl h.pair rfl
    exact h.body (k + 3)
  rw [balanceReset_ts_descriptor_continuation_shape]
  unfold resetTsDescriptorContinuation
  rw [execSequence_of_normal proto, execSequence_of_normal guard,
    execSequence_of_normal descriptors, execSequence_of_normal assigned,
    execSequence_of_normal loop]
  exact execStmt_adequate .empty (by omega)


theorem resetTsDescriptorsMachine_objectAt_old {m b ref} (hf : ref < m.nextObject) :
    objectAt (resetTsDescriptorsMachine m b) ref = objectAt m ref := by
  have hn : ref ≠ m.nextObject := Nat.ne_of_lt hf
  have hn1 : ref ≠ m.nextObject + 1 := Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_succ_self _))
  unfold resetTsDescriptorsMachine objectAt
  simp only [allocObject, Prod.fst]
  rw [lookup_replace_payload_other _ _ hn]
  simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hn, beq_eq_false_iff_ne.mpr hn1, if_false]

theorem resetTsCopyProtoEntry_objectAt (m f ref) :
    objectAt (resetTsCopyProtoEntry m f).1 ref = objectAt m ref := rfl

theorem resetTsCopyDescriptorEntry_objectAt_old {m f b ref} (hf : ref < m.nextObject) :
    objectAt (resetTsCopyDescriptorEntry m f b).1 ref = objectAt m ref :=
  resetTsDescriptorsMachine_objectAt_old hf

theorem resetTsCopyOverridesEntry_objectAt_old {m f b cell ref} (hf : ref < m.nextObject) :
    objectAt (resetTsCopyOverridesEntry m f b cell).1 ref = objectAt m ref := by
  change objectAt (allocObject (resetTsCopyDescriptorEntry m f b).1
    (literalObject .ts (resetTsCopyDescriptorEntry m f b).1)).1 ref = _
  rw [objectAt_allocObject_other]
  · exact resetTsCopyDescriptorEntry_objectAt_old hf
  · exact Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_add_of_pos_right (by decide : 0 < 2)))

set_option maxHeartbeats 1000000 in
theorem resetTsCopyIterationEntry_objectAt_old {m f b cell ref} (hf : ref < m.nextObject) :
    objectAt (resetTsCopyIterationEntry m f b cell).1 ref = objectAt m ref := by
  change objectAt (oneEntryMachine .ts (resetTsCopyOverridesEntry m f b cell).1 "balance"
    (.object (m.nextObject + 1))) ref = _
  unfold oneEntryMachine
  rw [objectAt_allocObject_other, objectAt_allocObject_other]
  · exact resetTsCopyOverridesEntry_objectAt_old hf
  · exact Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_add_of_pos_right (by decide : 0 < 3)))
  · exact Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_add_of_pos_right (by decide : 0 < 4)))

theorem resetTsCopyBoundEntry_objectAt_old {m f b cell ref} (hf : ref < m.nextObject) :
    objectAt (resetTsCopyBoundEntry m f b cell).1 ref = objectAt m ref :=
  resetTsCopyIterationEntry_objectAt_old (m := m) (f := f) (b := b) (cell := cell) (ref := ref) hf


def resetTsCopyStage (stage : Nat) (m : TargetMachine) (f : TargetFrame) (b : Int) (cell : CellRef) :
    TargetMachine × TargetFrame :=
  match stage with
  | 0 => resetTsCopyProtoEntry m f
  | 1 => resetTsCopyDescriptorEntry m f b
  | 2 => resetTsCopyOverridesEntry m f b cell
  | 3 => resetTsCopyIterationEntry m f b cell
  | _ => resetTsCopyBoundEntry m f b cell

def resetTsCopyFieldsEqual (e z : TargetMachine × TargetFrame) : Prop :=
  e.2 = z.2 ∧ e.1.cells = z.1.cells ∧ e.1.globals = z.1.globals ∧
    e.1.nextCell = z.1.nextCell ∧ e.1.nextObject = z.1.nextObject ∧
    e.1.objectPrototype = z.1.objectPrototype ∧ e.1.checkerRef = z.1.checkerRef

set_option maxHeartbeats 1000000 in
theorem resetTsCopyStage_fields_congr {m n f g b c cell stage}
    (hf : f = g) (hc : m.cells = n.cells) (hg : m.globals = n.globals)
    (hn : m.nextCell = n.nextCell) (ho : m.nextObject = n.nextObject)
    (hp : m.objectPrototype = n.objectPrototype) (hk : m.checkerRef = n.checkerRef) :
    resetTsCopyFieldsEqual (resetTsCopyStage stage m f b cell) (resetTsCopyStage stage n g c cell) := by
  unfold resetTsCopyStage
  split <;>
    simp only [resetTsCopyFieldsEqual, resetTsCopyProtoEntry, resetTsCopyDescriptorEntry,
      resetTsCopyOverridesEntry, resetTsCopyIterationEntry, resetTsCopyBoundEntry,
      resetTsDescriptorsMachine, snapshotBound, resetTsDescriptorPairBound,
      allocObject, allocCell, oneEntryMachine, Prod.fst, Prod.snd] <;>
    simp only [hf, hc, hg, hn, ho, hp, hk] <;> trivial



theorem resetTsDescriptorsMachine_entry (m : TargetMachine) (b : Int) :
    objectAt (resetTsDescriptorsMachine m b) (m.nextObject + 1) = .ok (resetTsDescriptorObject m b) := by
  have h : m.nextObject + 1 ≠ m.nextObject := Nat.ne_of_gt (Nat.lt_succ_self _)
  unfold resetTsDescriptorsMachine objectAt
  simp only [allocObject, Prod.fst]
  rw [lookup_replace_payload_other _ _ h]
  simp only [List.lookup_cons, beq_self_eq_true, if_true]

theorem resetTsDescriptorsMachine_map (m : TargetMachine) (b : Int) :
    objectAt (resetTsDescriptorsMachine m b) m.nextObject = .ok (resetTsDescriptorMap m) := by
  have h : m.nextObject + 1 ≠ m.nextObject := Nat.ne_of_gt (Nat.lt_succ_self _)
  simp only [resetTsDescriptorsMachine, objectAt, allocObject, Prod.fst,
    List.map_cons, List.lookup_cons, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h),
    if_false, beq_self_eq_true, if_true]

theorem oneEntryMachine_objectAt_old {lang m key value ref} (hf : ref < m.nextObject) :
    objectAt (oneEntryMachine lang m key value) ref = objectAt m ref := by
  unfold oneEntryMachine
  rw [objectAt_allocObject_other, objectAt_allocObject_other]
  · exact Nat.ne_of_lt hf
  · exact Nat.ne_of_lt (Nat.lt_trans hf (Nat.lt_succ_self _))

set_option maxHeartbeats 1000000 in
theorem resetTsCopyBoundEntry_descriptor {m f b cell} :
    objectAt (resetTsCopyBoundEntry m f b cell).1 (m.nextObject + 1) =
      .ok (resetTsDescriptorObject (resetTsCopyBoundEntry m f b cell).1 b) := by
  change objectAt (oneEntryMachine .ts (resetTsCopyOverridesEntry m f b cell).1 "balance"
    (.object (m.nextObject + 1))) (m.nextObject + 1) = .ok (resetTsDescriptorObject m b)
  rw [oneEntryMachine_objectAt_old]
  · change objectAt (allocObject (resetTsCopyDescriptorEntry m f b).1
      (literalObject .ts (resetTsCopyDescriptorEntry m f b).1)).1 (m.nextObject + 1) = .ok (resetTsDescriptorObject m b)
    rw [objectAt_allocObject_other]
    · exact resetTsDescriptorsMachine_entry (resetTsCopyProtoEntry m f).1 b
    · exact Nat.ne_of_lt (Nat.add_lt_add_left (by decide : 1 < 2) _)
  · exact Nat.add_lt_add_left (by decide : 1 < 3) _


theorem resetTsCopyOverridesEntry_map {m f b cell} :
    objectAt (resetTsCopyOverridesEntry m f b cell).1 m.nextObject =
      .ok (resetTsDescriptorMap m) := by
  change objectAt (allocObject (resetTsCopyDescriptorEntry m f b).1
    (literalObject .ts (resetTsCopyDescriptorEntry m f b).1)).1 m.nextObject = _
  rw [objectAt_allocObject_other]
  · exact resetTsDescriptorsMachine_map (resetTsCopyProtoEntry m f).1 b
  · exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2))

theorem resetTsCopyBoundEntry_overrides_literal {m f b cell} :
    objectAt (allocObject (resetTsCopyBoundEntry m f b cell).1
      (resetTsDefineLiteral (resetTsCopyBoundEntry m f b cell).1 b)).1 (m.nextObject + 2) =
      .ok (literalObject .ts m) := by
  rw [objectAt_allocObject_other]
  · change objectAt (oneEntryMachine .ts (resetTsCopyOverridesEntry m f b cell).1 "balance"
      (.object (m.nextObject + 1))) (m.nextObject + 2) = _
    rw [oneEntryMachine_objectAt_old]
    · exact objectAt_allocObject_fresh (resetTsCopyDescriptorEntry m f b).1
        (literalObject .ts (resetTsCopyDescriptorEntry m f b).1)
    · exact Nat.add_lt_add_left (by decide : 2 < 3) _
  · exact Nat.ne_of_lt (Nat.add_lt_add_left (by decide : 2 < 5) _)

theorem resetTsCopyBoundEntry_descriptor_literal {m f b cell} :
    objectAt (allocObject (resetTsCopyBoundEntry m f b cell).1
      (literalObject .ts (resetTsCopyBoundEntry m f b cell).1)).1 (m.nextObject + 1) =
      .ok (resetTsDescriptorObject m b) := by
  rw [objectAt_allocObject_other]
  · exact resetTsCopyBoundEntry_descriptor (m := m) (f := f) (b := b) (cell := cell)
  · exact Nat.ne_of_lt (Nat.add_lt_add_left (by decide : 1 < 5) _)

theorem resetTsCopy_entries_execute {m f b cell k}
    (hg : localValue (resetTsCopyOverridesEntry m f b cell).1
      (resetTsCopyOverridesEntry m f b cell).2 "Object" = .ok (.object 3))
    (hc : readPropertyValue .ts (resetTsCopyOverridesEntry m f b cell).1 (.object 3) "entries" =
      .ok ⟨(resetTsCopyOverridesEntry m f b cell).1, .ok (.builtin .objectEntries)⟩)
    (hd : localValue (resetTsCopyOverridesEntry m f b cell).1
      (resetTsCopyOverridesEntry m f b cell).2 "descriptors" = .ok (.object m.nextObject)) :
    let o := resetTsCopyOverridesEntry m f b cell
    evalExpr (k + 4) (balanceProgram .ts) o.1 o.2
      (.call (.property (.local "Object") "entries") (.sequence (.local "descriptors") .empty)) =
      .ok ⟨(resetTsCopyIterationEntry m f b cell).1, .ok (.object (o.1.nextObject + 1))⟩ := by
  apply evalExpr_adequate (.callBuiltin (.property (.localRead hg)
    (by simpa only [balanceProgram_lang] using hc)) (.cons (.localRead hd) .empty) (by decide) ?_) (by omega)
  rw [balanceProgram_lang]
  exact hostEntries_one resetTsCopyOverridesEntry_map rfl


theorem oneEntryMachine_ts_objects (m : TargetMachine) (key : String) (value : TargetValue) :
    objectAt (oneEntryMachine .ts m key value) (m.nextObject + 1) = .ok (oneEntryItems .ts m) ∧
    objectAt (oneEntryMachine .ts m key value) m.nextObject = .ok (oneEntryPair .ts m key value) := by
  have h : m.nextObject ≠ m.nextObject + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  simp only [oneEntryMachine, objectAt, allocObject, Prod.fst, List.lookup_cons,
    beq_self_eq_true, if_true, beq_eq_false_iff_ne.mpr h, if_false]
  constructor <;> trivial


theorem resetTsDescriptorCopyModel_final (m f b cell) :
    (resetTsDescriptorCopyModel m f b cell).1 =
      let bound := resetTsCopyBoundEntry m f b cell
      let literal := (allocObject bound.1 (resetTsDefineLiteral bound.1 b)).1
      { literal with objects := literal.objects.map (fun entry =>
        (entry.1, if entry.1 == m.nextObject + 2 then balanceHeapObject .ts m b else entry.2)) } := rfl

theorem resetTsCopyDescriptorValue_read {m ref b}
    (hr : ref ≠ m.checkerRef) (hp : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok (resetTsDescriptorObject m b)) :
    readPropertyValue .ts m (.object ref) "value" = .ok ⟨m, .ok (integerValue .ts b)⟩ := by
  simp [readPropertyValue, beq_eq_false_iff_ne.mpr hr, beq_eq_false_iff_ne.mpr hp,
    ho, resetTsDescriptorObject, readOwn, List.lookup,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem balanceResetTsCopyInitial_fields (b : Int) :
    resetTsCopyFieldsEqual (balanceResetMiddleEntry .ts b) (balanceResetMiddleEntry .ts 0) := by
  have h := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  unfold resetTsCopyFieldsEqual
  rw [balanceResetMiddleEntry_model, balanceResetMiddleEntry_model]
  simp only [resetCandidateMiddleModel, resetTsOverridesEntry, snapshotBound,
    allocCell, allocObject, Prod.fst, Prod.snd, beq_self_eq_true, if_true]
  simp only [h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2]
  trivial

def balanceResetTsCopyStage (stage : Nat) (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceResetMiddleEntry .ts b
  resetTsCopyStage stage e.1 e.2 b 26

theorem balanceResetTsCopyStage_fields (stage : Nat) (b : Int) :
    resetTsCopyFieldsEqual (balanceResetTsCopyStage stage b) (balanceResetTsCopyStage stage 0) := by
  have h := balanceResetTsCopyInitial_fields b
  exact resetTsCopyStage_fields_congr h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem balanceResetTsCopyStage_localValue (stage : Nat) (b : Int) (name : String) :
    localValue (balanceResetTsCopyStage stage b).1 (balanceResetTsCopyStage stage b).2 name =
      localValue (balanceResetTsCopyStage stage 0).1 (balanceResetTsCopyStage stage 0).2 name := by
  have h := balanceResetTsCopyStage_fields stage b
  exact localValue_fields_congr h.1 h.2.1 h.2.2.1

def resetTsCopyLocalInventory : List (Nat × String × TargetValue) :=
  [(0, "Object", .object 3), (0, "proto", .object 0), (0, "initialContext", .object 20),
   (1, "Object", .object 3), (1, "descriptors", .object 24),
   (2, "Object", .object 3), (2, "descriptors", .object 24),
   (4, "Object", .object 3), (4, "overrides", .object 26),
   (4, "name", .string "balance"), (4, "descriptor", .object 25)]

def resetTsCopyHostTable : HeapObject :=
  (objectAt (balanceCanonicalResetStage .ts 0 3).1 3).toOption.getD
    ⟨.jsOrdinary, some 0, [], [], [], false, false⟩

def resetTsCopyHostInventory : List (String × TargetValue) :=
  [("getPrototypeOf", .builtin .objectGetPrototypeOf), ("prototype", .object 0),
   ("getOwnPropertyDescriptors", .builtin .objectOwnDescriptors),
   ("entries", .builtin .objectEntries), ("defineProperty", .builtin .objectDefineProperty)]

def resetTsCopyFixedCheck : Prop :=
  let e := balanceResetMiddleEntry .ts 0
  let stage := (balanceCanonicalResetStage .ts 0 3).1
  e.1.nextObject = 24 ∧ e.1.nextCell = 27 ∧ e.1.checkerRef = 1 ∧ e.1.objectPrototype = 0 ∧
  stage.nextObject = 23 ∧ (balancePreparation .ts).1.nextObject = 20 ∧
  objectAt stage 3 = .ok resetTsCopyHostTable ∧ resetTsCopyHostTable.kind = .jsOrdinary ∧
  (resetTsCopyHostInventory.all fun entry => decide (resetTsCopyHostTable.own.lookup entry.1 =
    some ⟨some entry.2, none, none, true, true, true⟩)) = true ∧
  (resetTsCopyLocalInventory.all fun entry =>
    let s := balanceResetTsCopyStage entry.1 0
    decide (localValue s.1 s.2 entry.2.1 = .ok entry.2.2)) = true ∧
  snapshotAddress (balanceResetTsCopyStage 1 0).1 (balanceResetTsCopyStage 1 0).2 "overrides" = some 26 ∧
  e.1.cells.lookup 26 = some .undefined ∧ e.1.writableCells.lookup 26 = some true ∧
  (balanceResetTsCopyStage 4 0).1.objects.all (fun entry => entry.1 != 29) = true ∧
  localValue e.1 e.2 "Object" = .ok (.object 3) ∧
  localValue e.1 e.2 "initialContext" = .ok (.object 20)

instance : Decidable resetTsCopyFixedCheck := by unfold resetTsCopyFixedCheck; infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem resetTsCopyFixedCheck_true : resetTsCopyFixedCheck := by
  simp only [resetTsCopyFixedCheck, balanceResetTsCopyStage, resetTsCopyStage,
    resetTsCopyProtoEntry, resetTsCopyDescriptorEntry, resetTsCopyOverridesEntry,
    resetTsCopyIterationEntry, resetTsCopyBoundEntry,
    balanceResetMiddleEntry, balanceResetCandidateEntry,
    balanceCanonicalResetStage, balanceCanonicalResetEntry, balanceResetBodyEntry,
    balancePythonResetBodyEntry, balanceConstructorBodyEntry, balanceConstructorBoundEntry,
    balanceConstructorArgumentEntry, balanceStoredReset, balanceResetLookup, balanceStoredConstructor,
    balanceConstructorLookup, balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel



theorem resetTsCopyStage_keys_congr {m n f g b c cell stage}
    (ho : m.nextObject = n.nextObject)
    (hkeys : m.objects.map Prod.fst = n.objects.map Prod.fst) :
    (resetTsCopyStage stage m f b cell).1.objects.map Prod.fst =
      (resetTsCopyStage stage n g c cell).1.objects.map Prod.fst := by
  unfold resetTsCopyStage
  split <;>
    simp only [resetTsCopyProtoEntry, resetTsCopyDescriptorEntry,
      resetTsCopyOverridesEntry, resetTsCopyIterationEntry, resetTsCopyBoundEntry,
      resetTsDescriptorsMachine, snapshotBound, resetTsDescriptorPairBound,
      allocObject, allocCell, oneEntryMachine, Prod.fst, Prod.snd,
      List.map_cons, List.map_map, Function.comp_def] <;>
    simp only [ho, hkeys]

theorem resetTsCopyInitialModel_keys_congr {m n f g seed}
    (hn : m.nextObject = n.nextObject)
    (hk : m.objects.map Prod.fst = n.objects.map Prod.fst) :
    (resetCandidateMiddleModel .ts (m,f) seed).1.objects.map Prod.fst =
      (resetCandidateMiddleModel .ts (n,g) seed).1.objects.map Prod.fst := by
  simp only [resetCandidateMiddleModel, resetTsOverridesEntry, snapshotBound,
    allocCell, allocObject, Prod.fst, Prod.snd, beq_self_eq_true, if_true, List.map_cons]
  rw [hn,hk]

theorem balanceResetTsCopyInitial_keys (b : Int) :
    (balanceResetMiddleEntry .ts b).1.objects.map Prod.fst =
      (balanceResetMiddleEntry .ts 0).1.objects.map Prod.fst := by
  have h := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  have hk := balanceCanonicalResetStage_keys .ts b 3 (by decide)
  rw [balanceResetMiddleEntry_model, balanceResetMiddleEntry_model]
  exact resetTsCopyInitialModel_keys_congr
    (m := (balanceCanonicalResetStage .ts b 3).1) (n := (balanceCanonicalResetStage .ts 0 3).1)
    (f := (balanceCanonicalResetStage .ts b 3).2) (g := (balanceCanonicalResetStage .ts 0 3).2)
    (seed := (balancePreparation .ts).1.nextObject) h.2.2.2.2.1 hk


theorem balanceResetTsCopyStage_keys (stage : Nat) (b : Int) :
    (balanceResetTsCopyStage stage b).1.objects.map Prod.fst =
      (balanceResetTsCopyStage stage 0).1.objects.map Prod.fst :=
  resetTsCopyStage_keys_congr (balanceResetTsCopyInitial_fields b).2.2.2.2.1
    (balanceResetTsCopyInitial_keys b)

theorem balanceResetTsCopyStage_local {stage b key value}
    (he : (stage, key, value) ∈ resetTsCopyLocalInventory) :
    localValue (balanceResetTsCopyStage stage b).1 (balanceResetTsCopyStage stage b).2 key = .ok value := by
  rw [balanceResetTsCopyStage_localValue]
  obtain ⟨_, _, _, _, _, _, _, _, _, hl, _⟩ := resetTsCopyFixedCheck_true
  have h := (List.all_eq_true.mp hl) (stage,key,value) he
  simpa only [decide_eq_true_eq] using h

theorem balanceResetTsCopyInitial_numbers (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    e.1.nextObject = 24 ∧ e.1.nextCell = 27 ∧ e.1.checkerRef = 1 ∧ e.1.objectPrototype = 0 := by
  obtain ⟨hn, hc, hk, hp, _⟩ := resetTsCopyFixedCheck_true
  have h := balanceResetTsCopyInitial_fields b
  exact ⟨h.2.2.2.2.1.trans hn, h.2.2.2.1.trans hc,
    h.2.2.2.2.2.2.trans hk, h.2.2.2.2.2.1.trans hp⟩

theorem balanceResetTsCopyInitial_object3 (b : Int) :
    objectAt (balanceResetMiddleEntry .ts b).1 3 = .ok resetTsCopyHostTable := by
  obtain ⟨_, _, _, _, hn, hs, host, _⟩ := resetTsCopyFixedCheck_true
  have footprint := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  have hne : 3 ≠ (balanceCanonicalResetStage .ts b 3).1.nextObject := by
    rw [footprint.2.2.2.2.1, hn]; decide
  rw [balanceResetMiddleEntry_model,
    resetCandidateMiddleModel_objectAt_other (m := (balanceCanonicalResetStage .ts b 3).1)
      (f := (balanceCanonicalResetStage .ts b 3).2)
      (seed := (balancePreparation .ts).1.nextObject) (ref := 3) hne]
  exact (balanceCanonicalResetStage_objectAt .ts b 3 (by decide) 3
    (by rw [hs]; decide)).trans host

theorem balanceResetTsCopyStage_object3 (stage : Nat) (b : Int) :
    objectAt (balanceResetTsCopyStage stage b).1 3 = .ok resetTsCopyHostTable := by
  have hlt : 3 < (balanceResetMiddleEntry .ts b).1.nextObject := by
    rw [(balanceResetTsCopyInitial_numbers b).1]; decide
  unfold balanceResetTsCopyStage resetTsCopyStage
  split
  · exact (resetTsCopyProtoEntry_objectAt (balanceResetMiddleEntry .ts b).1
      (balanceResetMiddleEntry .ts b).2 3).trans (balanceResetTsCopyInitial_object3 b)
  · exact (resetTsCopyDescriptorEntry_objectAt_old (m := (balanceResetMiddleEntry .ts b).1)
      (f := (balanceResetMiddleEntry .ts b).2) (b := b) (ref := 3) hlt).trans (balanceResetTsCopyInitial_object3 b)
  · exact (resetTsCopyOverridesEntry_objectAt_old (m := (balanceResetMiddleEntry .ts b).1)
      (f := (balanceResetMiddleEntry .ts b).2) (b := b) (cell := 26) (ref := 3) hlt).trans (balanceResetTsCopyInitial_object3 b)
  · exact (resetTsCopyIterationEntry_objectAt_old (m := (balanceResetMiddleEntry .ts b).1)
      (f := (balanceResetMiddleEntry .ts b).2) (b := b) (cell := 26) (ref := 3) hlt).trans (balanceResetTsCopyInitial_object3 b)
  · exact (resetTsCopyBoundEntry_objectAt_old (m := (balanceResetMiddleEntry .ts b).1)
      (f := (balanceResetMiddleEntry .ts b).2) (b := b) (cell := 26) (ref := 3) hlt).trans (balanceResetTsCopyInitial_object3 b)

theorem resetTsCopyOrdinary_read {m ref object key value}
    (hr : ref ≠ m.checkerRef) (hp : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok object) (hk : object.kind = .jsOrdinary)
    (hv : object.own.lookup key = some ⟨some value, none, none, true, true, true⟩) :
    readPropertyValue .ts m (.object ref) key = .ok ⟨m, .ok value⟩ := by
  simp [readPropertyValue, beq_eq_false_iff_ne.mpr hr, beq_eq_false_iff_ne.mpr hp,
    ho, hk, readOwn, hv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem resetTsCopyStage_hostFields (stage : Nat) (m f b cell) :
    let e := resetTsCopyStage stage m f b cell
    e.1.checkerRef = m.checkerRef ∧ e.1.objectPrototype = m.objectPrototype := by
  unfold resetTsCopyStage
  split <;> simp only [resetTsCopyProtoEntry, resetTsCopyDescriptorEntry, resetTsCopyOverridesEntry,
    resetTsCopyIterationEntry, resetTsCopyBoundEntry, resetTsDescriptorsMachine,
    snapshotBound, resetTsDescriptorPairBound, allocObject, allocCell, oneEntryMachine,
    Prod.fst, Prod.snd] <;> trivial

theorem resetTsCopyHost_read {m key value}
    (he : (key,value) ∈ resetTsCopyHostInventory)
    (hc : m.checkerRef = 1) (hp : m.objectPrototype = 0)
    (ho : objectAt m 3 = .ok resetTsCopyHostTable) :
    readPropertyValue .ts m (.object 3) key = .ok ⟨m, .ok value⟩ := by
  obtain ⟨_, _, _, _, _, _, _, hk, hall, _⟩ := resetTsCopyFixedCheck_true
  have hv : resetTsCopyHostTable.own.lookup key =
      some ⟨some value, none, none, true, true, true⟩ :=
    of_decide_eq_true ((List.all_eq_true.mp hall) (key,value) he)
  exact resetTsCopyOrdinary_read (m := m) (ref := 3) (object := resetTsCopyHostTable)
    (by rw [hc]; decide) (by rw [hp]; decide) ho hk hv

theorem balanceResetTsCopyStage_numbers (stage : Nat) (b : Int) :
    let e := balanceResetTsCopyStage stage b
    e.1.checkerRef = 1 ∧ e.1.objectPrototype = 0 := by
  have hn := balanceResetTsCopyInitial_numbers b
  have hg := resetTsCopyStage_hostFields stage (balanceResetMiddleEntry .ts b).1
    (balanceResetMiddleEntry .ts b).2 b 26
  exact ⟨hg.1.trans hn.2.2.1, hg.2.trans hn.2.2.2⟩


theorem resetTsCopyBoundEntry_nextObject (m f b cell) :
    (resetTsCopyBoundEntry m f b cell).1.nextObject = m.nextObject + 5 := by
  simp only [resetTsCopyProtoEntry, resetTsCopyDescriptorEntry, resetTsCopyOverridesEntry,
    resetTsCopyIterationEntry, resetTsCopyBoundEntry, resetTsDescriptorsMachine,
    snapshotBound, resetTsDescriptorPairBound, allocObject, allocCell, oneEntryMachine,
    Prod.fst, Prod.snd]


theorem balanceResetTsCopyStage_fresh (b : Int) :
    ∀ entry ∈ (balanceResetTsCopyStage 4 b).1.objects,
      entry.1 ≠ (balanceResetTsCopyStage 4 b).1.nextObject := by
  have hn := (balanceResetTsCopyInitial_numbers b).1
  have hnext : (balanceResetTsCopyStage 4 b).1.nextObject = 29 := by
    exact (resetTsCopyBoundEntry_nextObject (balanceResetMiddleEntry .ts b).1
      (balanceResetMiddleEntry .ts b).2 b 26).trans (by rw [hn])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hf, _⟩ := resetTsCopyFixedCheck_true
  have hm (xs : List (ObjRef × HeapObject)) :
      xs.all (fun e => e.1 != 29) = (xs.map Prod.fst).all (fun ref => ref != 29) := by
    simp only [List.all_map]; rfl
  apply objects_all_fresh
  rw [hnext, hm, balanceResetTsCopyStage_keys, ← hm]
  exact hf

theorem balanceResetTsCopyInitial_writable (b : Int) :
    (balanceResetMiddleEntry .ts b).1.writableCells =
      (balanceResetMiddleEntry .ts 0).1.writableCells := rfl

theorem resetTsCopy_write_of_cells {m f b cell}
    (hv : m.cells.lookup cell = some .undefined)
    (hw : m.writableCells.lookup cell = some true)
    (hn0 : cell ≠ m.nextCell) (hn1 : cell ≠ m.nextCell + 1) :
    let d := resetTsCopyDescriptorEntry m f b
    let allocated := (allocObject d.1 (literalObject .ts d.1)).1
    writeCell allocated cell (.object d.1.nextObject) =
      .ok (resetTsCopyOverridesEntry m f b cell).1 := by
  simp only [resetTsCopyDescriptorEntry, resetTsCopyProtoEntry, snapshotBound,
    resetTsCopyOverridesEntry, resetTsDescriptorsMachine, allocCell, allocObject, Prod.fst, Prod.snd,
    writeCell, List.lookup_cons, beq_eq_false_iff_ne.mpr hn0, beq_eq_false_iff_ne.mpr hn1,
    if_false, hv, hw, reduceCtorEq, Bool.false_eq_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals rfl

theorem balanceResetTsCopy_write (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    let d := resetTsCopyDescriptorEntry e.1 e.2 b
    let allocated := (allocObject d.1 (literalObject .ts d.1)).1
    writeCell allocated 26 (.object d.1.nextObject) =
      .ok (resetTsCopyOverridesEntry e.1 e.2 b 26).1 := by
  have hn := (balanceResetTsCopyInitial_numbers b).2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcell, hw, _⟩ := resetTsCopyFixedCheck_true
  have hcellb : (balanceResetMiddleEntry .ts b).1.cells.lookup 26 = some .undefined := by
    rw [balanceResetMiddleEntry_cells]; exact hcell
  have hwb : (balanceResetMiddleEntry .ts b).1.writableCells.lookup 26 = some true := by
    rw [balanceResetTsCopyInitial_writable]; exact hw
  exact resetTsCopy_write_of_cells hcellb hwb
    (by rw [hn]; decide) (by rw [hn]; decide)



theorem resetTsCopyBoundEntry_prototype (m f b cell) :
    (resetTsCopyBoundEntry m f b cell).1.objectPrototype = m.objectPrototype := by
  simp only [resetTsCopyProtoEntry, resetTsCopyDescriptorEntry, resetTsCopyOverridesEntry,
    resetTsCopyIterationEntry, resetTsCopyBoundEntry, resetTsDescriptorsMachine,
    snapshotBound, resetTsDescriptorPairBound, allocObject, allocCell, oneEntryMachine,
    Prod.fst, Prod.snd]


theorem resetTsCopyBalance_prototype_congr {m n : TargetMachine} {b : Int}
    (hp : m.objectPrototype = n.objectPrototype) : balanceHeapObject .ts m b = balanceHeapObject .ts n b := by
  unfold balanceHeapObject
  rw [hp]

theorem resetTsCopyDescriptor_prototype_congr {m n : TargetMachine} {b : Int}
    (hp : m.objectPrototype = n.objectPrototype) : resetTsDescriptorObject m b = resetTsDescriptorObject n b := by
  unfold resetTsDescriptorObject
  rw [hp]

theorem resetTsCopyLiteral_prototype_congr {m n : TargetMachine}
    (hp : m.objectPrototype = n.objectPrototype) : literalObject .ts m = literalObject .ts n := by
  unfold literalObject
  rw [hp]

theorem resetTsCopyInitialModel_prototype (m f seed) :
    (resetCandidateMiddleModel .ts (m,f) seed).1.objectPrototype = m.objectPrototype := by
  simp only [resetCandidateMiddleModel, resetTsOverridesEntry, snapshotBound,
    allocCell, allocObject, Prod.fst, Prod.snd, beq_self_eq_true, if_true]

theorem resetTsCopySnapshots_prototype (m f) :
    (resetSnapshotsInstalled .ts m f).1.objectPrototype = m.objectPrototype := by
  simp only [resetSnapshotsInstalled, resetSnapshotHistory, resetSnapshotContext,
    resetSnapshotState, snapshotRollbackInstalled, functionInstalled, snapshotBound,
    allocCell, allocObject, allocClosure, Prod.fst, Prod.snd, beq_self_eq_true, if_true]

theorem balanceResetTsCopyInitial_prototype (b : Int) :
    (balanceResetMiddleEntry .ts b).1.objectPrototype = (balancePreparation .ts).1.objectPrototype := by
  have initial := resetTsCopyInitialModel_prototype (balanceCanonicalResetStage .ts b 3).1
    (balanceCanonicalResetStage .ts b 3).2 (balancePreparation .ts).1.nextObject
  rw [← balanceResetMiddleEntry_model] at initial
  apply initial.trans
  change (resetSnapshotsInstalled .ts (balanceCanonicalResetEntry .ts b).1
    (balanceCanonicalResetEntry .ts b).2).1.objectPrototype = _
  rw [resetTsCopySnapshots_prototype]
  change (balanceResetBodyEntry .ts b).1.objectPrototype = _
  simp only [balanceResetBodyEntry, balanceConstructorBodyEntry, balanceConstructorBoundEntry,
    balanceConstructorArgumentEntry, allocCell, allocObject, allocClosure, Prod.fst, Prod.snd]

theorem balanceResetTsCopy_seed (b : Int) :
    objectAt (balanceResetMiddleEntry .ts b).1 20 =
      .ok (balanceHeapObject .ts (balanceResetMiddleEntry .ts b).1 b) := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := resetTsCopyFixedCheck_true
  have h := balanceResetMiddleEntry_ts_seed_fixed b
  rw [hs] at h
  have hp : (balancePreparation .ts).1.objectPrototype =
      (balanceResetMiddleEntry .ts b).1.objectPrototype := (balanceResetTsCopyInitial_prototype b).symm
  have heq := resetTsCopyBalance_prototype_congr
    (m := (balancePreparation .ts).1) (n := (balanceResetMiddleEntry .ts b).1) (b := b) hp
  exact h.trans (congrArg Except.ok heq)

theorem balanceResetTsCopy_initial_reads (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    localValue e.1 e.2 "Object" = .ok (.object 3) ∧
      localValue e.1 e.2 "initialContext" = .ok (.object 20) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ho, hi⟩ := resetTsCopyFixedCheck_true
  exact ⟨(balanceResetMiddleEntry_localValue .ts b "Object").trans ho,
    (balanceResetMiddleEntry_localValue .ts b "initialContext").trans hi⟩

set_option maxHeartbeats 10000000 in

theorem balanceResetTsCopy_proto (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    ∀ k, evalExpr (k + 4) (balanceProgram .ts) e.1 e.2 resetTsProtoExpr =
      .ok ⟨e.1, .ok (.object e.1.objectPrototype)⟩ := by
  dsimp only
  let e := balanceResetMiddleEntry .ts b
  have nums := balanceResetTsCopyInitial_numbers b
  have hn : e.1.nextObject = 24 := nums.1
  have hlocal := balanceResetTsCopy_initial_reads b
  have host (stage : Nat) (key : String) (value : TargetValue)
      (he : (key,value) ∈ resetTsCopyHostInventory) :
      readPropertyValue .ts (balanceResetTsCopyStage stage b).1 (.object 3) key =
        .ok ⟨(balanceResetTsCopyStage stage b).1, .ok value⟩ :=
    resetTsCopyHost_read he (balanceResetTsCopyStage_numbers stage b).1
      (balanceResetTsCopyStage_numbers stage b).2 (balanceResetTsCopyStage_object3 stage b)
  intro k
  exact resetTsProtoExpr_execute (m := e.1) (f := e.2) (ref := 20) (object := 3) (b := b) (k := k) hlocal.1
    (resetTsCopyHost_read (by decide) nums.2.2.1 nums.2.2.2
      (balanceResetTsCopyInitial_object3 b)) hlocal.2 (balanceResetTsCopy_seed b)

theorem balanceResetTsCopy_guard (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    let p := resetTsCopyProtoEntry e.1 e.2
    ∀ k, evalExpr (k + 4) (balanceProgram .ts) p.1 p.2 resetTsProtoGuard =
      .ok ⟨p.1, .ok (.bool false)⟩ := by
  dsimp only
  let e := balanceResetMiddleEntry .ts b
  have nums := balanceResetTsCopyInitial_numbers b
  have hn : e.1.nextObject = 24 := nums.1
  have hlocal := balanceResetTsCopy_initial_reads b
  have host (stage : Nat) (key : String) (value : TargetValue)
      (he : (key,value) ∈ resetTsCopyHostInventory) :
      readPropertyValue .ts (balanceResetTsCopyStage stage b).1 (.object 3) key =
        .ok ⟨(balanceResetTsCopyStage stage b).1, .ok value⟩ :=
    resetTsCopyHost_read he (balanceResetTsCopyStage_numbers stage b).1
      (balanceResetTsCopyStage_numbers stage b).2 (balanceResetTsCopyStage_object3 stage b)
  intro k
  have hp : localValue (balanceResetTsCopyStage 0 b).1 (balanceResetTsCopyStage 0 b).2 "proto" =
      .ok (.object (balanceResetTsCopyStage 0 b).1.objectPrototype) := by
    rw [(balanceResetTsCopyStage_numbers 0 b).2]
    exact balanceResetTsCopyStage_local (b := b) (by decide : (0,"proto",TargetValue.object 0) ∈ _)
  have hc : readPropertyValue .ts (balanceResetTsCopyStage 0 b).1 (.object 3) "prototype" =
      .ok ⟨(balanceResetTsCopyStage 0 b).1, .ok (.object (balanceResetTsCopyStage 0 b).1.objectPrototype)⟩ := by
    rw [(balanceResetTsCopyStage_numbers 0 b).2]
    exact host 0 "prototype" (.object 0) (by decide)
  exact resetTsProtoGuard_execute
    (balanceResetTsCopyStage_local (b := b) (by decide : (0,"Object",TargetValue.object 3) ∈ _)) hc hp

theorem balanceResetTsCopy_descriptors (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    let p := resetTsCopyProtoEntry e.1 e.2
    ∀ k, evalExpr (k + 4) (balanceProgram .ts) p.1 p.2 resetTsOwnDescriptorsExpr =
      .ok ⟨resetTsDescriptorsMachine p.1 b, .ok (.object e.1.nextObject)⟩ := by
  dsimp only
  let e := balanceResetMiddleEntry .ts b
  have nums := balanceResetTsCopyInitial_numbers b
  have hn : e.1.nextObject = 24 := nums.1
  have hlocal := balanceResetTsCopy_initial_reads b
  have host (stage : Nat) (key : String) (value : TargetValue)
      (he : (key,value) ∈ resetTsCopyHostInventory) :
      readPropertyValue .ts (balanceResetTsCopyStage stage b).1 (.object 3) key =
        .ok ⟨(balanceResetTsCopyStage stage b).1, .ok value⟩ :=
    resetTsCopyHost_read he (balanceResetTsCopyStage_numbers stage b).1
      (balanceResetTsCopyStage_numbers stage b).2 (balanceResetTsCopyStage_object3 stage b)
  intro k
  let p := resetTsCopyProtoEntry e.1 e.2
  have hp : e.1.objectPrototype = p.1.objectPrototype := rfl
  have ho : objectAt p.1 20 = .ok (balanceHeapObject .ts p.1 b) :=
    (resetTsCopyProtoEntry_objectAt e.1 e.2 20).trans
      ((balanceResetTsCopy_seed b).trans (congrArg Except.ok
        (resetTsCopyBalance_prototype_congr (m := e.1) (n := p.1) (b := b) hp)))
  have peq : balanceResetTsCopyStage 0 b = p := rfl
  have hg := balanceResetTsCopyStage_local (b := b)
    (by decide : (0,"Object",TargetValue.object 3) ∈ resetTsCopyLocalInventory)
  have hi := balanceResetTsCopyStage_local (b := b)
    (by decide : (0,"initialContext",TargetValue.object 20) ∈ resetTsCopyLocalInventory)
  have hc := host 0 "getOwnPropertyDescriptors" (.builtin .objectOwnDescriptors) (by decide)
  rw [peq] at hg hi hc
  have result := resetTsOwnDescriptorsExpr_execute (m := p.1) (f := p.2) (ref := 20)
    (object := 3) (b := b) (k := k) hg hc hi ho
  have hpN : p.1.nextObject = e.1.nextObject := rfl
  rw [hpN] at result
  exact result

theorem balanceResetTsCopy_descriptor_object (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    let bound := resetTsCopyBoundEntry e.1 e.2 b 26
    objectAt bound.1 25 = .ok (resetTsDescriptorObject bound.1 b) := by
  have h := resetTsCopyBoundEntry_descriptor
    (m := (balanceResetMiddleEntry .ts b).1) (f := (balanceResetMiddleEntry .ts b).2) (b := b) (cell := 26)
  rw [(balanceResetTsCopyInitial_numbers b).1] at h
  exact h

theorem balanceResetTsCopyRaw_local {stage b key value raw}
    (heq : balanceResetTsCopyStage stage b = raw)
    (he : (stage,key,value) ∈ resetTsCopyLocalInventory) :
    localValue raw.1 raw.2 key = .ok value := by
  have h := balanceResetTsCopyStage_local (b := b) he
  rw [heq] at h
  exact h

theorem balanceResetTsCopyRaw_host {stage b key value raw}
    (heq : balanceResetTsCopyStage stage b = raw)
    (he : (key,value) ∈ resetTsCopyHostInventory) :
    readPropertyValue .ts raw.1 (.object 3) key = .ok ⟨raw.1, .ok value⟩ := by
  have h := resetTsCopyHost_read he (balanceResetTsCopyStage_numbers stage b).1
    (balanceResetTsCopyStage_numbers stage b).2 (balanceResetTsCopyStage_object3 stage b)
  rw [heq] at h
  exact h
theorem balanceResetTsCopy_physical (b : Int) :
    let e := balanceResetMiddleEntry .ts b
    ResetTsDescriptorCopyPhysical e.1 e.2 b 26 := by
  let e := balanceResetMiddleEntry .ts b
  have nums := balanceResetTsCopyInitial_numbers b
  have hn : e.1.nextObject = 24 := nums.1
  have hlocal := balanceResetTsCopy_initial_reads b
  have host (stage : Nat) (key : String) (value : TargetValue)
      (he : (key,value) ∈ resetTsCopyHostInventory) :
      readPropertyValue .ts (balanceResetTsCopyStage stage b).1 (.object 3) key =
        .ok ⟨(balanceResetTsCopyStage stage b).1, .ok value⟩ :=
    resetTsCopyHost_read he (balanceResetTsCopyStage_numbers stage b).1
      (balanceResetTsCopyStage_numbers stage b).2 (balanceResetTsCopyStage_object3 stage b)
  constructor
  · exact balanceResetTsCopy_proto b
  · exact balanceResetTsCopy_guard b
  · exact balanceResetTsCopy_descriptors b
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, ha, _⟩ := resetTsCopyFixedCheck_true
    have h := balanceResetTsCopyStage_fields 1 b
    exact (snapshotAddress_fields_congr
      (m := (balanceResetTsCopyStage 1 b).1) (n := (balanceResetTsCopyStage 1 0).1)
      (f := (balanceResetTsCopyStage 1 b).2) (g := (balanceResetTsCopyStage 1 0).2)
      h.1 h.2.2.1).trans ha
  · exact balanceResetTsCopy_write b
  · intro k
    let o := resetTsCopyOverridesEntry e.1 e.2 b 26
    have heq : balanceResetTsCopyStage 2 b = o := rfl
    have hg := balanceResetTsCopyRaw_local heq
      (by decide : (2,"Object",TargetValue.object 3) ∈ resetTsCopyLocalInventory)
    have hd := balanceResetTsCopyRaw_local heq
      (by decide : (2,"descriptors",TargetValue.object 24) ∈ resetTsCopyLocalInventory)
    have hc := balanceResetTsCopyRaw_host heq
      (by decide : ("entries",TargetValue.builtin .objectEntries) ∈ resetTsCopyHostInventory)
    apply resetTsCopy_entries_execute (m := e.1) (f := e.2) (b := b) (cell := 26) (k := k) hg hc
    rw [hn]
    exact hd
  · exact (oneEntryMachine_ts_objects (resetTsCopyOverridesEntry e.1 e.2 b 26).1
      "balance" (.object (e.1.nextObject + 1))).1
  · exact (oneEntryMachine_ts_objects (resetTsCopyOverridesEntry e.1 e.2 b 26).1
      "balance" (.object (e.1.nextObject + 1))).2
  · intro k
    let bound := resetTsCopyBoundEntry e.1 e.2 b 26
    let fresh := (allocObject bound.1 (literalObject .ts bound.1)).1
    have bpair : balanceResetTsCopyStage 4 b = bound := rfl
    have bfields := balanceResetTsCopyStage_numbers 4 b
    rw [bpair] at bfields
    have hg : localValue bound.1 bound.2 "Object" = .ok (.object 3) :=
      balanceResetTsCopyRaw_local (stage := 4) (b := b) (raw := bound) (by rfl) (by decide : (4,"Object",TargetValue.object 3) ∈ resetTsCopyLocalInventory)
    have ht : localValue bound.1 bound.2 "overrides" = .ok (.object 26) :=
      balanceResetTsCopyRaw_local (stage := 4) (b := b) (raw := bound) (by rfl) (by decide : (4,"overrides",TargetValue.object 26) ∈ resetTsCopyLocalInventory)
    have hname : localValue bound.1 bound.2 "name" = .ok (.string "balance") :=
      balanceResetTsCopyRaw_local (stage := 4) (b := b) (raw := bound) (by rfl) (by decide : (4,"name",TargetValue.string "balance") ∈ resetTsCopyLocalInventory)
    have hdlocal : localValue bound.1 bound.2 "descriptor" = .ok (.object 25) :=
      balanceResetTsCopyRaw_local (stage := 4) (b := b) (raw := bound) (by rfl) (by decide : (4,"descriptor",TargetValue.object 25) ∈ resetTsCopyLocalInventory)
    have hd : objectAt bound.1 25 = .ok (resetTsDescriptorObject bound.1 b) :=
      balanceResetTsCopy_descriptor_object b
    have hpFresh : e.1.objectPrototype = fresh.objectPrototype :=
      (resetTsCopyBoundEntry_prototype e.1 e.2 b 26).symm
    have hdBase : objectAt fresh (e.1.nextObject + 1) = .ok (resetTsDescriptorObject e.1 b) :=
      resetTsCopyBoundEntry_descriptor_literal (m := e.1) (f := e.2) (b := b) (cell := 26)
    have hdIndex : objectAt fresh (e.1.nextObject + 1) = objectAt fresh 25 :=
      congrArg (fun ref => objectAt fresh ref) (congrArg (fun n => n + 1) hn)
    have hdfresh : objectAt fresh 25 = .ok (resetTsDescriptorObject fresh b) :=
      hdIndex.symm.trans (hdBase.trans (congrArg Except.ok
        (resetTsCopyDescriptor_prototype_congr (m := e.1) (n := fresh) (b := b) hpFresh)))
    have hdfreshLocal : localValue fresh bound.2 "descriptor" = .ok (.object 25) :=
      (localValue_fields_congr (m := fresh) (n := bound.1)
        (f := bound.2) (g := bound.2) (name := "descriptor") rfl rfl rfl).trans hdlocal
    have hFreshChecker : fresh.checkerRef = 1 := bfields.1
    have hFreshProto : fresh.objectPrototype = 0 := bfields.2
    have hnChecker : 25 ≠ fresh.checkerRef := fun h => (by decide : 25 ≠ 1) (h.trans hFreshChecker)
    have hnProto : 25 ≠ fresh.objectPrototype := fun h => (by decide : 25 ≠ 0) (h.trans hFreshProto)
    have hvalue := resetTsCopyDescriptorValue_read hnChecker hnProto hdfresh
    have hprogram : readPropertyValue (balanceProgram .ts).lang fresh (.object 25) "value" =
        .ok ⟨fresh, .ok (integerValue .ts b)⟩ :=
      Eq.mpr (congrArg (fun lang => readPropertyValue lang fresh (.object 25) "value" =
        .ok ⟨fresh, .ok (integerValue .ts b)⟩) (balanceProgram_lang .ts)) hvalue
    have he : DepthDerivesExpr (balanceProgram .ts) fresh bound.2
        (.property (.local "descriptor") "value") ⟨fresh, .ok (integerValue .ts b)⟩ 1 :=
      DepthDerivesExpr.property (program := balanceProgram .ts) (.localRead hdfreshLocal) hprogram
    let literal := (allocObject bound.1 (resetTsDefineLiteral bound.1 b)).1
    have hvBase : objectAt literal (e.1.nextObject + 2) = .ok (literalObject .ts e.1) :=
      resetTsCopyBoundEntry_overrides_literal (m := e.1) (f := e.2) (b := b) (cell := 26)
    have hvIndex : objectAt literal (e.1.nextObject + 2) = objectAt literal 26 :=
      congrArg (fun ref => objectAt literal ref) (congrArg (fun n => n + 2) hn)
    have hpLiteral : e.1.objectPrototype = literal.objectPrototype :=
      (resetTsCopyBoundEntry_prototype e.1 e.2 b 26).symm
    have hover : objectAt literal 26 = .ok (literalObject .ts literal) :=
      hvIndex.symm.trans (hvBase.trans (congrArg Except.ok
        (resetTsCopyLiteral_prototype_congr (m := e.1) (n := literal) hpLiteral)))
    have beq : balanceResetTsCopyStage 4 b = bound := rfl
    have hfields := balanceResetTsCopyStage_numbers 4 b
    have hfresh := balanceResetTsCopyStage_fresh b
    rw [beq] at hfields hfresh
    have body := resetTsDescriptorCopyBody_execute (m := bound.1) (f := bound.2)
      (object := 3) (target := 26) (descriptor := 25) (b := b) (k := k) (bad := resetTsCopyAccessorError) hg
      (balanceResetTsCopyRaw_host beq
        (by decide : ("defineProperty",TargetValue.builtin .objectDefineProperty) ∈ resetTsCopyHostInventory))
      ht hname hdlocal hd hfresh he hover
    have hp : bound.1.objectPrototype = e.1.objectPrototype :=
      resetTsCopyBoundEntry_prototype e.1 e.2 b 26
    rw [resetTsCopyBalance_prototype_congr (m := bound.1) (n := e.1) (b := b) hp] at body
    rw [resetTsDescriptorCopyModel_final, hn]
    exact body

theorem balanceReset_ts_canonical_descriptor_copy_safe (b : Int) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 26) (balanceProgram .ts) e.1 e.2 (balanceResetMiddleStmt .ts 2) =
      .ok ⟨(resetTsDescriptorCopyModel e.1 e.2 b 26).1,
        (resetTsDescriptorCopyModel e.1 e.2 b 26).2, .normal⟩ := by
  have hi := (balanceResetTsCopy_initial_reads b).2
  dsimp only
  rw [balanceReset_ts_seed_present (k := k + 21) hi,
    balanceReset_ts_canonical_plain_guard_skip b (k + 18)]
  exact resetTsDescriptorContinuation_execute (balanceResetTsCopy_physical b)


theorem resetTsDescriptorCopyModel_objectAt_old {m f b cell ref}
    (hf : ref < m.nextObject) :
    objectAt (resetTsDescriptorCopyModel m f b cell).1 ref = objectAt m ref := by
  have h (i : Nat) : ref ≠ m.nextObject + i :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hf (Nat.le_add_right _ _))
  unfold objectAt resetTsDescriptorCopyModel
  simp only [snapshotBound, resetTsDescriptorsMachine, resetTsDescriptorPairBound,
    allocObject, allocCell, oneEntryMachine, Prod.fst, Prod.snd]
  rw [lookup_replace_payload_other _ _ (h 2)]
  simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr (h 5),
    beq_eq_false_iff_ne.mpr (h 4), beq_eq_false_iff_ne.mpr (h 3),
    beq_eq_false_iff_ne.mpr (h 2), if_false]
  have h0 : ref ≠ m.nextObject := by simpa only [Nat.add_zero] using h 0
  rw [lookup_replace_payload_other _ _ h0]
  simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr (h 1),
    beq_eq_false_iff_ne.mpr h0, if_false]


def balanceResetTsDescriptorEntry (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceResetMiddleEntry .ts b
  resetTsDescriptorCopyModel e.1 e.2 b 26

theorem resetTsDescriptorCopyModel_fields_congr {m n f g b c cell}
    (hf : f = g) (hc : m.cells = n.cells) (hg : m.globals = n.globals)
    (hn : m.nextCell = n.nextCell) (ho : m.nextObject = n.nextObject)
    (hp : m.objectPrototype = n.objectPrototype) (hk : m.checkerRef = n.checkerRef) :
    let e := resetTsDescriptorCopyModel m f b cell
    let z := resetTsDescriptorCopyModel n g c cell
    e.2 = z.2 ∧ e.1.cells = z.1.cells ∧ e.1.globals = z.1.globals ∧
      e.1.nextCell = z.1.nextCell ∧ e.1.nextObject = z.1.nextObject ∧
      e.1.objectPrototype = z.1.objectPrototype ∧ e.1.checkerRef = z.1.checkerRef := by
  simp only [resetTsDescriptorCopyModel, resetTsDescriptorsMachine, snapshotBound,
    resetTsDescriptorPairBound, allocObject, allocCell, oneEntryMachine, Prod.fst, Prod.snd]
  simp only [hf, hc, hg, hn, ho, hp, hk]
  trivial

theorem balanceResetTsDescriptorEntry_fields (b : Int) :
    let e := balanceResetTsDescriptorEntry b
    let z := balanceResetTsDescriptorEntry 0
    e.2 = z.2 ∧ e.1.cells = z.1.cells ∧ e.1.globals = z.1.globals ∧
      e.1.nextCell = z.1.nextCell ∧ e.1.nextObject = z.1.nextObject ∧
      e.1.objectPrototype = z.1.objectPrototype ∧ e.1.checkerRef = z.1.checkerRef := by
  have h := balanceResetTsCopyInitial_fields b
  dsimp only [balanceResetTsDescriptorEntry]
  exact resetTsDescriptorCopyModel_fields_congr
    (m := (balanceResetMiddleEntry .ts b).1) (n := (balanceResetMiddleEntry .ts 0).1)
    (f := (balanceResetMiddleEntry .ts b).2) (g := (balanceResetMiddleEntry .ts 0).2)
    (b := b) (c := 0) (cell := 26)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem balanceResetTsDescriptorEntry_localValue (b : Int) (name : String) :
    localValue (balanceResetTsDescriptorEntry b).1 (balanceResetTsDescriptorEntry b).2 name =
      localValue (balanceResetTsDescriptorEntry 0).1 (balanceResetTsDescriptorEntry 0).2 name := by
  have h := balanceResetTsDescriptorEntry_fields b
  exact localValue_fields_congr
    (m := (balanceResetTsDescriptorEntry b).1) (n := (balanceResetTsDescriptorEntry 0).1)
    (f := (balanceResetTsDescriptorEntry b).2) (g := (balanceResetTsDescriptorEntry 0).2)
    h.1 h.2.1 h.2.2.1

def resetTsCanonicalTableObject (ref : ObjRef) : HeapObject :=
  (objectAt (balanceCanonicalResetStage .ts 0 3).1 ref).toOption.getD
    (literalObject .ts TargetMachine.empty)

def resetTsCanonicalOverlayTables : List (Nat × String × TargetValue) :=
  [(3, "entries", .builtin .objectEntries), (3, "hasOwn", .builtin .objectHasOwn),
   (7, "context", .object 10), (10, "balance", .object 11),
   (11, "type", .string "integer"), (5, "isSafeInteger", .builtin .jsIsSafeInteger)]

def resetTsCanonicalOverlayTablesCheck : Bool :=
  resetTsCanonicalOverlayTables.all fun entry =>
    let m := (balanceCanonicalResetStage .ts 0 3).1
    decide (objectAt m entry.1 = .ok (resetTsCanonicalTableObject entry.1) ∧
      entry.1 ≠ 1 ∧ entry.1 ≠ 0 ∧
      (resetTsCanonicalTableObject entry.1).kind = .jsOrdinary ∧
      (resetTsCanonicalTableObject entry.1).own.lookup entry.2.1 =
        some ⟨some entry.2.2, none, none, true, true, true⟩)

theorem resetTsCanonicalOverlayTablesCheck_true : resetTsCanonicalOverlayTablesCheck = true := by
  simp only [resetTsCanonicalOverlayTablesCheck, resetTsCanonicalTableObject,
    balanceCanonicalResetStage, balanceCanonicalResetEntry, balanceResetBodyEntry,
    balancePythonResetBodyEntry, balanceConstructorBodyEntry, balanceConstructorBoundEntry,
    balanceConstructorArgumentEntry, balanceStoredReset, balanceResetLookup, balanceStoredConstructor,
    balanceConstructorLookup, balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel

theorem resetTsOrdinaryTable_read {m ref object key value}
    (hr : ref ≠ m.checkerRef) (hp : ref ≠ m.objectPrototype)
    (ho : objectAt m ref = .ok object) (hk : object.kind = .jsOrdinary)
    (hv : object.own.lookup key = some ⟨some value, none, none, true, true, true⟩) :
    readPropertyValue .ts m (.object ref) key = .ok ⟨m, .ok value⟩ := by
  simp [readPropertyValue, beq_eq_false_iff_ne.mpr hr, beq_eq_false_iff_ne.mpr hp,
    ho, hk, readOwn, hv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem resetTsCanonicalOverlayTable_read {m : TargetMachine} {entry}
    (he : entry ∈ resetTsCanonicalOverlayTables)
    (hc : m.checkerRef = 1) (hp : m.objectPrototype = 0)
    (ho : objectAt m entry.1 = objectAt (balanceCanonicalResetStage .ts 0 3).1 entry.1) :
    readPropertyValue .ts m (.object entry.1) entry.2.1 = .ok ⟨m, .ok entry.2.2⟩ := by
  have checks := (List.all_eq_true.mp resetTsCanonicalOverlayTablesCheck_true) entry he
  simp only [decide_eq_true_eq] at checks
  obtain ⟨obj, hn, hz, hk, hv⟩ := checks
  apply resetTsOrdinaryTable_read
  · rw [hc]; exact hn
  · rw [hp]; exact hz
  · exact ho.trans obj
  · exact hk
  · exact hv

def resetTsCanonicalOverlayBindings : List (String × TargetValue) :=
  [("Object", .object 3), ("world", .object 7),
   ("contextDefinitions", .object 10), ("Number", .object 5), ("candidate", .object 23)]

def resetTsCanonicalOverlayBindingsCheck : Bool :=
  let e := balanceResetMiddleEntry .ts 0
  resetTsCanonicalOverlayBindings.all fun entry => decide (localValue e.1 e.2 entry.1 = .ok entry.2)

theorem resetTsCanonicalOverlayBindingsCheck_true : resetTsCanonicalOverlayBindingsCheck = true := by
  simp only [resetTsCanonicalOverlayBindingsCheck, balanceResetMiddleEntry,
    balanceResetCandidateEntry, balanceCanonicalResetStage, balanceCanonicalResetEntry,
    balanceResetBodyEntry, balancePythonResetBodyEntry, balanceConstructorBodyEntry,
    balanceConstructorBoundEntry, balanceConstructorArgumentEntry, balanceStoredReset,
    balanceResetLookup, balanceStoredConstructor, balanceConstructorLookup,
    balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel

/-- Fixed canonical tables discharge the TS overlay premises after any allocation
    sequence preserving these physical reads. No helper execution is assumed. -/
def resetTsCanonicalOverlay_physical {m : TargetMachine} {f : TargetFrame} {b : Int}
    (hc : m.checkerRef = 1) (hp : m.objectPrototype = 0)
    (ho : ∀ ref, ref ∈ [3, 5, 7, 10, 11] →
      objectAt m ref = objectAt (balanceCanonicalResetStage .ts 0 3).1 ref)
    (hl : ∀ entry, entry ∈ resetTsCanonicalOverlayBindings →
      localValue m f entry.1 = localValue (balanceResetMiddleEntry .ts 0).1
        (balanceResetMiddleEntry .ts 0).2 entry.1)
    (hn : localValue m f "name" = .ok (.string "balance"))
    (hv : localValue m f "value" = .ok (integerValue .ts b)) :
    ResetTsOverlayPhysical m f b := by
  have loc (entry) (he : entry ∈ resetTsCanonicalOverlayBindings) :
      localValue m f entry.1 = .ok entry.2 := by
    have check := (List.all_eq_true.mp resetTsCanonicalOverlayBindingsCheck_true) entry he
    simp only [decide_eq_true_eq] at check
    exact (hl entry he).trans check
  have tab (entry) (he : entry ∈ resetTsCanonicalOverlayTables)
      (hr : entry.1 ∈ [3, 5, 7, 10, 11]) :=
    resetTsCanonicalOverlayTable_read he hc hp (ho entry.1 hr)
  refine ⟨3, 7, 10, 10, 11, 5, hv, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact loc ("Object", .object 3) (by decide)
  · exact tab (3, "hasOwn", .builtin .objectHasOwn) (by decide) (by decide)
  · exact loc ("world", .object 7) (by decide)
  · exact tab (7, "context", .object 10) (by decide) (by decide)
  · have checks := (List.all_eq_true.mp resetTsCanonicalOverlayTablesCheck_true)
      (10, "balance", .object 11) (by decide)
    simp only [decide_eq_true_eq] at checks
    refine ⟨⟨some (.object 11), none, none, true, true, true⟩, ?_⟩
    simp only [readOwn, ho 10 (by decide), checks.1, Bind.bind, Except.bind,
      checks.2.2.2.2, Pure.pure, Except.pure]
  · exact loc ("contextDefinitions", .object 10) (by decide)
  · exact tab (10, "balance", .object 11) (by decide) (by decide)
  · exact tab (11, "type", .string "integer") (by decide) (by decide)
  · exact loc ("Number", .object 5) (by decide)
  · exact tab (5, "isSafeInteger", .builtin .jsIsSafeInteger) (by decide) (by decide)

def balanceResetTsOverlayBound (b : Int) : TargetMachine × TargetFrame :=
  let e := balanceResetTsDescriptorEntry b
  resetOverlayPairBinding .ts (resetIterableMachine .ts e.1 b) e.2 (integerValue .ts b)

def resetTsDescriptorPostBindingsCheck : Bool :=
  let e := balanceResetTsDescriptorEntry 0
  let z := balanceResetMiddleEntry .ts 0
  resetTsCanonicalOverlayBindings.all fun entry =>
    let ref := (snapshotAddress e.1 e.2 entry.1).getD 0
    decide (entry.1 ≠ "name" ∧ entry.1 ≠ "value" ∧ entry.1 ≠ "this" ∧ entry.1 ≠ "self" ∧
      snapshotAddress e.1 e.2 entry.1 = some ref ∧ ref < e.1.nextCell ∧
      localValue e.1 e.2 entry.1 = localValue z.1 z.2 entry.1)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem resetTsDescriptorPostBindingsCheck_true : resetTsDescriptorPostBindingsCheck = true := by
  simp only [resetTsDescriptorPostBindingsCheck, balanceResetTsDescriptorEntry,
    balanceResetMiddleEntry, balanceResetCandidateEntry, balanceCanonicalResetStage,
    balanceCanonicalResetEntry, balanceResetBodyEntry, balancePythonResetBodyEntry,
    balanceConstructorBodyEntry, balanceConstructorBoundEntry, balanceConstructorArgumentEntry,
    balanceStoredReset, balanceResetLookup, balanceStoredConstructor, balanceConstructorLookup,
    balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel

theorem balanceResetTsOverlayBound_environment (b : Int) {entry}
    (he : entry ∈ resetTsCanonicalOverlayBindings) :
    localValue (balanceResetTsOverlayBound b).1 (balanceResetTsOverlayBound b).2 entry.1 =
      localValue (balanceResetMiddleEntry .ts 0).1 (balanceResetMiddleEntry .ts 0).2 entry.1 := by
  have check := (List.all_eq_true.mp resetTsDescriptorPostBindingsCheck_true) entry he
  simp only [decide_eq_true_eq] at check
  obtain ⟨hn, hv, ht, hs, ha, hf, hl⟩ := check
  have fields := balanceResetTsDescriptorEntry_fields b
  let e := balanceResetTsDescriptorEntry b
  let z := balanceResetTsDescriptorEntry 0
  let ref := (snapshotAddress z.1 z.2 entry.1).getD 0
  have address : snapshotAddress e.1 e.2 entry.1 = some ref := by
    rw [snapshotAddress_fields_congr (m := e.1) (n := z.1)
      (f := e.2) (g := z.2) fields.1 fields.2.2.1]; exact ha
  have fresh : ref < e.1.nextCell := by rw [fields.2.2.2.1]; exact hf
  have iterAddress : snapshotAddress (resetIterableMachine .ts e.1 b) e.2 entry.1 = some ref := address
  have iterFresh : ref < (resetIterableMachine .ts e.1 b).nextCell := fresh
  unfold balanceResetTsOverlayBound
  rw [resetOverlayPairBinding_preserves_local ⟨hn,hv,ht,hs⟩ iterAddress iterFresh,
    resetIterableMachine_localValue, balanceResetTsDescriptorEntry_localValue]
  exact hl


theorem resetTsDescriptorCopyModel_overrides_object {m f b cell} :
    objectAt (resetTsDescriptorCopyModel m f b cell).1 (m.nextObject + 2) =
      .ok (balanceHeapObject .ts (resetTsDescriptorCopyModel m f b cell).1 b) := by
  have h3 : m.nextObject + 2 ≠ m.nextObject + 3 := Nat.ne_of_lt (Nat.lt_succ_self _)
  have h4 : m.nextObject + 2 ≠ m.nextObject + 4 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
  have h5 : m.nextObject + 2 ≠ m.nextObject + 5 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _)) (Nat.le_succ _))
  simp only [resetTsDescriptorCopyModel, resetTsDescriptorsMachine, snapshotBound,
    resetTsDescriptorPairBound, allocObject, allocCell, oneEntryMachine,
    objectAt, List.lookup, balanceHeapObject, beq_eq_false_iff_ne.mpr h3,
    beq_eq_false_iff_ne.mpr h4, beq_eq_false_iff_ne.mpr h5, Nat.add_assoc, Prod.fst, Prod.snd,
    List.map_cons, List.lookup_cons, beq_self_eq_true, if_true, if_false]




def resetTsCanonicalOldReferencesCheck : Bool :=
  let stage := (balanceCanonicalResetStage .ts 0 3).1
  [3,5,7,10,11].all fun ref =>
    decide (ref < stage.nextObject ∧ ref ≠ (balancePreparation .ts).1.nextObject)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem resetTsCanonicalOldReferencesCheck_true : resetTsCanonicalOldReferencesCheck = true := by
  simp only [resetTsCanonicalOldReferencesCheck,
    balanceCanonicalResetStage, balanceCanonicalResetEntry, balanceResetBodyEntry,
    balancePythonResetBodyEntry, balanceConstructorBodyEntry, balanceConstructorBoundEntry,
    balanceConstructorArgumentEntry, balanceStoredReset, balanceResetLookup, balanceStoredConstructor,
    balanceConstructorLookup, balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel

theorem balanceResetTsOverlayBound_old_object (b : Int) {ref}
    (hf : ref < (balanceCanonicalResetStage .ts 0 3).1.nextObject)
    (hs : ref ≠ (balancePreparation .ts).1.nextObject) :
    objectAt (balanceResetTsOverlayBound b).1 ref =
      objectAt (balanceCanonicalResetStage .ts 0 3).1 ref := by
  have foot := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  have freshStage : ref < (balanceCanonicalResetStage .ts b 3).1.nextObject := by
    rw [foot.2.2.2.2.1]; exact hf
  have freshMiddle : ref < (balanceResetMiddleEntry .ts b).1.nextObject :=
    Nat.lt_of_lt_of_le freshStage (Nat.le_succ _)
  have freshPost : ref < (balanceResetTsDescriptorEntry b).1.nextObject :=
    Nat.lt_of_lt_of_le freshMiddle (Nat.le_add_right _ 6)
  unfold balanceResetTsOverlayBound
  rw [resetOverlayPairBinding_objectAt, resetIterableMachine_objectAt_other freshPost]
  unfold balanceResetTsDescriptorEntry
  rw [resetTsDescriptorCopyModel_objectAt_old freshMiddle,
    balanceResetMiddleEntry_model,
    resetCandidateMiddleModel_objectAt_other (Nat.ne_of_lt freshStage)]
  exact balanceCanonicalResetStage_objectAt .ts b 3 (by decide) ref hs


def resetTsDescriptorPostFixedCheck : Prop :=
  let e := balanceResetTsDescriptorEntry 0
  let middle := balanceResetMiddleEntry .ts 0
  e.1.checkerRef = 1 ∧ e.1.objectPrototype = 0 ∧
    (balanceCanonicalResetStage .ts 0 3).1.nextObject = 23 ∧ middle.1.nextObject = 24 ∧
    e.1.nextObject = 30 ∧ localValue e.1 e.2 "overrides" = .ok (.object 26)

instance : Decidable resetTsDescriptorPostFixedCheck := by
  unfold resetTsDescriptorPostFixedCheck; infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem resetTsDescriptorPostFixedCheck_true : resetTsDescriptorPostFixedCheck := by
  simp only [resetTsDescriptorPostFixedCheck, balanceResetTsDescriptorEntry,
    balanceResetMiddleEntry, balanceResetCandidateEntry, balanceCanonicalResetStage,
    balanceCanonicalResetEntry, balanceResetBodyEntry, balancePythonResetBodyEntry,
    balanceConstructorBodyEntry, balanceConstructorBoundEntry, balanceConstructorArgumentEntry,
    balanceStoredReset, balanceResetLookup, balanceStoredConstructor, balanceConstructorLookup,
    balanceConstructorName, balancePreparation_ts_eq]
  decide +kernel

def balanceResetTsOverlayBound_physical (b : Int) :
    ResetTsOverlayPhysical (balanceResetTsOverlayBound b).1 (balanceResetTsOverlayBound b).2 b := by
  have fields := balanceResetTsDescriptorEntry_fields b
  have fixed := resetTsDescriptorPostFixedCheck_true
  have checker : (balanceResetTsDescriptorEntry b).1.checkerRef = 1 :=
    fields.2.2.2.2.2.2.trans fixed.1
  have proto : (balanceResetTsDescriptorEntry b).1.objectPrototype = 0 :=
    fields.2.2.2.2.2.1.trans fixed.2.1
  apply resetTsCanonicalOverlay_physical
    (m := (balanceResetTsOverlayBound b).1) (f := (balanceResetTsOverlayBound b).2)
    checker proto
  · intro ref hr
    have h := (List.all_eq_true.mp resetTsCanonicalOldReferencesCheck_true) ref hr
    simp only [decide_eq_true_eq] at h
    exact balanceResetTsOverlayBound_old_object b h.1 h.2
  · intro entry he; exact balanceResetTsOverlayBound_environment b he
  · exact (resetOverlayPairBinding_reads .ts _ _ _).1
  · exact (resetOverlayPairBinding_reads .ts _ _ _).2

theorem balanceResetTsDescriptorEntry_old_object (b : Int) {ref}
    (hf : ref < (balanceCanonicalResetStage .ts 0 3).1.nextObject)
    (hs : ref ≠ (balancePreparation .ts).1.nextObject) :
    objectAt (balanceResetTsDescriptorEntry b).1 ref =
      objectAt (balanceCanonicalResetStage .ts 0 3).1 ref := by
  have foot := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  have freshStage : ref < (balanceCanonicalResetStage .ts b 3).1.nextObject := by
    rw [foot.2.2.2.2.1]; exact hf
  have freshMiddle : ref < (balanceResetMiddleEntry .ts b).1.nextObject :=
    Nat.lt_of_lt_of_le freshStage (Nat.le_succ _)
  unfold balanceResetTsDescriptorEntry
  rw [resetTsDescriptorCopyModel_objectAt_old freshMiddle,
    balanceResetMiddleEntry_model,
    resetCandidateMiddleModel_objectAt_other (Nat.ne_of_lt freshStage)]
  exact balanceCanonicalResetStage_objectAt .ts b 3 (by decide) ref hs

theorem balanceResetTsDescriptorEntry_entries (b : Int) :
    readPropertyValue .ts (balanceResetTsDescriptorEntry b).1 (.object 3) "entries" =
      .ok ⟨(balanceResetTsDescriptorEntry b).1, .ok (.builtin .objectEntries)⟩ := by
  have fields := balanceResetTsDescriptorEntry_fields b
  have fixed := resetTsDescriptorPostFixedCheck_true
  have old := (List.all_eq_true.mp resetTsCanonicalOldReferencesCheck_true) 3 (by decide)
  simp only [decide_eq_true_eq] at old
  exact resetTsCanonicalOverlayTable_read (entry := (3,"entries",.builtin .objectEntries))
    (by decide) (fields.2.2.2.2.2.2.trans fixed.1)
    (fields.2.2.2.2.2.1.trans fixed.2.1)
    (balanceResetTsDescriptorEntry_old_object b old.1 old.2)


theorem balanceResetTsDescriptorEntry_environment (b : Int) {entry}
    (he : entry ∈ resetTsCanonicalOverlayBindings) :
    localValue (balanceResetTsDescriptorEntry b).1 (balanceResetTsDescriptorEntry b).2 entry.1 =
      .ok entry.2 := by
  have post := (List.all_eq_true.mp resetTsDescriptorPostBindingsCheck_true) entry he
  have base := (List.all_eq_true.mp resetTsCanonicalOverlayBindingsCheck_true) entry he
  simp only [decide_eq_true_eq] at post base
  rw [balanceResetTsDescriptorEntry_localValue]
  exact post.2.2.2.2.2.2.trans base

theorem balanceResetTsDescriptorEntry_overrides (b : Int) :
    localValue (balanceResetTsDescriptorEntry b).1 (balanceResetTsDescriptorEntry b).2 "overrides" =
      .ok (.object 26) ∧
    objectAt (balanceResetTsDescriptorEntry b).1 26 =
      .ok (balanceHeapObject .ts (balanceResetTsDescriptorEntry b).1 b) := by
  have fixed := resetTsDescriptorPostFixedCheck_true
  have fields := balanceResetTsCopyInitial_fields b
  have n : (balanceResetMiddleEntry .ts b).1.nextObject = 24 := fields.2.2.2.2.1.trans fixed.2.2.2.1
  constructor
  · rw [balanceResetTsDescriptorEntry_localValue]; exact fixed.2.2.2.2.2
  · have obj := resetTsDescriptorCopyModel_overrides_object
      (m := (balanceResetMiddleEntry .ts b).1) (f := (balanceResetMiddleEntry .ts b).2)
      (b := b) (cell := 26)
    change objectAt (balanceResetTsDescriptorEntry b).1
      ((balanceResetMiddleEntry .ts b).1.nextObject + 2) = _ at obj
    rw [n] at obj
    exact obj

theorem resetTsDescriptorCopyModel_prototype (m : TargetMachine) (f : TargetFrame) (b : Int) (cell : CellRef) :
    (resetTsDescriptorCopyModel m f b cell).1.objectPrototype = m.objectPrototype := by
  simp only [resetTsDescriptorCopyModel, resetTsDescriptorsMachine, snapshotBound,
    resetTsDescriptorPairBound, allocObject, allocCell, oneEntryMachine, Prod.fst, Prod.snd]

theorem resetTsOverlayBinding_prototype (m : TargetMachine) (f : TargetFrame) (b : Int) :
    (resetOverlayPairBinding .ts (resetIterableMachine .ts m b) f (integerValue .ts b)).1.objectPrototype =
      m.objectPrototype := by
  simp only [resetOverlayPairBinding, resetIterableMachine, oneEntryMachine, forPairBound,
    allocObject, allocCell, Prod.fst, Prod.snd, beq_self_eq_true, if_true]

theorem balanceHeapObject_prototype_congr {lang : TargetLang} {m n : TargetMachine} (b : Int)
    (hp : m.objectPrototype = n.objectPrototype) :
    balanceHeapObject lang m b = balanceHeapObject lang n b := by
  simp only [balanceHeapObject, hp]

theorem balanceResetTsOverlayBound_candidate (b : Int) :
    localValue (balanceResetTsOverlayBound b).1 (balanceResetTsOverlayBound b).2 "candidate" =
      .ok (.object 23) ∧
    objectAt (balanceResetTsOverlayBound b).1 23 =
      .ok (balanceHeapObject .ts (balanceResetTsOverlayBound b).1 100) := by
  have fixed := resetTsDescriptorPostFixedCheck_true
  have fields := balanceResetTsDescriptorEntry_fields b
  have middle := balanceResetTsCopyInitial_fields b
  have foot := balanceCanonicalResetStage_footprint .ts b 3 (by decide)
  have np : (balanceResetTsDescriptorEntry b).1.nextObject = 30 := fields.2.2.2.2.1.trans fixed.2.2.2.2.1
  have nm : (balanceResetMiddleEntry .ts b).1.nextObject = 24 := middle.2.2.2.2.1.trans fixed.2.2.2.1
  have candidate := balanceResetMiddleEntry_candidate_object .ts b
  rw [foot.2.2.2.2.1, fixed.2.2.1] at candidate
  constructor
  · have env := balanceResetTsOverlayBound_environment b
      (entry := ("candidate", .object 23)) (by decide)
    have base := (List.all_eq_true.mp resetTsCanonicalOverlayBindingsCheck_true)
      ("candidate", .object 23) (by decide)
    simp only [decide_eq_true_eq] at base
    exact env.trans base
  · have hf : 23 < (balanceResetTsDescriptorEntry b).1.nextObject := by rw [np]; decide
    have hm : 23 < (balanceResetMiddleEntry .ts b).1.nextObject := by rw [nm]; decide
    have old : objectAt (balanceResetTsOverlayBound b).1 23 =
        objectAt (balanceResetMiddleEntry .ts b).1 23 := by
      unfold balanceResetTsOverlayBound
      rw [resetOverlayPairBinding_objectAt, resetIterableMachine_objectAt_other hf]
      unfold balanceResetTsDescriptorEntry
      exact resetTsDescriptorCopyModel_objectAt_old
        (m := (balanceResetMiddleEntry .ts b).1) (f := (balanceResetMiddleEntry .ts b).2)
        (b := b) (cell := 26) hm
    have p1 : (balanceResetTsOverlayBound b).1.objectPrototype =
        (balanceResetTsDescriptorEntry b).1.objectPrototype :=
      resetTsOverlayBinding_prototype (balanceResetTsDescriptorEntry b).1
        (balanceResetTsDescriptorEntry b).2 b
    have p2 : (balanceResetTsDescriptorEntry b).1.objectPrototype =
        (balanceResetMiddleEntry .ts b).1.objectPrototype :=
      resetTsDescriptorCopyModel_prototype (balanceResetMiddleEntry .ts b).1
        (balanceResetMiddleEntry .ts b).2 b 26
    have heap := balanceHeapObject_prototype_congr (lang := .ts)
      (m := (balanceResetMiddleEntry .ts b).1) (n := (balanceResetTsOverlayBound b).1) 100
      (p1.trans p2).symm
    exact old.trans (candidate.trans (congrArg Except.ok heap))


theorem balanceReset_ts_canonical_overlay_loop_safe (b : Int)
    (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetTsDescriptorEntry b
    execStmt (k + 12) (balanceProgram .ts) e.1 e.2 (balanceResetOverlayLoop .ts) =
      .ok ⟨balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b, e.2, .normal⟩ := by
  exact balanceReset_ts_seed_loop_safe (balanceResetTsDescriptorEntry_entries b)
    (balanceResetTsDescriptorEntry_environment b (entry := ("Object", .object 3)) (by decide))
    (balanceResetTsDescriptorEntry_overrides b).1 (balanceResetTsDescriptorEntry_overrides b).2
    (balanceResetTsOverlayBound_physical b)
    (balanceResetTsOverlayBound_candidate b).1 (balanceResetTsOverlayBound_candidate b).2 hb



/-- The real bounds method call allocates its receiver-bound closure and its
    values parameter before entering the source body. This boundary is uniform
    in the candidate payload; it does not assume successful helper execution. -/
def resetBoundsBodyEntry (m : TargetMachine) (method : TargetClosure) (candidate : ObjRef) :
    TargetMachine × TargetFrame :=
  let active := { method with receiver := some m.checkerRef }
  let bound := (allocClosure m active).1
  ((allocCell bound (.object candidate) true).1,
    { closureFrame active with locals := [("values", bound.nextCell)] })

theorem resetBoundsCall_eq_body {lang m f methodRef method candidate error k}
    (hr : localValue m f (if lang == .ts then "this" else "self") =
      .ok (.object m.checkerRef))
    (hv : localValue m f "candidate" = .ok (.object candidate))
    (hf : readCheckerField m (if lang == .ts then "checkBounds" else "_bounds") = .error error)
    (hm : m.classMethods.lookup (if lang == .ts then "checkBounds" else "_bounds") = some methodRef)
    (hc : closureAt m methodRef = .ok method)
    (hp : method.params = [⟨"values", none⟩]) :
    evalExpr (k + 3) (balanceProgram lang) m f (resetBoundsCall lang) = (do
      let body ← execStmt (k + 2) (balanceProgram lang)
        (resetBoundsBodyEntry m method candidate).1
        (resetBoundsBodyEntry m method candidate).2 method.body
      closureResult lang body) := by
  let active := { method with receiver := some m.checkerRef }
  let bound := (allocClosure m active).1
  have he : DepthDerivesExpr (balanceProgram lang) m f
      (.property (resetReceiver lang) (if lang == .ts then "checkBounds" else "_bounds"))
      ⟨bound, .ok (.closure m.nextClosure)⟩ 1 := by
    apply DepthDerivesExpr.property (.localRead hr)
    rw [balanceProgram_lang]
    exact readCheckerMethod_bound hf hm hc
  have value : localValue bound f "candidate" = .ok (.object candidate) := hv
  have ha : DepthDerivesArgs (balanceProgram lang) bound f
      (.sequence (.local "candidate") .empty) ⟨bound, .ok [.object candidate]⟩ 1 :=
    .cons (.localRead value) .empty
  have stored : closureAt bound m.nextClosure = .ok active := by
    simp [bound, closureAt, allocClosure, List.lookup]
  have params : DepthBindsProvided (balanceProgram lang) bound (closureFrame active)
      active.params active.pythonDefaults [.object candidate]
      (resetBoundsBodyEntry m method candidate).1
      (resetBoundsBodyEntry m method candidate).2 1 := by
    change DepthBindsProvided (balanceProgram lang) bound (closureFrame active)
      method.params active.pythonDefaults _ _ _ 1
    rw [hp]
    exact .cons (by simp) .empty
  have h := evalStoredCall_eq he ha stored params (k := k + 2)
    (Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le k)))
    (Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le k)))
    (Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le k)))
  simpa only [resetBoundsCall, balanceProgram_lang] using h

/-- Both generated invariant calls supply Ready and the actual candidate.
    Evaluating their argument list neither allocates nor inspects the balance. -/
theorem resetInvariantCall_args_execute {lang m f candidate k}
    (hv : localValue m f "candidate" = .ok (.object candidate))
    (hs : lang = .python → localValue m f "_INITIAL" = .ok (.string "Ready")) :
    evalArgValues (k + 3) (balanceProgram lang) m f
      (.sequence (if lang == .ts then .string "Ready" else .local "_INITIAL")
        (.sequence (.local "candidate") .empty)) =
      .ok ⟨m, .ok [.string "Ready", .object candidate]⟩ := by
  have state : DepthDerivesExpr (balanceProgram lang) m f
      (if lang == .ts then .string "Ready" else .local "_INITIAL")
      ⟨m, .ok (.string "Ready")⟩ 0 := by
    cases lang with
    | ts => exact .string "Ready"
    | python => exact .localRead (hs rfl)
  exact evalArgs_adequate (.cons state (.cons (.localRead hv) .empty))
    (Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))))

/-- The invariant call performs real receiver dispatch and then invokes the
    fresh closure with its two supplied arguments. Default binding and the
    emitted evaluator body remain inside callClosure, without a success premise. -/
theorem resetInvariantCall_eq_closure {lang m f methodRef method candidate error k}
    (hr : localValue m f (if lang == .ts then "this" else "self") =
      .ok (.object m.checkerRef))
    (hv : localValue m f "candidate" = .ok (.object candidate))
    (hs : lang = .python → localValue m f "_INITIAL" = .ok (.string "Ready"))
    (hf : readCheckerField m (if lang == .ts then "checkInvariants" else "_invariant") = .error error)
    (hm : m.classMethods.lookup (if lang == .ts then "checkInvariants" else "_invariant") = some methodRef)
    (hc : closureAt m methodRef = .ok method) :
    let bound := (allocClosure m { method with receiver := some m.checkerRef }).1
    evalExpr (k + 4) (balanceProgram lang) m f (resetInvariantCall lang) =
      callClosure (k + 3) (balanceProgram lang) bound m.nextClosure
        [.string "Ready", .object candidate] := by
  dsimp only
  let bound := (allocClosure m { method with receiver := some m.checkerRef }).1
  have callee : DepthDerivesExpr (balanceProgram lang) m f
      (.property (resetReceiver lang) (if lang == .ts then "checkInvariants" else "_invariant"))
      ⟨bound, .ok (.closure m.nextClosure)⟩ 1 := by
    apply DepthDerivesExpr.property (.localRead hr)
    rw [balanceProgram_lang]
    exact readCheckerMethod_bound hf hm hc
  have value : localValue bound f "candidate" = .ok (.object candidate) := hv
  have state : lang = .python → localValue bound f "_INITIAL" = .ok (.string "Ready") := hs
  unfold resetInvariantCall
  rw [evalExpr, evalExpr_adequate callee
    (Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le (k + 1))))]
  simp only [Bind.bind, Except.bind]
  rw [resetInvariantCall_args_execute value state]

/-- The source bounds comparisons reject neither endpoint nor any interior
    bounded integer. These are actual interpreter binary operations. -/
theorem resetBounds_reject_comparisons {lang : TargetLang} (m : TargetMachine) {b : Int}
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    binaryValue lang m .lt (integerValue lang b) (integerValue lang 0) =
      .ok (.ok (.bool false)) ∧
    binaryValue lang m .gt (integerValue lang b) (integerValue lang 9007199254740991) =
      .ok (.ok (.bool false)) := by
  have hmin : ¬ b < 0 := Int.not_lt.mpr hb.1
  have hmax : ¬ (9007199254740991 : Int) < b := Int.not_lt.mpr hb.2
  constructor
  · cases lang <;>
      change Except.ok (Except.ok (TargetValue.bool (decide (b < 0)))) = _ <;>
      simp only [hmin, decide_false]
  · cases lang <;>
      change Except.ok (Except.ok (TargetValue.bool (decide ((9007199254740991 : Int) < b)))) = _ <;>
      simp only [hmax, decide_false]

/-- The comparison nodes occurring in both emitted bounds methods execute
    constructively for every bounded value once their physical reads are known. -/
theorem resetBounds_comparison_execute {lang m f b minimum maximum k}
    (hv : localValue m f "value" = .ok (integerValue lang b))
    (hmin : evalExpr (k + 2) (balanceProgram lang) m f minimum =
      .ok ⟨m, .ok (integerValue lang 0)⟩)
    (hmax : evalExpr (k + 2) (balanceProgram lang) m f maximum =
      .ok ⟨m, .ok (integerValue lang 9007199254740991)⟩)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) :
    evalExpr (k + 3) (balanceProgram lang) m f (.binary .lt (.local "value") minimum) =
      .ok ⟨m, .ok (.bool false)⟩ ∧
    evalExpr (k + 3) (balanceProgram lang) m f (.binary .gt (.local "value") maximum) =
      .ok ⟨m, .ok (.bool false)⟩ := by
  have comparisons := resetBounds_reject_comparisons (lang := lang) m hb
  constructor
  · rw [evalExpr, evalExpr_adequate (.localRead hv) (Nat.zero_lt_succ _)]
    simp only [Bind.bind, Except.bind]
    rw [hmin]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang, comparisons.1]
  · rw [evalExpr, evalExpr_adequate (.localRead hv) (Nat.zero_lt_succ _)]
    simp only [Bind.bind, Except.bind]
    rw [hmax]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, balanceProgram_lang, comparisons.2]

/-- Source node numbers differ by one because TS has a separate entries loop. -/
def resetValidationIndex (lang : TargetLang) : Nat := if lang == .ts then 4 else 3

def resetValidationResult (lang : TargetLang) : TargetValue :=
  if lang == .ts then .undefined else .null

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem balanceReset_validation_shapes (lang : TargetLang) :
    balanceResetMiddleStmt lang (resetValidationIndex lang) =
      snapshotBindStmt lang "invalid" (resetBoundsCall lang) ∧
    balanceResetMiddleStmt lang (resetValidationIndex lang + 1) =
      .ifThenElse (.local "invalid")
        (ifYesStmt (balanceResetMiddleStmt lang (resetValidationIndex lang + 1))) .empty ∧
    balanceResetMiddleStmt lang (resetValidationIndex lang + 2) =
      snapshotBindStmt lang "violated" (resetInvariantCall lang) ∧
    balanceResetMiddleStmt lang (resetValidationIndex lang + 3) =
      .ifThenElse (.local "violated")
        (ifYesStmt (balanceResetMiddleStmt lang (resetValidationIndex lang + 3))) .empty := by
  cases lang <;>
    unfold balanceResetMiddleStmt balanceResetProtected balanceResetSnapshots
      balanceStoredReset balanceResetLookup balancePreparation resetValidationIndex
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

/-- Binding a successful helper result preserves all allocations performed by
    that helper, then skips the real source rejection branch. -/
theorem balanceReset_validation_bind_skip {lang m final f k} (invariant : Bool)
    (he : evalExpr (k + 2) (balanceProgram lang) m f
      (if invariant then resetInvariantCall lang else resetBoundsCall lang) =
      .ok ⟨final, .ok (resetValidationResult lang)⟩)
    (hn : lang = .python → snapshotAddress m f (if invariant then "violated" else "invalid") = none) :
    let name := if invariant then "violated" else "invalid"
    let bound := snapshotBound lang final f name (resetValidationResult lang)
    let index := resetValidationIndex lang + (if invariant then 2 else 0)
    execStmt (k + 3) (balanceProgram lang) m f (balanceResetMiddleStmt lang index) =
      .ok ⟨bound.1, bound.2, .normal⟩ ∧
    execStmt (k + 3) (balanceProgram lang) bound.1 bound.2
      (balanceResetMiddleStmt lang (index + 1)) = .ok ⟨bound.1, bound.2, .normal⟩ := by
  dsimp only
  have shapes := balanceReset_validation_shapes lang
  have bindShape : balanceResetMiddleStmt lang
      (resetValidationIndex lang + (if invariant then 2 else 0)) =
      snapshotBindStmt lang (if invariant then "violated" else "invalid")
        (if invariant then resetInvariantCall lang else resetBoundsCall lang) := by
    cases invariant
    · simpa using shapes.1
    · exact shapes.2.2.1
  have skipShape : balanceResetMiddleStmt lang
      (resetValidationIndex lang + (if invariant then 2 else 0) + 1) =
      .ifThenElse (.local (if invariant then "violated" else "invalid"))
        (ifYesStmt (balanceResetMiddleStmt lang
          (resetValidationIndex lang + (if invariant then 2 else 0) + 1))) .empty := by
    cases invariant
    · simpa using shapes.2.1
    · simpa only [Nat.add_assoc] using shapes.2.2.2
  constructor
  · rw [bindShape]
    exact execSnapshotBind he hn
  · rw [skipShape]
    have read : localValue
        (snapshotBound lang final f (if invariant then "violated" else "invalid") (resetValidationResult lang)).1
        (snapshotBound lang final f (if invariant then "violated" else "invalid") (resetValidationResult lang)).2
        (if invariant then "violated" else "invalid") = .ok (resetValidationResult lang) := by
      cases invariant <;> cases lang <;>
        simp [snapshotBound, localValue, readCell, allocCell, List.lookup]
    exact execStmt_adequate (.ifFalse (.localRead read)
      (by cases lang <;> rfl) .empty)
      (Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le (k + 1))))

/-- Actual canonical Python statement-2 execution feeds a candidate whose
    descriptor satisfies both primitive validation predicates for every bounded
    balance. Successful execution of the two validation bodies is still open. -/
theorem balanceReset_python_canonical_overlay_bounded (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .python b
    let final := balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b
    let ff := (balanceResetPythonOverlayBound b).2
    execStmt (k + 25) (balanceProgram .python) e.1 e.2 (balanceResetMiddleStmt .python 2) =
      .ok ⟨final, ff, .normal⟩ ∧
    resetCandidateBalanceRead final ff = .ok (some (integerValue .python b)) ∧
    binaryValue .python final .lt (integerValue .python b) (integerValue .python 0) =
      .ok (.ok (.bool false)) ∧
    binaryValue .python final .gt (integerValue .python b) (integerValue .python 9007199254740991) =
      .ok (.ok (.bool false)) := by
  have candidate := balanceReset_python_canonical_post_candidate b
  have range := balanceOverlayUpdated_candidate_range candidate.1 candidate.2 hb
  have comparisons := resetBounds_reject_comparisons
    (lang := .python) (balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b) hb
  exact ⟨(balanceReset_python_canonical_overlay_safe b (balance_natAbs hb) k).2,
    range.1, comparisons⟩


/-- The TS loop restores its caller frame; non-binder reads agree with the
    temporary iteration frame at the same physical machine. -/
theorem resetOverlayPairBinding_old_frame_read {lang m f value name}
    (hn : name ≠ "name") (hv : name ≠ "value") :
    localValue (resetOverlayPairBinding lang m f value).1 f name =
      localValue (resetOverlayPairBinding lang m f value).1
        (resetOverlayPairBinding lang m f value).2 name := by
  simp only [localValue, resetOverlayPairBinding, forPairBound, allocCell,
    Prod.fst, Prod.snd, List.lookup_cons,
    beq_eq_false_iff_ne.mpr hn, beq_eq_false_iff_ne.mpr hv, if_false]

theorem balanceReset_ts_canonical_overlay_candidate_read (b : Int) :
    resetCandidateBalanceRead
      (balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b)
      (balanceResetTsDescriptorEntry b).2 = .ok (some (integerValue .ts b)) := by
  have candidateLocal : localValue (balanceResetTsOverlayBound b).1
      (balanceResetTsDescriptorEntry b).2 "candidate" = .ok (.object 23) :=
    (resetOverlayPairBinding_old_frame_read (lang := .ts)
      (m := resetIterableMachine .ts (balanceResetTsDescriptorEntry b).1 b)
      (f := (balanceResetTsDescriptorEntry b).2) (value := integerValue .ts b)
      (name := "candidate") (by decide) (by decide)).trans
      (balanceResetTsOverlayBound_candidate b).1
  exact balanceOverlayUpdated_candidate_read candidateLocal (balanceResetTsOverlayBound_candidate b).2

/-- The actual TS supplied-seed statement and the following entries loop form
    the complete canonical overlay prefix. Validation is a later source node. -/
theorem balanceReset_ts_canonical_overlay_safe (b : Int)
    (hb : b.natAbs ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    execStmt (k + 27) (balanceProgram .ts) e.1 e.2
      (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts)) =
      .ok ⟨balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b,
        (balanceResetTsDescriptorEntry b).2, .normal⟩ := by
  dsimp only
  rw [execSequence_of_normal (balanceReset_ts_canonical_descriptor_copy_safe b k)]
  exact balanceReset_ts_canonical_overlay_loop_safe b hb (k + 14)

/-- Complete canonical TS overlay execution and physical validation predicates
    for every nonnegative bounded balance; helper-body execution is separate. -/
theorem balanceReset_ts_canonical_overlay_bounded (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) :
    let e := balanceResetMiddleEntry .ts b
    let final := balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b
    let ff := (balanceResetTsDescriptorEntry b).2
    execStmt (k + 27) (balanceProgram .ts) e.1 e.2
      (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts)) =
      .ok ⟨final, ff, .normal⟩ ∧
    resetCandidateBalanceRead final ff = .ok (some (integerValue .ts b)) ∧
    binaryValue .ts final .lt (integerValue .ts b) (integerValue .ts 0) =
      .ok (.ok (.bool false)) ∧
    binaryValue .ts final .gt (integerValue .ts b) (integerValue .ts 9007199254740991) =
      .ok (.ok (.bool false)) := by
  exact ⟨balanceReset_ts_canonical_overlay_safe b (balance_natAbs hb) k,
    balanceReset_ts_canonical_overlay_candidate_read b,
    resetBounds_reject_comparisons (lang := .ts) _ hb⟩

/-- Join the complete canonical TS overlay to the actual bounds-result binding
    and rejection guard. Whole helper execution remains an explicit premise;
    its final machine, including all allocations, is preserved. -/
theorem balanceReset_ts_canonical_overlay_bounds_bind (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) {helperFinal}
    (he : evalExpr (k + 26) (balanceProgram .ts)
      (balanceOverlayUpdated .ts (balanceResetTsOverlayBound b).1 23 b)
      (balanceResetTsDescriptorEntry b).2 (resetBoundsCall .ts) =
      .ok ⟨helperFinal, .ok .undefined⟩) :
    let e := balanceResetMiddleEntry .ts b
    let bound := snapshotBound .ts helperFinal (balanceResetTsDescriptorEntry b).2 "invalid" .undefined
    execStmt (k + 28) (balanceProgram .ts) e.1 e.2
      (.sequence (.sequence (balanceResetMiddleStmt .ts 2) (balanceResetOverlayLoop .ts))
        (balanceResetMiddleStmt .ts 4)) = .ok ⟨bound.1, bound.2, .normal⟩ ∧
    execStmt (k + 27) (balanceProgram .ts) bound.1 bound.2
      (balanceResetMiddleStmt .ts 5) = .ok ⟨bound.1, bound.2, .normal⟩ := by
  have bindings := balanceReset_validation_bind_skip (lang := .ts) (k := k + 24)
    false he (by intro h; cases h)
  dsimp only
  constructor
  · rw [execSequence_of_normal (balanceReset_ts_canonical_overlay_safe b (balance_natAbs hb) k)]
    exact bindings.1
  · exact bindings.2

/-- Python's canonical overlay occupies one source node; the same bounds-call
    premise joins it to the actual following binding and rejection guard. -/
theorem balanceReset_python_canonical_overlay_bounds_bind (b : Int)
    (hb : 0 ≤ b ∧ b ≤ 9007199254740991) (k : Nat) {helperFinal}
    (he : evalExpr (k + 24) (balanceProgram .python)
      (balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b)
      (balanceResetPythonOverlayBound b).2 (resetBoundsCall .python) =
      .ok ⟨helperFinal, .ok .null⟩)
    (hn : snapshotAddress
      (balanceOverlayUpdated .python (balanceResetPythonOverlayAfterHelper b) 79 b)
      (balanceResetPythonOverlayBound b).2 "invalid" = none) :
    let e := balanceResetMiddleEntry .python b
    let bound := snapshotBound .python helperFinal (balanceResetPythonOverlayBound b).2 "invalid" .null
    execStmt (k + 26) (balanceProgram .python) e.1 e.2
      (.sequence (balanceResetMiddleStmt .python 2) (balanceResetMiddleStmt .python 3)) =
      .ok ⟨bound.1, bound.2, .normal⟩ ∧
    execStmt (k + 25) (balanceProgram .python) bound.1 bound.2
      (balanceResetMiddleStmt .python 4) = .ok ⟨bound.1, bound.2, .normal⟩ := by
  have bindings := balanceReset_validation_bind_skip (lang := .python) (k := k + 22)
    false he (by intro _; exact hn)
  dsimp only
  constructor
  · rw [execSequence_of_normal (balanceReset_python_canonical_overlay_safe b (balance_natAbs hb) k).2]
    exact bindings.1
  · exact bindings.2

end Batch14CanonicalTsOverlay

end CanonicalResetComposition

end Harmonia.Applications.Kadmos.Generated
