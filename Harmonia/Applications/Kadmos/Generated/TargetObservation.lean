import Harmonia.Applications.Kadmos.Generated.TargetSemantics
import Harmonia.Applications.Kadmos.Generated.BalanceModel

namespace Harmonia.Applications.Kadmos.Generated

structure Normalized where
  allowed : Bool
  currentState : String
  context : List (String × Int)
  directive : Option String
  deriving DecidableEq, Repr

structure CheckerData where
  state : String
  context : List (String × Int)
  history : List TargetValue
  undo : Option ObjRef
  busy : Bool
  deriving DecidableEq, Repr

private def ownValue (m : TargetMachine) (ref : ObjRef) (key : String) :
    Except TargetError TargetValue := do
  match ← readOwn m ref key with
  | some descriptor =>
      match descriptor.value with
      | some value => return value
      | none => throw .badDescriptor
  | none => throw .badDescriptor

/-- Checked enumerable own-data read for verdict fields. A value combined with
    an accessor is malformed even when the referenced closure is live. -/
private def ownDataValue (m : TargetMachine) (ref : ObjRef) (key : String) :
    Except TargetError TargetValue := do
  match ← readOwn m ref key with
  | none => throw .badDescriptor
  | some descriptor =>
      if !descriptor.enumerable || descriptor.get.isSome || descriptor.set.isSome then
        throw .badDescriptor
      match descriptor.value with
      | some value => pure value
      | none => throw .badDescriptor

private def stringValue : TargetValue → Except TargetError String
  | .string text => .ok text
  | _ => .error .invalidTag

private def boolValue : TargetValue → Except TargetError Bool
  | .bool value => .ok value
  | _ => .error .invalidTag

private def optionalString : TargetValue → Except TargetError (Option String)
  | .null => .ok none
  | .string text => .ok (some text)
  | _ => .error .invalidTag

private def expectedNumberTag (lang : TargetLang) : NumberTag :=
  if lang == .ts then .jsNumber else .pyInt

private def numericContext (lang : TargetLang) (m : TargetMachine)
    (ref : ObjRef) : Except TargetError (List (String × Int)) := do
  let obj ← objectAt m ref
  let kind := if lang == .ts then ObjectKind.jsOrdinary else .pythonDict
  if obj.kind != kind && !(lang == .ts && obj.kind == .jsNullPrototype) then
    throw .invalidTag
  let mut values : List (String × Int) := []
  for (key, descriptor) in obj.own do
    if !descriptor.enumerable then throw .badDescriptor
    match descriptor.value with
    | some (.number tag n) =>
        if tag != expectedNumberTag lang then throw .invalidTag
        values := values ++ [(key, n)]
    | _ => throw .invalidTag
  return values

def logicalChecker (lang : TargetLang) (m : TargetMachine) :
    Except TargetError CheckerData := do
  let context ← numericContext lang m m.checker.context
  let history ← objectAt m m.checker.history
  let expectedHistory := if lang == .ts then ObjectKind.jsArray else .pythonList
  if history.kind != expectedHistory then throw .invalidTag
  return ⟨m.checker.state, context, history.items, m.checker.undo, m.checker.busy⟩

def logicalBalance (lang : TargetLang) (m : TargetMachine) :
    Except TargetError Int := do
  let checker ← logicalChecker lang m
  match checker.context with
  | [("balance", value)] => return value
  | _ => throw .invalidTag

def targetProjection (lang : TargetLang) (out : TargetOutcome) :
    Except TargetError Normalized := do
  let verdictRef ← match out.verdict with
    | .object ref => .ok ref
    | _ => .error .invalidTag
  let allowed ← boolValue (← ownValue out.machine verdictRef "allowed")
  let state ← stringValue (← ownValue out.machine verdictRef "currentState")
  let contextRef ← match ← ownValue out.machine verdictRef "context" with
    | .object ref => .ok ref
    | _ => .error .invalidTag
  let context ← numericContext lang out.machine contextRef
  let directive ← optionalString (← ownValue out.machine verdictRef "directiveAllowed")
  return ⟨allowed, state, context, directive⟩

def balanceSourceProjection (result : Harmonia.Applications.Kadmos.Result 1 1) :
    Normalized :=
  ⟨result.observation.verdict == .accepted, "Ready",
    [("balance", result.state.context 0)], result.observation.directive⟩

/-- Dereferenced first-call record contents. Heap identity and freeze metadata
    remain separate execution/HeapWF obligations. -/
structure BalanceRecord where
  step : Nat
  state : String
  action : String
  amount : TargetValue
  proposedDirectivePresent : Bool
  deriving DecidableEq, Repr

structure BalanceSaved where
  state : String
  balance : Int
  history : List BalanceRecord
  deriving DecidableEq, Repr

structure BalanceView where
  state : String
  balance : Int
  history : List BalanceRecord
  undo : Option BalanceSaved
  constructorSeed : Int
  busy : Bool
  deriving DecidableEq, Repr

def expectedRecord : TargetLang → Int → BalanceRecord
  | .ts, n => ⟨1, "Ready", "DEBIT", .number .jsNumber n, false⟩
  | .python, n => ⟨1, "Ready", "DEBIT", .number .pyFloat n, false⟩

private def objectRef : TargetValue → Except TargetError ObjRef
  | .object ref => .ok ref
  | _ => .error .invalidTag

/-- Exact own enumerable data keys, independent of property order. Equal
    cardinality plus presence of each distinct expected key rejects duplicates. -/
private def exactDataKeys (obj : HeapObject) (keys : List String) : Bool :=
  obj.own.length == keys.length &&
    keys.all (fun key => obj.own.any (fun entry => entry.1 == key)) &&
    obj.own.all (fun entry => entry.2.enumerable && entry.2.value.isSome &&
      entry.2.get.isNone && entry.2.set.isNone) &&
    obj.items.isEmpty && obj.setMembers.isEmpty && !obj.proxy

private def recordKind (lang : TargetLang) (obj : HeapObject) : Bool :=
  if lang == .ts then obj.kind == .jsOrdinary || obj.kind == .jsNullPrototype
  else obj.kind == .pythonDict

/-- Strict one-key numeric context decoder, also used for seed and savepoint.
    It rejects accessors, extra fields, wrong tags and noncanonical containers. -/
def balanceContextValue (lang : TargetLang) (m : TargetMachine) (ref : ObjRef) :
    Except TargetError Int := do
  let obj ← objectAt m ref
  if !recordKind lang obj then throw .invalidTag
  if !exactDataKeys obj ["balance"] then throw .badDescriptor
  match ← ownValue m ref "balance" with
  | .number tag b =>
      if tag != expectedNumberTag lang then throw .invalidTag
      return b
  | _ => throw .invalidTag

/-- Structural decoder lemma for a physical one-key data object. -/
theorem balanceContextValue_canonical {lang m ref b proto}
    (h : objectAt m ref = .ok
      ⟨(if lang == .ts then .jsOrdinary else .pythonDict), proto,
        [("balance", ⟨some (.number (if lang == .ts then .jsNumber else .pyInt) b),
          none, none, true, true, true⟩)], [], [], false, false⟩) :
    balanceContextValue lang m ref = .ok b := by
  cases lang <;> simp [balanceContextValue, recordKind, exactDataKeys,
    ownValue, readOwn, h, expectedNumberTag,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

private def decodeBalanceRecord (lang : TargetLang) (m : TargetMachine)
    (value : TargetValue) : Except TargetError BalanceRecord := do
  let ref ← objectRef value
  let obj ← objectAt m ref
  if !recordKind lang obj then throw .invalidTag
  let proposed := (obj.own.lookup "proposedDirective").isSome
  let keys := ["step", "state", "action", "eventPayload"] ++
    (if proposed then ["proposedDirective"] else [])
  if !exactDataKeys obj keys then throw .badDescriptor
  let step ← match ← ownValue m ref "step" with
    | .number tag n =>
        if tag != expectedNumberTag lang || n < 0 then throw .invalidTag
        pure n.toNat
    | _ => throw .invalidTag
  let state ← stringValue (← ownValue m ref "state")
  let action ← stringValue (← ownValue m ref "action")
  if proposed then
    let _ ← optionalString (← ownValue m ref "proposedDirective")
    pure ()
  let payloadRef ← objectRef (← ownValue m ref "eventPayload")
  let payload ← objectAt m payloadRef
  if !recordKind lang payload then throw .invalidTag
  if !exactDataKeys payload ["amount"] then throw .badDescriptor
  let amount ← ownValue m payloadRef "amount"
  match amount with
  | .number tag _ =>
      if tag != (if lang == .ts then .jsNumber else .pyFloat) then throw .invalidTag
  | _ => throw .invalidTag
  return ⟨step, state, action, amount, proposed⟩

def decodeBalanceHistory (lang : TargetLang) (m : TargetMachine)
    (ref : ObjRef) : Except TargetError (List BalanceRecord) := do
  let obj ← objectAt m ref
  if obj.kind != (if lang == .ts then .jsArray else .pythonList) then throw .invalidTag
  if !obj.own.isEmpty || !obj.setMembers.isEmpty || obj.proxy then throw .badDescriptor
  obj.items.mapM (decodeBalanceRecord lang m)

private def decodeBalanceSaved (lang : TargetLang) (m : TargetMachine)
    (ref : ObjRef) : Except TargetError BalanceSaved := do
  let obj ← objectAt m ref
  let (state, context, history) ←
    if lang == .ts then do
      if !recordKind lang obj then throw .invalidTag
      if !exactDataKeys obj ["state", "context", "history"] then throw .badDescriptor
      let state ← stringValue (← ownValue m ref "state")
      let context ← objectRef (← ownValue m ref "context")
      let history ← objectRef (← ownValue m ref "history")
      pure (state, context, history)
    else do
      if obj.kind != .pythonTuple then throw .invalidTag
      if !obj.own.isEmpty || !obj.setMembers.isEmpty || obj.proxy then throw .badDescriptor
      match obj.items with
      | [.string state, .object context, .object history] => pure (state, context, history)
      | _ => throw .invalidTag
  let balance ← balanceContextValue lang m context
  let records ← decodeBalanceHistory lang m history
  return ⟨state, balance, records⟩

/-- Checked content projection, not a fabricated target state. Both language
    savepoint layouts are dereferenced; missing/malformed content is an error.
    Execution proofs must additionally establish HeapWF before comparing views. -/
def balanceView (lang : TargetLang) (m : TargetMachine) :
    Except TargetError BalanceView := do
  let seedRef ← match m.checker.constructorSeed with
    | some ref => pure ref
    | none => throw .invalidTag
  let balance ← balanceContextValue lang m m.checker.context
  let history ← decodeBalanceHistory lang m m.checker.history
  let undo ← match m.checker.undo with
    | none => pure none
    | some ref => some <$> decodeBalanceSaved lang m ref
  let seed ← balanceContextValue lang m seedRef
  return ⟨m.checker.state, balance, history, undo, seed, m.checker.busy⟩

/-- Decode the actual verdict's violation object. Acceptance must have no
    violation; rejected verdicts must carry a string code. -/
def targetViolationCode (out : TargetOutcome) : Except TargetError (Option String) := do
  let ref ← objectRef out.verdict
  let allowed ← boolValue (← ownDataValue out.machine ref "allowed")
  match ← readOwn out.machine ref "violation" with
  | none =>
      if !allowed then throw .badDescriptor
      pure none
  | some descriptor =>
      if allowed || descriptor.get.isSome || descriptor.set.isSome ||
          !descriptor.enumerable then throw .badDescriptor
      let violationRef ← match descriptor.value with
        | some value => objectRef value
        | none => throw .badDescriptor
      return some (← stringValue (← ownDataValue out.machine violationRef "code"))

/-- Empty physical history container has an empty content view. -/
theorem decodeBalanceHistory_empty {lang m ref proto}
    (h : objectAt m ref = .ok
      ⟨(if lang == .ts then .jsArray else .pythonList), proto,
        [], [], [], false, false⟩) :
    decodeBalanceHistory lang m ref = .ok [] := by
  cases lang <;> simp [decodeBalanceHistory, h,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Compose successful content reads for a freshly reset checker. Physical
    constructor success and well-formedness are separate proof obligations. -/
theorem balanceView_constructed {lang m b seed}
    (hcontext : balanceContextValue lang m m.checker.context = .ok b)
    (hhistory : decodeBalanceHistory lang m m.checker.history = .ok [])
    (hseedRef : m.checker.constructorSeed = some seed)
    (hseed : balanceContextValue lang m seed = .ok b)
    (hundo : m.checker.undo = none) (hstate : m.checker.state = "Ready")
    (hidle : m.checker.busy = false) :
    balanceView lang m = .ok ⟨"Ready", b, [], none, b, false⟩ := by
  simp [balanceView, hcontext, hhistory, hseedRef, hseed, hundo, hstate, hidle,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

end Harmonia.Applications.Kadmos.Generated
