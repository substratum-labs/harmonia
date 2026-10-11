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

end Harmonia.Applications.Kadmos.Generated
