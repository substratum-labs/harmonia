import Harmonia.Applications.Kadmos.Generated.TargetMachine
import Harmonia.Applications.Kadmos.Generated.TargetJSON
import Harmonia.Applications.Kadmos.Generated.TargetRegex

set_option maxHeartbeats 5000000

namespace Harmonia.Applications.Kadmos.Generated

structure ExprOutcome where
  machine : TargetMachine
  result : Except TargetValue TargetValue
  deriving Repr

structure ArgsOutcome where
  machine : TargetMachine
  result : Except TargetValue (List TargetValue)
  deriving Repr

structure StmtOutcome where
  machine : TargetMachine
  frame : TargetFrame
  control : ControlResult
  deriving Repr

structure DefaultsOutcome where
  machine : TargetMachine
  result : Except TargetValue (List (Option TargetValue))
  deriving Repr

structure BindOutcome where
  machine : TargetMachine
  frame : TargetFrame
  result : Except TargetValue Unit
  deriving Repr

/-- Exact source catch selection, shared by the declarative control rules.
    This tests only exception tags; it assumes no generated helper result. -/
def controlCaught (catchType : Option String) : ControlResult → Bool
  | .raised errorValue =>
      catchType == some "any" || catchType == some "Exception" ||
        (match errorValue, catchType with
          | .exception className _, some wanted => className == wanted
          | _, _ => false)
  | _ => false

/-- Lexical catch binding allocates one fresh cell when the source names an
    exception binder, then records the active exception for a bare rethrow. -/
def bindCatchFrame (m : TargetMachine) (f : TargetFrame) (binder : Option String)
    (errorValue : TargetValue) : TargetMachine × TargetFrame :=
  let (updated, localFrame) := match binder with
    | none => (m, f)
    | some name =>
        let (updated, ref) := allocCell m errorValue true
        (updated, { f with locals := (name, ref) :: f.locals })
  (updated, { localFrame with control := .raised errorValue })

private def done (m : TargetMachine) (value : TargetValue) : ExprOutcome :=
  ⟨m, .ok value⟩

private def exception (m : TargetMachine) (className message : String) : ExprOutcome :=
  ⟨m, .error (.exception className message)⟩

private def number (lang : TargetLang) (n : Int) : TargetValue :=
  .number (if lang == .ts then .jsNumber else .pyInt) n

private def hostDescriptor (value : TargetValue) : Descriptor :=
  ⟨some value, none, none, true, true, true⟩

private def hostObject (m : TargetMachine) (entries : List (String × TargetValue)) :
    TargetMachine × ObjRef :=
  let own := entries.map fun entry => (entry.1, hostDescriptor entry.2)
  allocObject m ⟨.jsOrdinary, some m.objectPrototype, own, [], [], false, false⟩

private def hostGlobal (m : TargetMachine) (name : String) (value : TargetValue) :
    TargetMachine :=
  let (withCell, ref) := allocCell m value false
  { withCell with globals := (name, ref) :: withCell.globals }

private def importedModule (m : TargetMachine) (name : String) :
    Except TargetError (TargetMachine × TargetValue) := do
  let entries ← match name with
    | "json" => .ok [("loads", TargetValue.builtin .jsonLoads)]
    | "types" => .ok [("MappingProxyType", TargetValue.builtin .mappingProxy)]
    | "math" => .ok [("isfinite", TargetValue.builtin .isFinite)]
    | "re" => .ok [("compile", TargetValue.builtin .regexCompile),
        ("S", TargetValue.number .pyInt 1)]
    | "copy" => .ok [("deepcopy", TargetValue.builtin .deepCopy)]
    | _ => .error .unsupportedExpression
  let (updated, ref) := hostObject m entries
  .ok (updated, .object ref)

private def importedBinding (m : TargetMachine) (moduleName name : String) :
    Except TargetError (TargetMachine × Option TargetValue) :=
  if moduleName == "__future__" && name == "annotations" then .ok (m, none)
  else if moduleName == "typing" && name == "Any" then
    .ok (m, some (.builtin .pyObject))
  else if moduleName == "ports" && name == "IWorldChecker" then
    .ok (m, some (.classConstructor "IWorldChecker"))
  else if moduleName == "node:util" && name == "types" then do
    let (updated, ref) := hostObject m [("isProxy", .builtin .nodeIsProxy)]
    .ok (updated, some (.object ref))
  else .error .unsupportedExpression

def initialHostMachine (lang : TargetLang) : TargetMachine :=
  let m := TargetMachine.empty
  if lang == .ts then
    let (m, jsonRef) := hostObject m [("parse", .builtin .jsonParse)]
    let m := hostGlobal m "JSON" (.object jsonRef)
    let (m, objectRef) := hostObject m
      [("prototype", .object m.objectPrototype), ("entries", .builtin .objectEntries),
       ("hasOwn", .builtin .objectHasOwn), ("create", .builtin .objectCreate),
       ("getPrototypeOf", .builtin .objectGetPrototypeOf),
       ("getOwnPropertyNames", .builtin .objectGetOwnNames),
       ("getOwnPropertyDescriptor", .builtin .objectOwnDescriptor),
       ("getOwnPropertyDescriptors", .builtin .objectOwnDescriptors),
       ("defineProperty", .builtin .objectDefineProperty),
       ("freeze", .builtin .freeze), ("isFrozen", .builtin .isFrozen)]
    let m := hostGlobal m "Object" (.object objectRef)
    let (m, arrayRef) := hostObject m [("isArray", .builtin .arrayIsArray)]
    let m := hostGlobal m "Array" (.object arrayRef)
    let (m, numberRef) := hostObject m
      [("isFinite", .builtin .isFinite), ("isSafeInteger", .builtin .jsIsSafeInteger)]
    let withCallable := { m with callableObjects := (numberRef, .number) :: m.callableObjects }
    let m := hostGlobal withCallable "Number" (.object numberRef)
    let m := hostGlobal m "Set" (.builtin .setNew)
    let m := hostGlobal m "Error" (.builtin .newError)
    hostGlobal m "structuredClone" (.builtin .structuredClone)
  else
    let m := hostGlobal m "type" (.builtin .type)
    let m := hostGlobal m "dict" (.builtin .dict)
    let m := hostGlobal m "list" (.builtin .list)
    let m := hostGlobal m "tuple" (.builtin .tuple)
    let m := hostGlobal m "set" (.builtin .set)
    let m := hostGlobal m "float" (.builtin .float)
    let m := hostGlobal m "int" (.builtin .int)
    let m := hostGlobal m "str" (.builtin .strType)
    let m := hostGlobal m "bool" (.builtin .boolType)
    let m := hostGlobal m "len" (.builtin .length)
    let m := hostGlobal m "next" (.builtin .next)
    let m := hostGlobal m "isinstance" (.builtin .isinstance)
    let m := hostGlobal m "id" (.builtin .objectIdentity)
    let m := hostGlobal m "object" (.builtin .pyObject)
    let m := hostGlobal m "abs" (.builtin .abs)
    let m := hostGlobal m "any" (.builtin .any)
    let m := hostGlobal m "ValueError" (.builtin .newValueError)
    let m := hostGlobal m "RuntimeError" (.builtin .newRuntimeError)
    hostGlobal m "OverflowError" (.builtin .newOverflowError)

private def numeric : TargetValue → Option (NumberTag × Int)
  | .number tag n => some (tag, n)
  | _ => none

private def resultTag (lang : TargetLang) (left right : NumberTag) : NumberTag :=
  if lang == .ts then .jsNumber
  else if left == .pyFloat || right == .pyFloat then .pyFloat
  else .pyInt

private def safeIntermediate (n : Int) : Bool :=
  n.natAbs ≤ 9007199254740991

/-- Basic tagged binary operations, shared with the independent execution rules. -/
def binaryValue (lang : TargetLang) (m : TargetMachine) (op : BinaryOp)
    (left right : TargetValue) : Except TargetError (Except TargetValue TargetValue) :=
  let bool (v : Bool) : Except TargetError (Except TargetValue TargetValue) := .ok (.ok (.bool v))
  match op with
  | .strictEq => bool (left == right)
  | .strictNe => bool (left != right)
  | .eq =>
      match numeric left, numeric right with
      | some (_, l), some (_, r) => bool (l == r)
      | _, _ => bool (left == right)
  | .ne =>
      match numeric left, numeric right with
      | some (_, l), some (_, r) => bool (l != r)
      | _, _ => bool (left != right)
  | .isIdentity => bool (left == right)
  | .isNotIdentity => bool (left != right)
  | .inObject | .notInObject => do
      let present ← match right with
        | .object ref => do
            let obj ← objectAt m ref
            match obj.kind with
            | .pythonTuple | .pythonList | .jsArray => .ok (obj.items.contains left)
            | .pythonSet | .jsSet => .ok (obj.setMembers.contains left)
            | .pythonDict | .mappingProxy | .jsOrdinary | .jsNullPrototype =>
                match left with
                | .string key => .ok ((obj.own.lookup key).isSome)
                | _ => .ok false
            | _ => .error .unsupportedExpression
        | .string haystack =>
            match left with
            | .string needle => .ok (needle.isEmpty || (haystack.splitSourceOn needle).length > 1)
            | _ => .ok false
        | _ => .error .unsupportedExpression
      bool (if op == .inObject then present else !present)
  | _ =>
      match numeric left, numeric right with
      | some (ltag, l), some (rtag, r) =>
          let tag := resultTag lang ltag rtag
          match op with
          | .add =>
              if safeIntermediate (l + r) then .ok (.ok (.number tag (l + r)))
              else .error .outsideNumericDomain
          | .sub =>
              if safeIntermediate (l - r) then .ok (.ok (.number tag (l - r)))
              else .error .outsideNumericDomain
          | .mul =>
              if safeIntermediate (l * r) then .ok (.ok (.number tag (l * r)))
              else .error .outsideNumericDomain
          | .div =>
              if r == 0 || l % r != 0 then .error .outsideNumericDomain
              else .ok (.ok (.number tag (l / r)))
          | .lt => bool (l < r)
          | .le => bool (l ≤ r)
          | .gt => bool (l > r)
          | .ge => bool (l ≥ r)
          | _ => .ok (.error (.exception "TypeError" "unsupported operands"))
      | _, _ => .ok (.error (.exception "TypeError" "expected numeric operands"))

theorem binary_sub_js_safe (m : TargetMachine) (b n : Int)
    (h : (b - n).natAbs ≤ 9007199254740991) :
    binaryValue .ts m .sub (.number .jsNumber b) (.number .jsNumber n) =
      .ok (.ok (.number .jsNumber (b - n))) := by
  simp [binaryValue, numeric, resultTag, safeIntermediate, h]

theorem binary_sub_py_float_safe (m : TargetMachine) (b n : Int)
    (h : (b - n).natAbs ≤ 9007199254740991) :
    binaryValue .python m .sub (.number .pyFloat b) (.number .pyFloat n) =
      .ok (.ok (.number .pyFloat (b - n))) := by
  simp [binaryValue, numeric, resultTag, safeIntermediate, h]

private def localValue (m : TargetMachine) (frame : TargetFrame) (name : String) :
    Except TargetError TargetValue :=
  if name == "this" || name == "self" then
    match frame.receiver with
    | some ref => .ok (.object ref)
    | none => .error (.unboundLocal name)
  else match frame.locals.lookup name with
  | some ref => readCell m ref
  | none =>
      match frame.captures.lookup name with
      | some ref => readCell m ref
      | none =>
          match m.globals.lookup name with
          | some ref => readCell m ref
          | none => .error (.unboundLocal name)

private def readPropertyValue (lang : TargetLang) (m : TargetMachine)
    (receiver : TargetValue) (key : String) : Except TargetError ExprOutcome := do
  match receiver with
  | .object ref =>
      if ref == m.checkerRef then do
        match readCheckerField m key with
        | .ok value => return done m value
        | .error _ =>
            match m.classMethods.lookup key with
            | some methodRef =>
                let method ← closureAt m methodRef
                let (updated, boundRef) := allocClosure m
                  { method with receiver := some m.checkerRef }
                return done updated (.closure boundRef)
            | none => pure ()
            match ← readOwn m ref key with
            | some descriptor =>
                match descriptor.value with
                | some value => return done m value
                | none => throw .badDescriptor
            | none => throw (.unboundLocal key)
      let obj ← objectAt m ref
      if ref == m.objectPrototype && key == "toString" then
        return done m (.builtin .objectPrototypeToStringCall)
      if obj.kind == .jsArray && key == "length" then
        return done m (.number .jsNumber obj.items.length)
      if obj.kind == .jsSet && key == "size" then
        return done m (.number .jsNumber obj.setMembers.length)
      if obj.kind == .jsSet || obj.kind == .pythonSet then
        if key == "has" then return done m (.boundBuiltin .setHas receiver)
        if key == "add" then return done m (.boundBuiltin .setAdd receiver)
      if obj.kind == .jsArray then
        let method ← match key with
          | "push" => .ok .arrayPush | "map" => .ok .arrayMap
          | "find" => .ok .arrayFind | "some" => .ok .arraySome
          | "join" => .ok .arrayJoin | _ => .error .unsupportedExpression
        return done m (.boundBuiltin method receiver)
      if obj.kind == .pythonDict || obj.kind == .mappingProxy then
        if key == "get" then return done m (.boundBuiltin .dictGet receiver)
        if key == "items" then return done m (.boundBuiltin .dictItems receiver)
      if obj.kind == .pythonList && key == "append" then
        return done m (.boundBuiltin .arrayPush receiver)
      if obj.kind == .regexPattern then
        let method ← match key with
          | "match" => .ok BuiltinId.regexMatchAt
          | "fullmatch" => .ok .regexFullmatch
          | "test" => .ok .regexTest
          | "exec" => .ok .regexExec
          | _ => .error .unsupportedExpression
        return done m (.boundBuiltin method receiver)
      match ← readOwn m ref key with
      | some descriptor =>
          match descriptor.value with
          | some value => return done m value
          | none => throw .badDescriptor
      | none =>
          if lang == .ts then return done m .undefined
          else return exception m "AttributeError" key
  | .undefined | .null => return exception m "TypeError" "property of nullish value"
  | .string value =>
      if lang == .ts && key == "length" then
        return done m (.number .jsNumber value.toList.length)
      let method ← match key with
        | "replace" => .ok .stringReplace
        | "startsWith" | "startswith" => .ok .stringStartsWith
        | "slice" => .ok .stringSlice
        | "match" => .ok .stringMatch
        | "isspace" => .ok .stringIsSpace
        | "isdigit" => .ok .stringIsDigit
        | _ => .error .unsupportedExpression
      return done m (.boundBuiltin method receiver)
  | .regexMatch _ =>
      if key == "end" then return done m (.boundBuiltin .regexMatchEnd receiver)
      if key == "group" then return done m (.boundBuiltin .regexGroup receiver)
      throw .unsupportedExpression
  | .number .pyFloat _ =>
      if key == "is_integer" then return done m (.boundBuiltin .isInteger receiver)
      throw .unsupportedExpression
  | .builtin .dict =>
      if key == "items" then return done m (.builtin .dictItems)
      throw .unsupportedExpression
  | .builtin .objectPrototypeToStringCall =>
      if key == "call" then return done m (.builtin .objectPrototypeToStringCall)
      throw .unsupportedExpression
  | .exception _ message =>
      if key == "message" then return done m (.string message)
      return exception m "TypeError" "exception property"
  | _ => return exception m "TypeError" "property of primitive value"

private def normalizeIndex (lang : TargetLang) (length : Nat) (n : Int) : Option Nat :=
  let actual := if lang == .python && n < 0 then Int.ofNat length + n else n
  if 0 ≤ actual && actual < Int.ofNat length then some actual.toNat else none

private def normalizeSliceBound (length : Nat) (n : Int) : Nat :=
  let actual := if n < 0 then Int.ofNat length + n else n
  if actual < 0 then 0
  else if actual > Int.ofNat length then length
  else actual.toNat

private def makeEntries (lang : TargetLang) (m : TargetMachine)
    (own : List (String × Descriptor)) : Except TargetError (TargetMachine × List TargetValue) := do
  let mut machine := m
  let mut pairs : List TargetValue := []
  for (key, descriptor) in own do
    if descriptor.enumerable then
      match descriptor.value with
      | some value =>
          let kind := if lang == .ts then ObjectKind.jsArray else .pythonTuple
          let proto := if lang == .ts then some machine.objectPrototype else none
          let (updated, ref) := allocObject machine
            ⟨kind, proto, [], [.string key, value], [], false, false⟩
          machine := updated
          pairs := pairs ++ [.object ref]
      | none => throw .badDescriptor
  return (machine, pairs)

private def regexSource (m : TargetMachine) (ref : ObjRef) :
    Except TargetError String := do
  let pattern ← objectAt m ref
  if pattern.kind != .regexPattern then throw .invalidTag
  match pattern.own.lookup "source" with
  | some descriptor =>
      match descriptor.value with
      | some (.string source) => return source
      | _ => throw .badDescriptor
  | none => throw .badDescriptor

private def cloneValue (fuel : Nat) (m : TargetMachine) (value : TargetValue) :
    Except TargetError (TargetMachine × TargetValue) :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 => do
      match value with
      | .object sourceRef =>
          let source ← objectAt m sourceRef
          if source.proxy || source.kind == .mappingProxy then throw .badDescriptor
          let withoutOwn := { source with own := [] }
          let withoutItems := { withoutOwn with items := [] }
          let withoutMembers := { withoutItems with setMembers := [] }
          let unfrozen := { withoutMembers with frozen := false }
          let blank := { unfrozen with proxy := false }
          let (withBlank, destRef) := allocObject m blank
          let mut current := withBlank
          let mut own : List (String × Descriptor) := []
          for (key, descriptor) in source.own do
            match descriptor.value with
            | some fieldValue =>
                let (updated, copied) ← cloneValue fuel current fieldValue
                current := updated
                own := own ++ [(key, { descriptor with value := some copied })]
            | none => throw .badDescriptor
          let mut items : List TargetValue := []
          for item in source.items do
            let (updated, copied) ← cloneValue fuel current item
            current := updated
            items := items ++ [copied]
          let mut members : List TargetValue := []
          for member in source.setMembers do
            let (updated, copied) ← cloneValue fuel current member
            current := updated
            members := members ++ [copied]
          let withOwn := { blank with own := own }
          let withItems := { withOwn with items := items }
          let finalized ← replaceObject current destRef
            { withItems with setMembers := members }
          return (finalized, .object destRef)
      | _ => return (m, value)

mutual

private def jsonToValue (fuel : Nat) (lang : TargetLang) (m : TargetMachine)
    (value : TargetJSON) : Except TargetError (TargetMachine × TargetValue) :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match value with
    | .null => .ok (m, .null)
    | .bool b => .ok (m, .bool b)
    | .integer n => .ok (m, number lang n)
    | .string s => .ok (m, .string s)
    | .array items => do
        let (updated, values) ← jsonArrayValues fuel lang m items
        let kind := if lang == .ts then ObjectKind.jsArray else .pythonList
        let proto := if lang == .ts then some updated.objectPrototype else none
        let (final, ref) := allocObject updated ⟨kind, proto, [], values, [], false, false⟩
        return (final, .object ref)
    | .object fields => do
        let kind := if lang == .ts then ObjectKind.jsOrdinary else .pythonDict
        let proto := if lang == .ts then some m.objectPrototype else none
        let (withObject, ref) := allocObject m ⟨kind, proto, [], [], [], false, false⟩
        let final ← jsonObjectFields fuel lang withObject ref fields
        return (final, .object ref)
    | _ => .error .unsupportedExpression

private def jsonArrayValues (fuel : Nat) (lang : TargetLang) (m : TargetMachine)
    (items : TargetJSON) : Except TargetError (TargetMachine × List TargetValue) :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match items with
    | .empty => .ok (m, [])
    | .valueItem value rest => do
        let (updated, head) ← jsonToValue fuel lang m value
        let (final, tail) ← jsonArrayValues fuel lang updated rest
        return (final, head :: tail)
    | _ => .error .unsupportedExpression

private def jsonObjectFields (fuel : Nat) (lang : TargetLang)
    (m : TargetMachine) (destination : ObjRef) (fields : TargetJSON) :
    Except TargetError TargetMachine :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match fields with
    | .empty => .ok m
    | .keyVal key value rest => do
        let (updated, v) ← jsonToValue fuel lang m value
        let withField ← writeOwn updated destination key v
        jsonObjectFields fuel lang withField destination rest
    | _ => .error .unsupportedExpression

end

private def hostCall (lang : TargetLang) (m : TargetMachine) (id : BuiltinId)
    (receiver : Option TargetValue) (args : List TargetValue) :
    Except TargetError ExprOutcome := do
  match id, receiver, args with
  | .type, none, [value] =>
      let typeId ← match value with
        | .null => .ok BuiltinId.noneType
        | .bool _ => .ok .boolType
        | .string _ => .ok .strType
        | .number .pyInt _ => .ok .int
        | .number .pyFloat _ => .ok .float
        | .object ref => do
            let obj ← objectAt m ref
            match obj.kind with
            | .pythonDict => .ok .dict
            | .pythonList => .ok .list
            | .pythonTuple => .ok .tuple
            | .pythonSet => .ok .set
            | .mappingProxy => .ok .mappingProxy
            | _ => .ok .pyObject
        | _ => .ok .pyObject
      return done m (.builtin typeId)
  | .jsonParse, none, [.string source] =>
      match parseTargetJSON source with
      | .ok json =>
          let (updated, value) ← jsonToValue (source.toList.length * 4 + 1) .ts m json
          return done updated value
      | .error _ => throw .unsupportedExpression
  | .jsonLoads, none, [.string source] =>
      match parseTargetJSON source with
      | .ok json =>
          let (updated, value) ← jsonToValue (source.toList.length * 4 + 1) .python m json
          return done updated value
      | .error _ => throw .unsupportedExpression
  | .length, none, [.string s] => return done m (number lang s.toList.length)
  | .length, none, [.object ref] =>
      let obj ← objectAt m ref
      let size := match obj.kind with
        | .pythonDict | .mappingProxy => obj.own.length
        | .pythonList | .pythonTuple | .jsArray => obj.items.length
        | .pythonSet | .jsSet => obj.setMembers.length
        | _ => 0
      return done m (number lang size)
  | .length, _, _ => return exception m "TypeError" "len arity or type"
  | .float, none, [.number _ n] =>
      if !safeIntermediate n then throw .outsideNumericDomain
      return done m (.number .pyFloat n)
  | .float, none, [.string source] =>
      if source.isEmpty || !source.toList.all Char.isDigit then throw .outsideNumericDomain
      match source.toNat? with
      | some n =>
          if n > 9007199254740991 then throw .outsideNumericDomain
          return done m (.number .pyFloat n)
      | none => throw .outsideNumericDomain
  | .number, none, [.string source] =>
      if source.isEmpty || !source.toList.all Char.isDigit then throw .outsideNumericDomain
      match source.toNat? with
      | some n =>
          if n > 9007199254740991 then throw .outsideNumericDomain
          return done m (.number .jsNumber n)
      | none => throw .outsideNumericDomain
  | .int, none, [.number _ n] =>
      if !safeIntermediate n then throw .outsideNumericDomain
      return done m (.number .pyInt n)
  | .isInteger, some (.number .pyFloat _), [] => return done m (.bool true)
  | .isInteger, some (.number .pyInt _), [] => return done m (.bool true)
  | .isFinite, none, [.number _ _] => return done m (.bool true)
  | .jsIsSafeInteger, none, [.number .jsNumber n] =>
      return done m (.bool (safeIntermediate n))
  | .jsIsSafeInteger, none, [_] => return done m (.bool false)
  | .abs, none, [.number tag n] => return done m (.number tag n.natAbs)
  | .objectHasOwn, none, [.object ref, .string key] =>
      let own ← readOwn m ref key
      return done m (.bool own.isSome)
  | .objectCreate, none, [.null] =>
      let (updated, ref) := allocObject m
        ⟨.jsNullPrototype, none, [], [], [], false, false⟩
      return done updated (.object ref)
  | .objectGetOwnNames, none, [.object ref] =>
      let obj ← objectAt m ref
      let names := obj.own.map (fun entry => TargetValue.string entry.1)
      let (updated, namesRef) := allocObject m
        ⟨.jsArray, some m.objectPrototype, [], names, [], false, false⟩
      return done updated (.object namesRef)
  | .freeze, none, [.object ref] =>
      let obj ← objectAt m ref
      let own := obj.own.map (fun entry =>
        (entry.1, { entry.2 with writable := false, configurable := false }))
      let updated ← replaceObject m ref { obj with own := own, frozen := true }
      return done updated (.object ref)
  | .isFrozen, none, [.object ref] =>
      let obj ← objectAt m ref
      return done m (.bool obj.frozen)
  | .isinstance, none, [value, .object typeRef] =>
      let types ← objectAt m typeRef
      if types.kind != .pythonTuple then
        return exception m "TypeError" "isinstance types"
      let matchesType (typeValue : TargetValue) : Bool :=
        match value, typeValue with
        | .object ref, .builtin typeId =>
            match (objectAt m ref).toOption with
            | none => false
            | some obj =>
                (typeId == .list && obj.kind == .pythonList) ||
                (typeId == .tuple && obj.kind == .pythonTuple) ||
                (typeId == .set && obj.kind == .pythonSet) ||
                (typeId == .dict && obj.kind == .pythonDict)
        | .exception className _, .builtin .newRuntimeError =>
            className == "RuntimeError"
        | _, _ => false
      return done m (.bool (types.items.any matchesType))
  | .isinstance, none, [value, .builtin typeId] =>
      let matchesType := match value, typeId with
        | .exception className _, .newRuntimeError => className == "RuntimeError"
        | .exception className _, .newValueError => className == "ValueError"
        | _, _ => false
      return done m (.bool matchesType)
  | .arrayIsArray, none, [.object ref] =>
      let obj ← objectAt m ref
      return done m (.bool (obj.kind == .jsArray))
  | .arrayIsArray, none, [_] => return done m (.bool false)
  | .nodeIsProxy, none, [.object ref] =>
      let obj ← objectAt m ref
      return done m (.bool obj.proxy)
  | .nodeIsProxy, none, [_] => return done m (.bool false)
  | .objectGetPrototypeOf, none, [.object ref] =>
      let obj ← objectAt m ref
      return done m (obj.prototype.map TargetValue.object |>.getD .null)
  | .objectOwnDescriptors, none, [.object ref] =>
      let obj ← objectAt m ref
      let (withResult, resultRef) := allocObject m
        ⟨.jsOrdinary, some m.objectPrototype, [], [], [], false, false⟩
      let mut current := withResult
      for (key, descriptor) in obj.own do
        let (withEntry, entryRef) := allocObject current
          ⟨.jsOrdinary, some current.objectPrototype,
            [("value", hostDescriptor (descriptor.value.getD .undefined)),
             ("get", hostDescriptor (descriptor.get.map TargetValue.closure |>.getD .undefined)),
             ("set", hostDescriptor (descriptor.set.map TargetValue.closure |>.getD .undefined)),
             ("enumerable", hostDescriptor (.bool descriptor.enumerable)),
             ("writable", hostDescriptor (.bool descriptor.writable)),
             ("configurable", hostDescriptor (.bool descriptor.configurable))],
            [], [], false, false⟩
        current ← writeOwn withEntry resultRef key (.object entryRef)
      return done current (.object resultRef)
  | .objectOwnDescriptor, none, [.object ref, .string key] =>
      match ← readOwn m ref key with
      | none => return done m .undefined
      | some descriptor =>
          let (updated, descriptorRef) := allocObject m
            ⟨.jsOrdinary, some m.objectPrototype,
              [("value", hostDescriptor (descriptor.value.getD .undefined)),
               ("get", hostDescriptor (descriptor.get.map TargetValue.closure |>.getD .undefined)),
               ("set", hostDescriptor (descriptor.set.map TargetValue.closure |>.getD .undefined)),
               ("enumerable", hostDescriptor (.bool descriptor.enumerable)),
               ("writable", hostDescriptor (.bool descriptor.writable)),
               ("configurable", hostDescriptor (.bool descriptor.configurable))],
              [], [], false, false⟩
          return done updated (.object descriptorRef)
  | .objectDefineProperty, none, [.object targetRef, .string key, .object descriptorRef] =>
      let target ← objectAt m targetRef
      if target.frozen then return exception m "TypeError" "frozen target"
      let valueDescriptor ← readOwn m descriptorRef "value"
      let value ← match valueDescriptor with
        | some entry => match entry.value with
            | some v => .ok v
            | none => .error .badDescriptor
        | none => .error .badDescriptor
      let flag (name : String) : Except TargetError Bool := do
        match ← readOwn m descriptorRef name with
        | some entry =>
            match entry.value with
            | some (.bool b) => return b
            | _ => throw .badDescriptor
        | none => return false
      let newDescriptor : Descriptor :=
        ⟨some value, none, none, ← flag "enumerable", ← flag "writable",
          ← flag "configurable"⟩
      let own := if target.own.any (fun entry => entry.1 == key) then
        target.own.map (fun entry =>
          if entry.1 == key then (key, newDescriptor) else entry)
        else target.own ++ [(key, newDescriptor)]
      let updated ← replaceObject m targetRef { target with own := own }
      return done updated (.object targetRef)
  | .objectEntries, none, [.object ref] =>
      let obj ← objectAt m ref
      let (updated, pairs) ← makeEntries .ts m obj.own
      let (final, arrayRef) := allocObject updated
        ⟨.jsArray, some updated.objectPrototype, [], pairs, [], false, false⟩
      return done final (.object arrayRef)
  | .dictItems, some (.object ref), [] =>
      let obj ← objectAt m ref
      let (updated, pairs) ← makeEntries .python m obj.own
      let (final, listRef) := allocObject updated
        ⟨.pythonList, none, [], pairs, [], false, false⟩
      return done final (.object listRef)
  | .dictItems, none, [.object ref] =>
      let obj ← objectAt m ref
      let (updated, pairs) ← makeEntries .python m obj.own
      let (final, listRef) := allocObject updated
        ⟨.pythonList, none, [], pairs, [], false, false⟩
      return done final (.object listRef)
  | .dictGet, some (.object ref), [.string key] =>
      match ← readOwn m ref key with
      | some descriptor =>
          match descriptor.value with
          | some value => return done m value
          | none => throw .badDescriptor
      | none => return done m .null
  | .dictGet, some (.object ref), [.string key, fallback] =>
      match ← readOwn m ref key with
      | some descriptor =>
          match descriptor.value with
          | some value => return done m value
          | none => throw .badDescriptor
      | none => return done m fallback
  | .mappingProxy, none, [.object ref] =>
      let obj ← objectAt m ref
      if obj.kind != .pythonDict then
        return exception m "TypeError" "MappingProxyType expects dict"
      let (updated, proxyRef) := allocObject m
        ⟨.mappingProxy, some ref, obj.own, [], [], true, false⟩
      return done updated (.object proxyRef)
  | .regexCompile, none, [.string pattern] =>
      let (updated, ref) := allocObject m
        ⟨.regexPattern, none, [("source", hostDescriptor (.string pattern))],
          [], [], false, false⟩
      return done updated (.object ref)
  | .regexCompile, none, [.string pattern, .number _ flags] =>
      let (updated, ref) := allocObject m
        ⟨.regexPattern, none,
          [("source", hostDescriptor (.string pattern)),
           ("flags", hostDescriptor (.number .pyInt flags))],
          [], [], false, false⟩
      return done updated (.object ref)
  | .regexMatchAt, some (.object ref), [.string expression, .number .pyInt offset] =>
      let pattern ← regexSource m ref
      if pattern != pythonTokenPattern then throw .unsupportedExpression
      if offset < 0 then return exception m "ValueError" "negative regex offset"
      match tokenMatchAt expression offset.toNat with
      | some result => return done m (.regexMatch result)
      | none => return done m .null
  | .regexFullmatch, some (.object ref), [.string source] =>
      let pattern ← regexSource m ref
      if pattern == pythonNamePattern then
        if identifierFullMatch source then
          return done m (.regexMatch ⟨source, 0, source.toList.length, []⟩)
        else return done m .null
      else if pattern == pythonEffectPattern then
        match effectFullMatch source with
        | some result => return done m (.regexMatch result)
        | none => return done m .null
      else throw .unsupportedExpression
  | .regexTest, some (.object ref), [.string source] =>
      let pattern ← regexSource m ref
      let first := source.toList.head?
      let startsDigit := first.any Char.isDigit
      let startsName := first.any (fun c => c.isAlpha || c == '_')
      if pattern == "/^\\d/" then return done m (.bool startsDigit)
      if pattern == "/^[A-Za-z_]/" then return done m (.bool startsName)
      if pattern == "/^[A-Za-z_][A-Za-z_0-9]*$/" then
        return done m (.bool (identifierFullMatch source))
      throw .unsupportedExpression
  | .regexExec, some (.object ref), [.string source] =>
      let pattern ← regexSource m ref
      if pattern != "/^([A-Za-z_][A-Za-z_0-9]*)\\s*=\\s*(.+)$/" then
        throw .unsupportedExpression
      match effectFullMatch source with
      | none => return done m .null
      | some result =>
          let items := TargetValue.string result.full ::
            (result.groups.map fun g => g.map TargetValue.string |>.getD .undefined)
          let (updated, matchRef) := allocObject m
            ⟨.jsArray, some m.objectPrototype, [], items, [], false, false⟩
          return done updated (.object matchRef)
  | .regexMatchEnd, some (.regexMatch result), [] =>
      return done m (.number .pyInt result.stop)
  | .regexGroup, some (.regexMatch result), [] =>
      return done m (.string result.full)
  | .regexGroup, some (.regexMatch result), [.number .pyInt 0] =>
      return done m (.string result.full)
  | .regexGroup, some (.regexMatch result), [.number .pyInt group] =>
      if group ≤ 0 then return exception m "IndexError" "regex group"
      match result.groups[group.toNat - 1]? with
      | some (some value) => return done m (.string value)
      | some none => return done m .null
      | none => return exception m "IndexError" "regex group"
  | .stringIsSpace, some (.string s), [] =>
      return done m (.bool (!s.isEmpty && s.toList.all
        (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')))
  | .stringIsDigit, some (.string s), [] =>
      return done m (.bool (!s.isEmpty && s.toList.all Char.isDigit))
  | .stringSlice, some (.string s), [.number _ first, .number _ last] =>
      let chars := s.toList
      let startIndex := normalizeSliceBound chars.length first
      let stopIndex := normalizeSliceBound chars.length last
      return done m (.string (String.mk ((chars.drop startIndex).take (stopIndex - startIndex))))
  | .stringStartsWith, some (.string s), [.string leading] =>
      return done m (.bool (s.startsWith leading))
  | .stringMatch, some (.string source), [.object regexRef] =>
      let pattern ← regexSource m regexRef
      let tokenPattern := "/=>|==|!=|>=|<=|&&|\\|\\||[()+\\-*/<>!.]|\\d+(?:\\.\\d+)?|[A-Za-z_][A-Za-z_0-9]*|'(?:[^'\\\\]|\\\\.)*'/g"
      if pattern != tokenPattern then throw .unsupportedExpression
      match tokenizeWorldExpr source with
      | none => return done m .null
      | some [] => return done m .null
      | some tokens =>
          let (updated, ref) := allocObject m
            ⟨.jsArray, some m.objectPrototype, [], tokens.map TargetValue.string,
              [], false, false⟩
          return done updated (.object ref)
  | .arrayJoin, some (.object ref), [.string separator] =>
      let obj ← objectAt m ref
      if obj.kind != .jsArray then return exception m "TypeError" "join target"
      let mut pieces : List String := []
      for item in obj.items do
        match item with
        | .string s => pieces := pieces ++ [s]
        | _ => return exception m "TypeError" "join element"
      return done m (.string (separator.intercalate pieces))
  | .stringReplace, some (.string source), [.string needle, .string replacement] =>
      if needle.isEmpty then throw .unsupportedExpression
      return done m (.string (replacement.intercalate (source.splitSourceOn needle)))
  | .stringReplace, some (.string source), [.object regexRef, .string replacement] =>
      let pattern ← regexSource m regexRef
      if pattern == "/\\s+/g" && replacement == "" then
        let kept := source.toList.filter (fun c =>
          c != ' ' && c != '\t' && c != '\n' && c != '\r')
        return done m (.string (String.mk kept))
      else if pattern == "/\\\\'/g" then
        return done m (.string (replacement.intercalate (source.splitSourceOn "\\'")))
      else throw .unsupportedExpression
  | .arrayPush, some (.object ref), [value] =>
      let obj ← objectAt m ref
      if obj.kind != .pythonList && obj.kind != .jsArray then
        return exception m "TypeError" "push target"
      if obj.frozen then return exception m "TypeError" "frozen array"
      let newItems := obj.items ++ [value]
      let updated ← replaceObject m ref { obj with items := newItems }
      if lang == .ts then return done updated (.number .jsNumber newItems.length)
      else return done updated .null
  | .pyObject, none, [] =>
      let (updated, ref) := allocObject m
        ⟨.pythonOrdinary, none, [], [], [], false, false⟩
      return done updated (.object ref)
  | .deepCopy, none, [value] =>
      let (updated, copy) ← cloneValue 2048 m value
      return done updated copy
  | .structuredClone, none, [value] =>
      let (updated, copy) ← cloneValue 2048 m value
      return done updated copy
  | .dict, none, [] =>
      let (updated, ref) := allocObject m
        ⟨.pythonDict, none, [], [], [], false, false⟩
      return done updated (.object ref)
  | .dict, none, [.object sourceRef] =>
      let source ← objectAt m sourceRef
      if source.kind != .pythonDict && source.kind != .mappingProxy then
        return exception m "TypeError" "dict source"
      let (updated, ref) := allocObject m
        ⟨.pythonDict, none, source.own, [], [], false, false⟩
      return done updated (.object ref)
  | .setNew, none, [] =>
      let (updated, ref) := allocObject m
        ⟨.jsSet, some m.objectPrototype, [], [], [], false, false⟩
      return done updated (.object ref)
  | .set, none, [] =>
      let (updated, ref) := allocObject m
        ⟨.pythonSet, none, [], [], [], false, false⟩
      return done updated (.object ref)
  | .setHas, some (.object ref), [value] =>
      let obj ← objectAt m ref
      if obj.kind != .jsSet && obj.kind != .pythonSet then
        return exception m "TypeError" "set target"
      return done m (.bool (obj.setMembers.contains value))
  | .setAdd, some (.object ref), [value] =>
      let obj ← objectAt m ref
      if obj.kind != .jsSet && obj.kind != .pythonSet then
        return exception m "TypeError" "set target"
      let members := if obj.setMembers.contains value then obj.setMembers
        else obj.setMembers ++ [value]
      let updated ← replaceObject m ref { obj with setMembers := members }
      return done updated (.object ref)
  | .objectIdentity, none, [.object ref] =>
      return done m (.number .pyInt ref)
  | .objectPrototypeToStringCall, none, [.object ref] =>
      let obj ← objectAt m ref
      let tag := match obj.kind with
        | .jsOrdinary | .jsNullPrototype => "[object Object]"
        | .jsArray => "[object Array]"
        | .jsSet => "[object Set]"
        | _ => "[object Object]"
      return done m (.string tag)
  | _, _, _ => throw (.unsupportedHostPrimitive id)

theorem host_float_exact (m : TargetMachine) (n : Int)
    (h : n.natAbs ≤ 9007199254740991) :
    hostCall .python m .float none [.number .pyInt n] =
      .ok (done m (.number .pyFloat n)) := by
  unfold hostCall
  simp only [safeIntermediate, h, ↓reduceIte]
  rfl

theorem host_int_exact (m : TargetMachine) (n : Int)
    (h : n.natAbs ≤ 9007199254740991) :
    hostCall .python m .int none [.number .pyFloat n] =
      .ok (done m (.number .pyInt n)) := by
  unfold hostCall
  simp only [safeIntermediate, h, ↓reduceIte]
  rfl

private def bindOne (lang : TargetLang) (m : TargetMachine)
    (frame : TargetFrame) (name : String) (value : TargetValue) :
    Except TargetError (TargetMachine × TargetFrame) := do
  if lang == .python then
    match frame.locals.lookup name with
    | some ref => return (← writeCell m ref value, frame)
    | none =>
        let (updated, ref) := allocCell m value true
        return (updated, { frame with locals := (name, ref) :: frame.locals })
  else
    let (updated, ref) := allocCell m value false
    return (updated, { frame with locals := (name, ref) :: frame.locals })

private def bindLoopValue (lang : TargetLang) (m : TargetMachine)
    (frame : TargetFrame) (binders : List String) (item : TargetValue) :
    Except TargetError (TargetMachine × TargetFrame) := do
  match binders with
  | [name] => bindOne lang m frame name item
  | [first, second] =>
      match item with
      | .object ref =>
          let pair ← objectAt m ref
          match pair.items with
          | [left, right] =>
              let (m, frame) ← bindOne lang m frame first left
              bindOne lang m frame second right
          | _ => throw .badBinderCardinality
      | _ => throw .badBinderCardinality
  | _ => throw .badBinderCardinality

private def sealCell (m : TargetMachine) (ref : CellRef) : TargetMachine :=
  let permissions := m.writableCells.map fun entry =>
    (entry.1, if entry.1 == ref then false else entry.2)
  { m with writableCells := permissions }

-- The interpreter is deliberately over target syntax only. No source World,
-- Bridge certificate, sourceEval or reference `interpret` is imported here.
mutual

def evalExpr (fuel : Nat) (program : TargetProgram) (m : TargetMachine)
    (frame : TargetFrame) (expr : TargetExpr) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match expr with
    | .undefined => .ok (done m .undefined)
    | .null => .ok (done m .null)
    | .bool b => .ok (done m (.bool b))
    | .integer n => .ok (done m (number program.lang n))
    | .string s => .ok (done m (.string s))
    | .regexLiteral source => do
        if program.lang != .ts then throw .unsupportedExpression
        let (updated, ref) := allocObject m
          ⟨.regexPattern, some m.objectPrototype,
            [("source", hostDescriptor (.string source))], [], [], false, false⟩
        return done updated (.object ref)
    | .newExpr constructorCall => evalExpr fuel program m frame constructorCall
    | .formatted parts => evalFormattedParts fuel program m frame parts ""
    | .local name => do return done m (← localValue m frame name)
    | .global name => do return done m (← localValue m frame name)
    | .checkerField name => do return done m (← readCheckerField m name)
    | .postIncrement name => do
        if program.lang != .ts then throw .unsupportedExpression
        let address := (frame.locals.lookup name).orElse fun _ =>
          (frame.captures.lookup name).orElse fun _ => m.globals.lookup name
        match address with
        | none => throw (.unboundLocal name)
        | some ref =>
            match ← readCell m ref with
            | .number tag n =>
                if !safeIntermediate (n + 1) then throw .outsideNumericDomain
                let updated ← writeCell m ref (.number tag (n + 1))
                return done updated (.number tag n)
            | _ => return exception m "TypeError" "postincrement operand"
    | .builtin id args => do
        let values ← evalArgValues fuel program m frame args
        match values.result with
        | .error e => return ⟨values.machine, .error e⟩
        | .ok xs =>
            if id == .next then resumeNext fuel program values.machine xs
            else if id == .tuple then consumeIterable fuel program values.machine .pythonTuple xs
            else if id == .list then consumeIterable fuel program values.machine .pythonList xs
            else hostCall program.lang values.machine id none xs
    | .lambdaExpr names body =>
        let params := names.map (fun name => (⟨name, none⟩ : ParamSpec))
        let defaults := names.map (fun _ => (none : Option TargetValue))
        let captures := frame.locals ++ frame.captures
        let closure : TargetClosure :=
          ⟨frame.qualifiedName ++ ".lambda", params, defaults,
            .returnValue body, captures, frame.receiver⟩
        let (updated, ref) := allocClosure m closure
        .ok (done updated (.closure ref))
    | .call callee args => do
        let functionValue ← evalExpr fuel program m frame callee
        match functionValue.result with
        | .error e => return ⟨functionValue.machine, .error e⟩
        | .ok callable =>
            let values ← evalArgValues fuel program functionValue.machine frame args
            match values.result with
            | .error e => return ⟨values.machine, .error e⟩
            | .ok xs =>
                match callable with
                | .builtin id =>
                    if id == .next then resumeNext fuel program values.machine xs
                    else if id == .tuple then consumeIterable fuel program values.machine .pythonTuple xs
                    else if id == .list then consumeIterable fuel program values.machine .pythonList xs
                    else hostCall program.lang values.machine id none xs
                | .boundBuiltin id receiver =>
                    if id == .arrayFind || id == .arraySome || id == .arrayMap then
                      evalArrayMethod fuel program values.machine id receiver xs
                    else hostCall program.lang values.machine id (some receiver) xs
                | .closure ref => callClosure fuel program values.machine ref xs
                | .object ref =>
                    match values.machine.callableObjects.lookup ref with
                    | some id => hostCall program.lang values.machine id none xs
                    | none => return exception values.machine "TypeError" "not callable"
                | _ => return exception values.machine "TypeError" "not callable"
    | .object fields => do
        let kind := if program.lang == .ts then ObjectKind.jsOrdinary else .pythonDict
        let proto := if program.lang == .ts then some m.objectPrototype else none
        let (fresh, ref) := allocObject m ⟨kind, proto, [], [], [], false, false⟩
        evalObjectFields fuel program fresh frame ref fields
    | .array items | .tuple items => do
        let kind := if program.lang == .ts then ObjectKind.jsArray
          else if expr matches .tuple _ then ObjectKind.pythonTuple else ObjectKind.pythonList
        let proto := if program.lang == .ts then some m.objectPrototype else none
        let (fresh, ref) := allocObject m ⟨kind, proto, [], [], [], false, false⟩
        evalArrayElems fuel program fresh frame ref items
    | .dictComprehension keyExpr valueExpr binders iterable filter => do
        if program.lang != .python then throw .unsupportedExpression
        let source ← evalExpr fuel program m frame iterable
        match source.result with
        | .error e => return ⟨source.machine, .error e⟩
        | .ok (.object sourceRef) =>
            let sourceObj ← objectAt source.machine sourceRef
            if sourceObj.kind != .pythonList && sourceObj.kind != .pythonTuple then
              return exception source.machine "TypeError" "comprehension iterable"
            let (updated, dest) := allocObject source.machine
              ⟨.pythonDict, none, [], [], [], false, false⟩
            let compFrame : TargetFrame :=
              ⟨frame.qualifiedName ++ ".dictComp", [], [],
                frame.locals ++ frame.captures, frame.receiver, .normal⟩
            evalDictCompItems fuel program updated compFrame dest binders
              sourceObj.items keyExpr valueExpr filter
        | .ok _ => return exception source.machine "TypeError" "comprehension iterable"
    | .listComprehension valueExpr binders iterable filter => do
        if program.lang != .python then throw .unsupportedExpression
        let source ← evalExpr fuel program m frame iterable
        match source.result with
        | .error e => return ⟨source.machine, .error e⟩
        | .ok (.object sourceRef) =>
            let sourceObj ← objectAt source.machine sourceRef
            if sourceObj.kind != .pythonList && sourceObj.kind != .pythonTuple then
              return exception source.machine "TypeError" "comprehension iterable"
            let (updated, dest) := allocObject source.machine
              ⟨.pythonList, none, [], [], [], false, false⟩
            let compFrame : TargetFrame :=
              ⟨frame.qualifiedName ++ ".listComp", [], [],
                frame.locals ++ frame.captures, frame.receiver, .normal⟩
            evalListCompItems fuel program updated compFrame dest binders
              sourceObj.items valueExpr filter
        | .ok _ => return exception source.machine "TypeError" "comprehension iterable"
    | .generator valueExpr binders iterable filter => do
        if program.lang != .python then throw .unsupportedExpression
        let source ← evalExpr fuel program m frame iterable
        match source.result with
        | .error e => return ⟨source.machine, .error e⟩
        | .ok (.object sourceRef) =>
            let sourceObj ← objectAt source.machine sourceRef
            if sourceObj.kind != .pythonList && sourceObj.kind != .pythonTuple then
              return exception source.machine "TypeError" "generator iterable"
            let (updated, ref) := allocObject source.machine
              ⟨.pythonGenerator, none, [], [], [], false, false⟩
            let generatorFrame : TargetFrame :=
              ⟨frame.qualifiedName ++ ".generator", [], [],
                frame.locals ++ frame.captures, frame.receiver, .normal⟩
            let state : GeneratorState :=
              ⟨valueExpr, binders, filter, sourceObj.items, generatorFrame⟩
            return done { updated with generators := (ref, state) :: updated.generators } (.object ref)
        | .ok _ => return exception source.machine "TypeError" "generator iterable"
    | .index receiver key => do
        let base ← evalExpr fuel program m frame receiver
        match base.result with
        | .error e => return ⟨base.machine, .error e⟩
        | .ok baseValue =>
            let position ← evalExpr fuel program base.machine frame key
            match position.result with
            | .error e => return ⟨position.machine, .error e⟩
            | .ok (.string field) => readPropertyValue program.lang position.machine baseValue field
            | .ok (.number _ n) =>
                match baseValue with
                | .object ref =>
                    let obj ← objectAt position.machine ref
                    match (normalizeIndex program.lang obj.items.length n).bind obj.items.get? with
                    | some value => return done position.machine value
                    | none =>
                        if program.lang == .ts then return done position.machine .undefined
                        else return exception position.machine "IndexError" "index out of range"
                | .string s =>
                    match (normalizeIndex program.lang s.toList.length n).bind s.toList.get? with
                    | some c => return done position.machine (.string (String.singleton c))
                    | none => return exception position.machine "IndexError" "string index out of range"
                | _ => return exception position.machine "TypeError" "not indexable"
            | .ok _ => return exception position.machine "TypeError" "invalid index"
    | .slice receiver start stop => do
        let base ← evalExpr fuel program m frame receiver
        match base.result with
        | .error e => return ⟨base.machine, .error e⟩
        | .ok (.string s) =>
            let first ← evalExpr fuel program base.machine frame start
            match first.result with
            | .error e => return ⟨first.machine, .error e⟩
            | .ok firstValue =>
                let last ← evalExpr fuel program first.machine frame stop
                match last.result with
                | .error e => return ⟨last.machine, .error e⟩
                | .ok lastValue =>
                    match numeric firstValue, numeric lastValue with
                    | some (_, a), some (_, b) =>
                        let chars := s.toList
                        let startIndex := normalizeSliceBound chars.length a
                        let stopIndex := normalizeSliceBound chars.length b
                        let len := stopIndex - startIndex
                        return done last.machine (.string (String.mk ((chars.drop startIndex).take len)))
                    | _, _ => return exception last.machine "TypeError" "slice index"
        | .ok _ => return exception base.machine "TypeError" "not sliceable"
    | .property receiver key => do
        let value ← evalExpr fuel program m frame receiver
        match value.result with
        | .error e => return ⟨value.machine, .error e⟩
        | .ok v => readPropertyValue program.lang value.machine v key
    | .optionalProperty receiver key => do
        let value ← evalExpr fuel program m frame receiver
        match value.result with
        | .error e => return ⟨value.machine, .error e⟩
        | .ok .undefined | .ok .null => return done value.machine .undefined
        | .ok v => readPropertyValue program.lang value.machine v key
    | .binary op left right => do
        let lhs ← evalExpr fuel program m frame left
        match lhs.result with
        | .error e => return ⟨lhs.machine, .error e⟩
        | .ok lv =>
            let rhs ← evalExpr fuel program lhs.machine frame right
            match rhs.result with
            | .error e => return ⟨rhs.machine, .error e⟩
            | .ok rv =>
                if program.lang == .python && op == .add then
                  match lv, rv with
                  | .object leftRef, .object rightRef =>
                      let leftObj ← objectAt rhs.machine leftRef
                      let rightObj ← objectAt rhs.machine rightRef
                      if leftObj.kind == .pythonList && rightObj.kind == .pythonList then
                        let (updated, ref) := allocObject rhs.machine
                          ⟨.pythonList, none, [], leftObj.items ++ rightObj.items,
                            [], false, false⟩
                        return done updated (.object ref)
                  | _, _ => pure ()
                return ⟨rhs.machine, ← binaryValue program.lang rhs.machine op lv rv⟩
    | .andThen left right => do
        let lhs ← evalExpr fuel program m frame left
        match lhs.result with
        | .error e => return ⟨lhs.machine, .error e⟩
        | .ok lv =>
            if ← sourceTruthy program.lang lhs.machine lv then
              evalExpr fuel program lhs.machine frame right
            else return done lhs.machine lv
    | .orElse left right => do
        let lhs ← evalExpr fuel program m frame left
        match lhs.result with
        | .error e => return ⟨lhs.machine, .error e⟩
        | .ok lv =>
            if ← sourceTruthy program.lang lhs.machine lv then return done lhs.machine lv
            else evalExpr fuel program lhs.machine frame right
    | .nullCoalesce left right => do
        let lhs ← evalExpr fuel program m frame left
        match lhs.result with
        | .error e => return ⟨lhs.machine, .error e⟩
        | .ok .undefined | .ok .null => evalExpr fuel program lhs.machine frame right
        | .ok value => return done lhs.machine value
    | .conditional cond yes no => do
        let outcome ← evalExpr fuel program m frame cond
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok value =>
            if ← sourceTruthy program.lang outcome.machine value then
              evalExpr fuel program outcome.machine frame yes
            else evalExpr fuel program outcome.machine frame no
    | .unary .not value => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok value => return done outcome.machine (.bool (!(← sourceTruthy program.lang outcome.machine value)))
    | .unary .neg value => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok value =>
            match numeric value with
            | some (tag, n) => return done outcome.machine (.number tag (-n))
            | none => return exception outcome.machine "TypeError" "expected number"
    | .unary .typeof value => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok value =>
            let tag := match value with
              | .undefined => "undefined"
              | .null | .object _ | .regexMatch _ => "object"
              | .bool _ => "boolean"
              | .string _ => "string"
              | .number _ _ => "number"
              | .closure _ | .builtin _ | .boundBuiltin _ _ | .classConstructor _ => "function"
              | .exception _ _ => "object"
            return done outcome.machine (.string tag)
    | .typeCast value _ => evalExpr fuel program m frame value
    | .nonNull value => evalExpr fuel program m frame value
    | expr => .error (.unsupportedNode (reprStr expr))

private def evalObjectFields (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (destination : ObjRef)
    (fields : TargetExpr) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match fields with
    | .empty => .ok (done m (.object destination))
    | .objectEntry key value rest => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok v =>
            let updated ← writeOwn outcome.machine destination key v
            evalObjectFields fuel program updated frame destination rest
    | .objectSpread source rest => do
        let outcome ← evalExpr fuel program m frame source
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok (.object ref) =>
            let origin ← objectAt outcome.machine ref
            let mut updated := outcome.machine
            for (key, descriptor) in origin.own do
              if descriptor.enumerable then
                match descriptor.value with
                | some v => updated ← writeOwn updated destination key v
                | none => throw .badDescriptor
            evalObjectFields fuel program updated frame destination rest
        | .ok _ => return exception outcome.machine "TypeError" "object spread source"
    | _ => .error .unsupportedExpression

private def evalArrayElems (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (destination : ObjRef)
    (items : TargetExpr) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match items with
    | .empty => .ok (done m (.object destination))
    | .sequence value rest => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok v =>
            let obj ← objectAt outcome.machine destination
            let updated ← replaceObject outcome.machine destination
              { obj with items := obj.items ++ [v] }
            evalArrayElems fuel program updated frame destination rest
    | .arraySpread source rest => do
        let outcome ← evalExpr fuel program m frame source
        match outcome.result with
        | .error e => return ⟨outcome.machine, .error e⟩
        | .ok (.object ref) =>
            let origin ← objectAt outcome.machine ref
            let obj ← objectAt outcome.machine destination
            let updated ← replaceObject outcome.machine destination
              { obj with items := obj.items ++ origin.items }
            evalArrayElems fuel program updated frame destination rest
        | .ok _ => return exception outcome.machine "TypeError" "array spread source"
    | _ => .error .unsupportedExpression

private def evalArgValues (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (args : TargetExpr) :
    Except TargetError ArgsOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match args with
    | .empty => .ok ⟨m, .ok []⟩
    | .sequence first rest => do
        let value ← evalExpr fuel program m frame first
        match value.result with
        | .error e => return ⟨value.machine, .error e⟩
        | .ok v =>
            let others ← evalArgValues fuel program value.machine frame rest
            match others.result with
            | .error e => return ⟨others.machine, .error e⟩
            | .ok vs => return ⟨others.machine, .ok (v :: vs)⟩
    | _ => .error .unsupportedExpression

private def evalCompFilter (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (filter : TargetExpr) :
    Except TargetError (TargetMachine × Except TargetValue Bool) := do
  if filter == .empty then return (m, .ok true)
  let test ← evalExpr fuel program m frame filter
  match test.result with
  | .error e => return (test.machine, .error e)
  | .ok v =>
      let truth ← sourceTruthy .python test.machine v
      return (test.machine, .ok truth)

private def evalDictCompItems (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (destination : ObjRef)
    (binders : List String) (items : List TargetValue)
    (keyExpr valueExpr filter : TargetExpr) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match items with
    | [] => .ok (done m (.object destination))
    | item :: rest => do
        let (boundMachine, boundFrame) ← bindLoopValue .python m frame binders item
        let (afterFilter, shouldInclude) ← evalCompFilter fuel program boundMachine boundFrame filter
        match shouldInclude with
        | .error e => return ⟨afterFilter, .error e⟩
        | .ok false =>
            evalDictCompItems fuel program afterFilter boundFrame destination
              binders rest keyExpr valueExpr filter
        | .ok true => do
            let key ← evalExpr fuel program afterFilter boundFrame keyExpr
            match key.result with
            | .error e => return ⟨key.machine, .error e⟩
            | .ok (.string field) =>
                let value ← evalExpr fuel program key.machine boundFrame valueExpr
                match value.result with
                | .error e => return ⟨value.machine, .error e⟩
                | .ok v =>
                    let updated ← writeOwn value.machine destination field v
                    evalDictCompItems fuel program updated boundFrame destination
                      binders rest keyExpr valueExpr filter
            | .ok _ => return exception key.machine "TypeError" "dict key"

private def evalListCompItems (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (destination : ObjRef)
    (binders : List String) (items : List TargetValue)
    (valueExpr filter : TargetExpr) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match items with
    | [] => .ok (done m (.object destination))
    | item :: rest => do
        let (boundMachine, boundFrame) ← bindLoopValue .python m frame binders item
        let (afterFilter, includeItem) ← evalCompFilter fuel program boundMachine boundFrame filter
        match includeItem with
        | .error e => return ⟨afterFilter, .error e⟩
        | .ok false =>
            evalListCompItems fuel program afterFilter boundFrame destination binders rest valueExpr filter
        | .ok true => do
            let value ← evalExpr fuel program afterFilter boundFrame valueExpr
            match value.result with
            | .error e => return ⟨value.machine, .error e⟩
            | .ok v =>
                let obj ← objectAt value.machine destination
                let updated ← replaceObject value.machine destination
                  { obj with items := obj.items ++ [v] }
                evalListCompItems fuel program updated boundFrame destination
                  binders rest valueExpr filter

private def evalArrayMethod (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (id : BuiltinId) (receiver : TargetValue)
    (args : List TargetValue) : Except TargetError ExprOutcome := do
  match receiver, args with
  | .object arrayRef, [.closure callbackRef] =>
      let obj ← objectAt m arrayRef
      if obj.kind != .jsArray then return exception m "TypeError" "array callback target"
      evalArrayMethodItems fuel program m id callbackRef obj.items []
  | _, _ => return exception m "TypeError" "array callback arguments"

private def evalArrayMethodItems (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (id : BuiltinId) (callbackRef : ClosureRef)
    (items acc : List TargetValue) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
      match items with
      | [] =>
          if id == .arraySome then .ok (done m (.bool false))
          else if id == .arrayFind then .ok (done m .undefined)
          else
            let (updated, ref) := allocObject m
              ⟨.jsArray, some m.objectPrototype, [], acc, [], false, false⟩
            .ok (done updated (.object ref))
      | item :: rest => do
          let callback ← callClosure fuel program m callbackRef [item]
          match callback.result with
          | .error e => return ⟨callback.machine, .error e⟩
          | .ok value =>
              if id == .arrayMap then
                evalArrayMethodItems fuel program callback.machine id callbackRef rest
                  (acc ++ [value])
              else if ← sourceTruthy .ts callback.machine value then
                return done callback.machine
                  (if id == .arraySome then .bool true else item)
              else evalArrayMethodItems fuel program callback.machine id callbackRef rest acc

private def evalFormattedParts (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (parts : TargetExpr)
    (acc : String) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
      match parts with
      | .empty => .ok (done m (.string acc))
      | .formatPart literal value rest => do
          if value == .empty then
            evalFormattedParts fuel program m frame rest (acc ++ literal)
          else
            let result ← evalExpr fuel program m frame value
            match result.result with
            | .error e => return ⟨result.machine, .error e⟩
            | .ok v =>
                let rendered ← match v with
                  | .string s => .ok s
                  | .number _ n => .ok (toString n)
                  | .bool true => .ok (if program.lang == .ts then "true" else "True")
                  | .bool false => .ok (if program.lang == .ts then "false" else "False")
                  | .null => .ok (if program.lang == .ts then "null" else "None")
                  | _ => .error .unsupportedExpression
                evalFormattedParts fuel program result.machine frame rest
                  (acc ++ literal ++ rendered)
      | _ => .error .unsupportedExpression

def execStmt (fuel : Nat) (program : TargetProgram) (m : TargetMachine)
    (frame : TargetFrame) (stmt : TargetStmt) : Except TargetError StmtOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match stmt with
    | .empty => .ok ⟨m, frame, .normal⟩
    | .sequence first rest => do
        let head ← execStmt fuel program m frame first
        match head.control with
        | .normal => execStmt fuel program head.machine head.frame rest
        | _ => return head
    | .letLocal name mutable value => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok v =>
            let (updated, ref) := allocCell outcome.machine v mutable
            return ⟨updated, { frame with locals := (name, ref) :: frame.locals }, .normal⟩
    | .nonlocalNames names => do
        for name in names do
          if (frame.captures.lookup name).isNone then throw (.unboundLocal name)
        return ⟨m, frame, .normal⟩
    | .importModule moduleName alias => do
        let (updated, value) ← importedModule m moduleName
        let (final, ref) := allocCell updated value (program.lang == .python)
        return ⟨final, { frame with locals := (alias, ref) :: frame.locals }, .normal⟩
    | .fromImport moduleName name alias => do
        let (updated, value) ← importedBinding m moduleName name
        match value with
        | none => return ⟨updated, frame, .normal⟩
        | some v =>
            let (final, ref) := allocCell updated v (program.lang == .python)
            return ⟨final, { frame with locals := (alias, ref) :: frame.locals }, .normal⟩
    | .defineClass name base body => do
        let evaluatedBase ← evalExpr fuel program m frame base
        match evaluatedBase.result with
        | .error e => return ⟨evaluatedBase.machine, frame, .raised e⟩
        | .ok (.classConstructor _) =>
            let classFrame : TargetFrame :=
              ⟨name, [], [], frame.locals ++ frame.captures, none, .normal⟩
            let executed ← execStmt fuel program evaluatedBase.machine classFrame body
            match executed.control with
            | .normal =>
                let mut methods : List (String × ClosureRef) := []
                for (methodName, address) in executed.frame.locals do
                  match ← readCell executed.machine address with
                  | .closure methodRef => methods := (methodName, methodRef) :: methods
                  | _ => throw .badDescriptor
                let withMethods := { executed.machine with classMethods := methods }
                let (final, ref) := allocCell withMethods (.classConstructor name) true
                return ⟨final, { frame with locals := (name, ref) :: frame.locals }, .normal⟩
            | _ => return ⟨executed.machine, frame, executed.control⟩
        | .ok _ => return ⟨evaluatedBase.machine, frame,
            .raised (.exception "TypeError" "invalid class base")⟩
    | .defineGetter name body =>
        execStmt fuel program m frame (.defineFunction name [] body)
    | .defineFunction name params body => do
        let evaluated ← evalDefaults fuel program m frame params
        match evaluated.result with
        | .error e => return ⟨evaluated.machine, frame, .raised e⟩
        | .ok defaults =>
            let (withCell, cell) := allocCell evaluated.machine .undefined true
            let captures := (name, cell) :: frame.locals ++ frame.captures
            let closure : TargetClosure :=
              ⟨frame.qualifiedName ++ "." ++ name, params, defaults, body,
                captures, frame.receiver⟩
            let (withClosure, ref) := allocClosure withCell closure
            let withValue ← writeCell withClosure cell (.closure ref)
            let final := if program.lang == .ts then sealCell withValue cell else withValue
            return ⟨final, { frame with locals := (name, cell) :: frame.locals }, .normal⟩
    | .assign (.local name) value => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok v =>
            let address := (frame.locals.lookup name).orElse fun _ =>
              (frame.captures.lookup name).orElse fun _ => m.globals.lookup name
            match address with
            | some ref =>
                let updated ← writeCell outcome.machine ref v
                return ⟨updated, frame, .normal⟩
            | none =>
                if program.lang == .ts then throw (.unboundLocal name)
                let (updated, ref) := allocCell outcome.machine v true
                return ⟨updated, { frame with locals := (name, ref) :: frame.locals }, .normal⟩
    | .augment (.local name) op value => do
        let address := (frame.locals.lookup name).orElse fun _ =>
          (frame.captures.lookup name).orElse fun _ => m.globals.lookup name
        let ref ← match address with
          | some ref => .ok ref
          | none => .error (.unboundLocal name)
        let old ← readCell m ref
        let rhs ← evalExpr fuel program m frame value
        match rhs.result with
        | .error e => return ⟨rhs.machine, frame, .raised e⟩
        | .ok v =>
            let combined ← binaryValue program.lang rhs.machine op old v
            match combined with
            | .error e => return ⟨rhs.machine, frame, .raised e⟩
            | .ok result =>
                let updated ← writeCell rhs.machine ref result
                return ⟨updated, frame, .normal⟩
    | .assign (.field name) value => do
        let outcome ← evalExpr fuel program m frame value
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok v =>
            let updated ← writeCheckerField outcome.machine name v
            return ⟨updated, frame, .normal⟩
    | .assign (.property receiver name) value => do
        let base ← evalExpr fuel program m frame receiver
        match base.result with
        | .error e => return ⟨base.machine, frame, .raised e⟩
        | .ok baseValue =>
            let outcome ← evalExpr fuel program base.machine frame value
            match outcome.result with
            | .error e => return ⟨outcome.machine, frame, .raised e⟩
            | .ok v =>
                match baseValue with
                | .object ref =>
                    let updated ← if ref == outcome.machine.checkerRef then
                      writeCheckerField outcome.machine name v
                      else writeOwn outcome.machine ref name v
                    return ⟨updated, frame, .normal⟩
                | _ => return ⟨outcome.machine, frame,
                    .raised (.exception "TypeError" "invalid property assignment")⟩
    | .assign (.index receiver key) value => do
        let base ← evalExpr fuel program m frame receiver
        match base.result with
        | .error e => return ⟨base.machine, frame, .raised e⟩
        | .ok baseValue =>
            let index ← evalExpr fuel program base.machine frame key
            match index.result with
            | .error e => return ⟨index.machine, frame, .raised e⟩
            | .ok keyValue =>
                let rhs ← evalExpr fuel program index.machine frame value
                match rhs.result with
                | .error e => return ⟨rhs.machine, frame, .raised e⟩
                | .ok v =>
                    match baseValue, keyValue with
                    | .object ref, .string field =>
                        let updated ← writeOwn rhs.machine ref field v
                        return ⟨updated, frame, .normal⟩
                    | _, _ => return ⟨rhs.machine, frame,
                        .raised (.exception "TypeError" "invalid indexed assignment")⟩
    | .doExpr expr => do
        let outcome ← evalExpr fuel program m frame expr
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok _ => return ⟨outcome.machine, frame, .normal⟩
    | .returnValue expr => do
        let outcome ← evalExpr fuel program m frame expr
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok v => return ⟨outcome.machine, frame, .returned v⟩
    | .returnVoid => .ok ⟨m, frame, .returned .undefined⟩
    | .throwValue expr => do
        let outcome ← evalExpr fuel program m frame expr
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok v => return ⟨outcome.machine, frame, .raised v⟩
    | .rethrow =>
        match frame.control with
        | .raised value => .ok ⟨m, frame, .raised value⟩
        | _ => .error .wrongControl
    | .ifThenElse cond yes no => do
        let outcome ← evalExpr fuel program m frame cond
        match outcome.result with
        | .error e => return ⟨outcome.machine, frame, .raised e⟩
        | .ok v =>
            if ← sourceTruthy program.lang outcome.machine v then
              execStmt fuel program outcome.machine frame yes
            else execStmt fuel program outcome.machine frame no
    | .breakTarget target => .ok ⟨m, frame, .broke target⟩
    | .continueTarget target => .ok ⟨m, frame, .continued target⟩
    | .whileDo cond body => do
        let condition ← evalExpr fuel program m frame cond
        match condition.result with
        | .error e => return ⟨condition.machine, frame, .raised e⟩
        | .ok value =>
            if !(← sourceTruthy program.lang condition.machine value) then
              return ⟨condition.machine, frame, .normal⟩
            let result ← execStmt fuel program condition.machine frame body
            match result.control with
            | .normal | .continued "loop" =>
                execStmt fuel program result.machine result.frame (.whileDo cond body)
            | .broke "loop" => return ⟨result.machine, result.frame, .normal⟩
            | _ => return result
    | .forDo binders iterable body => do
        let source ← evalExpr fuel program m frame iterable
        match source.result with
        | .error e => return ⟨source.machine, frame, .raised e⟩
        | .ok (.object ref) =>
            let obj ← objectAt source.machine ref
            match obj.kind with
            | .jsArray | .pythonList | .pythonTuple =>
                execForItems fuel program source.machine frame binders obj.items body
            | _ => return ⟨source.machine, frame,
                .raised (.exception "TypeError" "not iterable")⟩
        | .ok _ => return ⟨source.machine, frame,
            .raised (.exception "TypeError" "not iterable")⟩
    | .switchOn scrutinee cases => do
        let value ← evalExpr fuel program m frame scrutinee
        match value.result with
        | .error e => return ⟨value.machine, frame, .raised e⟩
        | .ok v => evalSwitchCases fuel program value.machine frame v false cases
    | .tryCatchFinally body catchType binder handler cleanup => do
        let attempted ← execStmt fuel program m frame body
        let handled ← match attempted.control with
          | .raised errorValue =>
              let catches := controlCaught catchType (.raised errorValue)
              if catches then do
                let (updated, activeFrame) :=
                  bindCatchFrame attempted.machine attempted.frame binder errorValue
                let handled ← execStmt fuel program updated activeFrame handler
                pure { handled with frame := { handled.frame with control := .normal } }
              else .ok attempted
          | _ => .ok attempted
        let finalized ← execStmt fuel program handled.machine handled.frame cleanup
        match finalized.control with
        | .normal => return ⟨finalized.machine, finalized.frame, handled.control⟩
        | _ => return finalized
    | stmt => .error (.unsupportedNode (reprStr stmt))

private def evalSwitchCases (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (value : TargetValue)
    (matched : Bool) (cases : TargetStmt) : Except TargetError StmtOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match cases with
    | .empty => .ok ⟨m, frame, .normal⟩
    | .switchCase label body next =>
        if matched || value == .string label then do
          let result ← execStmt fuel program m frame body
          match result.control with
          | .normal => evalSwitchCases fuel program result.machine result.frame value true next
          | .broke "switch" => return ⟨result.machine, result.frame, .normal⟩
          | _ => return result
        else evalSwitchCases fuel program m frame value false next
    | _ => .error .unsupportedStatement

private def execForItems (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (outerFrame : TargetFrame) (binders : List String)
    (items : List TargetValue) (body : TargetStmt) : Except TargetError StmtOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match items with
    | [] => .ok ⟨m, outerFrame, .normal⟩
    | item :: rest => do
        let (boundMachine, loopFrame) ← bindLoopValue program.lang m outerFrame binders item
        let result ← execStmt fuel program boundMachine loopFrame body
        let nextFrame := if program.lang == .ts then outerFrame else result.frame
        match result.control with
        | .normal | .continued "loop" =>
            execForItems fuel program result.machine nextFrame binders rest body
        | .broke "loop" => return ⟨result.machine, nextFrame, .normal⟩
        | _ => return result

private def evalOneDefault (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (param : ParamSpec) :
    Except TargetError (TargetMachine × Except TargetValue (Option TargetValue)) := do
  if program.lang == .python then
    match param.defaultValue with
    | some expr =>
        let outcome ← evalExpr fuel program m frame expr
        match outcome.result with
        | .error e => return (outcome.machine, .error e)
        | .ok value => return (outcome.machine, .ok (some value))
    | none => return (m, .ok none)
  else return (m, .ok none)

private def evalDefaults (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (params : List ParamSpec) :
    Except TargetError DefaultsOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match params with
    | [] => .ok ⟨m, .ok []⟩
    | param :: rest => do
        let first ← evalOneDefault fuel program m frame param
        match first with
        | (updated, .error e) => return ⟨updated, .error e⟩
        | (updated, .ok value) =>
            let tail ← evalDefaults fuel program updated frame rest
            match tail.result with
            | .error e => return ⟨tail.machine, .error e⟩
            | .ok values => return ⟨tail.machine, .ok (value :: values)⟩

private def bindCallParams (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (frame : TargetFrame) (params : List ParamSpec)
    (defaults : List (Option TargetValue)) (args : List TargetValue) :
    Except TargetError BindOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 =>
    match params with
    | [] =>
        if program.lang == .python && !args.isEmpty then
          .ok ⟨m, frame, .error (.exception "TypeError" "too many arguments")⟩
        else .ok ⟨m, frame, .ok ()⟩
    | param :: rest => do
        let provided := args.head?
        let needsDefault := provided.isNone ||
          (program.lang == .ts && provided == some .undefined)
        let selected ←
          if !needsDefault then .ok (m, .ok (provided.getD .undefined))
          else if program.lang == .python then
            match defaults.head?.join with
            | some value => .ok (m, .ok value)
            | none => .ok (m, .error (.exception "TypeError" "missing argument"))
          else
            match param.defaultValue with
            | some expr => do
                let outcome ← evalExpr fuel program m frame expr
                .ok (outcome.machine, outcome.result)
            | none => .ok (m, .ok .undefined)
        match selected with
        | (updated, .error e) => return ⟨updated, frame, .error e⟩
        | (updated, .ok value) =>
            let (withCell, ref) := allocCell updated value true
            let nextFrame := { frame with locals := (param.name, ref) :: frame.locals }
            bindCallParams fuel program withCell nextFrame rest (defaults.drop 1)
              (if provided.isSome then args.drop 1 else args)

private def callClosure (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (ref : ClosureRef) (args : List TargetValue) :
    Except TargetError ExprOutcome := do
  let closure ← closureAt m ref
  let newFrame : TargetFrame :=
    ⟨closure.qualifiedName, [], [], closure.captures, closure.receiver, .normal⟩
  let bindings ← bindCallParams fuel program m newFrame closure.params
    closure.pythonDefaults args
  match bindings.result with
  | .error e => return ⟨bindings.machine, .error e⟩
  | .ok _ =>
      let executed ← execStmt fuel program bindings.machine bindings.frame closure.body
      match executed.control with
      | .returned value => return done executed.machine value
      | .normal => return done executed.machine (if program.lang == .ts then .undefined else .null)
      | .raised value => return ⟨executed.machine, .error value⟩
      | _ => throw .wrongControl

private def resumeNext (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (args : List TargetValue) : Except TargetError ExprOutcome :=
  match args with
  | [.object ref] => resumeGenerator fuel program m ref none
  | [.object ref, fallback] => resumeGenerator fuel program m ref (some fallback)
  | _ => .ok (exception m "TypeError" "next arguments")

private def resumeGenerator (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (ref : ObjRef) (fallback : Option TargetValue) :
    Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 => do
      let state ← generatorAt m ref
      match state.remaining with
      | [] =>
          match fallback with
          | some value => return done m value
          | none => return exception m "StopIteration" "generator exhausted"
      | item :: rest =>
          let (boundMachine, boundFrame) ← bindLoopValue .python m state.frame
            state.binders item
          let advanced : GeneratorState := { state with remaining := rest, frame := boundFrame }
          let machine ← replaceGenerator boundMachine ref advanced
          let (filtered, selected) ← evalCompFilter fuel program machine boundFrame state.filterExpr
          match selected with
          | .error e => return ⟨filtered, .error e⟩
          | .ok false => resumeGenerator fuel program filtered ref fallback
          | .ok true => evalExpr fuel program filtered boundFrame state.valueExpr

private def consumeIterable (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (kind : ObjectKind) (args : List TargetValue) :
    Except TargetError ExprOutcome := do
  match args with
  | [] =>
      let (updated, ref) := allocObject m ⟨kind, none, [], [], [], false, false⟩
      return done updated (.object ref)
  | [.object sourceRef] =>
      let source ← objectAt m sourceRef
      if source.kind == .pythonGenerator then
        consumeGenerator fuel program m sourceRef kind []
      else if source.kind == .pythonList || source.kind == .pythonTuple then
        let (updated, ref) := allocObject m
          ⟨kind, none, [], source.items, [], false, false⟩
        return done updated (.object ref)
      else return exception m "TypeError" "not iterable"
  | _ => return exception m "TypeError" "iterable constructor arity"

private def consumeGenerator (fuel : Nat) (program : TargetProgram)
    (m : TargetMachine) (generatorRef : ObjRef) (kind : ObjectKind)
    (acc : List TargetValue) : Except TargetError ExprOutcome :=
  match fuel with
  | 0 => .error .exhaustedFuel
  | fuel + 1 => do
      let result ← resumeGenerator fuel program m generatorRef none
      match result.result with
      | .ok value => consumeGenerator fuel program result.machine generatorRef kind (acc ++ [value])
      | .error (.exception "StopIteration" _) =>
          let (updated, ref) := allocObject result.machine
            ⟨kind, none, [], acc, [], false, false⟩
          return done updated (.object ref)
      | .error e => return ⟨result.machine, .error e⟩

end

theorem eval_sub_js_safe (program : TargetProgram) (hLang : program.lang = .ts)
    (m : TargetMachine) (frame : TargetFrame) (b n : Int)
    (h : (b - n).natAbs ≤ 9007199254740991) :
    (evalExpr 20 program m frame
      (.binary .sub (.integer b) (.integer n))).toOption.bind
        (fun out => out.result.toOption) = some (.number .jsNumber (b - n)) := by
  simp [evalExpr, number, done, hLang, binary_sub_js_safe, h,
    Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map]
  rfl

theorem eval_float_from_py_int (program : TargetProgram)
    (hLang : program.lang = .python) (m : TargetMachine)
    (frame : TargetFrame) (n : Int)
    (h : n.natAbs ≤ 9007199254740991) :
    (evalExpr 20 program m frame
      (.builtin .float (.sequence (.integer n) .empty))).toOption.bind
        (fun out => out.result.toOption) = some (.number .pyFloat n) := by
  simp [evalExpr, evalArgValues, number, done, hLang, host_float_exact, h,
    Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map]
  rfl

theorem eval_sub_py_float_safe (program : TargetProgram)
    (hLang : program.lang = .python) (m : TargetMachine)
    (frame : TargetFrame) (b n : Int)
    (hb : b.natAbs ≤ 9007199254740991)
    (hn : n.natAbs ≤ 9007199254740991)
    (hd : (b - n).natAbs ≤ 9007199254740991) :
    (evalExpr 20 program m frame
      (.binary .sub (.builtin .float (.sequence (.integer b) .empty))
        (.builtin .float (.sequence (.integer n) .empty)))).toOption.bind
        (fun out => out.result.toOption) = some (.number .pyFloat (b - n)) := by
  simp [evalExpr, evalArgValues, number, done, hLang,
    host_float_exact, binary_sub_py_float_safe, hb, hn, hd,
    Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map]
  rfl

inductive RequestShape where
  | ordinaryRecord | exactDict | noArgument
  deriving DecidableEq, Repr

structure TargetSeed where
  lang : TargetLang
  shape : RequestShape
  balance : Int
  extraFields : List (String × TargetValue)
  proxy : Bool
  accessor : Bool
  deriving DecidableEq, Repr

def canonicalBalanceSeed (lang : TargetLang) (balance : Int) : TargetSeed :=
  ⟨lang, if lang == .ts then .ordinaryRecord else .exactDict,
    balance, [], false, false⟩

def defaultContextSeed (lang : TargetLang) : TargetSeed :=
  ⟨lang, .noArgument, 0, [], false, false⟩

private def allocateSeed (m : TargetMachine) (seed : TargetSeed) :
    Except TargetError (TargetMachine × TargetValue) := do
  if seed.shape == .noArgument then return (m, .null)
  if !safeIntermediate seed.balance then throw .outsideNumericDomain
  if (seed.lang == .ts && seed.shape != .ordinaryRecord) ||
      (seed.lang == .python && seed.shape != .exactDict) then throw .invalidTag
  let balanceValue := number seed.lang seed.balance
  let descriptor := if seed.accessor then
      (⟨none, some 0, none, true, true, true⟩ : Descriptor)
    else hostDescriptor balanceValue
  let extra := seed.extraFields.map fun entry => (entry.1, hostDescriptor entry.2)
  let kind := if seed.lang == .ts then ObjectKind.jsOrdinary else .pythonDict
  let proto := if seed.lang == .ts then some m.objectPrototype else none
  let (updated, ref) := allocObject m
    ⟨kind, proto, ("balance", descriptor) :: extra, [], [], false, seed.proxy⟩
  return (updated, .object ref)

private def installTSMethodsGo (m : TargetMachine) (moduleFrame : TargetFrame) :
    List TargetFunction → TargetMachine × List (String × ClosureRef)
  | [] => (m, [])
  | function :: rest =>
      if function.qualifiedName.startsWith "WorldChecker." then
        let methodName := function.qualifiedName.drop "WorldChecker.".length
        let closure : TargetClosure :=
          ⟨function.qualifiedName, function.params, [], function.body,
            moduleFrame.locals ++ moduleFrame.captures, none⟩
        let (updated, ref) := allocClosure m closure
        let (final, methods) := installTSMethodsGo updated moduleFrame rest
        (final, (methodName, ref) :: methods)
      else installTSMethodsGo m moduleFrame rest

private def installTSMethods (program : TargetProgram) (m : TargetMachine)
    (moduleFrame : TargetFrame) : TargetMachine :=
  let (updated, methods) := installTSMethodsGo m moduleFrame program.functions
  { updated with classMethods := methods }

def targetConstructWithFuel (fuel : Nat) (program : TargetProgram) (seed : TargetSeed) :
    Except TargetError TargetMachine := do
  if seed.lang != program.lang then throw .invalidTag
  let moduleFrame : TargetFrame := ⟨"module", [], [], [], none, .normal⟩
  let moduleResult ← execStmt fuel program (initialHostMachine program.lang)
    moduleFrame program.moduleInit
  if moduleResult.control != .normal then throw .wrongControl
  let machine ←
    if program.lang == .ts then do
      let withMethods := installTSMethods program moduleResult.machine moduleResult.frame
      let fieldsFrame : TargetFrame :=
        ⟨"WorldChecker.fields", [], [], moduleResult.frame.locals,
          some withMethods.checkerRef, .normal⟩
      let fields ← execStmt fuel program withMethods fieldsFrame program.classFields
      if fields.control != .normal then throw .wrongControl
      pure fields.machine
    else .ok moduleResult.machine
  let (withSeed, seedValue) ← allocateSeed machine seed
  let methodName := if program.lang == .ts then "constructor" else "__init__"
  let receiverName := if program.lang == .ts then "this" else "self"
  let callFrame : TargetFrame :=
    ⟨"construct", [], [], moduleResult.frame.locals,
      some withSeed.checkerRef, .normal⟩
  -- The seed is a heap reference supplied as an explicit argument.
  let (withArgument, address) := allocCell withSeed seedValue true
  let argumentFrame := { callFrame with locals := [("initialContext", address)] }
  let actualCall : TargetExpr :=
    .call (.property (.local receiverName) methodName)
      (.sequence (.local "initialContext") .empty)
  let result ← evalExpr fuel program withArgument argumentFrame actualCall
  match result.result with
  | .ok _ => return result.machine
  | .error e => throw (.sourceException e)

def targetConstruct (program : TargetProgram) (seed : TargetSeed) :
    Except TargetError TargetMachine :=
  targetConstructWithFuel 100 program seed

structure TargetRequest where
  lang : TargetLang
  shape : RequestShape
  transitionId : String
  amount : Int
  deriving DecidableEq, Repr

def canonicalDebitRequest (lang : TargetLang) (n : Int) : TargetRequest :=
  ⟨lang, if lang == .ts then .ordinaryRecord else .exactDict, "DEBIT", n⟩

structure TargetOutcome where
  machine : TargetMachine
  verdict : TargetValue
  deriving DecidableEq, Repr

def targetStepWithFuel (fuel : Nat) (program : TargetProgram) (machine : TargetMachine)
    (request : TargetRequest) : Except TargetError TargetOutcome := do
  if request.lang != program.lang || !safeIntermediate request.amount then
    throw .outsideNumericDomain
  if (request.lang == .ts && request.shape != .ordinaryRecord) ||
      (request.lang == .python && request.shape != .exactDict) then
    throw .invalidTag
  let kind := if request.lang == .ts then ObjectKind.jsOrdinary else .pythonDict
  let proto := if request.lang == .ts then some machine.objectPrototype else none
  let (withPayload, payloadRef) := allocObject machine
    ⟨kind, proto, [("amount", hostDescriptor (number request.lang request.amount))],
      [], [], false, false⟩
  let (withRequest, requestRef) := allocObject withPayload
    ⟨kind, proto,
      [("transitionId", hostDescriptor (.string request.transitionId)),
       ("eventPayload", hostDescriptor (.object payloadRef))],
      [], [], false, false⟩
  let receiverName := if request.lang == .ts then "this" else "self"
  let (withCell, cell) := allocCell withRequest (.object requestRef) true
  let frame : TargetFrame :=
    ⟨"step-call", [], [("request", cell)], [], some withCell.checkerRef, .normal⟩
  let expression : TargetExpr :=
    .call (.property (.local receiverName) "step")
      (.sequence (.local "request") .empty)
  let result ← evalExpr fuel program withCell frame expression
  match result.result with
  | .ok verdict => return ⟨result.machine, verdict⟩
  | .error e => throw (.sourceException e)

def targetStep (program : TargetProgram) (machine : TargetMachine)
    (request : TargetRequest) : Except TargetError TargetOutcome :=
  targetStepWithFuel 100 program machine request

end Harmonia.Applications.Kadmos.Generated
