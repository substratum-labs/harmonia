import Harmonia.Applications.Kadmos.Generated.TargetMachine

set_option maxHeartbeats 1000000

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

private def done (m : TargetMachine) (value : TargetValue) : ExprOutcome :=
  ⟨m, .ok value⟩

private def exception (m : TargetMachine) (className message : String) : ExprOutcome :=
  ⟨m, .error (.exception className message)⟩

private def number (lang : TargetLang) (n : Int) : TargetValue :=
  .number (if lang == .ts then .jsNumber else .pyInt) n

private def numeric : TargetValue → Option (NumberTag × Int)
  | .number tag n => some (tag, n)
  | _ => none

private def resultTag (lang : TargetLang) (left right : NumberTag) : NumberTag :=
  if lang == .ts then .jsNumber
  else if left == .pyFloat || right == .pyFloat then .pyFloat
  else .pyInt

private def safeIntermediate (n : Int) : Bool :=
  n.natAbs ≤ 9007199254740991

private def binaryValue (lang : TargetLang) (op : BinaryOp)
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
            match ← readOwn m ref key with
            | some descriptor =>
                match descriptor.value with
                | some value => return done m value
                | none => throw .badDescriptor
            | none => throw (.unboundLocal key)
      let obj ← objectAt m ref
      if obj.kind == .jsArray && key == "length" then
        return done m (.number .jsNumber obj.items.length)
      if obj.kind == .jsSet && key == "size" then
        return done m (.number .jsNumber obj.setMembers.length)
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

private def hostCall (lang : TargetLang) (m : TargetMachine) (id : BuiltinId)
    (receiver : Option TargetValue) (args : List TargetValue) :
    Except TargetError ExprOutcome := do
  match id, receiver, args with
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
  | .int, none, [.number _ n] =>
      if !safeIntermediate n then throw .outsideNumericDomain
      return done m (.number .pyInt n)
  | .isInteger, some (.number .pyFloat _), [] => return done m (.bool true)
  | .isInteger, some (.number .pyInt _), [] => return done m (.bool true)
  | .isFinite, none, [.number _ _] => return done m (.bool true)
  | .abs, none, [.number tag n] => return done m (.number tag n.natAbs)
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
  | _, _, _ => throw (.unsupportedHostPrimitive id)

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
        | .ok xs => hostCall program.lang values.machine id none xs
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
                | .builtin id => hostCall program.lang values.machine id none xs
                | .boundBuiltin id receiver =>
                    hostCall program.lang values.machine id (some receiver) xs
                | .closure ref => callClosure fuel program values.machine ref xs
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
            | .ok rv => return ⟨rhs.machine, ← binaryValue program.lang op lv rv⟩
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
    | _ => .error .unsupportedExpression

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
              let catches := catchType == some "any" || catchType == some "Exception" ||
                (match errorValue, catchType with
                  | .exception className _, some wanted => className == wanted
                  | _, _ => false)
              if catches then do
                let (updated, localFrame) ← match binder with
                  | none => .ok (attempted.machine, attempted.frame)
                  | some name =>
                      let (updated, ref) := allocCell attempted.machine errorValue true
                      let localFrame := { attempted.frame with locals := (name, ref) :: attempted.frame.locals }
                      .ok (updated, localFrame)
                execStmt fuel program updated localFrame handler
              else .ok attempted
          | _ => .ok attempted
        let finalized ← execStmt fuel program handled.machine handled.frame cleanup
        match finalized.control with
        | .normal => return ⟨finalized.machine, finalized.frame, handled.control⟩
        | _ => return finalized
    | _ => .error .unsupportedStatement

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

end

end Harmonia.Applications.Kadmos.Generated
