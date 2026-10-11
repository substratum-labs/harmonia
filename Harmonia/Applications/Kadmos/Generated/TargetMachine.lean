import Harmonia.Applications.Kadmos.Generated.TargetSyntax

set_option maxHeartbeats 1000000

namespace Harmonia.Applications.Kadmos.Generated

abbrev ObjRef := Nat
abbrev CellRef := Nat
abbrev ClosureRef := Nat

inductive NumberTag where | jsNumber | pyInt | pyFloat deriving DecidableEq, Repr

structure MatchValue where
  full : String
  start : Nat
  stop : Nat
  groups : List (Option String)
  deriving DecidableEq, Repr

inductive TargetValue where
  | undefined | null | bool (value : Bool) | string (value : String)
  | number (tag : NumberTag) (value : Int)
  | object (ref : ObjRef) | closure (ref : ClosureRef)
  | builtin (id : BuiltinId) | boundBuiltin (id : BuiltinId) (receiver : TargetValue)
  | regexMatch (value : MatchValue)
  | exception (className message : String)
  deriving DecidableEq, Repr

structure Descriptor where
  value : Option TargetValue
  get : Option ClosureRef
  set : Option ClosureRef
  enumerable : Bool
  writable : Bool
  configurable : Bool
  deriving DecidableEq, Repr

inductive ObjectKind where
  | jsOrdinary | jsArray | jsSet | jsPrototype | jsNullPrototype
  | pythonDict | pythonList | pythonTuple | pythonSet | mappingProxy
  | pythonOrdinary | regexPattern
  deriving DecidableEq, Repr

structure HeapObject where
  kind : ObjectKind
  prototype : Option ObjRef
  own : List (String × Descriptor)
  items : List TargetValue
  setMembers : List TargetValue
  frozen : Bool
  proxy : Bool
  deriving DecidableEq, Repr

structure TargetStore where
  state : String
  context : ObjRef
  history : ObjRef
  undo : Option ObjRef
  constructorSeed : Option ObjRef
  busy : Bool
  instanceAttrs : List (String × TargetValue)
  deriving DecidableEq, Repr

inductive ControlResult where
  | normal | returned (value : TargetValue)
  | broke (target : String) | continued (target : String)
  | raised (value : TargetValue)
  deriving DecidableEq, Repr

structure TargetFrame where
  qualifiedName : String
  remaining : List TargetStmt
  locals : List (String × CellRef)
  captures : List (String × CellRef)
  receiver : Option ObjRef
  control : ControlResult
  deriving DecidableEq, Repr

structure TargetClosure where
  qualifiedName : String
  params : List ParamSpec
  pythonDefaults : List (Option TargetValue)
  body : TargetStmt
  captures : List (String × CellRef)
  receiver : Option ObjRef
  deriving DecidableEq, Repr

structure TargetMachine where
  globals : List (String × CellRef)
  frames : List TargetFrame
  cells : List (CellRef × TargetValue)
  writableCells : List (CellRef × Bool)
  objects : List (ObjRef × HeapObject)
  closures : List (ClosureRef × TargetClosure)
  nextCell : CellRef
  nextObject : ObjRef
  nextClosure : ClosureRef
  objectPrototype : ObjRef
  checkerRef : ObjRef
  checker : TargetStore
  fuel : Nat
  deriving DecidableEq, Repr

def TargetMachine.empty : TargetMachine :=
  ⟨[], [], [], [], [(0, ⟨.jsPrototype, none, [], [], [], true, false⟩),
    (1, ⟨.pythonOrdinary, none, [], [], [], false, false⟩)], [], 0, 2, 0, 0, 1,
   ⟨"", 0, 0, none, none, false, []⟩, 0⟩

inductive TargetError where
  | danglingObject (ref : ObjRef)
  | danglingCell (ref : CellRef)
  | immutableCell (ref : CellRef)
  | invalidTag | wrongArity | badDescriptor | frozenObject
  | unsupportedHostPrimitive (id : BuiltinId)
  | unboundLocal (name : String)
  | unsupportedExpression
  | unsupportedStatement
  | badBinderCardinality
  | outsideNumericDomain
  | wrongControl | exhaustedFuel
  deriving DecidableEq, Repr

def objectAt (m : TargetMachine) (ref : ObjRef) : Except TargetError HeapObject :=
  match m.objects.lookup ref with
  | some o => .ok o
  | none => .error (.danglingObject ref)

def readCheckerField (m : TargetMachine) (name : String) :
    Except TargetError TargetValue :=
  if ["busy", "#busy", "_busy"].contains name then .ok (.bool m.checker.busy)
  else if ["state", "#state", "__state"].contains name then .ok (.string m.checker.state)
  else if ["context", "#context", "__context"].contains name then .ok (.object m.checker.context)
  else if ["history", "#history", "__history"].contains name then .ok (.object m.checker.history)
  else if ["undo", "#undo", "__undo"].contains name then
    .ok (m.checker.undo.map TargetValue.object |>.getD .null)
  else if ["constructorSeed", "#constructorSeed", "__constructor_seed"].contains name then
    .ok (m.checker.constructorSeed.map TargetValue.object |>.getD .null)
  else match m.checker.instanceAttrs.lookup name with
    | some v => .ok v
    | none => .error (.unboundLocal name)

def writeCheckerField (m : TargetMachine) (name : String) (value : TargetValue) :
    Except TargetError TargetMachine :=
  if ["busy", "#busy", "_busy"].contains name then
    match value with
    | .bool b => .ok { m with checker := { m.checker with busy := b } }
    | _ => .error .invalidTag
  else if ["state", "#state", "__state"].contains name then
    match value with
    | .string s => .ok { m with checker := { m.checker with state := s } }
    | _ => .error .invalidTag
  else if ["context", "#context", "__context"].contains name then
    match value with
    | .object ref => .ok { m with checker := { m.checker with context := ref } }
    | _ => .error .invalidTag
  else if ["history", "#history", "__history"].contains name then
    match value with
    | .object ref => .ok { m with checker := { m.checker with history := ref } }
    | _ => .error .invalidTag
  else if ["undo", "#undo", "__undo"].contains name then
    match value with
    | .null => .ok { m with checker := { m.checker with undo := none } }
    | .object ref => .ok { m with checker := { m.checker with undo := some ref } }
    | _ => .error .invalidTag
  else if ["constructorSeed", "#constructorSeed", "__constructor_seed"].contains name then
    match value with
    | .null => .ok { m with checker := { m.checker with constructorSeed := none } }
    | .object ref => .ok { m with checker := { m.checker with constructorSeed := some ref } }
    | _ => .error .invalidTag
  else
    let attrs := (name, value) :: m.checker.instanceAttrs.filter (fun entry => entry.1 != name)
    .ok { m with checker := { m.checker with instanceAttrs := attrs } }

def readCell (m : TargetMachine) (ref : CellRef) : Except TargetError TargetValue :=
  match m.cells.lookup ref with
  | some value => .ok value
  | none => .error (.danglingCell ref)

def writeCell (m : TargetMachine) (ref : CellRef) (value : TargetValue) :
    Except TargetError TargetMachine :=
  match m.cells.lookup ref with
  | none => .error (.danglingCell ref)
  | some _ => do
      if m.writableCells.lookup ref == some false then throw (.immutableCell ref)
      let cells := m.cells.map fun entry =>
        (entry.1, if entry.1 == ref then value else entry.2)
      .ok { m with cells := cells }

def allocCell (m : TargetMachine) (value : TargetValue) (mutable : Bool) :
    TargetMachine × CellRef :=
  let ref := m.nextCell
  let withValue := { m with cells := (ref, value) :: m.cells }
  let withPermission := { withValue with writableCells := (ref, mutable) :: m.writableCells }
  ({ withPermission with nextCell := ref + 1 }, ref)

def readOwn (m : TargetMachine) (ref : ObjRef) (key : String) :
    Except TargetError (Option Descriptor) := do
  let o ← objectAt m ref
  return o.own.lookup key

def replaceObject (m : TargetMachine) (ref : ObjRef) (value : HeapObject) :
    Except TargetError TargetMachine := do
  let _ ← objectAt m ref
  let objects := m.objects.map fun entry =>
    (entry.1, if entry.1 == ref then value else entry.2)
  return { m with objects := objects }

def writeOwn (m : TargetMachine) (ref : ObjRef) (key : String)
    (value : TargetValue) : Except TargetError TargetMachine := do
  let o ← objectAt m ref
  if o.frozen || o.kind == .mappingProxy then throw .frozenObject
  match o.own.lookup key with
  | some d =>
      if !d.writable || d.value.isNone then throw .badDescriptor
      let own := o.own.map fun entry =>
        (entry.1, if entry.1 == key then { d with value := some value } else entry.2)
      replaceObject m ref { o with own := own }
  | none =>
      let descriptor : Descriptor := ⟨some value, none, none, true, true, true⟩
      replaceObject m ref { o with own := o.own ++ [(key, descriptor)] }

def allocObject (m : TargetMachine) (o : HeapObject) : TargetMachine × ObjRef :=
  let ref := m.nextObject
  ({ m with objects := (ref, o) :: m.objects, nextObject := ref + 1 }, ref)

-- JS and Python use different container truth rules. This function has no
-- reference-model dependency, and malformed object references fail explicitly.
def sourceTruthy (lang : TargetLang) (m : TargetMachine)
    (value : TargetValue) : Except TargetError Bool :=
  match value with
  | .undefined | .null => .ok false
  | .bool b => .ok b
  | .number _ n => .ok (n != 0)
  | .string s => .ok (!s.isEmpty)
  | .closure _ | .builtin _ | .boundBuiltin _ _ | .regexMatch _ | .exception _ _ => .ok true
  | .object ref => do
      let o ← objectAt m ref
      if lang == .ts then return true
      match o.kind with
      | .pythonDict | .mappingProxy => return !o.own.isEmpty
      | .pythonList | .pythonTuple => return !o.items.isEmpty
      | .pythonSet => return !o.setMembers.isEmpty
      | _ => return true

end Harmonia.Applications.Kadmos.Generated
