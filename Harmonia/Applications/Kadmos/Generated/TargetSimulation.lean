import Harmonia.Applications.Kadmos.Generated.TargetSemantics

namespace Harmonia.Applications.Kadmos.Generated

/-- Unfueled execution configurations for scalar/property expressions, ordered
    object fields and arguments, supplied-parameter closure/host calls, and
    lexical/control statements. Remaining collection/default paths are separate. -/
inductive TargetFocus where
  | eval (expr : TargetExpr)
  | exec (stmt : TargetStmt)
  | objectFields (destination : ObjRef) (fields : TargetExpr)
  | arguments (args : TargetExpr)
  | argumentValues (values : List TargetValue)
  | invoke (ref : ClosureRef) (args : List TargetValue)
  | bindParams (params : List ParamSpec) (defaults : List (Option TargetValue))
      (args : List TargetValue) (body : TargetStmt)
  | value (value : TargetValue)
  | exit (control : ControlResult)
  deriving Repr

/-- Continuations own ordered children and pending statement actions. A
    finalizer saves the outcome control before a caught frame is cleared. -/
inductive ResumeFrame where
  | objectValue (destination : ObjRef) (key : String) (rest : TargetExpr)
  | property (key : String)
  | callCallee (args : TargetExpr)
  | callArguments (ref : ClosureRef)
  | hostArguments (id : BuiltinId) (receiver : Option TargetValue)
  | argumentHead (rest : TargetExpr)
  | argumentTail (value : TargetValue)
  | callReturn (caller : TargetFrame)
  | binaryLeft (op : BinaryOp) (right : TargetExpr)
  | binaryRight (op : BinaryOp) (left : TargetValue)
  | stmtIf (yes no : TargetStmt)
  | stmtSequence (rest : TargetStmt)
  | stmtReturn | stmtThrow
  | stmtAssignField (name : String)
  | stmtAssignPropertyReceiver (name : String) (value : TargetExpr)
  | stmtAssignPropertyValue (receiver : TargetValue) (name : String)
  | stmtLetLocal (name : String) (mutable : Bool)
  | stmtAssignLocal (name : String) (globals : List (String × CellRef))
  | stmtDoExpr
  | stmtProtect (catchType binder : Option String) (handler cleanup : TargetStmt)
  | stmtHandledFinally (cleanup : TargetStmt)
  | stmtFinally (saved : ControlResult)
  deriving Repr

structure TargetConfig where
  machine : TargetMachine
  frame : TargetFrame
  focus : TargetFocus
  continuation : List ResumeFrame
  deriving Repr

def exprResultFocus : Except TargetValue TargetValue → TargetFocus
  | .ok value => .value value
  | .error value => .exit (.raised value)

def integerValue (lang : TargetLang) (n : Int) : TargetValue :=
  .number (if lang == .ts then .jsNumber else .pyInt) n

/-- Fresh ordinary object/dict literal, before its source fields execute. -/
def literalObject (lang : TargetLang) (m : TargetMachine) : HeapObject :=
  ⟨(if lang == .ts then .jsOrdinary else .pythonDict),
    (if lang == .ts then some m.objectPrototype else none), [], [], [], false, false⟩

/-- Closure calls start with captured cell addresses and an empty local scope. -/
def closureFrame (closure : TargetClosure) : TargetFrame :=
  ⟨closure.qualifiedName, [], [], closure.captures, closure.receiver, .normal⟩

/-- Translate only the executed body's control; this does not execute code. -/
def closureResult (lang : TargetLang) (out : StmtOutcome) : Except TargetError ExprOutcome :=
  match out.control with
  | .returned value => .ok ⟨out.machine, .ok value⟩
  | .normal => .ok ⟨out.machine, .ok (if lang == .ts then .undefined else .null)⟩
  | .raised value => .ok ⟨out.machine, .error value⟩
  | _ => .error .wrongControl

/-- Explicitly provided arguments, with TS undefined-default selection excluded.
    Defaults remain recorded and advance in lockstep; no default is assumed. -/
inductive DepthBindsProvided (program : TargetProgram) : TargetMachine → TargetFrame →
    List ParamSpec → List (Option TargetValue) → List TargetValue →
    TargetMachine → TargetFrame → Nat → Prop where
  | empty {m f defaults} : DepthBindsProvided program m f [] defaults [] m f 0
  | cons {m f param params defaults value values final ff rank}
      (hn : (program.lang == .ts && (some value == some TargetValue.undefined)) = false)
      (ht : DepthBindsProvided program (allocCell m value true).1
        { f with locals := (param.name, m.nextCell) :: f.locals }
        params (defaults.drop 1) values final ff rank) :
      DepthBindsProvided program m f (param :: params) defaults (value :: values)
        final ff (1 + rank)

theorem bindProvided_adequate {program m f params defaults args final ff rank k}
    (h : DepthBindsProvided program m f params defaults args final ff rank)
    (hk : rank < k) :
    bindCallParams k program m f params defaults args = .ok ⟨final, ff, .ok ()⟩ := by
  induction h generalizing k with
  | empty =>
      cases k with
      | zero => exfalso; omega
      | succ k => simp [bindCallParams]
  | @cons m f param params defaults value values final ff rank hn ht ih =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hr : rank < k := by omega
          have ht : program.lang = .ts → value ≠ .undefined := by simpa using hn
          have hnot : ¬program.lang = .ts ∨ ¬value = .undefined := by
            by_cases hl : program.lang = .ts
            · exact .inr (ht hl)
            · exact .inl hl
          simpa [bindCallParams, hnot, allocCell, Bind.bind, Pure.pure, Except.bind,
            Except.pure] using ih hr

/-- These call targets dispatch through the basic host primitive rather than
    the iterable/generator or callback executor. -/
def DirectHostDispatch (id : BuiltinId) (receiver : Option TargetValue) : Prop :=
  match receiver with
  | none => id ≠ .next ∧ id ≠ .tuple ∧ id ≠ .list
  | some _ => id ≠ .arrayFind ∧ id ≠ .arraySome ∧ id ≠ .arrayMap

/-- Invalid property assignment still evaluates its RHS before reporting
    the source TypeError. This is a tag predicate, not an executor premise. -/
def NonObjectValue : TargetValue → Prop
  | .object _ => False
  | _ => True

/-- No evaluator or depth budget occurs in a transition premise. The binary
    primitive is the existing basic operation, never a generated helper body.
    Python list addition has allocation semantics and is outside this slice. -/
inductive SmallStep (program : TargetProgram) : TargetConfig → TargetConfig → Prop where
  | undefined {m f c} :
      SmallStep program ⟨m, f, .eval .undefined, c⟩ ⟨m, f, .value .undefined, c⟩
  | null {m f c} :
      SmallStep program ⟨m, f, .eval .null, c⟩ ⟨m, f, .value .null, c⟩
  | bool {m f c} (b : Bool) :
      SmallStep program ⟨m, f, .eval (.bool b), c⟩ ⟨m, f, .value (.bool b), c⟩
  | integer {m f c} (n : Int) :
      SmallStep program ⟨m, f, .eval (.integer n), c⟩
        ⟨m, f, .value (integerValue program.lang n), c⟩
  | string {m f c} (s : String) :
      SmallStep program ⟨m, f, .eval (.string s), c⟩ ⟨m, f, .value (.string s), c⟩
  | localRead {m f c name value} (h : localValue m f name = .ok value) :
      SmallStep program ⟨m, f, .eval (.local name), c⟩ ⟨m, f, .value value, c⟩
  | global {m f c name value} (h : localValue m f name = .ok value) :
      SmallStep program ⟨m, f, .eval (.global name), c⟩ ⟨m, f, .value value, c⟩
  | checkerField {m f c name value} (h : readCheckerField m name = .ok value) :
      SmallStep program ⟨m, f, .eval (.checkerField name), c⟩ ⟨m, f, .value value, c⟩
  | callEnter {m f c callee args} :
      SmallStep program ⟨m, f, .eval (.call callee args), c⟩
        ⟨m, f, .eval callee, .callCallee args :: c⟩
  | callCalleeRaised {m f c args value} :
      SmallStep program ⟨m, f, .exit (.raised value), .callCallee args :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | callClosureArgs {m f c ref args} :
      SmallStep program ⟨m, f, .value (.closure ref), .callCallee args :: c⟩
        ⟨m, f, .arguments args, .callArguments ref :: c⟩
  | callBuiltinArgs {m f c id args} :
      SmallStep program ⟨m, f, .value (.builtin id), .callCallee args :: c⟩
        ⟨m, f, .arguments args, .hostArguments id none :: c⟩
  | callBoundBuiltinArgs {m f c id receiver args} :
      SmallStep program ⟨m, f, .value (.boundBuiltin id receiver), .callCallee args :: c⟩
        ⟨m, f, .arguments args, .hostArguments id (some receiver) :: c⟩
  | hostArgsRaised {m f c id receiver value} :
      SmallStep program ⟨m, f, .exit (.raised value), .hostArguments id receiver :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | hostArgsFinish {m f c id receiver values out}
      (hi : DirectHostDispatch id receiver)
      (hh : hostCall program.lang m id receiver values = .ok out) :
      SmallStep program ⟨m, f, .argumentValues values, .hostArguments id receiver :: c⟩
        ⟨out.machine, f, exprResultFocus out.result, c⟩
  | argsEmpty {m f c} :
      SmallStep program ⟨m, f, .arguments .empty, c⟩ ⟨m, f, .argumentValues [], c⟩
  | argsCons {m f c first rest} :
      SmallStep program ⟨m, f, .arguments (.sequence first rest), c⟩
        ⟨m, f, .eval first, .argumentHead rest :: c⟩
  | argsHead {m f c value rest} :
      SmallStep program ⟨m, f, .value value, .argumentHead rest :: c⟩
        ⟨m, f, .arguments rest, .argumentTail value :: c⟩
  | argsTail {m f c value values} :
      SmallStep program ⟨m, f, .argumentValues values, .argumentTail value :: c⟩
        ⟨m, f, .argumentValues (value :: values), c⟩
  | argsHeadRaised {m f c rest value} :
      SmallStep program ⟨m, f, .exit (.raised value), .argumentHead rest :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | argsTailRaised {m f c head value} :
      SmallStep program ⟨m, f, .exit (.raised value), .argumentTail head :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | callArgsRaised {m f c ref value} :
      SmallStep program ⟨m, f, .exit (.raised value), .callArguments ref :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | callInvoke {m f c ref values} :
      SmallStep program ⟨m, f, .argumentValues values, .callArguments ref :: c⟩
        ⟨m, f, .invoke ref values, c⟩
  | closureEnter {m f c ref args closure}
      (hc : closureAt m ref = .ok closure) :
      SmallStep program ⟨m, f, .invoke ref args, c⟩
        ⟨m, closureFrame closure,
          .bindParams closure.params closure.pythonDefaults args closure.body,
          .callReturn f :: c⟩
  | paramsEmpty {m f c defaults body} :
      SmallStep program ⟨m, f, .bindParams [] defaults [] body, c⟩
        ⟨m, f, .exec body, c⟩
  | paramsCons {m f c param params defaults value values body}
      (hn : (program.lang == .ts && (some value == some TargetValue.undefined)) = false) :
      SmallStep program ⟨m, f, .bindParams (param :: params) defaults (value :: values) body, c⟩
        ⟨(allocCell m value true).1,
          { f with locals := (param.name, m.nextCell) :: f.locals },
          .bindParams params (defaults.drop 1) values body, c⟩
  | closureReturn {m f caller c control out}
      (hc : closureResult program.lang ⟨m, f, control⟩ = .ok out) :
      SmallStep program ⟨m, f, .exit control, .callReturn caller :: c⟩
        ⟨out.machine, caller, exprResultFocus out.result, c⟩
  | objectEnter {m f c fields} :
      SmallStep program ⟨m, f, .eval (.object fields), c⟩
        ⟨(allocObject m (literalObject program.lang m)).1, f,
          .objectFields m.nextObject fields, c⟩
  | objectEmpty {m f c ref} :
      SmallStep program ⟨m, f, .objectFields ref .empty, c⟩
        ⟨m, f, .value (.object ref), c⟩
  | objectEntry {m f c ref key value rest} :
      SmallStep program ⟨m, f, .objectFields ref (.objectEntry key value rest), c⟩
        ⟨m, f, .eval value, .objectValue ref key rest :: c⟩
  | objectWrite {m final f c ref key value rest}
      (hw : writeOwn m ref key value = .ok final) :
      SmallStep program ⟨m, f, .value value, .objectValue ref key rest :: c⟩
        ⟨final, f, .objectFields ref rest, c⟩
  | objectRaised {m f c ref key rest value} :
      SmallStep program ⟨m, f, .exit (.raised value), .objectValue ref key rest :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | propertyEnter {m f c receiver key} :
      SmallStep program ⟨m, f, .eval (.property receiver key), c⟩
        ⟨m, f, .eval receiver, .property key :: c⟩
  | propertyRaised {m f c key value} :
      SmallStep program ⟨m, f, .exit (.raised value), .property key :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | propertyFinish {m f c key receiver out}
      (hp : readPropertyValue program.lang m receiver key = .ok out) :
      SmallStep program ⟨m, f, .value receiver, .property key :: c⟩
        ⟨out.machine, f, exprResultFocus out.result, c⟩
  | binaryEnter {m f c op left right} :
      SmallStep program ⟨m, f, .eval (.binary op left right), c⟩
        ⟨m, f, .eval left, .binaryLeft op right :: c⟩
  | binaryNext {m f c op left right} :
      SmallStep program ⟨m, f, .value left, .binaryLeft op right :: c⟩
        ⟨m, f, .eval right, .binaryRight op left :: c⟩
  | binaryLeftRaised {m f c op right value} :
      SmallStep program ⟨m, f, .exit (.raised value), .binaryLeft op right :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | binaryRightRaised {m f c op left value} :
      SmallStep program ⟨m, f, .exit (.raised value), .binaryRight op left :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | binaryFinish {m f c op left right result}
      (hOp : op ≠ .add)
      (hApply : binaryValue program.lang m op left right = .ok result) :
      SmallStep program ⟨m, f, .value right, .binaryRight op left :: c⟩
        ⟨m, f, exprResultFocus result, c⟩

  | stmtLetLocalEnter {m f c name mutable expr} :
      SmallStep program ⟨m, f, .exec (.letLocal name mutable expr), c⟩
        ⟨m, f, .eval expr, .stmtLetLocal name mutable :: c⟩
  | stmtLetLocalFinish {m f c name mutable value} :
      SmallStep program ⟨m, f, .value value, .stmtLetLocal name mutable :: c⟩
        ⟨(allocCell m value mutable).1,
          { f with locals := (name, m.nextCell) :: f.locals }, .exit .normal, c⟩
  | stmtLetLocalRaised {m f c name mutable value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtLetLocal name mutable :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtAssignLocalEnter {m f c name expr} :
      SmallStep program ⟨m, f, .exec (.assign (.local name) expr), c⟩
        ⟨m, f, .eval expr, .stmtAssignLocal name m.globals :: c⟩
  | stmtAssignLocalFinish {m final f c name globals ref value}
      (hAddress : (f.locals.lookup name).orElse (fun _ =>
        (f.captures.lookup name).orElse (fun _ => globals.lookup name)) = some ref)
      (hWrite : writeCell m ref value = .ok final) :
      SmallStep program ⟨m, f, .value value, .stmtAssignLocal name globals :: c⟩
        ⟨final, f, .exit .normal, c⟩
  | stmtAssignPythonLocal {m f c name globals value}
      (hLang : program.lang = .python)
      (hAddress : (f.locals.lookup name).orElse (fun _ =>
        (f.captures.lookup name).orElse (fun _ => globals.lookup name)) = none) :
      SmallStep program ⟨m, f, .value value, .stmtAssignLocal name globals :: c⟩
        ⟨(allocCell m value true).1,
          { f with locals := (name, m.nextCell) :: f.locals }, .exit .normal, c⟩
  | stmtAssignLocalRaised {m f c name globals value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtAssignLocal name globals :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtAssignPropertyEnter {m f c receiver name expr} :
      SmallStep program ⟨m, f, .exec (.assign (.property receiver name) expr), c⟩
        ⟨m, f, .eval receiver, .stmtAssignPropertyReceiver name expr :: c⟩
  | stmtAssignPropertyReceiverFinish {m f c name expr value} :
      SmallStep program ⟨m, f, .value value, .stmtAssignPropertyReceiver name expr :: c⟩
        ⟨m, f, .eval expr, .stmtAssignPropertyValue value name :: c⟩
  | stmtAssignPropertyReceiverRaised {m f c name expr error} :
      SmallStep program ⟨m, f, .exit (.raised error), .stmtAssignPropertyReceiver name expr :: c⟩
        ⟨m, f, .exit (.raised error), c⟩
  | stmtAssignPropertyValueRaised {m f c name receiver error} :
      SmallStep program ⟨m, f, .exit (.raised error), .stmtAssignPropertyValue receiver name :: c⟩
        ⟨m, f, .exit (.raised error), c⟩
  | stmtAssignPropertyFinish {m final f c name ref value}
      (hWrite : (if ref == m.checkerRef then writeCheckerField m name value
        else writeOwn m ref name value) = .ok final) :
      SmallStep program ⟨m, f, .value value, .stmtAssignPropertyValue (.object ref) name :: c⟩
        ⟨final, f, .exit .normal, c⟩
  | stmtAssignPropertyInvalid {m f c name receiver value}
      (hTag : NonObjectValue receiver) :
      SmallStep program ⟨m, f, .value value, .stmtAssignPropertyValue receiver name :: c⟩
        ⟨m, f, .exit (.raised (.exception "TypeError" "invalid property assignment")), c⟩
  | stmtDoExprEnter {m f c expr} :
      SmallStep program ⟨m, f, .exec (.doExpr expr), c⟩
        ⟨m, f, .eval expr, .stmtDoExpr :: c⟩
  | stmtDoExprFinish {m f c value} :
      SmallStep program ⟨m, f, .value value, .stmtDoExpr :: c⟩
        ⟨m, f, .exit .normal, c⟩
  | stmtDoExprRaised {m f c value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtDoExpr :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtIfEnter {m f c cond yes no} :
      SmallStep program ⟨m, f, .exec (.ifThenElse cond yes no), c⟩
        ⟨m, f, .eval cond, .stmtIf yes no :: c⟩
  | stmtIfTrue {m f c yes no value}
      (h : sourceTruthy program.lang m value = .ok true) :
      SmallStep program ⟨m, f, .value value, .stmtIf yes no :: c⟩
        ⟨m, f, .exec yes, c⟩
  | stmtIfFalse {m f c yes no value}
      (h : sourceTruthy program.lang m value = .ok false) :
      SmallStep program ⟨m, f, .value value, .stmtIf yes no :: c⟩
        ⟨m, f, .exec no, c⟩
  | stmtIfRaised {m f c yes no value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtIf yes no :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtEmpty {m f c} :
      SmallStep program ⟨m, f, .exec .empty, c⟩ ⟨m, f, .exit .normal, c⟩
  | stmtNonlocalNames {m f c names}
      (h : names.all (fun name => (f.captures.lookup name).isSome) = true) :
      SmallStep program ⟨m, f, .exec (.nonlocalNames names), c⟩
        ⟨m, f, .exit .normal, c⟩
  | stmtSequence {m f c first rest} :
      SmallStep program ⟨m, f, .exec (.sequence first rest), c⟩
        ⟨m, f, .exec first, .stmtSequence rest :: c⟩
  | stmtSequenceNext {m f c rest} :
      SmallStep program ⟨m, f, .exit .normal, .stmtSequence rest :: c⟩
        ⟨m, f, .exec rest, c⟩
  | stmtSequenceExit {m f c rest control} (h : control ≠ .normal) :
      SmallStep program ⟨m, f, .exit control, .stmtSequence rest :: c⟩
        ⟨m, f, .exit control, c⟩
  | stmtReturnVoid {m f c} :
      SmallStep program ⟨m, f, .exec .returnVoid, c⟩
        ⟨m, f, .exit (.returned .undefined), c⟩
  | stmtReturnEnter {m f c expr} :
      SmallStep program ⟨m, f, .exec (.returnValue expr), c⟩
        ⟨m, f, .eval expr, .stmtReturn :: c⟩
  | stmtReturnFinish {m f c value} :
      SmallStep program ⟨m, f, .value value, .stmtReturn :: c⟩
        ⟨m, f, .exit (.returned value), c⟩
  | stmtReturnRaised {m f c value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtReturn :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtThrowEnter {m f c expr} :
      SmallStep program ⟨m, f, .exec (.throwValue expr), c⟩
        ⟨m, f, .eval expr, .stmtThrow :: c⟩
  | stmtThrowFinish {m f c value} :
      SmallStep program ⟨m, f, .value value, .stmtThrow :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtThrowRaised {m f c value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtThrow :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtRethrow {m f c value} (h : f.control = .raised value) :
      SmallStep program ⟨m, f, .exec .rethrow, c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtBreak {m f c label} :
      SmallStep program ⟨m, f, .exec (.breakTarget label), c⟩
        ⟨m, f, .exit (.broke label), c⟩
  | stmtContinue {m f c label} :
      SmallStep program ⟨m, f, .exec (.continueTarget label), c⟩
        ⟨m, f, .exit (.continued label), c⟩
  | stmtAssignFieldEnter {m f c name expr} :
      SmallStep program ⟨m, f, .exec (.assign (.field name) expr), c⟩
        ⟨m, f, .eval expr, .stmtAssignField name :: c⟩
  | stmtAssignFieldFinish {m final f c name value}
      (h : writeCheckerField m name value = .ok final) :
      SmallStep program ⟨m, f, .value value, .stmtAssignField name :: c⟩
        ⟨final, f, .exit .normal, c⟩
  | stmtAssignFieldRaised {m f c name value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtAssignField name :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtProtectEnter {m f c body catchType binder handler cleanup} :
      SmallStep program ⟨m, f, .exec (.tryCatchFinally body catchType binder handler cleanup), c⟩
        ⟨m, f, .exec body, .stmtProtect catchType binder handler cleanup :: c⟩
  | stmtProtectUncaught {m f c control catchType binder handler cleanup}
      (h : controlCaught catchType control = false) :
      SmallStep program ⟨m, f, .exit control, .stmtProtect catchType binder handler cleanup :: c⟩
        ⟨m, f, .exec cleanup, .stmtFinally control :: c⟩
  | stmtProtectCaught {m f c errorValue catchType binder handler cleanup}
      (h : controlCaught catchType (.raised errorValue) = true) :
      SmallStep program
        ⟨m, f, .exit (.raised errorValue), .stmtProtect catchType binder handler cleanup :: c⟩
        ⟨(bindCatchFrame m f binder errorValue).1,
          (bindCatchFrame m f binder errorValue).2,
          .exec handler, .stmtHandledFinally cleanup :: c⟩
  | stmtHandlerExit {m f c control cleanup} :
      SmallStep program ⟨m, f, .exit control, .stmtHandledFinally cleanup :: c⟩
        ⟨m, { f with control := .normal }, .exec cleanup, .stmtFinally control :: c⟩
  | stmtFinallyNormal {m f c saved} :
      SmallStep program ⟨m, f, .exit .normal, .stmtFinally saved :: c⟩
        ⟨m, f, .exit saved, c⟩
  | stmtFinallyOverride {m f c saved control} (h : control ≠ .normal) :
      SmallStep program ⟨m, f, .exit control, .stmtFinally saved :: c⟩
        ⟨m, f, .exit control, c⟩

inductive Runs (program : TargetProgram) : TargetConfig → TargetConfig → Prop where
  | refl (config) : Runs program config config
  | tail {first middle last} : Runs program first middle →
      SmallStep program middle last → Runs program first last

theorem Runs.single {program first last} (h : SmallStep program first last) :
    Runs program first last := .tail (.refl first) h

theorem Runs.trans {program first middle last}
    (hFirst : Runs program first middle) (hLast : Runs program middle last) :
    Runs program first last := by
  induction hLast with
  | refl => exact hFirst
  | tail _ hStep ih => exact .tail ih hStep

/-- A separately indexed diagnostic trace count. Counting is relational:
    Prop-valued Runs proofs cannot be eliminated into a Nat function. The count
    is never an executable fuel premise and never uses TargetMachine.fuel. -/
inductive CountedRuns (program : TargetProgram) :
    TargetConfig → TargetConfig → Nat → Prop where
  | refl (config) : CountedRuns program config config 0
  | tail {first middle last n} : CountedRuns program first middle n →
      SmallStep program middle last → CountedRuns program first last (n + 1)

theorem CountedRuns.single {program first last} (h : SmallStep program first last) :
    CountedRuns program first last 1 := .tail (.refl first) h

theorem CountedRuns.trans {program first middle last n m}
    (hFirst : CountedRuns program first middle n)
    (hLast : CountedRuns program middle last m) :
    CountedRuns program first last (n + m) := by
  induction hLast with
  | refl => simpa using hFirst
  | tail _ step ih => simpa [Nat.add_assoc] using CountedRuns.tail ih step

theorem CountedRuns.forget {program first last n}
    (h : CountedRuns program first last n) : Runs program first last := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact .tail ih step

def ExprRuns (program : TargetProgram) (machine : TargetMachine)
    (frame : TargetFrame) (expr : TargetExpr) (outcome : ExprOutcome) : Prop :=
  Runs program ⟨machine, frame, .eval expr, []⟩
    ⟨outcome.machine, frame, exprResultFocus outcome.result, []⟩

theorem provided_path_runs {program m f params defaults args final ff rank}
    (h : DepthBindsProvided program m f params defaults args final ff rank)
    (body : TargetStmt) (c : List ResumeFrame) :
    Runs program ⟨m, f, .bindParams params defaults args body, c⟩
      ⟨final, ff, .exec body, c⟩ := by
  induction h with
  | empty => exact .single .paramsEmpty
  | cons hn ht ih => exact (Runs.single (.paramsCons hn)).trans ih

def argsResultFocus : Except TargetValue (List TargetValue) → TargetFocus
  | .ok values => .argumentValues values
  | .error value => .exit (.raised value)

mutual
/-- Semantic derivations, independent of evaluator success. Sibling children
    share the predecessor depth: their maximum, not their sum, determines rank.
    This relation does not assert coverage of all syntax. -/
inductive DepthDerivesExpr (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetExpr → ExprOutcome → Nat → Prop where
  | undefined {m f} : DepthDerivesExpr program m f .undefined ⟨m, .ok .undefined⟩ 0
  | null {m f} : DepthDerivesExpr program m f .null ⟨m, .ok .null⟩ 0
  | bool {m f} (b : Bool) : DepthDerivesExpr program m f (.bool b) ⟨m, .ok (.bool b)⟩ 0
  | integer {m f} (n : Int) : DepthDerivesExpr program m f (.integer n)
      ⟨m, .ok (integerValue program.lang n)⟩ 0
  | string {m f} (s : String) : DepthDerivesExpr program m f (.string s) ⟨m, .ok (.string s)⟩ 0
  | localRead {m f name value} (h : localValue m f name = .ok value) :
      DepthDerivesExpr program m f (.local name) ⟨m, .ok value⟩ 0
  | global {m f name value} (h : localValue m f name = .ok value) :
      DepthDerivesExpr program m f (.global name) ⟨m, .ok value⟩ 0
  | checkerField {m f name value} (h : readCheckerField m name = .ok value) :
      DepthDerivesExpr program m f (.checkerField name) ⟨m, .ok value⟩ 0
  | callCalleeRaised {m f callee args final value rank}
      (he : DepthDerivesExpr program m f callee ⟨final, .error value⟩ rank) :
      DepthDerivesExpr program m f (.call callee args) ⟨final, .error value⟩ (1 + rank)
  | callArgsRaised {m f callee args middle final ref value re ra}
      (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.closure ref)⟩ re)
      (ha : DepthDerivesArgs program middle f args ⟨final, .error value⟩ ra) :
      DepthDerivesExpr program m f (.call callee args) ⟨final, .error value⟩ (1 + max re ra)
  | callBuiltin {m f callee args middle final id values out re ra}
      (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.builtin id)⟩ re)
      (ha : DepthDerivesArgs program middle f args ⟨final, .ok values⟩ ra)
      (hi : id ≠ .next ∧ id ≠ .tuple ∧ id ≠ .list)
      (hh : hostCall program.lang final id none values = .ok out) :
      DepthDerivesExpr program m f (.call callee args) out (1 + max re ra)
  | callBoundBuiltin {m f callee args middle final id receiver values out re ra}
      (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.boundBuiltin id receiver)⟩ re)
      (ha : DepthDerivesArgs program middle f args ⟨final, .ok values⟩ ra)
      (hi : id ≠ .arrayFind ∧ id ≠ .arraySome ∧ id ≠ .arrayMap)
      (hh : hostCall program.lang final id (some receiver) values = .ok out) :
      DepthDerivesExpr program m f (.call callee args) out (1 + max re ra)
  | callBuiltinArgsRaised {m f callee args middle final id value re ra}
      (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.builtin id)⟩ re)
      (ha : DepthDerivesArgs program middle f args ⟨final, .error value⟩ ra) :
      DepthDerivesExpr program m f (.call callee args) ⟨final, .error value⟩ (1 + max re ra)
  | callBoundArgsRaised {m f callee args middle final id receiver value re ra}
      (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.boundBuiltin id receiver)⟩ re)
      (ha : DepthDerivesArgs program middle f args ⟨final, .error value⟩ ra) :
      DepthDerivesExpr program m f (.call callee args) ⟨final, .error value⟩ (1 + max re ra)
  | callClosure {m f callee args middle bound final ff ref values closure executed out re ra rp rb}
      (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.closure ref)⟩ re)
      (ha : DepthDerivesArgs program middle f args ⟨bound, .ok values⟩ ra)
      (hc : closureAt bound ref = .ok closure)
      (hp : DepthBindsProvided program bound (closureFrame closure) closure.params
        closure.pythonDefaults values final ff rp)
      (hb : DepthDerivesStmt program final ff closure.body executed rb)
      (ho : closureResult program.lang executed = .ok out) :
      DepthDerivesExpr program m f (.call callee args) out
        (1 + max re (max ra (max rp rb)))
  | objectFields {m f fields out rank}
      (hf : DepthDerivesFields program (allocObject m (literalObject program.lang m)).1
        f m.nextObject fields out rank) :
      DepthDerivesExpr program m f (.object fields) out (1 + rank)
  | objectEmpty {m f} :
      DepthDerivesExpr program m f (.object .empty)
        ⟨(allocObject m (literalObject program.lang m)).1, .ok (.object m.nextObject)⟩ 1
  | objectOne {m f key expr middle final value rank}
      (he : DepthDerivesExpr program (allocObject m (literalObject program.lang m)).1
        f expr ⟨middle, .ok value⟩ rank)
      (hw : writeOwn middle m.nextObject key value = .ok final) :
      DepthDerivesExpr program m f (.object (.objectEntry key expr .empty))
        ⟨final, .ok (.object m.nextObject)⟩ (2 + rank)
  | objectOneRaised {m f key expr final value rank}
      (he : DepthDerivesExpr program (allocObject m (literalObject program.lang m)).1
        f expr ⟨final, .error value⟩ rank) :
      DepthDerivesExpr program m f (.object (.objectEntry key expr .empty))
        ⟨final, .error value⟩ (2 + rank)
  | propertyRaised {m f receiver key final value rank}
      (he : DepthDerivesExpr program m f receiver ⟨final, .error value⟩ rank) :
      DepthDerivesExpr program m f (.property receiver key) ⟨final, .error value⟩ (1 + rank)
  | property {m f receiver key middle value out rank}
      (he : DepthDerivesExpr program m f receiver ⟨middle, .ok value⟩ rank)
      (hp : readPropertyValue program.lang middle value key = .ok out) :
      DepthDerivesExpr program m f (.property receiver key) out (1 + rank)
  | binaryLeftRaised {m f left right op final value rank}
      (hLeft : DepthDerivesExpr program m f left ⟨final, .error value⟩ rank) :
      DepthDerivesExpr program m f (.binary op left right) ⟨final, .error value⟩ (1 + rank)
  | binaryRightRaised {m f left right op middle final lv value leftRank rightRank}
      (hLeft : DepthDerivesExpr program m f left ⟨middle, .ok lv⟩ leftRank)
      (hRight : DepthDerivesExpr program middle f right ⟨final, .error value⟩ rightRank) :
      DepthDerivesExpr program m f (.binary op left right) ⟨final, .error value⟩
        (1 + max leftRank rightRank)
  | binary {m f left right op middle final lv rv result leftRank rightRank}
      (hOp : op ≠ .add)
      (hLeft : DepthDerivesExpr program m f left ⟨middle, .ok lv⟩ leftRank)
      (hRight : DepthDerivesExpr program middle f right ⟨final, .ok rv⟩ rightRank)
      (hApply : binaryValue program.lang final op lv rv = .ok result) :
      DepthDerivesExpr program m f (.binary op left right) ⟨final, result⟩
        (1 + max leftRank rightRank)

inductive DepthDerivesFields (program : TargetProgram) :
    TargetMachine → TargetFrame → ObjRef → TargetExpr → ExprOutcome → Nat → Prop where
  | empty {m f ref} : DepthDerivesFields program m f ref .empty ⟨m, .ok (.object ref)⟩ 0
  | raised {m f ref key expr rest final value rank}
      (he : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesFields program m f ref (.objectEntry key expr rest)
        ⟨final, .error value⟩ (1 + rank)
  | entry {m f ref key expr rest middle updated value out re rf}
      (he : DepthDerivesExpr program m f expr ⟨middle, .ok value⟩ re)
      (hw : writeOwn middle ref key value = .ok updated)
      (hf : DepthDerivesFields program updated f ref rest out rf) :
      DepthDerivesFields program m f ref (.objectEntry key expr rest) out (1 + max re rf)

inductive DepthDerivesArgs (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetExpr → ArgsOutcome → Nat → Prop where
  | empty {m f} : DepthDerivesArgs program m f .empty ⟨m, .ok []⟩ 0
  | headRaised {m f first rest final value rank}
      (he : DepthDerivesExpr program m f first ⟨final, .error value⟩ rank) :
      DepthDerivesArgs program m f (.sequence first rest) ⟨final, .error value⟩ (1 + rank)
  | tailRaised {m f first rest middle final value error re ra}
      (he : DepthDerivesExpr program m f first ⟨middle, .ok value⟩ re)
      (ha : DepthDerivesArgs program middle f rest ⟨final, .error error⟩ ra) :
      DepthDerivesArgs program m f (.sequence first rest) ⟨final, .error error⟩ (1 + max re ra)
  | cons {m f first rest middle final value values re ra}
      (he : DepthDerivesExpr program m f first ⟨middle, .ok value⟩ re)
      (ha : DepthDerivesArgs program middle f rest ⟨final, .ok values⟩ ra) :
      DepthDerivesArgs program m f (.sequence first rest) ⟨final, .ok (value :: values)⟩
        (1 + max re ra)

/-- Ranked statement derivations. Each recursive sequence tail is a depth edge;
    first/rest, body/cleanup and expression siblings share predecessor fuel. -/
inductive DepthDerivesStmt (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetStmt → StmtOutcome → Nat → Prop where
  | letLocal {m f name mutable expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank) :
      DepthDerivesStmt program m f (.letLocal name mutable expr)
        ⟨(allocCell final value mutable).1,
          { f with locals := (name, final.nextCell) :: f.locals }, .normal⟩ (1 + rank)
  | letLocalRaised {m f name mutable expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.letLocal name mutable expr)
        ⟨final, f, .raised value⟩ (1 + rank)
  | assignLocal {m f name expr middle final value ref rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨middle, .ok value⟩ rank)
      (hAddress : (f.locals.lookup name).orElse (fun _ =>
        (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) = some ref)
      (hWrite : writeCell middle ref value = .ok final) :
      DepthDerivesStmt program m f (.assign (.local name) expr)
        ⟨final, f, .normal⟩ (1 + rank)
  | assignPythonLocal {m f name expr final value rank}
      (hLang : program.lang = .python)
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank)
      (hAddress : (f.locals.lookup name).orElse (fun _ =>
        (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) = none) :
      DepthDerivesStmt program m f (.assign (.local name) expr)
        ⟨(allocCell final value true).1,
          { f with locals := (name, final.nextCell) :: f.locals }, .normal⟩ (1 + rank)
  | assignLocalRaised {m f name expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.assign (.local name) expr)
        ⟨final, f, .raised value⟩ (1 + rank)
  | assignProperty {m f receiver name expr middle written final ref value rr rv}
      (hReceiver : DepthDerivesExpr program m f receiver ⟨middle, .ok (.object ref)⟩ rr)
      (hValue : DepthDerivesExpr program middle f expr ⟨written, .ok value⟩ rv)
      (hWrite : (if ref == written.checkerRef then writeCheckerField written name value
        else writeOwn written ref name value) = .ok final) :
      DepthDerivesStmt program m f (.assign (.property receiver name) expr)
        ⟨final, f, .normal⟩ (1 + max rr rv)
  | assignPropertyReceiverRaised {m f receiver name expr final error rank}
      (hReceiver : DepthDerivesExpr program m f receiver ⟨final, .error error⟩ rank) :
      DepthDerivesStmt program m f (.assign (.property receiver name) expr)
        ⟨final, f, .raised error⟩ (1 + rank)
  | assignPropertyValueRaised {m f receiver name expr middle final base error rr rv}
      (hReceiver : DepthDerivesExpr program m f receiver ⟨middle, .ok base⟩ rr)
      (hValue : DepthDerivesExpr program middle f expr ⟨final, .error error⟩ rv) :
      DepthDerivesStmt program m f (.assign (.property receiver name) expr)
        ⟨final, f, .raised error⟩ (1 + max rr rv)
  | assignPropertyInvalid {m f receiver name expr middle final base value rr rv}
      (hReceiver : DepthDerivesExpr program m f receiver ⟨middle, .ok base⟩ rr)
      (hValue : DepthDerivesExpr program middle f expr ⟨final, .ok value⟩ rv)
      (hTag : NonObjectValue base) :
      DepthDerivesStmt program m f (.assign (.property receiver name) expr)
        ⟨final, f, .raised (.exception "TypeError" "invalid property assignment")⟩
        (1 + max rr rv)
  | doExpr {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank) :
      DepthDerivesStmt program m f (.doExpr expr) ⟨final, f, .normal⟩ (1 + rank)
  | doExprRaised {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.doExpr expr) ⟨final, f, .raised value⟩ (1 + rank)
  | ifTrue {m f cond yes no middle value out rCond rBranch}
      (hCond : DepthDerivesExpr program m f cond ⟨middle, .ok value⟩ rCond)
      (hTruth : sourceTruthy program.lang middle value = .ok true)
      (hBranch : DepthDerivesStmt program middle f yes out rBranch) :
      DepthDerivesStmt program m f (.ifThenElse cond yes no) out
        (1 + max rCond rBranch)
  | ifFalse {m f cond yes no middle value out rCond rBranch}
      (hCond : DepthDerivesExpr program m f cond ⟨middle, .ok value⟩ rCond)
      (hTruth : sourceTruthy program.lang middle value = .ok false)
      (hBranch : DepthDerivesStmt program middle f no out rBranch) :
      DepthDerivesStmt program m f (.ifThenElse cond yes no) out
        (1 + max rCond rBranch)
  | ifRaised {m f cond yes no final value rank}
      (hCond : DepthDerivesExpr program m f cond ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.ifThenElse cond yes no)
        ⟨final, f, .raised value⟩ (1 + rank)
  | empty {m f} : DepthDerivesStmt program m f .empty ⟨m, f, .normal⟩ 0
  | nonlocalNames {m f names}
      (h : names.all (fun name => (f.captures.lookup name).isSome) = true) :
      DepthDerivesStmt program m f (.nonlocalNames names) ⟨m, f, .normal⟩ 0
  | returnVoid {m f} :
      DepthDerivesStmt program m f .returnVoid ⟨m, f, .returned .undefined⟩ 0
  | breakTarget {m f} (label : String) :
      DepthDerivesStmt program m f (.breakTarget label) ⟨m, f, .broke label⟩ 0
  | continueTarget {m f} (label : String) :
      DepthDerivesStmt program m f (.continueTarget label) ⟨m, f, .continued label⟩ 0
  | rethrow {m f value} (h : f.control = .raised value) :
      DepthDerivesStmt program m f .rethrow ⟨m, f, .raised value⟩ 0
  | sequenceNormal {m f first rest middle midFrame final rankFirst rankRest}
      (hFirst : DepthDerivesStmt program m f first ⟨middle, midFrame, .normal⟩ rankFirst)
      (hRest : DepthDerivesStmt program middle midFrame rest final rankRest) :
      DepthDerivesStmt program m f (.sequence first rest) final (1 + max rankFirst rankRest)
  | sequenceExit {m f first rest out rank}
      (hFirst : DepthDerivesStmt program m f first out rank)
      (hExit : out.control ≠ .normal) :
      DepthDerivesStmt program m f (.sequence first rest) out (1 + rank)
  | returnValue {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank) :
      DepthDerivesStmt program m f (.returnValue expr) ⟨final, f, .returned value⟩ (1 + rank)
  | returnRaised {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.returnValue expr) ⟨final, f, .raised value⟩ (1 + rank)
  | throwValue {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank) :
      DepthDerivesStmt program m f (.throwValue expr) ⟨final, f, .raised value⟩ (1 + rank)
  | throwRaised {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.throwValue expr) ⟨final, f, .raised value⟩ (1 + rank)
  | assignField {m f name expr middle final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨middle, .ok value⟩ rank)
      (hWrite : writeCheckerField middle name value = .ok final) :
      DepthDerivesStmt program m f (.assign (.field name) expr) ⟨final, f, .normal⟩ (1 + rank)
  | assignFieldRaised {m f name expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.assign (.field name) expr) ⟨final, f, .raised value⟩ (1 + rank)
  | finallyNormal {m f body catchType binder handler cleanup attempted final finalFrame rb rc}
      (hBody : DepthDerivesStmt program m f body attempted rb)
      (hUncaught : controlCaught catchType attempted.control = false)
      (hCleanup : DepthDerivesStmt program attempted.machine attempted.frame cleanup
        ⟨final, finalFrame, .normal⟩ rc) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        ⟨final, finalFrame, attempted.control⟩ (1 + max rb rc)
  | finallyOverride {m f body catchType binder handler cleanup attempted final rb rc}
      (hBody : DepthDerivesStmt program m f body attempted rb)
      (hUncaught : controlCaught catchType attempted.control = false)
      (hCleanup : DepthDerivesStmt program attempted.machine attempted.frame cleanup final rc)
      (hExit : final.control ≠ .normal) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        final (1 + max rb rc)

  | caughtFinallyNormal {m f body catchType binder handler cleanup middle midFrame errorValue
      handled final finalFrame rb rh rc}
      (hBody : DepthDerivesStmt program m f body ⟨middle, midFrame, .raised errorValue⟩ rb)
      (hCaught : controlCaught catchType (.raised errorValue) = true)
      (hHandler : DepthDerivesStmt program (bindCatchFrame middle midFrame binder errorValue).1
        (bindCatchFrame middle midFrame binder errorValue).2 handler handled rh)
      (hCleanup : DepthDerivesStmt program handled.machine
        { handled.frame with control := .normal } cleanup ⟨final, finalFrame, .normal⟩ rc) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        ⟨final, finalFrame, handled.control⟩ (1 + max rb (max rh rc))
  | caughtFinallyOverride {m f body catchType binder handler cleanup middle midFrame errorValue
      handled final rb rh rc}
      (hBody : DepthDerivesStmt program m f body ⟨middle, midFrame, .raised errorValue⟩ rb)
      (hCaught : controlCaught catchType (.raised errorValue) = true)
      (hHandler : DepthDerivesStmt program (bindCatchFrame middle midFrame binder errorValue).1
        (bindCatchFrame middle midFrame binder errorValue).2 handler handled rh)
      (hCleanup : DepthDerivesStmt program handled.machine
        { handled.frame with control := .normal } cleanup final rc)
      (hExit : final.control ≠ .normal) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        final (1 + max rb (max rh rc))

end

def StmtRuns (program : TargetProgram) (machine : TargetMachine) (frame : TargetFrame)
    (stmt : TargetStmt) (outcome : StmtOutcome) : Prop :=
  Runs program ⟨machine, frame, .exec stmt, []⟩
    ⟨outcome.machine, outcome.frame, .exit outcome.control, []⟩

mutual
theorem expr_path_runs_cont {program machine frame expr outcome rank}
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (continuation : List ResumeFrame) :
    Runs program ⟨machine, frame, .eval expr, continuation⟩
      ⟨outcome.machine, frame, exprResultFocus outcome.result, continuation⟩ := by
  cases h with
  | undefined => exact Runs.single .undefined
  | null => exact Runs.single .null
  | bool b => exact Runs.single (.bool b)
  | integer n => exact Runs.single (.integer n)
  | string s => exact Runs.single (.string s)
  | localRead h => exact .single (.localRead h)
  | global h => exact .single (.global h)
  | checkerField h => exact .single (.checkerField h)
  | callCalleeRaised he =>
      exact ((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail .callCalleeRaised
  | callArgsRaised he ha =>
      exact ((((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail
        .callClosureArgs).trans (args_path_runs_cont ha _)).tail .callArgsRaised
  | callBuiltin he ha hi hh =>
      exact ((((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail
        .callBuiltinArgs).trans (args_path_runs_cont ha _)).tail (.hostArgsFinish hi hh)
  | callBoundBuiltin he ha hi hh =>
      exact ((((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail
        .callBoundBuiltinArgs).trans (args_path_runs_cont ha _)).tail (.hostArgsFinish hi hh)
  | callBuiltinArgsRaised he ha =>
      exact ((((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail
        .callBuiltinArgs).trans (args_path_runs_cont ha _)).tail .hostArgsRaised
  | callBoundArgsRaised he ha =>
      exact ((((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail
        .callBoundBuiltinArgs).trans (args_path_runs_cont ha _)).tail .hostArgsRaised
  | callClosure he ha hc hp hb ho =>
      exact ((((((((Runs.single .callEnter).trans (expr_path_runs_cont he _)).tail
        .callClosureArgs).trans (args_path_runs_cont ha _)).tail .callInvoke).tail
          (.closureEnter hc)).trans (provided_path_runs hp _ _)).trans
            (stmt_path_runs_cont hb _)).tail (.closureReturn ho)
  | objectFields hf =>
      exact (Runs.single .objectEnter).trans (fields_path_runs_cont hf _)
  | objectEmpty => exact (Runs.single .objectEnter).tail .objectEmpty
  | objectOne he hw =>
      exact ((((Runs.single .objectEnter).tail .objectEntry).trans ((expr_path_runs_cont he) _)).tail
        (.objectWrite hw)).tail .objectEmpty
  | objectOneRaised he =>
      exact (((Runs.single .objectEnter).tail .objectEntry).trans ((expr_path_runs_cont he) _)).tail .objectRaised
  | propertyRaised he =>
      exact ((Runs.single .propertyEnter).trans ((expr_path_runs_cont he) _)).tail .propertyRaised
  | property he hp =>
      exact ((Runs.single .propertyEnter).trans ((expr_path_runs_cont he) _)).tail (.propertyFinish hp)
  | binaryLeftRaised hLeft =>
      exact ((Runs.single .binaryEnter).trans ((expr_path_runs_cont hLeft) _)).tail .binaryLeftRaised
  | binaryRightRaised hLeft hRight =>
      exact (((Runs.single .binaryEnter).trans ((expr_path_runs_cont hLeft) _)).tail
        .binaryNext |>.trans ((expr_path_runs_cont hRight) _)).tail .binaryRightRaised
  | binary hOp hLeft hRight hApply =>
      exact (((Runs.single .binaryEnter).trans ((expr_path_runs_cont hLeft) _)).tail
        .binaryNext |>.trans ((expr_path_runs_cont hRight) _)).tail (.binaryFinish hOp hApply)
termination_by rank
decreasing_by all_goals omega

theorem fields_path_runs_cont {program m f ref fields out rank}
    (h : DepthDerivesFields program m f ref fields out rank) (c : List ResumeFrame) :
    Runs program ⟨m, f, .objectFields ref fields, c⟩
      ⟨out.machine, f, exprResultFocus out.result, c⟩ := by
  cases h with
  | empty => exact .single .objectEmpty
  | raised he =>
      exact ((Runs.single .objectEntry).trans (expr_path_runs_cont he _)).tail .objectRaised
  | entry he hw hf =>
      exact (((Runs.single .objectEntry).trans (expr_path_runs_cont he _)).tail
        (.objectWrite hw)).trans (fields_path_runs_cont hf _)
termination_by rank
decreasing_by all_goals omega

theorem args_path_runs_cont {program m f args out rank}
    (h : DepthDerivesArgs program m f args out rank) (c : List ResumeFrame) :
    Runs program ⟨m, f, .arguments args, c⟩
      ⟨out.machine, f, argsResultFocus out.result, c⟩ := by
  cases h with
  | empty => exact .single .argsEmpty
  | headRaised he =>
      exact ((Runs.single .argsCons).trans (expr_path_runs_cont he _)).tail .argsHeadRaised
  | tailRaised he ha =>
      exact ((((Runs.single .argsCons).trans (expr_path_runs_cont he _)).tail
        .argsHead).trans (args_path_runs_cont ha _)).tail .argsTailRaised
  | cons he ha =>
      exact ((((Runs.single .argsCons).trans (expr_path_runs_cont he _)).tail
        .argsHead).trans (args_path_runs_cont ha _)).tail .argsTail
termination_by rank
decreasing_by all_goals omega

theorem stmt_path_runs_cont {program machine frame stmt outcome rank}
    (h : DepthDerivesStmt program machine frame stmt outcome rank)
    (continuation : List ResumeFrame) :
    Runs program ⟨machine, frame, .exec stmt, continuation⟩
      ⟨outcome.machine, outcome.frame, .exit outcome.control, continuation⟩ := by
  cases h with
  | letLocal he =>
      exact ((Runs.single .stmtLetLocalEnter).trans (expr_path_runs_cont he _)).trans
        (.single .stmtLetLocalFinish)
  | letLocalRaised he =>
      exact ((Runs.single .stmtLetLocalEnter).trans (expr_path_runs_cont he _)).trans
        (.single .stmtLetLocalRaised)
  | assignLocal he ha hw =>
      exact ((Runs.single .stmtAssignLocalEnter).trans (expr_path_runs_cont he _)).trans
        (.single (.stmtAssignLocalFinish ha hw))
  | assignPythonLocal hl he ha =>
      exact ((Runs.single .stmtAssignLocalEnter).trans (expr_path_runs_cont he _)).trans
        (.single (.stmtAssignPythonLocal hl ha))
  | assignLocalRaised he =>
      exact ((Runs.single .stmtAssignLocalEnter).trans (expr_path_runs_cont he _)).trans
        (.single .stmtAssignLocalRaised)
  | assignProperty hr hv hw =>
      exact ((((Runs.single .stmtAssignPropertyEnter).trans
        (expr_path_runs_cont hr _)).trans (.single .stmtAssignPropertyReceiverFinish)).trans
          (expr_path_runs_cont hv _)).trans (.single (.stmtAssignPropertyFinish hw))
  | assignPropertyReceiverRaised hr =>
      exact ((Runs.single .stmtAssignPropertyEnter).trans
        (expr_path_runs_cont hr _)).trans (.single .stmtAssignPropertyReceiverRaised)
  | assignPropertyValueRaised hr hv =>
      exact ((((Runs.single .stmtAssignPropertyEnter).trans
        (expr_path_runs_cont hr _)).trans (.single .stmtAssignPropertyReceiverFinish)).trans
          (expr_path_runs_cont hv _)).trans (.single .stmtAssignPropertyValueRaised)
  | assignPropertyInvalid hr hv ht =>
      exact ((((Runs.single .stmtAssignPropertyEnter).trans
        (expr_path_runs_cont hr _)).trans (.single .stmtAssignPropertyReceiverFinish)).trans
          (expr_path_runs_cont hv _)).trans (.single (.stmtAssignPropertyInvalid ht))
  | doExpr he =>
      exact ((Runs.single .stmtDoExprEnter).trans (expr_path_runs_cont he _)).trans
        (.single .stmtDoExprFinish)
  | doExprRaised he =>
      exact ((Runs.single .stmtDoExprEnter).trans (expr_path_runs_cont he _)).trans
        (.single .stmtDoExprRaised)
  | ifTrue hc ht hb =>
      exact (((Runs.single .stmtIfEnter).trans (expr_path_runs_cont hc _)).trans
        (.single (.stmtIfTrue ht))).trans ((stmt_path_runs_cont hb) _)
  | ifFalse hc ht hb =>
      exact (((Runs.single .stmtIfEnter).trans (expr_path_runs_cont hc _)).trans
        (.single (.stmtIfFalse ht))).trans ((stmt_path_runs_cont hb) _)
  | ifRaised hc =>
      exact ((Runs.single .stmtIfEnter).trans (expr_path_runs_cont hc _)).trans
        (.single .stmtIfRaised)
  | empty => exact .single .stmtEmpty
  | nonlocalNames h => exact .single (.stmtNonlocalNames h)
  | returnVoid => exact .single .stmtReturnVoid
  | breakTarget label => exact .single .stmtBreak
  | continueTarget label => exact .single .stmtContinue
  | rethrow h => exact .single (.stmtRethrow h)
  | sequenceNormal hFirst hRest =>
      exact ((Runs.single .stmtSequence).trans ((stmt_path_runs_cont hFirst) _)).trans
        ((Runs.single .stmtSequenceNext).trans ((stmt_path_runs_cont hRest) _))
  | sequenceExit hFirst hExit =>
      exact ((Runs.single .stmtSequence).trans ((stmt_path_runs_cont hFirst) _)).trans
        (.single (.stmtSequenceExit hExit))
  | returnValue hExpr =>
      exact ((Runs.single .stmtReturnEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtReturnFinish)
  | returnRaised hExpr =>
      exact ((Runs.single .stmtReturnEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtReturnRaised)
  | throwValue hExpr =>
      exact ((Runs.single .stmtThrowEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtThrowFinish)
  | throwRaised hExpr =>
      exact ((Runs.single .stmtThrowEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtThrowRaised)
  | assignField hExpr hWrite =>
      exact ((Runs.single .stmtAssignFieldEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single (.stmtAssignFieldFinish hWrite))
  | assignFieldRaised hExpr =>
      exact ((Runs.single .stmtAssignFieldEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtAssignFieldRaised)
  | finallyNormal hBody hUncaught hCleanup =>
      exact ((((Runs.single .stmtProtectEnter).trans ((stmt_path_runs_cont hBody) _)).trans
        (.single (.stmtProtectUncaught hUncaught))).trans ((stmt_path_runs_cont hCleanup) _)).trans
          (.single .stmtFinallyNormal)
  | finallyOverride hBody hUncaught hCleanup hExit =>
      exact ((((Runs.single .stmtProtectEnter).trans ((stmt_path_runs_cont hBody) _)).trans
        (.single (.stmtProtectUncaught hUncaught))).trans ((stmt_path_runs_cont hCleanup) _)).trans
          (.single (.stmtFinallyOverride hExit))

  | caughtFinallyNormal hb hc hh hcl =>
      exact ((((((Runs.single .stmtProtectEnter).trans ((stmt_path_runs_cont hb) _)).trans
        (.single (.stmtProtectCaught hc))).trans ((stmt_path_runs_cont hh) _)).trans
          (.single .stmtHandlerExit)).trans ((stmt_path_runs_cont hcl) _)).trans (.single .stmtFinallyNormal)
  | caughtFinallyOverride hb hc hh hcl he =>
      exact ((((((Runs.single .stmtProtectEnter).trans ((stmt_path_runs_cont hb) _)).trans
        (.single (.stmtProtectCaught hc))).trans ((stmt_path_runs_cont hh) _)).trans
          (.single .stmtHandlerExit)).trans ((stmt_path_runs_cont hcl) _)).trans (.single (.stmtFinallyOverride he))
termination_by rank
decreasing_by all_goals omega
end

theorem expr_path_runs {program machine frame expr outcome rank}
    (h : DepthDerivesExpr program machine frame expr outcome rank) :
    ExprRuns program machine frame expr outcome := expr_path_runs_cont h []

private theorem nonlocalNames_exec {program m f names k}
    (h : names.all (fun name => (f.captures.lookup name).isSome) = true) :
    execStmt (k + 1) program m f (.nonlocalNames names) = .ok ⟨m, f, .normal⟩ := by
  induction names with
  | nil => simp [execStmt, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | cons name rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hn : (f.captures.lookup name).isNone = false := by
        cases hh : f.captures.lookup name <;> simp_all
      have ht := ih h.2
      simp only [execStmt] at ht ⊢
      simpa [List.forIn_cons, hn, Bind.bind, Pure.pure, Except.bind, Except.pure] using ht

set_option maxHeartbeats 1000000 in
mutual
theorem evalExpr_adequate {program machine frame expr outcome rank k}
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (hr : rank < k) : evalExpr k program machine frame expr = .ok outcome := by
  cases h with
  | undefined => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | null => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | bool b => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | integer n => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | string s => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | localRead h | global h | checkerField h =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          simp [evalExpr, h, Bind.bind, Pure.pure, Except.bind, Except.pure]
          rfl
  | @callCalleeRaised m f callee args final value rank he =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hk : rank < k := by omega
          simp [evalExpr, evalExpr_adequate he hk, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @callArgsRaised m f callee args middle final ref value re ra he ha =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hke : re < k := by omega
          have hka : ra < k := by omega
          simp [evalExpr, evalExpr_adequate he hke, evalArgs_adequate ha hka,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @callBuiltin m f callee args middle final id values out re ra he ha hi hh
  | @callBoundBuiltin m f callee args middle final id receiver values out re ra he ha hi hh =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hre : re < k := by omega
          have hra : ra < k := by omega
          simpa [evalExpr, evalExpr_adequate he hre, evalArgs_adequate ha hra,
            hi.1, hi.2.1, hi.2.2, Bind.bind, Pure.pure, Except.bind, Except.pure] using hh
  | @callBuiltinArgsRaised m f callee args middle final id value re ra he ha
  | @callBoundArgsRaised m f callee args middle final id receiver value re ra he ha =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hre : re < k := by omega
          have hra : ra < k := by omega
          simp [evalExpr, evalExpr_adequate he hre, evalArgs_adequate ha hra,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @callClosure m f callee args middle bound final ff ref values closure executed out re ra rp rb he ha hc hp hb ho =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hke : re < k := by omega
          have hka : ra < k := by omega
          have hkp : rp < k := by omega
          have hkb : rb < k := by omega
          simp only [evalExpr, evalExpr_adequate he hke, evalArgs_adequate ha hka,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
          simp only [callClosure, hc, Bind.bind, Except.bind]
          change (do
            let bindings ← bindCallParams k program bound (closureFrame closure)
              closure.params closure.pythonDefaults values
            match bindings.result with
            | .error e => pure ⟨bindings.machine, .error e⟩
            | .ok _ => do
              let result ← execStmt k program bindings.machine bindings.frame closure.body
              closureResult program.lang result : Except TargetError ExprOutcome) = _
          simpa only [bindProvided_adequate hp hkp, execStmt_adequate hb hkb,
            Bind.bind, Pure.pure, Except.bind, Except.pure] using ho
  | @objectFields m f fields out rank hf =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hk : rank < k := by omega
          simp only [evalExpr]
          exact evalFields_adequate hf hk
  | objectEmpty =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          cases k with
          | zero => exfalso; omega
          | succ k => simp only [evalExpr, evalObjectFields]; rfl
  | @objectOne m f key expr middle final value rank he hw =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          cases k with
          | zero => exfalso; omega
          | succ k =>
              have hk : rank < k := by omega
              simp only [evalExpr]
              change evalObjectFields (k + 1) program
                (allocObject machine (literalObject program.lang machine)).1 frame machine.nextObject
                (.objectEntry key expr .empty) = _
              simp only [evalObjectFields, (evalExpr_adequate he) hk, hw, Bind.bind, Pure.pure,
                Except.bind, Except.pure]
              cases k with
              | zero => exfalso; omega
              | succ k => simp only [evalObjectFields]; rfl
  | @objectOneRaised m f key expr final value rank he =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          cases k with
          | zero => exfalso; omega
          | succ k =>
              have hk : rank < k := by omega
              simp only [evalExpr]
              change evalObjectFields (k + 1) program
                (allocObject machine (literalObject program.lang machine)).1 frame machine.nextObject
                (.objectEntry key expr .empty) = _
              simp only [evalObjectFields, (evalExpr_adequate he) hk, Bind.bind, Pure.pure,
                Except.bind, Except.pure]
  | @propertyRaised m f receiver key final value rank he =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hk : rank < k := by omega
          simp [evalExpr, (evalExpr_adequate he) hk, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @property m f receiver key middle value out rank he hp =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hk : rank < k := by omega
          simpa [evalExpr, (evalExpr_adequate he) hk, Bind.bind, Pure.pure, Except.bind, Except.pure] using hp
  | @binaryLeftRaised m f left right op final value rank hLeft =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hl : rank < k := by omega
          simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, (evalExpr_adequate hLeft) hl]
  | @binaryRightRaised m f left right op middle final lv value leftRank rightRank hLeft hRight =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hl : leftRank < k := by omega
          have hr' : rightRank < k := by omega
          simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, (evalExpr_adequate hLeft) hl, (evalExpr_adequate hRight) hr']
  | @binary m f left right op middle final lv rv result leftRank rightRank hOp hLeft hRight hApply =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hl : leftRank < k := by omega
          have hr' : rightRank < k := by omega
          simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, (evalExpr_adequate hLeft) hl, (evalExpr_adequate hRight) hr', hOp, hApply]
termination_by rank
decreasing_by all_goals omega

theorem evalFields_adequate {program m f ref fields out rank k}
    (h : DepthDerivesFields program m f ref fields out rank) (hk : rank < k) :
    evalObjectFields k program m f ref fields = .ok out := by
  cases h with
  | empty =>
      cases k with
      | zero => exfalso; omega
      | succ k => simp [evalObjectFields]; rfl
  | @raised m f ref key expr rest final value rank he =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hr : rank < k := by omega
          simp [evalObjectFields, evalExpr_adequate he hr,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @entry m f ref key expr rest middle updated value out re rf he hw hf =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hre : re < k := by omega
          have hrf : rf < k := by omega
          simp [evalObjectFields, evalExpr_adequate he hre, hw, evalFields_adequate hf hrf,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
termination_by rank
decreasing_by all_goals omega

theorem evalArgs_adequate {program m f args out rank k}
    (h : DepthDerivesArgs program m f args out rank) (hk : rank < k) :
    evalArgValues k program m f args = .ok out := by
  cases h with
  | empty =>
      cases k with
      | zero => exfalso; omega
      | succ k => simp [evalArgValues]
  | @headRaised m f first rest final value rank he =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hr : rank < k := by omega
          simp [evalArgValues, evalExpr_adequate he hr,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @tailRaised m f first rest middle final value error re ra he ha
  | @cons m f first rest middle final value values re ra he ha =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hre : re < k := by omega
          have hra : ra < k := by omega
          simp [evalArgValues, evalExpr_adequate he hre, evalArgs_adequate ha hra,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
termination_by rank
decreasing_by all_goals omega

theorem execStmt_adequate {program machine frame stmt outcome rank k}
    (h : DepthDerivesStmt program machine frame stmt outcome rank)
    (hr : rank < k) : execStmt k program machine frame stmt = .ok outcome := by
  cases h with
  | @letLocal m f name mutable expr final value r he
  | @letLocalRaised m f name mutable expr final value r he
  | @assignLocalRaised m f name expr final value r he
  | @doExpr m f expr final value r he
  | @doExprRaised m f expr final value r he =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate he hk, allocCell,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @assignLocal m f name expr middle final value ref r he ha hw =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate he hk, ha, hw,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @assignPythonLocal m f name expr final value r hl he ha =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate he hk, hl, ha, allocCell,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @assignProperty m f receiver name expr middle written final ref value rr rv hReceiver hValue hWrite =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hrr : rr < k := by omega
          have hrv : rv < k := by omega
          simp only [execStmt, evalExpr_adequate hReceiver hrr,
            evalExpr_adequate hValue hrv, Bind.bind, Except.bind, Pure.pure, Except.pure]
          split at hWrite <;> simp_all
  | @assignPropertyReceiverRaised m f receiver name expr final error rank hReceiver =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : rank < k := by omega
          simp [execStmt, evalExpr_adequate hReceiver hk,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
  | @assignPropertyValueRaised m f receiver name expr middle final base error rr rv hReceiver hValue =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hrr : rr < k := by omega
          have hrv : rv < k := by omega
          simp [execStmt, evalExpr_adequate hReceiver hrr,
            evalExpr_adequate hValue hrv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | @assignPropertyInvalid m f receiver name expr middle final base value rr rv hReceiver hValue hTag =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hrr : rr < k := by omega
          have hrv : rv < k := by omega
          simp only [execStmt, evalExpr_adequate hReceiver hrr,
            evalExpr_adequate hValue hrv, Bind.bind, Except.bind, Pure.pure, Except.pure]
          cases base <;> simp_all [NonObjectValue]
  | @ifTrue m f cond yes no middle value out rc rb hc ht hb
  | @ifFalse m f cond yes no middle value out rc rb hc ht hb =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hck : rc < k := by omega
          have hbk : rb < k := by omega
          simp [execStmt, evalExpr_adequate hc hck, ht, (execStmt_adequate hb) hbk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @ifRaised m f cond yes no final value rank hc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : rank < k := by omega
          simp [execStmt, evalExpr_adequate hc hk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | empty | returnVoid | breakTarget | continueTarget =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k => simp only [execStmt]
  | nonlocalNames h =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k => exact nonlocalNames_exec h
  | rethrow h =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k => simp [execStmt, h]
  | @sequenceNormal m f first rest middle midFrame final r1 r2 h1 h2 =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have h1k : r1 < k := by omega
          have h2k : r2 < k := by omega
          simp [execStmt, (execStmt_adequate h1) h1k, (execStmt_adequate h2) h2k,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @sequenceExit m f first rest out r h1 hExit =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          cases hc : outcome.control <;> simp_all [execStmt, (execStmt_adequate h1) hk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @returnValue m f expr final value r hExpr
  | @returnRaised m f expr final value r hExpr
  | @throwValue m f expr final value r hExpr
  | @throwRaised m f expr final value r hExpr
  | @assignFieldRaised m f name expr final value r hExpr =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate hExpr hk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @assignField m f name expr middle final value r hExpr hWrite =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate hExpr hk, hWrite,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @finallyNormal m f body ct binder handler cleanup attempted final finalFrame rb rc hb hu hc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hck : rc < k := by omega
          cases hctrl : attempted.control <;>
            simp only [hctrl] at hu <;>
            simp only [execStmt, (execStmt_adequate hb) hbk, (execStmt_adequate hc) hck, hctrl, hu, Bool.false_eq_true,
              ↓reduceIte, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @finallyOverride m f body ct binder handler cleanup attempted final rb rc hb hu hc he =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hck : rc < k := by omega
          cases hctrl : attempted.control <;> cases hf : outcome.control <;>
            simp only [hctrl] at hu <;>
            simp only [execStmt, (execStmt_adequate hb) hbk, (execStmt_adequate hc) hck, hctrl, hf, hu, Bool.false_eq_true,
              ↓reduceIte, Bind.bind, Pure.pure, Except.bind, Except.pure]
          all_goals first | exact False.elim (he hf) | rfl

  | @caughtFinallyNormal m f body ct binder handler cleanup middle midFrame err handled final ff rb rh rc hb ht hh hc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hhk : rh < k := by omega
          have hck : rc < k := by omega
          simp only [execStmt, (execStmt_adequate hb) hbk, ht, ↓reduceIte,
            (execStmt_adequate hh) hhk, (execStmt_adequate hc) hck, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @caughtFinallyOverride m f body ct binder handler cleanup middle midFrame err handled final rb rh rc hb ht hh hc he =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hhk : rh < k := by omega
          have hck : rc < k := by omega
          cases hf : outcome.control <;>
            simp only [execStmt, (execStmt_adequate hb) hbk, ht, ↓reduceIte,
              (execStmt_adequate hh) hhk, (execStmt_adequate hc) hck, hf, Bind.bind, Pure.pure, Except.bind, Except.pure]
          all_goals first | exact False.elim (he hf) | rfl

termination_by rank
decreasing_by all_goals omega
end

/-- Once provided arguments are bound, invocation is exactly execution of
    the stored body followed by its control translation. Body success is not
    assumed, and no additional fuel edge occurs at `callClosure`. -/
theorem callClosure_eq_of_provided {program m ref closure values final ff rank k}
    (hc : closureAt m ref = .ok closure)
    (hp : DepthBindsProvided program m (closureFrame closure) closure.params
      closure.pythonDefaults values final ff rank)
    (hk : rank < k) :
    callClosure k program m ref values = (do
      let body ← execStmt k program final ff closure.body
      closureResult program.lang body) := by
  simp only [callClosure, hc, Bind.bind, Except.bind]
  change (do
    let bindings ← bindCallParams k program m (closureFrame closure)
      closure.params closure.pythonDefaults values
    match bindings.result with
    | .error e => pure ⟨bindings.machine, .error e⟩
    | .ok _ => do
      let result ← execStmt k program bindings.machine bindings.frame closure.body
      closureResult program.lang result : Except TargetError ExprOutcome) = _
  simp only [bindProvided_adequate hp hk, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Peel only the reached callee/argument/binding phases from an actual stored
    closure call. The unknown parsed body and all its outcomes remain on the
    RHS; its recursion-depth obligation is separate from these phases. -/
theorem evalStoredCall_eq
    {program m f callee args middle bound ref values closure final ff re ra rp k}
    (he : DepthDerivesExpr program m f callee ⟨middle, .ok (.closure ref)⟩ re)
    (ha : DepthDerivesArgs program middle f args ⟨bound, .ok values⟩ ra)
    (hc : closureAt bound ref = .ok closure)
    (hp : DepthBindsProvided program bound (closureFrame closure) closure.params
      closure.pythonDefaults values final ff rp)
    (hke : re < k) (hka : ra < k) (hkp : rp < k) :
    evalExpr (k + 1) program m f (.call callee args) = (do
      let body ← execStmt k program final ff closure.body
      closureResult program.lang body) := by
  simp only [evalExpr, evalExpr_adequate he hke, evalArgs_adequate ha hka,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  exact callClosure_eq_of_provided hc hp hkp

/-- Method access allocates an actual receiver-bound copy of a stored closure;
    object/cell allocation in the caller does not become a helper primitive. -/
theorem readCheckerMethod_bound {lang m name error methodRef method}
    (hf : readCheckerField m name = .error error)
    (hm : m.classMethods.lookup name = some methodRef)
    (hc : closureAt m methodRef = .ok method) :
    readPropertyValue lang m (.object m.checkerRef) name =
      .ok ⟨(allocClosure m { method with receiver := some m.checkerRef }).1,
        .ok (.closure m.nextClosure)⟩ := by
  simp [readPropertyValue, hf, hm, hc, allocClosure, Functor.map, Except.map]
  rfl

/-- Adequacy forces any two supported paths of the same expression to have
    the same result, even if their derivation ranks differ. -/
theorem DepthDerivesExpr.deterministic {program m f expr out₁ out₂ r₁ r₂}
    (h₁ : DepthDerivesExpr program m f expr out₁ r₁)
    (h₂ : DepthDerivesExpr program m f expr out₂ r₂) : out₁ = out₂ := by
  have hk₁ : r₁ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hk₂ : r₂ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact Except.ok.inj ((evalExpr_adequate h₁ hk₁).symm.trans (evalExpr_adequate h₂ hk₂))

/-- Syntax coverage of this read-only proof slice; `.add` needs a separate
    Python list-concatenation rule before entering the common binary case. -/
inductive ScalarSyntax : TargetExpr → Prop where
  | undefined : ScalarSyntax .undefined
  | null : ScalarSyntax .null
  | bool (b : Bool) : ScalarSyntax (.bool b)
  | integer (n : Int) : ScalarSyntax (.integer n)
  | string (s : String) : ScalarSyntax (.string s)
  | localRead (name : String) : ScalarSyntax (.local name)
  | global (name : String) : ScalarSyntax (.global name)
  | checkerField (name : String) : ScalarSyntax (.checkerField name)
  | binary {op left right} (hOp : op ≠ .add)
      (hLeft : ScalarSyntax left) (hRight : ScalarSyntax right) :
      ScalarSyntax (.binary op left right)

/-- Evaluator soundness for the explicitly covered syntax, including raised
    source outcomes on either ordered child. No success premise occurs in the
    semantic derivation constructors themselves. -/
theorem evalScalar_sound {program machine frame expr outcome k}
    (hs : ScalarSyntax expr)
    (h : evalExpr k program machine frame expr = .ok outcome) :
    ∃ rank, DepthDerivesExpr program machine frame expr outcome rank ∧ rank < k := by
  induction hs generalizing k machine outcome with
  | undefined =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .undefined, by omega⟩
  | null =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .null, by omega⟩
  | bool b =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .bool b, by omega⟩
  | integer n =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .integer n, by omega⟩
  | string s =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .string s, by omega⟩
  | localRead name =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hv : localValue machine frame name with
          | error e =>
              simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
          | ok value =>
              simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
              cases h
              exact ⟨0, .localRead hv, by omega⟩
  | global name =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hv : localValue machine frame name with
          | error e =>
              simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
          | ok value =>
              simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
              cases h
              exact ⟨0, .global hv, by omega⟩
  | checkerField name =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hv : readCheckerField machine name with
          | error e =>
              simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
          | ok value =>
              simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
              cases h
              exact ⟨0, .checkerField hv, by omega⟩
  | @binary op left right hOp _ _ ihLeft ihRight =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hLeft : evalExpr k program machine frame left with
          | error err => simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft] at h
          | ok lhs =>
              rcases lhs with ⟨middle, lhs⟩
              obtain ⟨leftRank, leftPath, leftBound⟩ := ihLeft hLeft
              cases lhs with
              | error value =>
                  have heq : outcome = ⟨middle, .error value⟩ := by
                    simpa [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft] using h.symm
                  subst outcome
                  exact ⟨1 + leftRank, .binaryLeftRaised leftPath, by omega⟩
              | ok lv =>
                  cases hRight : evalExpr k program middle frame right with
                  | error err => simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight] at h
                  | ok rhs =>
                      rcases rhs with ⟨final, rhs⟩
                      obtain ⟨rightRank, rightPath, rightBound⟩ := ihRight hRight
                      cases rhs with
                      | error value =>
                          have heq : outcome = ⟨final, .error value⟩ := by
                            simpa [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight] using h.symm
                          subst outcome
                          exact ⟨1 + max leftRank rightRank,
                            .binaryRightRaised leftPath rightPath, by omega⟩
                      | ok rv =>
                          cases hApply : binaryValue program.lang final op lv rv with
                          | error err => simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight, hOp, hApply] at h
                          | ok result =>
                              have heq : outcome = ⟨final, result⟩ := by
                                simpa [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight, hOp, hApply] using h.symm
                              subst outcome
                              exact ⟨1 + max leftRank rightRank,
                                .binary hOp leftPath rightPath hApply, by omega⟩

/-- Executable soundness for scalar-receiver property paths. The property
    operation may allocate a bound closure; its complete outcome is retained. -/
theorem evalProperty_sound {program m f receiver key out k}
    (hs : ScalarSyntax receiver)
    (he : evalExpr k program m f (.property receiver key) = .ok out) :
    ∃ rank, DepthDerivesExpr program m f (.property receiver key) out rank ∧ rank < k := by
  cases k with
  | zero => simp [evalExpr] at he
  | succ k =>
      cases hv : evalExpr k program m f receiver with
      | error e => simp [evalExpr, hv, Bind.bind, Except.bind] at he
      | ok result =>
          obtain ⟨r, hd, hr⟩ := evalScalar_sound hs hv
          cases result with
          | mk middle result =>
              cases result with
              | error value =>
                  simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at he
                  cases he
                  exact ⟨1 + r, .propertyRaised hd, by omega⟩
              | ok value =>
                  simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at he
                  exact ⟨1 + r, .property hd he, by omega⟩

/-- Reverse adequacy for ordered property assignment with scalar children.
    Outer executor errors remain errors; successful source exceptions retain
    the heap produced by the last evaluated child. -/
theorem execPropertyAssign_sound {program m f receiver name value out k}
    (hr : ScalarSyntax receiver) (hv : ScalarSyntax value)
    (he : execStmt k program m f (.assign (.property receiver name) value) = .ok out) :
    ∃ rank, DepthDerivesStmt program m f (.assign (.property receiver name) value) out rank ∧
      rank < k := by
  cases k with
  | zero => simp [execStmt] at he
  | succ k =>
      cases er : evalExpr k program m f receiver with
      | error e => simp [execStmt, er, Bind.bind, Except.bind] at he
      | ok base =>
          obtain ⟨rr, dr, br⟩ := evalScalar_sound hr er
          rcases base with ⟨middle, base⟩
          cases base with
          | error e =>
              simp only [execStmt, er, Bind.bind, Pure.pure, Except.bind,
                Except.pure, Except.ok.injEq] at he
              cases he
              exact ⟨1 + rr, .assignPropertyReceiverRaised dr, by omega⟩
          | ok base =>
              cases ev : evalExpr k program middle f value with
              | error e => simp [execStmt, er, ev, Bind.bind, Except.bind] at he
              | ok rhs =>
                  obtain ⟨rv, dv, bv⟩ := evalScalar_sound hv ev
                  rcases rhs with ⟨written, rhs⟩
                  cases rhs with
                  | error e =>
                      simp only [execStmt, er, ev, Bind.bind, Pure.pure, Except.bind,
                        Except.pure, Except.ok.injEq] at he
                      cases he
                      exact ⟨1 + max rr rv, .assignPropertyValueRaised dr dv, by omega⟩
                  | ok rhs =>
                      cases base with
                      | object ref =>
                          cases ew : (if ref == written.checkerRef then
                            writeCheckerField written name rhs else writeOwn written ref name rhs) with
                          | error e =>
                              cases hc : ref == written.checkerRef <;>
                                simp_all [execStmt, Bind.bind, Except.bind]
                          | ok final =>
                              have ho : out = ⟨final, f, .normal⟩ := by
                                cases hc : ref == written.checkerRef <;>
                                  simp only [hc, Bool.false_eq_true,
                                    ↓reduceIte] at ew <;>
                                  simpa [execStmt, er, ev, hc, ew, Bind.bind, Pure.pure,
                                    Except.bind, Except.pure] using he.symm
                              subst out
                              exact ⟨1 + max rr rv, .assignProperty dr dv ew, by omega⟩
                      | _ =>
                          simp only [execStmt, er, ev, Bind.bind, Pure.pure, Except.bind,
                            Except.pure, Except.ok.injEq] at he
                          cases he
                          exact ⟨1 + max rr rv, .assignPropertyInvalid dr dv trivial, by omega⟩

/-- Scalar syntax preserves the heap. Property reads are excluded because
    binding a generated method allocates a fresh receiver-bound closure. -/
theorem evalScalar_machine_eq {program m f expr out k}
    (hs : ScalarSyntax expr) (he : evalExpr k program m f expr = .ok out) :
    out.machine = m := by
  induction hs generalizing m out k with
  | undefined | null | bool | integer | string =>
      cases k with
      | zero => simp [evalExpr] at he
      | succ k => simp [evalExpr, Except.ok.injEq] at he; cases he; rfl
  | localRead name | global name =>
      cases k with
      | zero => simp [evalExpr] at he
      | succ k =>
          cases hv : localValue m f name <;>
            simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at he
          cases he; rfl
  | checkerField name =>
      cases k with
      | zero => simp [evalExpr] at he
      | succ k =>
          cases hv : readCheckerField m name <;>
            simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at he
          cases he; rfl
  | @binary op left right hop hl hr ihl ihr =>
      cases k with
      | zero => simp [evalExpr] at he
      | succ k =>
          cases el : evalExpr k program m f left with
          | error e => simp [evalExpr, el, Bind.bind, Except.bind] at he
          | ok lo =>
              have hm := ihl el
              cases lo with
              | mk lm lr =>
                cases lr with
                | error v =>
                    simp [evalExpr, el, Bind.bind, Pure.pure, Except.bind, Except.pure] at he
                    cases he; exact hm
                | ok lv =>
                    cases er : evalExpr k program lm f right with
                    | error e => simp [evalExpr, el, er, Bind.bind, Except.bind] at he
                    | ok ro =>
                        have hm' := ihr er
                        cases ro with
                        | mk rm rr =>
                          cases rr with
                          | error v =>
                              simp [evalExpr, el, er, Bind.bind, Pure.pure, Except.bind, Except.pure] at he
                              cases he; simp_all
                          | ok rv =>
                              simp only [evalExpr, el, er, hop, ↓reduceIte, Bind.bind,
                                Pure.pure, Except.bind, Except.pure] at he
                              cases eb : binaryValue program.lang rm op lv rv <;>
                                simp_all [Functor.map, Except.map]
                              cases he; simp_all

theorem stmt_path_runs {program machine frame stmt outcome rank}
    (h : DepthDerivesStmt program machine frame stmt outcome rank) :
    StmtRuns program machine frame stmt outcome := stmt_path_runs_cont h []

/-- Reverse adequacy for the supported statement paths, including a mutating
    finalizer. No executable success is a premise of a semantic derivation. -/
theorem DepthDerivesStmt.deterministic {program m f stmt out₁ out₂ r₁ r₂}
    (h₁ : DepthDerivesStmt program m f stmt out₁ r₁)
    (h₂ : DepthDerivesStmt program m f stmt out₂ r₂) : out₁ = out₂ := by
  have hk₁ : r₁ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hk₂ : r₂ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact Except.ok.inj ((execStmt_adequate h₁ hk₁).symm.trans (execStmt_adequate h₂ hk₂))

/-- Explicit coverage for lexical statement soundness. Scalar children may
    read captured cells and raise; generated calls are still outside this slice. -/
inductive LexicalStmtSyntax : TargetStmt → Prop where
  | letLocal {name mutable expr} (h : ScalarSyntax expr) :
      LexicalStmtSyntax (.letLocal name mutable expr)
  | assignLocal {name expr} (h : ScalarSyntax expr) :
      LexicalStmtSyntax (.assign (.local name) expr)
  | doExpr {expr} (h : ScalarSyntax expr) : LexicalStmtSyntax (.doExpr expr)

/-- Every successful executable lexical statement has an unfueled derivation
    with rank below the executable depth. Outer target errors (unbound TS name,
    immutable cell, etc.) are never reclassified as successful source outcomes. -/
theorem execLexical_sound {program m f stmt out k}
    (hs : LexicalStmtSyntax stmt) (he : execStmt k program m f stmt = .ok out) :
    ∃ rank, DepthDerivesStmt program m f stmt out rank ∧ rank < k := by
  cases k with
  | zero => simp [execStmt] at he
  | succ k =>
      cases hs with
      | @letLocal name mutable expr hs =>
          cases hv : evalExpr k program m f expr with
          | error e => simp [execStmt, hv, Bind.bind, Except.bind] at he
          | ok result =>
              obtain ⟨r, hd, hr⟩ := evalScalar_sound hs hv
              cases result with
              | mk final result =>
                cases result with
                | error value =>
                    simp only [execStmt, hv, Bind.bind, Pure.pure,
                      Except.bind, Except.pure, Except.ok.injEq] at he
                    cases he
                    exact ⟨1 + r, .letLocalRaised hd, by omega⟩
                | ok value =>
                    simp only [execStmt, hv, Bind.bind, Pure.pure,
                      Except.bind, Except.pure, Except.ok.injEq] at he
                    cases he
                    exact ⟨1 + r, .letLocal hd, by omega⟩
      | @doExpr expr hs =>
          cases hv : evalExpr k program m f expr with
          | error e => simp [execStmt, hv, Bind.bind, Except.bind] at he
          | ok result =>
              obtain ⟨r, hd, hr⟩ := evalScalar_sound hs hv
              cases result with
              | mk final result =>
                cases result with
                | error value =>
                    simp only [execStmt, hv, Bind.bind, Pure.pure,
                      Except.bind, Except.pure, Except.ok.injEq] at he
                    cases he
                    exact ⟨1 + r, .doExprRaised hd, by omega⟩
                | ok value =>
                    simp only [execStmt, hv, Bind.bind, Pure.pure,
                      Except.bind, Except.pure, Except.ok.injEq] at he
                    cases he
                    exact ⟨1 + r, .doExpr hd, by omega⟩
      | @assignLocal name expr hs =>
          cases hv : evalExpr k program m f expr with
          | error e => simp [execStmt, hv, Bind.bind, Except.bind] at he
          | ok result =>
              obtain ⟨r, hd, hr⟩ := evalScalar_sound hs hv
              cases result with
              | mk middle result =>
                cases result with
                | error value =>
                    simp only [execStmt, hv, Bind.bind, Pure.pure,
                      Except.bind, Except.pure, Except.ok.injEq] at he
                    cases he
                    exact ⟨1 + r, .assignLocalRaised hd, by omega⟩
                | ok value =>
                    cases ha : (f.locals.lookup name).orElse (fun _ =>
                      (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) with
                    | some ref =>
                        cases hw : writeCell middle ref value with
                        | error e =>
                            simp [execStmt, hv, ha, hw, Bind.bind,
                              Pure.pure, Except.bind, Except.pure] at he
                        | ok final =>
                            simp only [execStmt, hv, ha, hw, Bind.bind, Pure.pure,
                              Except.bind, Except.pure, Except.ok.injEq] at he
                            cases he
                            exact ⟨1 + r, .assignLocal hd ha hw, by omega⟩
                    | none =>
                        cases hl : program.lang with
                        | ts =>
                            simp [execStmt, hv, ha, hl, Bind.bind,
                              Pure.pure, Except.bind, Except.pure] at he
                        | python =>
                            simp [execStmt, hv, ha, hl,
                              Bind.bind, Pure.pure, Except.bind, Except.pure] at he
                            cases he
                            exact ⟨1 + r, .assignPythonLocal hl hd ha, by omega⟩

/-- Finite address/descriptor checks. Values stored in the heap do not
    recursively traverse objects: liveness checks references, including cycles. -/
def liveValueCheck (m : TargetMachine) : TargetValue → Bool
  | .object ref => (m.objects.lookup ref).isSome
  | .closure ref => (m.closures.lookup ref).isSome
  | .boundBuiltin _ receiver => liveValueCheck m receiver
  | _ => true

def uniqueKeys {α β : Type} [BEq α] : List (α × β) → Bool
  | [] => true
  | entry :: rest => !(rest.any (fun other => entry.1 == other.1)) && uniqueKeys rest

def liveOptionalObject (m : TargetMachine) : Option ObjRef → Bool
  | none => true
  | some ref => (m.objects.lookup ref).isSome

def liveControlCheck (m : TargetMachine) : ControlResult → Bool
  | .returned value | .raised value => liveValueCheck m value
  | _ => true

def frameWFCheck (m : TargetMachine) (f : TargetFrame) : Bool :=
  (f.locals ++ f.captures).all (fun entry => (m.cells.lookup entry.2).isSome) &&
    liveOptionalObject m f.receiver && liveControlCheck m f.control

def descriptorWFCheck (m : TargetMachine) (d : Descriptor) : Bool :=
  (match d.value with | none => true | some value => liveValueCheck m value) &&
    (match d.get with | none => true | some ref => (m.closures.lookup ref).isSome) &&
    (match d.set with | none => true | some ref => (m.closures.lookup ref).isSome)

def objectWFCheck (m : TargetMachine) (o : HeapObject) : Bool :=
  liveOptionalObject m o.prototype && uniqueKeys o.own &&
    o.own.all (fun entry => descriptorWFCheck m entry.2) &&
    o.items.all (liveValueCheck m) && o.setMembers.all (liveValueCheck m)

def closureWFCheck (m : TargetMachine) (c : TargetClosure) : Bool :=
  c.captures.all (fun entry => (m.cells.lookup entry.2).isSome) &&
    c.pythonDefaults.all (fun value => match value with
      | none => true | some value => liveValueCheck m value) &&
    liveOptionalObject m c.receiver

def generatorWFCheck (m : TargetMachine) (ref : ObjRef) (g : GeneratorState) : Bool :=
  ((m.objects.lookup ref).map HeapObject.kind == some .pythonGenerator) &&
    frameWFCheck m g.frame && g.remaining.all (liveValueCheck m)

/-- Shared heap invariant, applicable before construction as well as after it.
    Canonical checker container shapes are a separate representation predicate.
    No evaluator success, ideal constructor, or fixed allocation IDs are assumed. -/
def heapWFCheck (_lang : TargetLang) (m : TargetMachine) : Bool :=
  uniqueKeys m.objects && uniqueKeys m.cells && uniqueKeys m.closures &&
    uniqueKeys m.generators && uniqueKeys m.writableCells &&
    m.objects.all (fun entry => entry.1 < m.nextObject && objectWFCheck m entry.2 &&
      (entry.2.kind != .pythonGenerator || (m.generators.lookup entry.1).isSome)) &&
    m.cells.all (fun entry => entry.1 < m.nextCell && liveValueCheck m entry.2) &&
    m.closures.all (fun entry => entry.1 < m.nextClosure && closureWFCheck m entry.2) &&
    m.generators.all (fun entry => generatorWFCheck m entry.1 entry.2) &&
    m.writableCells.all (fun entry => (m.cells.lookup entry.1).isSome) &&
    m.cells.all (fun entry => (m.writableCells.lookup entry.1).isSome) &&
    m.globals.all (fun entry => (m.cells.lookup entry.2).isSome) &&
    m.frames.all (frameWFCheck m) &&
    m.classMethods.all (fun entry => (m.closures.lookup entry.2).isSome) &&
    m.callableObjects.all (fun entry => (m.objects.lookup entry.1).isSome) &&
    ((m.objects.lookup m.objectPrototype).map HeapObject.kind == some .jsPrototype) &&
    (m.objects.lookup m.checkerRef).isSome &&
    (m.objects.lookup m.checker.context).isSome &&
    (m.objects.lookup m.checker.history).isSome &&
    liveOptionalObject m m.checker.undo && liveOptionalObject m m.checker.constructorSeed &&
    m.checker.instanceAttrs.all (fun entry => liveValueCheck m entry.2)

def HeapWF (lang : TargetLang) (m : TargetMachine) : Prop := heapWFCheck lang m = true

instance (lang : TargetLang) (m : TargetMachine) : Decidable (HeapWF lang m) :=
  inferInstanceAs (Decidable (heapWFCheck lang m = true))

/-- The structural invariant entails freshness of the next object address.
    The host clone can therefore preserve every older object on replacement. -/
theorem HeapWF.object_fresh {lang m} (h : HeapWF lang m) :
    ∀ e ∈ m.objects, e.1 ≠ m.nextObject := by
  unfold HeapWF heapWFCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨_, _, _, _, _, ho, _⟩ := h
  intro entry hEntry
  have hLive := (List.all_eq_true.mp ho) entry hEntry
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hLive
  exact Nat.ne_of_lt hLive.1.1

def FrameWF (m : TargetMachine) (f : TargetFrame) : Prop := frameWFCheck m f = true

theorem scalar_runs_heapWF {program machine frame expr outcome rank lang}
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (hs : ScalarSyntax expr)
    (hwf : HeapWF lang machine) : HeapWF lang outcome.machine := by
  rw [evalScalar_machine_eq hs (evalExpr_adequate h (Nat.lt_succ_self rank))]
  exact hwf

end Harmonia.Applications.Kadmos.Generated
