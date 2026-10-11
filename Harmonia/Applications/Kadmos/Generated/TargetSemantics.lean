import Harmonia.Applications.Kadmos.Generated.TargetMachine

namespace Harmonia.Applications.Kadmos.Generated

structure ExprOutcome where
  machine : TargetMachine
  result : Except TargetValue TargetValue
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
  match frame.locals.lookup name with
  | some ref => readCell m ref
  | none =>
      match frame.captures.lookup name with
      | some ref => readCell m ref
      | none =>
          match m.globals.lookup name with
          | some ref => readCell m ref
          | none => .error (.unboundLocal name)

-- The interpreter is deliberately over target syntax only. No source World,
-- Bridge certificate, sourceEval or reference `interpret` is imported here.
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

end Harmonia.Applications.Kadmos.Generated
