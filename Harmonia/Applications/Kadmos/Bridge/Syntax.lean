import Harmonia.Applications.Kadmos.World

namespace Harmonia.Applications.Kadmos.Bridge

inductive FieldOrigin where | event | request deriving DecidableEq, Repr
inductive SourceExpr where
  | int (n : Int) | bool (b : Bool)
  | context (id : String) | field (origin : FieldOrigin) (id : String)
  | stateEq (phaseId : String)
  | add (l r : SourceExpr) | sub (l r : SourceExpr)
  | eqInt (l r : SourceExpr) | lt (l r : SourceExpr) | le (l r : SourceExpr)
  | gt (l r : SourceExpr) | ge (l r : SourceExpr)
  | and (l r : SourceExpr) | or (l r : SourceExpr)
  | implies (l r : SourceExpr) | not (e : SourceExpr)
  deriving DecidableEq, Repr
structure SourceEnv where
  phase : String
  context : String → Int
  fields : String → Int
inductive BridgeError where
  | lexical (offset : Nat) | syntax (offset : Nat)
  | unsupported (token : String) | unbound (id : String)
  | duplicate (id : String) | reserved (id : String)
  | wrongSort (role : String) | invalidBounds (id : String)
  | unsafeLiteral (value : Int) | invalidProfile (id : String)
  | unknownProperty (path : String) | malformedEffect (index : Nat)
  | malformedWorld (reason : SpecError) | projection
  deriving DecidableEq

private def identStart (c : Char) : Bool := c.isAlpha || c == '_'
private def identRest (c : Char) : Bool := c.isAlphanum || c == '_'
private def decimalNat (s : String) : Nat :=
  s.toList.foldl (fun n c => 10*n + (c.toNat - '0'.toNat)) 0

private def numberToken (s : String) : Bool := s.toList.any Char.isDigit && s.toList.all Char.isDigit
private def identToken (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identStart c && cs.all identRest

private def lexStep (fuel : Nat) (cs : List Char) (acc : List String) : Except BridgeError (List String) :=
  match fuel with
  | 0 => .error (.lexical 0)
  | fuel + 1 =>
    match cs with
    | [] => .ok acc.reverse
    | c :: rest =>
      if c.isWhitespace then lexStep fuel rest acc
      else if identStart c then
        let tail := rest.takeWhile identRest
        lexStep fuel (rest.dropWhile identRest) ((String.mk (c :: tail)) :: acc)
      else if c.isDigit then
        let tail := rest.takeWhile Char.isDigit
        lexStep fuel (rest.dropWhile Char.isDigit) ((String.mk (c :: tail)) :: acc)
      else if c == '\'' then
        let tail := rest.takeWhile (· != '\'')
        if tail.contains '\\' then .error (.unsupported "string escape")
        else match rest.dropWhile (· != '\'') with
          | [] => .error (.syntax 0)
          | _ :: after => lexStep fuel after (("'" ++ String.mk tail ++ "'") :: acc)
      else
        match c, rest with
        | '=', '>' :: after => lexStep fuel after ("=>" :: acc)
        | '=', '=' :: after => lexStep fuel after ("==" :: acc)
        | '!', '=' :: _ => .error (.unsupported "!=")
        | '>', '=' :: after => lexStep fuel after (">=" :: acc)
        | '<', '=' :: after => lexStep fuel after ("<=" :: acc)
        | '&', '&' :: after => lexStep fuel after ("&&" :: acc)
        | '|', '|' :: after => lexStep fuel after ("||" :: acc)
        | '*', _ => .error (.unsupported "*")
        | '/', _ => .error (.unsupported "/")
        | '-', _ => lexStep fuel rest ("-" :: acc)
        | '+', _ => lexStep fuel rest ("+" :: acc)
        | '(', _ => lexStep fuel rest ("(" :: acc)
        | ')', _ => lexStep fuel rest (")" :: acc)
        | '.', _ => lexStep fuel rest ("." :: acc)
        | '<', _ => lexStep fuel rest ("<" :: acc)
        | '>', _ => lexStep fuel rest (">" :: acc)
        | '!', _ => lexStep fuel rest ("!" :: acc)
        | '=', _ => lexStep fuel rest ("=" :: acc)
        | _, _ => .error (.lexical 0)

def tokenize (s : String) : Except BridgeError (List String) :=
  lexStep (s.toList.length + 1) s.toList []

private def priority : String → Nat
  | "=>" => 1 | "||" => 2 | "&&" => 3 | "==" => 4
  | ">" | ">=" | "<" | "<=" => 5
  | "+" | "-" => 6
  | "!" => 7
  | _ => 0
private def combine (op : String) (l r : SourceExpr) : SourceExpr :=
  match op with
  | "=>" => .implies l r | "||" => .or l r | "&&" => .and l r
  | "==" => .eqInt l r | ">" => .gt l r | ">=" => .ge l r
  | "<" => .lt l r | "<=" => .le l r | "+" => .add l r
  | "-" => .sub l r | _ => l

private def quotedContent (s : String) : Option String :=
  match s.toList with
  | '\'' :: tail =>
    match tail.reverse with
    | '\'' :: inner => some (String.mk inner.reverse)
    | _ => none
  | _ => none

inductive ParsedToken where
  | atom (e : SourceExpr) | op (s : String) | leftParen | rightParen

private def classify : List String → Except BridgeError (List ParsedToken)
  | [] => .ok []
  | "state" :: "==" :: phase :: rest => do
    match quotedContent phase with
    | some id => return .atom (.stateEq id) :: (← classify rest)
    | none => throw (.syntax 0)
  | "event" :: "." :: id :: rest => do
    if identToken id then return .atom (.field .event id) :: (← classify rest)
    else throw (.syntax 0)
  | "request" :: "." :: id :: rest => do
    if identToken id then return .atom (.field .request id) :: (← classify rest)
    else throw (.syntax 0)
  | tok :: rest => do
    let t ← if tok == "(" then .ok .leftParen
      else if tok == ")" then .ok .rightParen
      else if tok == "true" then .ok (.atom (.bool true))
      else if tok == "false" then .ok (.atom (.bool false))
      else if tok == "null" then .error (.unsupported "null")
      else if priority tok > 0 || tok == "!" then .ok (.op tok)
      else if numberToken tok then .ok (.atom (.int (Int.ofNat (decimalNat tok))))
      else if identToken tok && tok != "state" && tok != "event" && tok != "request" then .ok (.atom (.context tok))
      else .error (.syntax 0)
    return t :: (← classify rest)

structure ParseStack where
  values : List SourceExpr
  operators : List String
  expectOperand : Bool

private def reduceOne (op : String) (values : List SourceExpr) : Except BridgeError (List SourceExpr) :=
  if op == "!" then
    match values with
    | x :: xs => .ok (.not x :: xs)
    | _ => .error (.syntax 0)
  else
    match values with
    | r :: l :: xs => .ok (combine op l r :: xs)
    | _ => .error (.syntax 0)

private def popHigher (prec : Nat) (rightAssoc : Bool) (values : List SourceExpr) :
    List String → Except BridgeError (List SourceExpr × List String)
  | [] => .ok (values,[])
  | op :: rest =>
    if op == "(" || priority op < prec || (rightAssoc && priority op == prec) then
      .ok (values,op :: rest)
    else do
      let v ← reduceOne op values
      popHigher prec rightAssoc v rest

private def closeParen (values : List SourceExpr) : List String → Except BridgeError (List SourceExpr × List String)
  | [] => .error (.syntax 0)
  | "(" :: rest => .ok (values,rest)
  | op :: rest => do
    let v ← reduceOne op values
    closeParen v rest

private def parseStep (s : ParseStack) (tok : ParsedToken) : Except BridgeError ParseStack := do
  match tok with
  | .atom e =>
    if s.expectOperand then return ⟨e :: s.values,s.operators,false⟩
    else throw (.syntax 0)
  | .leftParen =>
    if s.expectOperand then return ⟨s.values,"(" :: s.operators,true⟩
    else throw (.syntax 0)
  | .rightParen =>
    if s.expectOperand then throw (.syntax 0)
    let (v,ops) ← closeParen s.values s.operators
    return ⟨v,ops,false⟩
  | .op op =>
    if op == "!" then
      if s.expectOperand then return ⟨s.values,"!" :: s.operators,true⟩
      else throw (.syntax 0)
    if s.expectOperand then
      if op == "-" then throw (.unsupported "unary -") else throw (.syntax 0)
    let (v,ops) ← popHigher (priority op) (op == "=>") s.values s.operators
    return ⟨v,op :: ops,true⟩

private def finish (values : List SourceExpr) : List String → Except BridgeError (List SourceExpr)
  | [] => .ok values
  | "(" :: _ => .error (.syntax 0)
  | op :: rest => do
    finish (← reduceOne op values) rest

def parseSourceExpr (s : String) : Except BridgeError SourceExpr := do
  let tokens ← tokenize s
  let parsed ← classify tokens
  let state ← parsed.foldlM parseStep ⟨[],[],true⟩
  if state.expectOperand then throw (.syntax 0)
  let values ← finish state.values state.operators
  match values with
  | [e] => .ok e
  | _ => .error (.syntax 0)

def srcInt : Value → Except EvalError Int
  | .int n => .ok n
  | .bool _ => .error .expectedInt
def srcBool : Value → Except EvalError Bool
  | .bool b => .ok b
  | .int _ => .error .expectedBool

def sourceEval (ρ : SourceEnv) : SourceExpr → Except EvalError Value
  | .int n => .ok (.int n)
  | .bool b => .ok (.bool b)
  | .context id => .ok (.int (ρ.context id))
  | .field _ id => .ok (.int (ρ.fields id))
  | .stateEq id => .ok (.bool (ρ.phase == id))
  | .add l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .int ((← srcInt a) + (← srcInt b))
  | .sub l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .int ((← srcInt a) - (← srcInt b))
  | .eqInt l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool (decide ((← srcInt a) = (← srcInt b)))
  | .lt l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool ((← srcInt a) < (← srcInt b))
  | .le l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool ((← srcInt a) ≤ (← srcInt b))
  | .gt l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool (!decide ((← srcInt a) ≤ (← srcInt b)))
  | .ge l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool (!decide ((← srcInt a) < (← srcInt b)))
  | .and l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool ((← srcBool a) && (← srcBool b))
  | .or l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool ((← srcBool a) || (← srcBool b))
  | .implies l r => do
    let a ← sourceEval ρ l; let b ← sourceEval ρ r
    return .bool (!(← srcBool a) || (← srcBool b))
  | .not e => do
    return .bool (!(← srcBool (← sourceEval ρ e)))

/-- Eager, independent visit safety. The binary premise visits both children. -/
inductive sourceSafe (ρ : SourceEnv) : SourceExpr → Prop where
  | int (n) (h : safeInt n) : sourceSafe ρ (.int n)
  | bool (b) : sourceSafe ρ (.bool b)
  | context (id) (h : safeInt (ρ.context id)) : sourceSafe ρ (.context id)
  | field (o id) (h : safeInt (ρ.fields id)) : sourceSafe ρ (.field o id)
  | stateEq (id) : sourceSafe ρ (.stateEq id)
  | add (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r)
      (hs : ∀ x y, sourceEval ρ l = .ok (.int x) → sourceEval ρ r = .ok (.int y) → safeInt (x+y)) : sourceSafe ρ (.add l r)
  | sub (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r)
      (hs : ∀ x y, sourceEval ρ l = .ok (.int x) → sourceEval ρ r = .ok (.int y) → safeInt (x-y)) : sourceSafe ρ (.sub l r)
  | eqInt (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.eqInt l r)
  | lt (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.lt l r)
  | le (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.le l r)
  | gt (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.gt l r)
  | ge (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.ge l r)
  | and (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.and l r)
  | or (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.or l r)
  | implies (l r) (hl : sourceSafe ρ l) (hr : sourceSafe ρ r) : sourceSafe ρ (.implies l r)
  | not (e) (h : sourceSafe ρ e) : sourceSafe ρ (.not e)

end Harmonia.Applications.Kadmos.Bridge
