import Init

namespace Harmonia.Applications.Kadmos.Generated

inductive TargetLang where | ts | python deriving DecidableEq, Repr

inductive TokenKind where
  | identifier | numeral | quoted | regex | spacing | punctuation | comment
  deriving DecidableEq, Repr

structure SourceToken where
  kind : TokenKind
  text : String
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

inductive ParseError where
  | unterminatedString (offset : Nat)
  | invalidCharacter (offset : Nat)
  | unsupportedSyntax (offset : Nat)
  deriving DecidableEq, Repr

private def identStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
private def identRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

-- The scanner keeps whitespace, comments, quote escapes and exact character spans.
-- Later parsing must account for Python indentation rather than erasing it.
private def scanQuote (fuel : Nat) (quote : Char) (offset : Nat)
    (rest acc : List Char) : Except ParseError (List Char × List Char × Nat) :=
  match fuel, rest with
  | 0, _ => .error (.unterminatedString offset)
  | _, [] => .error (.unterminatedString offset)
  | fuel + 1, c :: cs =>
    if c == quote then .ok ((quote :: acc).reverse, cs, offset + 1)
    else if c == '\\' then
      match cs with
      | [] => .error (.unterminatedString offset)
      | escaped :: tail => scanQuote fuel quote (offset + 2) tail (escaped :: c :: acc)
    else scanQuote fuel quote (offset + 1) cs (c :: acc)

private def scanRegex (fuel : Nat) (offset : Nat) (inClass : Bool)
    (rest acc : List Char) : Except ParseError (List Char × List Char × Nat) :=
  match fuel, rest with
  | 0, _ => .error (.unterminatedString offset)
  | _, [] => .error (.unterminatedString offset)
  | fuel + 1, c :: cs =>
    if c == '\\' then
      match cs with
      | [] => .error (.unterminatedString offset)
      | escaped :: tail => scanRegex fuel (offset + 2) inClass tail (escaped :: c :: acc)
    else if c == '[' then scanRegex fuel (offset + 1) true cs (c :: acc)
    else if c == ']' then scanRegex fuel (offset + 1) false cs (c :: acc)
    else if c == '/' && !inClass then .ok ((c :: acc).reverse, cs, offset + 1)
    else scanRegex fuel (offset + 1) inClass cs (c :: acc)

private def scan (lang : TargetLang) (fuel offset : Nat) (input : List Char)
    (acc : List SourceToken) : Except ParseError (List SourceToken) :=
  match fuel, input with
  | 0, _ => .error (.unsupportedSyntax offset)
  | _, [] => .ok acc.reverse
  | fuel + 1, c :: cs =>
    if c == '"' || c == '\'' || c == '`' then do
      let (quoted, tail, stop) ← scanQuote (cs.length + 1) c (offset + 1) cs [c]
      scan lang fuel stop tail (⟨.quoted, String.mk quoted, offset, stop⟩ :: acc)
    else if c.isWhitespace then
      let tail := cs.takeWhile Char.isWhitespace
      let len := tail.length + 1
      scan lang fuel (offset + len) (cs.dropWhile Char.isWhitespace)
        (⟨.spacing, String.mk (c :: tail), offset, offset + len⟩ :: acc)
    else if identStart c then
      let tail := cs.takeWhile identRest
      let len := tail.length + 1
      scan lang fuel (offset + len) (cs.dropWhile identRest)
        (⟨.identifier, String.mk (c :: tail), offset, offset + len⟩ :: acc)
    else if c.isDigit then
      let tail := cs.takeWhile Char.isDigit
      let len := tail.length + 1
      scan lang fuel (offset + len) (cs.dropWhile Char.isDigit)
        (⟨.numeral, String.mk (c :: tail), offset, offset + len⟩ :: acc)
    else if (lang == .python && c == '#') ||
            (lang == .ts && c == '/' && cs.head? == some '/') then
      let tail := cs.takeWhile (· != '\n')
      let len := tail.length + 1
      scan lang fuel (offset + len) (cs.dropWhile (· != '\n'))
        (⟨.comment, String.mk (c :: tail), offset, offset + len⟩ :: acc)
    else if lang == .ts && c == '/' &&
            (acc.dropWhile (·.kind == .spacing)).head?.map
              (fun t => t.kind == .punctuation && ["=", "(", "!", ",", ":"].contains t.text)
              != some false then do
      let (regex, tail, stop) ← scanRegex (cs.length + 1) (offset + 1) false cs ['/']
      let flags := tail.takeWhile Char.isAlpha
      let after := tail.dropWhile Char.isAlpha
      let last := stop + flags.length
      scan lang fuel last after (⟨.regex, String.mk (regex ++ flags), offset, last⟩ :: acc)
    else if c.toNat < 32 || c.toNat > 126 then .error (.invalidCharacter offset)
    else scan lang fuel (offset + 1) cs
      (⟨.punctuation, String.singleton c, offset, offset + 1⟩ :: acc)

def tokenizeSource (lang : TargetLang) (source : String) : Except ParseError (List SourceToken) :=
  scan lang (source.toList.length + 1) 0 source.toList []

-- Syntax nodes name source operations. User-defined functions do not appear in
-- BuiltinId: their bodies must be parsed into TargetStmt and called normally.
inductive BuiltinId where
  | jsonParse | jsonLoads | number | float | int | typeof | type | isinstance
  | objectPrototype | objectPrototypeToStringCall | objectGetPrototypeOf
  | objectCreate | objectEntries | objectHasOwn | objectOwnDescriptors
  | objectDefineProperty | arrayIsArray | nodeIsProxy | structuredClone
  | deepCopy | dict | list | tuple | set | mappingProxy | objectIdentity
  | regexCompile | regexMatchAt | regexFullmatch | regexExec | regexTest
  | regexMatchEnd | regexGroup | stringReplace | stringJoin | stringSlice
  | stringStartsWith | stringIsSpace | stringIsDigit | stringLength
  | length | stringIndex | arrayIndex | arrayPush | dictGet | dictItems
  | getOrDefault | isFinite | isInteger | abs | isFrozen | freeze
  | setNew | setHas | setAdd | setSize | next | any | enumerate
  deriving DecidableEq, Repr

inductive BinaryOp where
  | add | sub | mul | div | eq | strictEq | ne | strictNe
  | lt | le | gt | ge | inObject | notInObject | isIdentity | isNotIdentity
  deriving DecidableEq, Repr

inductive UnaryOp where
  | not | neg | positive | typeof
  deriving DecidableEq, Repr

inductive TargetExpr where
  | empty | sequence (first rest : TargetExpr)
  | regexLiteral (source : String)
  | undefined | null | bool (b : Bool) | integer (n : Int) | string (s : String)
  | local (name : String) | checkerField (name : String) | global (name : String)
  | property (receiver : TargetExpr) (name : String)
  | optionalProperty (receiver : TargetExpr) (name : String)
  | index (receiver key : TargetExpr)
  | call (callee args : TargetExpr)
  | builtin (id : BuiltinId) (args : TargetExpr)
  | unary (op : UnaryOp) (value : TargetExpr)
  | binary (op : BinaryOp) (left right : TargetExpr)
  | andThen (left right : TargetExpr) | orElse (left right : TargetExpr)
  | nullCoalesce (left right : TargetExpr)
  | conditional (cond yes no : TargetExpr)
  | object (fields : TargetExpr) | objectEntry (key : String) (value rest : TargetExpr)
  | objectSpread (value rest : TargetExpr)
  | array (items : TargetExpr) | tuple (items : TargetExpr)
  | arraySpread (value rest : TargetExpr)
  | postIncrement (name : String)
  | closure (qualifiedName : String)
  | listComprehension (value : TargetExpr) (binders : List String)
      (iterable filter : TargetExpr)
  | dictComprehension (key value : TargetExpr) (binders : List String)
      (iterable filter : TargetExpr)
  | generator (value : TargetExpr) (binders : List String)
      (iterable filter : TargetExpr)
  | formatted (parts : TargetExpr)
  | formatPart (text : String) (value rest : TargetExpr)
  deriving DecidableEq, Repr

inductive AssignTarget where
  | local (name : String) | field (name : String)
  | property (receiver : TargetExpr) (name : String)
  | index (receiver key : TargetExpr)
  deriving DecidableEq, Repr

inductive TargetStmt where
  | empty | sequence (first rest : TargetStmt)
  | letLocal (name : String) (value : TargetExpr)
  | assign (target : AssignTarget) (value : TargetExpr)
  | doExpr (value : TargetExpr)
  | ifThenElse (cond : TargetExpr) (yes no : TargetStmt)
  | forDo (binders : List String) (iterable : TargetExpr) (body : TargetStmt)
  | whileDo (cond : TargetExpr) (body : TargetStmt)
  | returnValue (value : TargetExpr) | returnVoid
  | throwValue (value : TargetExpr) | rethrow
  | breakTarget (label : String) | continueTarget (label : String)
  | tryCatchFinally (body : TargetStmt) (binder : Option String)
      (handler cleanup : TargetStmt)
  deriving DecidableEq, Repr

structure ParamSpec where
  name : String
  defaultValue : Option TargetExpr
  deriving DecidableEq, Repr

structure TargetFunction where
  qualifiedName : String
  params : List ParamSpec
  body : TargetStmt
  deriving DecidableEq, Repr

structure TargetProgram where
  lang : TargetLang
  moduleInit : TargetStmt
  classFields : TargetStmt
  functions : List TargetFunction
  worldData : TargetExpr
  contextDefaultsData : TargetExpr
  deriving DecidableEq, Repr

-- The full statement grammar, independent SourceParses relation and checked
-- desugaring are still Task 2 RED. Tokens and schema carry no behavior theorem.

end Harmonia.Applications.Kadmos.Generated
