import Harmonia.Applications.Kadmos.Generated.TargetSyntax

namespace Harmonia.Applications.Kadmos.Generated

private def significant (xs : List SourceToken) : List String :=
  (xs.filter (fun t => t.kind != .spacing && t.kind != .comment)).map SourceToken.text

private def combineSymbols : List String → List String
  | "+" :: "+" :: rest => "++" :: combineSymbols rest
  | "is" :: "not" :: rest => "is not" :: combineSymbols rest
  | "not" :: "in" :: rest => "not in" :: combineSymbols rest
  | "." :: "." :: "." :: rest => "..." :: combineSymbols rest
  | "=" :: "=" :: "=" :: rest => "===" :: combineSymbols rest
  | "!" :: "=" :: "=" :: rest => "!==" :: combineSymbols rest
  | "=" :: "=" :: rest => "==" :: combineSymbols rest
  | "!" :: "=" :: rest => "!=" :: combineSymbols rest
  | ">" :: "=" :: rest => ">=" :: combineSymbols rest
  | "<" :: "=" :: rest => "<=" :: combineSymbols rest
  | "&" :: "&" :: rest => "&&" :: combineSymbols rest
  | "|" :: "|" :: rest => "||" :: combineSymbols rest
  | "?" :: "?" :: rest => "??" :: combineSymbols rest
  | "?" :: "." :: rest => "?." :: combineSymbols rest
  | "=" :: ">" :: rest => "=>" :: combineSymbols rest
  | "/" :: "/" :: rest => "//" :: combineSymbols rest
  | "*" :: "*" :: rest => "**" :: combineSymbols rest
  | x :: rest => x :: combineSymbols rest
  | [] => []

private def tokenIsIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_' || c == '$') &&
      cs.all (fun x => x.isAlphanum || x == '_' || x == '$')

private def decimalToken (s : String) : Bool :=
  match s.splitOn "." with
  | [whole, fraction] => !whole.isEmpty && !fraction.isEmpty &&
      whole.toList.all Char.isDigit && fraction.toList.all Char.isDigit
  | _ => false

private def quotedContent (s : String) : Option String :=
  match s.toList with
  | '"' :: xs =>
      match xs.reverse with
      | '"' :: inner => some (String.mk inner.reverse)
      | _ => none
  | '\'' :: xs =>
      match xs.reverse with
      | '\'' :: inner => some (String.mk inner.reverse)
      | _ => none
  | _ => none

private def unescapeChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: c :: rest => do
      let decoded ← match c with
        | '"' => some '"' | '\'' => some '\'' | '\\' => some '\\'
        | '/' => some '/' | 'n' => some '\n' | 'r' => some '\r'
        | 't' => some '\t' | _ => none
      return decoded :: (← unescapeChars rest)
  | '\\' :: [] => none
  | c :: rest => return c :: (← unescapeChars rest)

private def decodedQuoted (s : String) : Option String := do
  let raw ← quotedContent s
  return String.mk (← unescapeChars raw.toList)

private def templateContent (s : String) : Option String :=
  match s.toList with
  | '`' :: xs =>
      match xs.reverse with
      | '`' :: inner => some (String.mk inner.reverse)
      | _ => none
  | _ => none

private def takeFormatPrefix (lang : TargetLang) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | '$' :: '{' :: rest =>
      if lang == .ts then ([], some rest)
      else let (head, tail) := takeFormatPrefix lang ('{' :: rest)
           ('$' :: head, tail)
  | '{' :: rest =>
      if lang == .python then ([], some rest)
      else let (head, tail) := takeFormatPrefix lang rest
           ('{' :: head, tail)
  | c :: rest =>
      let (head, tail) := takeFormatPrefix lang rest
      (c :: head, tail)

private def precedence : String → Nat
  | "??" | "||" | "or" => 2
  | "&&" | "and" => 3
  | "==" | "===" | "!=" | "!==" | "is" | "is not" => 4
  | ">" | ">=" | "<" | "<=" | "in" | "not in" | "instanceof" => 5
  | "+" | "-" => 6
  | "*" | "/" => 7
  | _ => 0

private def combineBinary (op : String) (left right : TargetExpr) : TargetExpr :=
  match op with
  | "+" => .binary .add left right
  | "-" => .binary .sub left right
  | "*" => .binary .mul left right
  | "/" => .binary .div left right
  | "==" => .binary .eq left right
  | "===" => .binary .strictEq left right
  | "!=" => .binary .ne left right
  | "!==" => .binary .strictNe left right
  | ">" => .binary .gt left right
  | ">=" => .binary .ge left right
  | "<" => .binary .lt left right
  | "<=" => .binary .le left right
  | "in" => .binary .inObject left right
  | "not in" => .binary .notInObject left right
  | "is" => .binary .isIdentity left right
  | "is not" => .binary .isNotIdentity left right
  | "instanceof" => .binary .instanceOf left right
  | "&&" | "and" => .andThen left right
  | "||" | "or" => .orElse left right
  | "??" => .nullCoalesce left right
  | _ => left

private def parseLambdaParams : List String → Except ParseError (List String × List String)
  | ":" :: rest => .ok ([], rest)
  | name :: "," :: rest => do
      if !tokenIsIdentifier name then throw (.unsupportedSyntax 0)
      let (others, after) ← parseLambdaParams rest
      return (name :: others, after)
  | name :: ":" :: rest =>
      if tokenIsIdentifier name then .ok ([name], rest)
      else .error (.unsupportedSyntax 0)
  | _ => .error (.unsupportedSyntax 0)

private def typeBoundary (token : String) : Bool :=
  ["as", ",", ")", "}", ":", ";", "?", "&&", "||", "??", "+", "-", "*", "/",
   "==", "===", "!=", "!==", "in", "is"].contains token

private def typeToken (token : String) : Bool :=
  tokenIsIdentifier token || token.toNat?.isSome ||
    ["<", ">", "[", "]", "|", ".", ","].contains token ||
    (quotedContent token).isSome

private def takeCastType (fuel angle bracket : Nat) (acc : List String) :
    List String → Except ParseError (String × List String)
  | [] =>
      if angle == 0 && bracket == 0 && !acc.isEmpty then
        .ok (String.join acc.reverse, [])
      else .error (.unsupportedSyntax 0)
  | token :: rest =>
      match fuel with
      | 0 => .error (.unsupportedSyntax 0)
      | fuel + 1 =>
          if angle == 0 && bracket == 0 && (typeBoundary token || token == "]" || token == ">") then
            if acc.isEmpty then .error (.unsupportedSyntax 0)
            else .ok (String.join acc.reverse, token :: rest)
          else if !typeToken token then .error (.unsupportedSyntax 0)
          else if token == "<" then takeCastType fuel (angle + 1) bracket (token :: acc) rest
          else if token == ">" then takeCastType fuel (angle - 1) bracket (token :: acc) rest
          else if token == "[" then takeCastType fuel angle (bracket + 1) (token :: acc) rest
          else if token == "]" then takeCastType fuel angle (bracket - 1) (token :: acc) rest
          else takeCastType fuel angle bracket (token :: acc) rest

mutual

private def parseFormatParts (fuel : Nat) (lang : TargetLang) (chars : List Char) :
    Except ParseError TargetExpr :=
  match fuel with
  | 0 => .error (.unsupportedSyntax 0)
  | fuel + 1 => do
      let (headText, rest) := takeFormatPrefix lang chars
      match rest with
      | none => return .formatPart (String.mk headText) .empty .empty
      | some afterOpen =>
          let inner := afterOpen.takeWhile (· != '}')
          match afterOpen.dropWhile (· != '}') with
          | [] => throw (.unsupportedSyntax 0)
          | _ :: after =>
              let tokens := combineSymbols (significant (← tokenizeSource lang (String.mk inner)))
              let (value, remaining) ← parseExprAt fuel 0 tokens
              if !remaining.isEmpty then throw (.unsupportedSyntax 0)
              let next ← if after.isEmpty then .ok TargetExpr.empty
                else parseFormatParts fuel lang after
              return .formatPart (String.mk headText) value next

private def parseHead (fuel : Nat) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, [] => .error (.unsupportedSyntax 0)
  | fuel + 1, "!" :: rest => do
      let (value, tail) ← parseExprAt fuel 8 rest
      return (.unary .not value, tail)
  | fuel + 1, "typeof" :: rest => do
      let (value, tail) ← parseExprAt fuel 8 rest
      return (.unary .typeof value, tail)
  | fuel + 1, "new" :: rest => do
      let (value, tail) ← parseExprAt fuel 8 rest
      return (.newExpr value, tail)
  | fuel + 1, "lambda" :: rest => do
      let (params, bodyTokens) ← parseLambdaParams rest
      let (body, tail) ← parseExprAt fuel 0 bodyTokens
      return (.lambdaExpr params body, tail)
  | fuel + 1, "(" :: name :: ")" :: "=>" :: rest => do
      if !tokenIsIdentifier name then throw (.unsupportedSyntax 0)
      let (body, tail) ← parseExprAt fuel 0 rest
      return (.lambdaExpr [name] body, tail)
  | fuel + 1, "not" :: rest => do
      let (value, tail) ← parseExprAt fuel 8 rest
      return (.unary .not value, tail)
  | fuel + 1, "-" :: rest => do
      let (value, tail) ← parseExprAt fuel 8 rest
      return (.unary .neg value, tail)
  | fuel + 1, "(" :: rest => do
      let (inside, tail) ← parseExprAt fuel 0 rest
      match tail with
      | ")" :: after => return (inside, after)
      | "for" :: after =>
          let (binders, iterable, filter, remaining) ← parseCompClause fuel after
          match remaining with
          | ")" :: final => return (.generator inside binders iterable filter, final)
          | _ => throw (.unsupportedSyntax 0)
      | "," :: after =>
          let (others, remaining) ← parseArgList fuel after
          return (.tuple (.sequence inside others), remaining)
      | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, "{" :: rest => do
      let (fields, tail) ← parseObjectFields fuel rest
      match fields with
      | .dictComprehension key value binders iterable filter =>
          return (.dictComprehension key value binders iterable filter, tail)
      | _ => return (.object fields, tail)
  | fuel + 1, "[" :: rest => do
      let (items, tail) ← parseArrayElems fuel rest
      match items with
      | .listComprehension value binders iterable filter =>
          return (.listComprehension value binders iterable filter, tail)
      | _ => return (.array items, tail)
  | _, "r" :: token :: rest =>
      match quotedContent token with
      | some raw => .ok (.string raw, rest)
      | none => .ok (.local "r", token :: rest)
  | fuel + 1, "f" :: token :: rest => do
      let content ← match decodedQuoted token with
        | some s => .ok s
        | none => .error (.unsupportedSyntax 0)
      let parts ← parseFormatParts fuel .python content.toList
      return (.formatted parts, rest)
  | fuel + 1, token :: rest =>
      if token == "true" || token == "True" then .ok (.bool true, rest)
      else if token == "false" || token == "False" then .ok (.bool false, rest)
      else if ["null", "None"].contains token then .ok (.null, rest)
      else if token == "undefined" then .ok (.undefined, rest)
      else match token.toNat? with
        | some n => .ok (.integer (Int.ofNat n), rest)
        | none => match templateContent token with
          | some s => do
              let parts ← parseFormatParts fuel .ts s.toList
              .ok (.formatted parts, rest)
          | none => match decodedQuoted token with
            | some s => .ok (.string s, rest)
            | none =>
                if decimalToken token then .ok (.decimal token, rest)
                else if token.startsWith "/" && token.length > 1 then
                  .ok (.regexLiteral token, rest)
                else if tokenIsIdentifier token then .ok (.local token, rest)
                else .error (.unsupportedSyntax 0)

private def parsePostfix (fuel : Nat) (left : TargetExpr) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, "++" :: rest =>
      match left with
      | .local name => parsePostfix fuel (.postIncrement name) rest
      | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, "." :: "#" :: name :: rest =>
      if tokenIsIdentifier name then parsePostfix fuel (.property left ("#" ++ name)) rest
      else throw (.unsupportedSyntax 0)
  | fuel + 1, "." :: name :: rest =>
      if tokenIsIdentifier name then parsePostfix fuel (.property left name) rest
      else throw (.unsupportedSyntax 0)
  | fuel + 1, "?." :: name :: rest =>
      if tokenIsIdentifier name then parsePostfix fuel (.optionalProperty left name) rest
      else throw (.unsupportedSyntax 0)
  | fuel + 1, "!" :: rest => parsePostfix fuel (.nonNull left) rest
  | fuel + 1, "(" :: rest => do
      let (args, tail) ← parseArgList fuel rest
      parsePostfix fuel (.call left args) tail
  | fuel + 1, "[" :: rest => do
      let (key, tail) ← parseExprAt fuel 0 rest
      match tail with
      | "]" :: after => parsePostfix fuel (.index left key) after
      | ":" :: after =>
          let (stop, remaining) ← parseExprAt fuel 0 after
          match remaining with
          | "]" :: final => parsePostfix fuel (.slice left key stop) final
          | _ => throw (.unsupportedSyntax 0)
      | _ => throw (.unsupportedSyntax 0)
  | _, _ => .ok (left, tokens)

private def parseArgList (fuel : Nat) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, ")" :: rest => .ok (.empty, rest)
  | fuel + 1, _ => do
      let (arg, tail) ← parseExprAt fuel 0 tokens
      match tail with
      | "for" :: after =>
          let (binders, iterable, filter, remaining) ← parseCompClause fuel after
          match remaining with
          | ")" :: final => return (.sequence (.generator arg binders iterable filter) .empty, final)
          | _ => throw (.unsupportedSyntax 0)
      | ")" :: rest => return (.sequence arg .empty, rest)
      | "," :: rest =>
          let (others, after) ← parseArgList fuel rest
          return (.sequence arg others, after)
      | _ => throw (.unsupportedSyntax 0)

private def parseObjectFields (fuel : Nat) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, "}" :: rest => .ok (.empty, rest)
  | fuel + 1, "..." :: rest => do
      let (value, tail) ← parseExprAt fuel 0 rest
      match tail with
      | "}" :: after => return (.objectSpread value .empty, after)
      | "," :: after =>
          let (other, remaining) ← parseObjectFields fuel after
          return (.objectSpread value other, remaining)
      | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, "**" :: rest => do
      let (value, tail) ← parseExprAt fuel 0 rest
      match tail with
      | "}" :: after => return (.objectSpread value .empty, after)
      | "," :: after =>
          let (other, remaining) ← parseObjectFields fuel after
          return (.objectSpread value other, remaining)
      | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, key :: ":" :: rest => do
      let name ← match decodedQuoted key with
        | some s => .ok s
        | none => if tokenIsIdentifier key then .ok key else .error (.unsupportedSyntax 0)
      let (value, tail) ← parseExprAt fuel 0 rest
      match tail with
      | "for" :: after =>
          let (binders, iterable, filter, remaining) ← parseCompClause fuel after
          let keyExpr := if (decodedQuoted key).isSome then TargetExpr.string name
            else TargetExpr.local name
          match remaining with
          | "}" :: final => return (.dictComprehension keyExpr value binders iterable filter, final)
          | _ => throw (.unsupportedSyntax 0)
      | "}" :: after => return (.objectEntry name value .empty, after)
      | "," :: after =>
          let (other, remaining) ← parseObjectFields fuel after
          return (.objectEntry name value other, remaining)
      | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, key :: "," :: rest =>
      if tokenIsIdentifier key then do
        let (other, remaining) ← parseObjectFields fuel rest
        return (.objectEntry key (.local key) other, remaining)
      else throw (.unsupportedSyntax 0)
  | _, key :: "}" :: rest =>
      if tokenIsIdentifier key then .ok (.objectEntry key (.local key) .empty, rest)
      else .error (.unsupportedSyntax 0)
  | _, _ => .error (.unsupportedSyntax 0)

private def parseArrayElems (fuel : Nat) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, "]" :: rest => .ok (.empty, rest)
  | fuel + 1, "..." :: rest => do
      let (value, tail) ← parseExprAt fuel 0 rest
      match tail with
      | "]" :: after => return (.arraySpread value .empty, after)
      | "," :: after =>
          let (other, remaining) ← parseArrayElems fuel after
          return (.arraySpread value other, remaining)
      | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, _ => do
      let (value, tail) ← parseExprAt fuel 0 tokens
      match tail with
      | "for" :: after =>
          let (binders, iterable, filter, remaining) ← parseCompClause fuel after
          match remaining with
          | "]" :: final => return (.listComprehension value binders iterable filter, final)
          | _ => throw (.unsupportedSyntax 0)
      | "]" :: after => return (.sequence value .empty, after)
      | "," :: after =>
          let (other, remaining) ← parseArrayElems fuel after
          return (.sequence value other, remaining)
      | _ => throw (.unsupportedSyntax 0)

private def parseCompBinders (fuel : Nat) (tokens : List String) :
    Except ParseError (List String × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, name :: "," :: rest =>
      if tokenIsIdentifier name then do
        let (others, after) ← parseCompBinders fuel rest
        return (name :: others, after)
      else throw (.unsupportedSyntax 0)
  | _, name :: "in" :: rest =>
      if tokenIsIdentifier name then .ok ([name], rest)
      else .error (.unsupportedSyntax 0)
  | _, _ => .error (.unsupportedSyntax 0)

private def parseCompClause (fuel : Nat) (tokens : List String) :
    Except ParseError (List String × TargetExpr × TargetExpr × List String) :=
  match fuel with
  | 0 => .error (.unsupportedSyntax 0)
  | fuel + 1 => do
      let (binders, after) ← parseCompBinders fuel tokens
      let (iterable, tail) ← parseExprAt fuel 2 after
      match tail with
      | "if" :: rest =>
          let (filter, final) ← parseExprAt fuel 2 rest
          return (binders, iterable, filter, final)
      | _ => return (binders, iterable, .empty, tail)

private def parseRest (fuel minPrec : Nat) (left : TargetExpr) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel, tokens with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, [] => .ok (left, [])
  | fuel + 1, "as" :: rest => do
      let (kind, remaining) ← takeCastType (rest.length + 1) 0 0 [] rest
      parseRest fuel minPrec (.typeCast left kind) remaining
  | fuel + 1, "?" :: rest =>
      if minPrec > 1 then .ok (left, "?" :: rest)
      else do
        let (yes, tail) ← parseExprAt fuel 0 rest
        match tail with
        | ":" :: after =>
            let (no, remaining) ← parseExprAt fuel 1 after
            parseRest fuel minPrec (.conditional left yes no) remaining
        | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, "if" :: rest =>
      if minPrec > 1 then .ok (left, "if" :: rest)
      else do
        let (cond, tail) ← parseExprAt fuel 0 rest
        match tail with
        | "else" :: after =>
            let (no, remaining) ← parseExprAt fuel 1 after
            parseRest fuel minPrec (.conditional cond left no) remaining
        | _ => throw (.unsupportedSyntax 0)
  | fuel + 1, op :: rest =>
      let prec := precedence op
      if prec == 0 || prec < minPrec then .ok (left, op :: rest)
      else do
        let (right, tail) ← parseExprAt fuel (prec + 1) rest
        parseRest fuel minPrec (combineBinary op left right) tail

private def parseExprAt (fuel minPrec : Nat) (tokens : List String) :
    Except ParseError (TargetExpr × List String) :=
  match fuel with
  | 0 => .error (.unsupportedSyntax 0)
  | fuel + 1 => do
      let (head, tail) ← parseHead fuel tokens
      let (head, tail) ← parsePostfix fuel head tail
      parseRest fuel minPrec head tail

end

def parseTargetExpr (lang : TargetLang) (source : String) :
    Except ParseError TargetExpr := do
  let tokens := combineSymbols (significant (← tokenizeSource lang source))
  let (expr, tail) ← parseExprAt ((tokens.length + 1) * 16) 0 tokens
  if tail.isEmpty then return expr
  else throw (.unsupportedSyntax 0)

end Harmonia.Applications.Kadmos.Generated
