import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser

namespace Harmonia.Applications.Kadmos.Generated

structure PythonLine where
  indent : Nat
  text : String
  deriving DecidableEq, Repr

private def classifyLine (line : String) : Option PythonLine :=
  let chars := line.toList
  let leading := chars.takeWhile (· == ' ')
  let body := String.mk (chars.dropWhile (· == ' '))
  let trimmed := String.mk ((body.toList.reverse.dropWhile (· == ' ')).reverse)
  if trimmed.isEmpty || trimmed.startsWith "#" then none
  else some ⟨leading.length, trimmed⟩

def pythonLines (source : String) : List PythonLine :=
  (source.splitOn "\n").filterMap classifyLine

private def withoutColon (s : String) : Except ParseError String :=
  match s.toList.reverse with
  | ':' :: rest => .ok (String.mk rest.reverse)
  | _ => .error (.unsupportedSyntax 0)

private def assignmentOffset (depth : Nat) (previous : Option String) :
    List SourceToken → Option Nat
  | [] => none
  | token :: rest =>
      let current := token.text
      if current == "=" && depth == 0 && previous != some "=" &&
          previous != some "!" && previous != some "<" && previous != some ">" &&
          rest.head?.map SourceToken.text != some "=" then some token.start
      else if ["(", "[", "{"].contains current then
        assignmentOffset (depth + 1) (some current) rest
      else if [")", "]", "}"].contains current then
        assignmentOffset (depth - 1) (some current) rest
      else assignmentOffset depth (some current) rest

private def splitAssignment (s : String) : Except ParseError (Option (String × String)) := do
  let all ← tokenizeSource .python s
  let significant := all.filter (fun t => t.kind != .spacing && t.kind != .comment)
  match assignmentOffset 0 none significant with
  | none => return none
  | some pos => return some (String.mk (s.toList.take pos),
      String.mk (s.toList.drop (pos + 1)))

private def augmentationOffset (depth : Nat) : List SourceToken → Option (Nat × Nat)
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if depth == 0 && first.text == "+" && second.text == "=" &&
          first.stop == second.start then some (first.start, second.stop)
      else if ["(", "[", "{"].contains first.text then
        augmentationOffset (depth + 1) (second :: rest)
      else if [")", "]", "}"].contains first.text then
        augmentationOffset (depth - 1) (second :: rest)
      else augmentationOffset depth (second :: rest)

private def splitAugmentation (s : String) : Except ParseError (Option (String × String)) := do
  let all ← tokenizeSource .python s
  let significant := all.filter (fun t => t.kind != .spacing && t.kind != .comment)
  match augmentationOffset 0 significant with
  | none => return none
  | some (start, stop) => return some (String.mk (s.toList.take start),
      String.mk (s.toList.drop stop))

private def annotationOffset (depth : Nat) : List SourceToken → Option Nat
  | [] => none
  | token :: rest =>
      if token.text == ":" && depth == 0 then some token.start
      else if ["(", "[", "{"].contains token.text then annotationOffset (depth + 1) rest
      else if [")", "]", "}"].contains token.text then annotationOffset (depth - 1) rest
      else annotationOffset depth rest

private def stripAnnotation (left : String) : Except ParseError String := do
  let all ← tokenizeSource .python left
  let significant := all.filter (fun t => t.kind != .spacing && t.kind != .comment)
  match annotationOffset 0 significant with
  | none => return left
  | some pos => return String.mk (left.toList.take pos)

private def assignmentTarget : TargetExpr → Except ParseError AssignTarget
  | .local name => .ok (.local name)
  | .property receiver name => .ok (.property receiver name)
  | .index receiver key => .ok (.index receiver key)
  | _ => .error (.unsupportedSyntax 0)

private def trimSpaces (s : String) : String :=
  let chars := s.toList.dropWhile (· == ' ')
  String.mk ((chars.reverse.dropWhile (· == ' ')).reverse)

private def validBinder (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') &&
      cs.all (fun x => x.isAlphanum || x == '_')

private def parseForHeader (s : String) : Except ParseError (List String × TargetExpr) := do
  let noColon ← withoutColon (s.drop 4)
  match noColon.splitOn " in " with
  | [binderText, iterableText] =>
      let binders := (binderText.splitOn ",").map trimSpaces
      if binders.isEmpty || !binders.all validBinder then throw (.unsupportedSyntax 0)
      return (binders, ← parseTargetExpr .python iterableText)
  | _ => throw (.unsupportedSyntax 0)

private def parseExceptHeader (s : String) : Except ParseError (Option String × Option String) := do
  let text ← withoutColon (s.drop 7)
  match text.splitOn " as " with
  | [kind] =>
      if validBinder kind then return (some kind, none)
      else throw (.unsupportedSyntax 0)
  | [kind, binder] =>
      if validBinder kind && validBinder binder then return (some kind, some binder)
      else throw (.unsupportedSyntax 0)
  | _ => throw (.unsupportedSyntax 0)

private def parseParameter (source : String) : Except ParseError ParamSpec := do
  let parts := source.splitOn "="
  let (namePart, defaultPart) ← match parts with
    | [name] => .ok (name, none)
    | [name, value] => .ok (name, some value)
    | _ => .error (.unsupportedSyntax 0)
  let name := trimSpaces (← stripAnnotation namePart)
  if !validBinder name then throw (.unsupportedSyntax 0)
  let value ← (match defaultPart with
    | none => .ok none
    | some source => do return some (← parseTargetExpr .python source) :
      Except ParseError (Option TargetExpr))
  return ⟨name, value⟩

private def splitParamsAux (depth : Nat) (current : List Char) (acc : List String) :
    List Char → Except ParseError (List String)
  | [] =>
      if depth == 0 then .ok ((String.mk current.reverse :: acc).reverse)
      else .error (.unsupportedSyntax 0)
  | '[' :: rest => splitParamsAux (depth + 1) ('[' :: current) acc rest
  | ']' :: rest =>
      if depth == 0 then .error (.unsupportedSyntax 0)
      else splitParamsAux (depth - 1) (']' :: current) acc rest
  | ',' :: rest =>
      if depth == 0 then splitParamsAux depth [] (String.mk current.reverse :: acc) rest
      else splitParamsAux depth (',' :: current) acc rest
  | c :: rest => splitParamsAux depth (c :: current) acc rest

private def splitParams (s : String) : Except ParseError (List String) :=
  splitParamsAux 0 [] [] s.toList

private def parseDefHeader (source : String) : Except ParseError (String × List ParamSpec) := do
  if !source.endsWith ":" then throw (.unsupportedSyntax 0)
  match (source.drop 4).splitOn "(" with
  | [name, tail] =>
      let name := trimSpaces name
      if !validBinder name then throw (.unsupportedSyntax 0)
      match tail.splitOn ")" with
      | [params, _returnAnnotation] =>
          let paramSpecs ← if params.isEmpty then .ok []
            else (← splitParams params).mapM parseParameter
          return (name, paramSpecs)
      | _ => throw (.unsupportedSyntax 0)
  | _ => throw (.unsupportedSyntax 0)

private def parseImportLine (source : String) : Except ParseError TargetStmt := do
  if source.startsWith "import " then
    match (source.drop 7).splitOn " as " with
    | [name] => return .importModule name name
    | [name, alias] => return .importModule name alias
    | _ => throw (.unsupportedSyntax 0)
  else if source.startsWith "from " then
    match (source.drop 5).splitOn " import " with
    | [moduleName, binding] =>
        match binding.splitOn " as " with
        | [name] => return .fromImport moduleName name name
        | [name, alias] => return .fromImport moduleName name alias
        | _ => throw (.unsupportedSyntax 0)
    | _ => throw (.unsupportedSyntax 0)
  else throw (.unsupportedSyntax 0)

mutual

private def parsePythonSuite (fuel indent : Nat) (lines : List PythonLine) :
    Except ParseError (TargetStmt × List PythonLine) :=
  match fuel, lines with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, [] => .ok (.empty, [])
  | fuel + 1, line :: rest =>
      if line.indent < indent then .ok (.empty, line :: rest)
      else if line.indent > indent then .error (.unsupportedSyntax 0)
      else do
        let (stmt, after) ← parsePythonStatement fuel indent line.text rest
        let (more, tail) ← parsePythonSuite fuel indent after
        return (.sequence stmt more, tail)

private def parsePythonElse (fuel indent : Nat) (lines : List PythonLine) :
    Except ParseError (TargetStmt × List PythonLine) :=
  match fuel, lines with
  | 0, _ => .error (.unsupportedSyntax 0)
  | _, [] => .ok (.empty, [])
  | fuel + 1, line :: rest =>
      if line.indent != indent then .ok (.empty, line :: rest)
      else if line.text == "else:" then parsePythonSuite fuel (indent + 4) rest
      else if line.text.startsWith "elif " then
        parsePythonStatement fuel indent ("if " ++ line.text.drop 5) rest
      else .ok (.empty, line :: rest)

private def parsePythonTryTail (fuel indent : Nat) (body : TargetStmt)
    (lines : List PythonLine) : Except ParseError (TargetStmt × List PythonLine) :=
  match fuel with
  | 0 => .error (.unsupportedSyntax 0)
  | fuel + 1 => do
      let (catchType, binder, handler, afterCatch) ←
        match lines with
        | line :: rest =>
            if line.indent == indent && line.text.startsWith "except " then do
              let (kind, binder) ← parseExceptHeader line.text
              let (handler, tail) ← parsePythonSuite fuel (indent + 4) rest
              .ok (kind, binder, handler, tail)
            else .ok (none, none, TargetStmt.empty, lines)
        | [] => .ok (none, none, TargetStmt.empty, [])
      match afterCatch with
      | line :: rest =>
          if line.indent == indent && line.text == "finally:" then do
            let (cleanup, tail) ← parsePythonSuite fuel (indent + 4) rest
            return (.tryCatchFinally body catchType binder handler cleanup, tail)
          else if catchType.isSome then
            return (.tryCatchFinally body catchType binder handler .empty, afterCatch)
          else throw (.unsupportedSyntax 0)
      | [] =>
          if catchType.isSome then return (.tryCatchFinally body catchType binder handler .empty, [])
          else throw (.unsupportedSyntax 0)

private def parsePythonStatement (fuel indent : Nat) (source : String)
    (lines : List PythonLine) : Except ParseError (TargetStmt × List PythonLine) :=
  match fuel with
  | 0 => .error (.unsupportedSyntax 0)
  | fuel + 1 =>
      if source.startsWith "import " || source.startsWith "from " then do
        return (← parseImportLine source, lines)
      else if source.startsWith "class " then do
        if !source.endsWith ":" then throw (.unsupportedSyntax 0)
        match (source.drop 6).splitOn "(" with
        | [name, tail] =>
            if !validBinder name then throw (.unsupportedSyntax 0)
            match tail.splitOn ")" with
            | [baseText, ":"] =>
                let base ← parseTargetExpr .python baseText
                let (body, after) ← parsePythonSuite fuel (indent + 4) lines
                return (.defineClass name base body, after)
            | _ => throw (.unsupportedSyntax 0)
        | _ => throw (.unsupportedSyntax 0)
      else if source == "@property" then do
        match lines with
        | header :: rest => do
            if header.indent != indent || !header.text.startsWith "def " then
              throw (.unsupportedSyntax 0)
            let (name, params) ← parseDefHeader header.text
            if params.map ParamSpec.name != ["self"] then throw (.unsupportedSyntax 0)
            let (body, after) ← parsePythonSuite fuel (indent + 4) rest
            return (.defineGetter name body, after)
        | [] => throw (.unsupportedSyntax 0)
      else if source.startsWith "def " then do
        let (name, params) ← parseDefHeader source
        let (body, after) ← parsePythonSuite fuel (indent + 4) lines
        let explicitParams := if indent == 4 && params.head?.map ParamSpec.name == some "self"
          then params.drop 1 else params
        return (.defineFunction name explicitParams body, after)
      else if source.startsWith "if " then do
        let condText ← withoutColon (source.drop 3)
        let cond ← parseTargetExpr .python condText
        let (yes, after) ← parsePythonSuite fuel (indent + 4) lines
        let (no, tail) ← parsePythonElse fuel indent after
        return (.ifThenElse cond yes no, tail)
      else if source.startsWith "for " then do
        let (binders, iterable) ← parseForHeader source
        let (body, after) ← parsePythonSuite fuel (indent + 4) lines
        return (.forDo binders iterable body, after)
      else if source.startsWith "while " then do
        let cond ← parseTargetExpr .python (← withoutColon (source.drop 6))
        let (body, after) ← parsePythonSuite fuel (indent + 4) lines
        return (.whileDo cond body, after)
      else if source == "try:" then do
        let (body, after) ← parsePythonSuite fuel (indent + 4) lines
        parsePythonTryTail fuel indent body after
      else if source.startsWith "raise " then do
        let expr ← parseTargetExpr .python (source.drop 6)
        return (.throwValue expr, lines)
      else if source == "raise" then return (.rethrow, lines)
      else if source.startsWith "return " then do
        let expr ← parseTargetExpr .python (source.drop 7)
        return (.returnValue expr, lines)
      else if source == "return" then return (.returnVoid, lines)
      else if source == "break" then return (.breakTarget "loop", lines)
      else if source == "continue" then return (.continueTarget "loop", lines)
      else if source.startsWith "nonlocal " then do
        let names := ((source.drop 9).splitOn ",").map trimSpaces
        if names.isEmpty || !names.all validBinder then throw (.unsupportedSyntax 0)
        return (.nonlocalNames names, lines)
      else do
        match ← splitAugmentation source with
        | some (left, right) =>
            let lhs ← assignmentTarget (← parseTargetExpr .python left)
            let rhs ← parseTargetExpr .python right
            return (.augment lhs .add rhs, lines)
        | none =>
            match ← splitAssignment source with
            | some (left, right) =>
                let left ← stripAnnotation left
                let lhs ← if (left.splitOn ",").length > 1 then do
                    let names := (left.splitOn ",").map trimSpaces
                    if !names.all validBinder then throw (.unsupportedSyntax 0)
                    .ok (AssignTarget.tupleLocals names)
                  else assignmentTarget (← parseTargetExpr .python left)
                let rhs ← parseTargetExpr .python right
                return (.assign lhs rhs, lines)
            | none =>
                let expr ← parseTargetExpr .python source
                return (.doExpr expr, lines)

end

def parsePythonBlock (source : String) (indent : Nat) : Except ParseError TargetStmt := do
  let lines := pythonLines source
  let (body, rest) ← parsePythonSuite (lines.length * 2 + 1) indent lines
  if rest.isEmpty then return body
  else throw (.unsupportedSyntax 0)

def parsePythonProgram (source : String) : Except ParseError TargetProgram := do
  let moduleBody ← parsePythonBlock source 0
  return ⟨.python, moduleBody, .empty, [], .local "_WORLD", .local "_DEFAULTS"⟩

end Harmonia.Applications.Kadmos.Generated
