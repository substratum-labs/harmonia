import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser

namespace Harmonia.Applications.Kadmos.Generated

private def renderAfter (previousStop : Nat) : List SourceToken → String
  | [] => ""
  | token :: rest =>
      (if previousStop == token.start then "" else " ") ++ token.text ++
        renderAfter token.stop rest

private def render : List SourceToken → String
  | [] => ""
  | first :: rest => first.text ++ renderAfter first.stop rest

private def significant (tokens : List SourceToken) : List SourceToken :=
  tokens.filter (fun t => t.kind != .spacing && t.kind != .comment)

private def updateDepth (depth : Nat × Nat × Nat) (token : String) : Nat × Nat × Nat :=
  match token with
  | "(" => (depth.1 + 1, depth.2.1, depth.2.2)
  | ")" => (depth.1 - 1, depth.2.1, depth.2.2)
  | "[" => (depth.1, depth.2.1 + 1, depth.2.2)
  | "]" => (depth.1, depth.2.1 - 1, depth.2.2)
  | "{" => (depth.1, depth.2.1, depth.2.2 + 1)
  | "}" => (depth.1, depth.2.1, depth.2.2 - 1)
  | _ => depth

private def atTop (depth : Nat × Nat × Nat) : Bool :=
  depth.1 == 0 && depth.2.1 == 0 && depth.2.2 == 0

private def takeStatement (fuel : Nat) (depth : Nat × Nat × Nat)
    (acc : List SourceToken) : List SourceToken → Except ParseError (List SourceToken × List SourceToken)
  | [] => .error (.unsupportedSyntax 0)
  | token :: rest =>
      match fuel with
      | 0 => .error (.unsupportedSyntax token.start)
      | fuel + 1 =>
          if token.text == ";" && atTop depth then .ok (acc.reverse, rest)
          else takeStatement fuel (updateDepth depth token.text) (token :: acc) rest

private def takeDelimited (fuel : Nat) (opening closing : String) (depth : Nat)
    (acc : List SourceToken) : List SourceToken → Except ParseError (List SourceToken × List SourceToken)
  | [] => .error (.unsupportedSyntax 0)
  | token :: rest =>
      match fuel with
      | 0 => .error (.unsupportedSyntax token.start)
      | fuel + 1 =>
          if token.text == closing && depth == 1 then .ok (acc.reverse, rest)
          else if token.text == opening then
            takeDelimited fuel opening closing (depth + 1) (token :: acc) rest
          else if token.text == closing then
            takeDelimited fuel opening closing (depth - 1) (token :: acc) rest
          else takeDelimited fuel opening closing depth (token :: acc) rest

private def splitAssignment (depth : Nat × Nat × Nat) (acc : List SourceToken) :
    List SourceToken → Option (List SourceToken × List SourceToken)
  | [] => none
  | token :: rest =>
      if token.text == "=" && atTop depth then some (acc.reverse, rest)
      else splitAssignment (updateDepth depth token.text) (token :: acc) rest

private def toAssignmentTarget : TargetExpr → Except ParseError AssignTarget
  | .local name => .ok (.local name)
  | .property receiver name => .ok (.property receiver name)
  | .index receiver key => .ok (.index receiver key)
  | _ => .error (.unsupportedSyntax 0)

private def parseForBinders : List SourceToken → Except ParseError (List String)
  | [] => .ok []
  | [name] =>
      if name.kind == .identifier then .ok [name.text]
      else .error (.unsupportedSyntax 0)
  | name :: comma :: rest => do
      if name.kind != .identifier || comma.text != "," then throw (.unsupportedSyntax 0)
      return name.text :: (← parseForBinders rest)

private def parseForHeader (tokens : List SourceToken) :
    Except ParseError (List String × TargetExpr) := do
  match tokens with
  | keyword :: next :: rest =>
      if keyword.text != "const" && keyword.text != "let" then throw (.unsupportedSyntax 0)
      if next.text == "[" then
        let (binderTokens, tail) ← takeDelimited (rest.length + 1) "[" "]" 1 [] rest
        let names ← parseForBinders binderTokens
        match tail with
        | ofToken :: iterable =>
            if ofToken.text != "of" then throw (.unsupportedSyntax 0)
            return (names, ← parseTargetExpr .ts (render iterable))
        | [] => throw (.unsupportedSyntax 0)
      else if next.kind == .identifier then
        match rest with
        | ofToken :: iterable =>
            if ofToken.text != "of" then throw (.unsupportedSyntax 0)
            return ([next.text], ← parseTargetExpr .ts (render iterable))
        | [] => throw (.unsupportedSyntax 0)
      else throw (.unsupportedSyntax 0)
  | _ => throw (.unsupportedSyntax 0)

private def parseSimpleStatement (tokens : List SourceToken) : Except ParseError TargetStmt := do
  match tokens with
  | [] => throw (.unsupportedSyntax 0)
  | first :: rest =>
    if first.text == "return" then
      if rest.isEmpty then return .returnVoid
      else return .returnValue (← parseTargetExpr .ts (render rest))
    else if first.text == "throw" then
      return .throwValue (← parseTargetExpr .ts (render rest))
    else if first.text == "break" && rest.isEmpty then return .breakTarget "loop"
    else if first.text == "continue" && rest.isEmpty then return .continueTarget "loop"
    else if first.text == "const" || first.text == "let" then
      match splitAssignment (0, 0, 0) [] rest with
      | some (nameTokens, valueTokens) =>
          match nameTokens with
          | name :: annotation =>
              if name.kind != .identifier ||
                  (!annotation.isEmpty && annotation.head?.map SourceToken.text != some ":") then
                throw (.unsupportedSyntax 0)
              if annotation.head?.map SourceToken.text == some ":" && annotation.length < 2 then
                throw (.unsupportedSyntax 0)
              return .letLocal name.text (first.text == "let")
                (← parseTargetExpr .ts (render valueTokens))
          | [] => throw (.unsupportedSyntax 0)
      | none =>
          if first.text != "let" then throw (.unsupportedSyntax 0)
          match rest with
          | name :: annotation =>
              if name.kind != .identifier || annotation.head?.map SourceToken.text != some ":" ||
                  annotation.length < 2 then throw (.unsupportedSyntax 0)
              return .letLocal name.text true .undefined
          | [] => throw (.unsupportedSyntax 0)
  match splitAssignment (0, 0, 0) [] tokens with
  | some (left, right) =>
      let target ← toAssignmentTarget (← parseTargetExpr .ts (render left))
      let value ← parseTargetExpr .ts (render right)
      return .assign target value
  | none => return .doExpr (← parseTargetExpr .ts (render tokens))

private def takeParamTokens (acc : List SourceToken) : List SourceToken →
    List SourceToken × List SourceToken
  | [] => (acc.reverse, [])
  | token :: rest =>
      if token.text == "," then (acc.reverse, rest)
      else takeParamTokens (token :: acc) rest

private def parseArrowParam (tokens : List SourceToken) : Except ParseError ParamSpec := do
  match tokens with
  | [] => throw (.unsupportedSyntax 0)
  | name :: rest =>
      if name.kind != .identifier then throw (.unsupportedSyntax 0)
      match splitAssignment (0, 0, 0) [] rest with
      | none => return ⟨name.text, none⟩
      | some (_, defaultTokens) =>
          return ⟨name.text, some (← parseTargetExpr .ts (render defaultTokens))⟩

private def parseArrowParams : Nat → List SourceToken → Except ParseError (List ParamSpec)
  | _, [] => .ok []
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, tokens => do
      let (first, rest) := takeParamTokens [] tokens
      let param ← parseArrowParam first
      return param :: (← parseArrowParams fuel rest)

private def dropArrowType : List SourceToken → Option (List SourceToken)
  | first :: second :: rest =>
      if first.text == "=" && second.text == ">" then some rest
      else dropArrowType (second :: rest)
  | _ => none

private def retargetSwitchBreak : TargetStmt → TargetStmt
  | .breakTarget "loop" => .breakTarget "switch"
  | .sequence first rest =>
      .sequence (retargetSwitchBreak first) (retargetSwitchBreak rest)
  | .ifThenElse cond yes no =>
      .ifThenElse cond (retargetSwitchBreak yes) (retargetSwitchBreak no)
  | .tryCatchFinally body kind binder handler cleanup =>
      .tryCatchFinally (retargetSwitchBreak body) kind binder
        (retargetSwitchBreak handler) (retargetSwitchBreak cleanup)
  | stmt => stmt

private def takeUntilCase (fuel : Nat) (depth : Nat × Nat × Nat)
    (acc : List SourceToken) : List SourceToken → Except ParseError (List SourceToken × List SourceToken)
  | [] => .ok (acc.reverse, [])
  | token :: rest =>
      match fuel with
      | 0 => .error (.unsupportedSyntax token.start)
      | fuel + 1 =>
          if token.text == "case" && atTop depth then .ok (acc.reverse, token :: rest)
          else takeUntilCase fuel (updateDepth depth token.text) (token :: acc) rest

mutual

private def parseBlockTokens : Nat → List SourceToken → Except ParseError TargetStmt
  | _, [] => .ok .empty
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, tokens => do
      let (first, tail) ← parseOne fuel tokens
      let rest ← parseBlockTokens fuel tail
      return .sequence first rest

private def parseOne : Nat → List SourceToken → Except ParseError (TargetStmt × List SourceToken)
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, first :: second :: rest =>
      if first.text == "if" && second.text == "(" then do
        let (condTokens, afterCond) ← takeDelimited (rest.length + 1) "(" ")" 1 [] rest
        let cond ← parseTargetExpr .ts (render condTokens)
        let (yes, afterYes) ← parseTSBody fuel afterCond
        match afterYes with
        | elseToken :: afterElse =>
            if elseToken.text == "else" then do
              let (no, tail) ← parseTSBody fuel afterElse
              return (.ifThenElse cond yes no, tail)
            else return (.ifThenElse cond yes .empty, afterYes)
        | [] => return (.ifThenElse cond yes .empty, [])
      else if first.text == "for" && second.text == "(" then do
        let (header, afterHeader) ← takeDelimited (rest.length + 1) "(" ")" 1 [] rest
        let (binders, iterable) ← parseForHeader header
        let (body, tail) ← parseTSBody fuel afterHeader
        return (.forDo binders iterable body, tail)
      else if first.text == "while" && second.text == "(" then do
        let (condition, afterCondition) ← takeDelimited (rest.length + 1)
          "(" ")" 1 [] rest
        let cond ← parseTargetExpr .ts (render condition)
        let (body, tail) ← parseTSBody fuel afterCondition
        return (.whileDo cond body, tail)
      else if first.text == "switch" && second.text == "(" then do
        let (condition, afterCondition) ← takeDelimited (rest.length + 1)
          "(" ")" 1 [] rest
        let scrutinee ← parseTargetExpr .ts (render condition)
        match afterCondition with
        | brace :: afterBrace =>
            if brace.text != "{" then throw (.unsupportedSyntax 0)
            let (inside, tail) ← takeDelimited (afterBrace.length + 1)
              "{" "}" 1 [] afterBrace
            let cases ← parseSwitchCases fuel inside
            return (.switchOn scrutinee cases, tail)
        | [] => throw (.unsupportedSyntax 0)
      else if first.text == "try" && second.text == "{" then do
        let (body, afterBody) ← parseTSBody fuel (second :: rest)
        parseTSTryTail fuel body afterBody
      else do
        let (head, tail) ← takeStatement (rest.length + 3) (0, 0, 0) []
          (first :: second :: rest)
        match ← parseArrowDeclaration fuel head with
        | some stmt => return (stmt, tail)
        | none => return (← parseSimpleStatement head, tail)
  | _ + 1, tokens => do
      let (head, tail) ← takeStatement (tokens.length + 1) (0, 0, 0) [] tokens
      return (← parseSimpleStatement head, tail)

private def parseTSBody : Nat → List SourceToken → Except ParseError (TargetStmt × List SourceToken)
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, first :: rest =>
      if first.text == "{" then do
        let (inside, tail) ← takeDelimited (rest.length + 1) "{" "}" 1 [] rest
        return (← parseBlockTokens fuel inside, tail)
      else parseOne fuel (first :: rest)
  | _, [] => .error (.unsupportedSyntax 0)

private def parseArrowDeclaration : Nat → List SourceToken →
    Except ParseError (Option TargetStmt)
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, tokens => do
      match tokens with
      | keyword :: rest =>
          if keyword.text != "const" && keyword.text != "let" then return none
          let (nameTokens, valueTokens) ← match splitAssignment (0, 0, 0) [] rest with
            | some parts => .ok parts
            | none => return none
          let name ← match nameTokens with
            | first :: _ =>
                if first.kind == .identifier then .ok first.text
                else .error (.unsupportedSyntax 0)
            | [] => .error (.unsupportedSyntax 0)
          match valueTokens with
          | openParen :: afterOpen =>
              if openParen.text != "(" then return none
              let (paramTokens, afterParams) ← takeDelimited (afterOpen.length + 1)
                "(" ")" 1 [] afterOpen
              let afterArrow ← match dropArrowType afterParams with
                | some rest => .ok rest
                | none => return none
              let params ← parseArrowParams (paramTokens.length + 1) paramTokens
              match afterArrow with
              | brace :: bodyTokens =>
                  if brace.text == "{" then do
                    let (inside, final) ← takeDelimited (bodyTokens.length + 1)
                      "{" "}" 1 [] bodyTokens
                    if !final.isEmpty then throw (.unsupportedSyntax 0)
                    let body ← parseBlockTokens fuel inside
                    return some (.defineFunction name params body)
                  else do
                    let value ← parseTargetExpr .ts (render afterArrow)
                    return some (.defineFunction name params (.returnValue value))
              | [] => throw (.unsupportedSyntax 0)
          | _ => return none
      | [] => return none

private def parseSwitchCases : Nat → List SourceToken → Except ParseError TargetStmt
  | _, [] => .ok .empty
  | 0, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, keyword :: label :: colon :: rest => do
      if keyword.text != "case" || colon.text != ":" then throw (.unsupportedSyntax 0)
      let label ← match ← parseTargetExpr .ts label.text with
        | .string s => .ok s
        | _ => .error (.unsupportedSyntax 0)
      let (bodyTokens, remaining) ← match rest with
        | brace :: afterBrace =>
            if brace.text == "{" then
              takeDelimited (afterBrace.length + 1) "{" "}" 1 [] afterBrace
            else takeUntilCase (rest.length + 1) (0, 0, 0) [] rest
        | [] => .ok ([], [])
      let body ← parseBlockTokens fuel bodyTokens
      let next ← parseSwitchCases fuel remaining
      return .switchCase label (retargetSwitchBreak body) next
  | _, _ => .error (.unsupportedSyntax 0)

private def parseTSTryTail : Nat → TargetStmt → List SourceToken →
    Except ParseError (TargetStmt × List SourceToken)
  | 0, _, _ => .error (.unsupportedSyntax 0)
  | fuel + 1, body, tokens => do
      let (catchType, binder, handler, afterCatch) ←
        match tokens with
        | keyword :: rest =>
            if keyword.text == "catch" then
              match rest with
              | openParen :: afterOpen =>
                  if openParen.text == "(" then do
                    let (binderTokens, afterBinder) ← takeDelimited (afterOpen.length + 1)
                      "(" ")" 1 [] afterOpen
                    match binderTokens with
                    | name :: _ =>
                        if name.kind != .identifier then throw (.unsupportedSyntax 0)
                        let (handler, tail) ← parseTSBody fuel afterBinder
                        .ok (some "any", some name.text, handler, tail)
                    | [] => throw (.unsupportedSyntax 0)
                  else if openParen.text == "{" then do
                    let (handler, tail) ← parseTSBody fuel rest
                    .ok (some "any", none, handler, tail)
                  else throw (.unsupportedSyntax 0)
              | [] => throw (.unsupportedSyntax 0)
            else .ok (none, none, TargetStmt.empty, tokens)
        | [] => .ok (none, none, TargetStmt.empty, [])
      match afterCatch with
      | keyword :: rest =>
          if keyword.text == "finally" then do
            let (cleanup, tail) ← parseTSBody fuel rest
            return (.tryCatchFinally body catchType binder handler cleanup, tail)
          else if catchType.isSome then
            return (.tryCatchFinally body catchType binder handler .empty, afterCatch)
          else throw (.unsupportedSyntax 0)
      | [] =>
          if catchType.isSome then return (.tryCatchFinally body catchType binder handler .empty, [])
          else throw (.unsupportedSyntax 0)

end

def parseTSBlock (source : String) : Except ParseError TargetStmt := do
  let tokens := significant (← tokenizeSource .ts source)
  parseBlockTokens ((tokens.length + 1) * 16) tokens

end Harmonia.Applications.Kadmos.Generated
