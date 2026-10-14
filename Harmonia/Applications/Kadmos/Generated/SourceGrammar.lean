import Harmonia.Applications.Kadmos.Generated.SourceLexical

namespace Harmonia.Applications.Kadmos.Generated

def formatOpen : TargetLang → String
  | .ts => "${"
  | .python => "{"

private def joinWith (separator : String) : List String → String
  | [] => ""
  | [last] => last
  | first :: rest => first ++ separator ++ joinWith separator rest

/-- A deterministic first delimiter, used only to describe where a checked
    format production may split. It is independent of `parseFormatParts`. -/
def splitFirstFormat (source delimiter : String) : Option (String × String) :=
  match source.splitSourceOn delimiter with
  | [] | [_] => none
  | first :: rest => some (first, joinWith delimiter rest)

/-- Unescaped Python format text cannot own a closing interpolation brace. -/
def formatLiteralCheck (lang : TargetLang) (text : String) : Bool :=
  lang != .python || !text.toList.contains '}'

def FormatIdentifier (lang : TargetLang) (name : String) : Prop :=
  (lang = .ts ∧ name = "this") ∨ ExpressionIdentifier lang name

inductive FormatSyntax : TargetLang → String → TargetExpr → Prop where
  | empty (lang : TargetLang) : FormatSyntax lang "" .empty
  | literal {lang : TargetLang} {text : String}
      (hNonempty : text.isEmpty = false)
      (hNoHole : splitFirstFormat text (formatOpen lang) = none)
      (hLiteral : formatLiteralCheck lang text = true) :
      FormatSyntax lang text (.formatPart text .empty .empty)
  | hole {lang : TargetLang} {headText name tail : String} {rest : TargetExpr}
      (hNoHole : splitFirstFormat headText (formatOpen lang) = none)
      (hName : FormatIdentifier lang name)
      (hRest : FormatSyntax lang tail rest)
      (hLiteral : formatLiteralCheck lang headText = true) :
      FormatSyntax lang (headText ++ formatOpen lang ++ name ++ "}" ++ tail)
        (.formatPart headText (.local name) rest)

/-- This fragment has no escape lowering: unescaped content must not contain
    its closing delimiter or a backslash. Escaped literals need a separate
    decoding production before they can be admitted. -/
def formatContentCheck (delimiter : Char) (content : String) : Bool :=
  content.toList.all (fun c => c != delimiter && c != '\\' && c != '\n' && c != '\r')

inductive FormatWrapper : TargetLang → String → String → Prop where
  | ts (content : String) (hContent : formatContentCheck '`' content = true) : FormatWrapper .ts ("`" ++ content ++ "`") content
  | pythonDouble (content : String)
      (hContent : formatContentCheck '"' content = true) :
      FormatWrapper .python ("f\"" ++ content ++ "\"") content
  | pythonSingle (content : String)
      (hContent : formatContentCheck '\'' content = true) :
      FormatWrapper .python ("f'" ++ content ++ "'") content

/-- Binding power of the represented expression node. Binary source rules
    require their children to have at least the operator's power, with a
    strictly stronger right child for left association. This is independent
    of the raw expression decoder. Parenthesized forms need a separate rule
    when admitted to this restricted grammar. -/
def exprBindingPower : TargetExpr → Nat
  | .binary op _ _ => match op with
      | .mul | .div => 7
      | .add | .sub => 6
      | .lt | .le | .gt | .ge | .instanceOf => 5
      | .eq | .strictEq | .ne | .strictNe | .inObject | .notInObject
      | .isIdentity | .isNotIdentity => 4
  | .andThen _ _ => 3
  | .orElse _ _ | .nullCoalesce _ _ => 2
  | .conditional _ _ _ => 1
  | .unary _ _ | .newExpr _ | .postIncrement _ => 8
  | _ => 9

def finalCallOpenAux : Nat → List SourceToken → Option Nat
  | _, [] => none
  | depth, token :: rest =>
      if token.text == ")" then finalCallOpenAux (depth + 1) rest
      else if token.text == "(" then
        if depth == 1 then some token.start
        else finalCallOpenAux (depth - 1) rest
      else finalCallOpenAux depth rest

/-- The final call's opening parenthesis comes from independently validated
    lexical tokens, counting nested calls backwards from the final `)`. -/
def finalCallOpen (tokens : List SourceToken) : Option Nat :=
  let significant := tokens.filter (fun token =>
    token.kind != .spacing && token.kind != .comment)
  match significant.reverse with
  | close :: rest =>
      if close.text == ")" then finalCallOpenAux 1 rest else none
  | [] => none

theorem finalCallOpen.unique_on_source {lang source tokens₁ tokens₂ at₁ at₂}
    (hLex₁ : Lexes lang source tokens₁)
    (hLex₂ : Lexes lang source tokens₂)
    (hOpen₁ : finalCallOpen tokens₁ = some at₁)
    (hOpen₂ : finalCallOpen tokens₂ = some at₂) : at₁ = at₂ := by
  have hTokens := Lexes.unique hLex₁ hLex₂
  subst tokens₂
  rw [hOpen₁] at hOpen₂
  cases hOpen₂
  rfl

/-- An integral numeral must be delimited before a member dot. The current
    fragment has no parenthesized-numeral production; this source condition
    leaves that future production possible without admitting `1.foo`. -/
def dotReceiverCheck (base : String) (receiver : TargetExpr) : Bool :=
  match receiver with
  | .integer _ => base.endsWith ")"
  | _ => true

mutual
/-- Source productions, independent of the executable decoder. Argument
    sequences have their own sort: a bare expression cannot also be an
    argument-list AST for the same source. -/
inductive ExprSyntax : TargetLang → String → TargetExpr → Prop where
  | call {lang : TargetLang} {calleeText argsText : String}
      {callee args : TargetExpr} {tokens : List SourceToken}
      (hLex : Lexes lang (calleeText ++ "(" ++ argsText ++ ")") tokens)
      (hOpen : finalCallOpen tokens = some calleeText.length)
      (hCalleeNonempty : calleeText.isEmpty = false)
      (hCallee : ExprSyntax lang calleeText callee)
      (hArgs : ArgumentSyntax lang argsText args)
      (hPower : 9 ≤ exprBindingPower callee) :
      ExprSyntax lang (calleeText ++ "(" ++ argsText ++ ")") (.call callee args)
  | tsTypeof {valueText : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts valueText value)
      (hPower : 8 ≤ exprBindingPower value) :
      ExprSyntax .ts ("typeof " ++ valueText) (.unary .typeof value)
  | tsStrictNe {leftText rightText : String} {left right : TargetExpr}
      (hLeft : ExprSyntax .ts leftText left)
      (hRight : ExprSyntax .ts rightText right)
      (hLeftPower : 4 ≤ exprBindingPower left)
      (hRightPower : 4 < exprBindingPower right) :
      ExprSyntax .ts (leftText ++ " !== " ++ rightText)
        (.binary .strictNe left right)
  | pythonIsNot {leftText rightText : String} {left right : TargetExpr}
      (hLeft : ExprSyntax .python leftText left)
      (hRight : ExprSyntax .python rightText right)
      (hLeftPower : 5 < exprBindingPower left)
      (hRightPower : 5 < exprBindingPower right) :
      ExprSyntax .python (leftText ++ " is not " ++ rightText)
        (.binary .isNotIdentity left right)
  | tsNew {valueText : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts valueText value)
      (hPower : 9 ≤ exprBindingPower value) :
      ExprSyntax .ts ("new " ++ valueText) (.newExpr value)
  | tsBool (value : Bool) :
      ExprSyntax .ts (if value then "true" else "false") (.bool value)
  | pythonBool (value : Bool) :
      ExprSyntax .python (if value then "True" else "False") (.bool value)
  | tsNull : ExprSyntax .ts "null" .null
  | pythonNone : ExprSyntax .python "None" .null
  | tsUndefined : ExprSyntax .ts "undefined" .undefined
  | tsThis : ExprSyntax .ts "this" (.local "this")
  | numeral {lang : TargetLang} {source : String} {n : Nat}
      (hNumeral : source.toNat? = some n) :
      ExprSyntax lang source (.integer (Int.ofNat n))
  | decimal {lang : TargetLang} {source : String}
      (hNumber : numberTokenCheck source = true)
      (hDot : source.toList.contains '.' = true) :
      ExprSyntax lang source (.decimal source)
  | string {lang : TargetLang} {source value : String}
      (hLiteral : StringLiteralSyntax lang source value) :
      ExprSyntax lang source (.string value)
  | local {lang : TargetLang} {name : String}
      (hName : ExpressionIdentifier lang name) : ExprSyntax lang name (.local name)
  | property {lang : TargetLang} {base name : String} {receiver : TargetExpr}
      (hBaseNonempty : base.isEmpty = false)
      (hBase : ExprSyntax lang base receiver)
      (hName : PropertyIdentifier lang name)
      (hPower : 9 ≤ exprBindingPower receiver)
      (hDot : dotReceiverCheck base receiver = true) :
      ExprSyntax lang (base ++ "." ++ name) (.property receiver name)
  | tsOptionalProperty {base name : String} {receiver : TargetExpr}
      (hBaseNonempty : base.isEmpty = false)
      (hBase : ExprSyntax .ts base receiver)
      (hName : IdentifierText name)
      (hPower : 9 ≤ exprBindingPower receiver) :
      ExprSyntax .ts (base ++ "?." ++ name)
        (.optionalProperty receiver name)
  | index {lang : TargetLang} {base keyText : String}
      {receiver key : TargetExpr}
      (hBaseNonempty : base.isEmpty = false)
      (hBase : ExprSyntax lang base receiver)
      (hKey : ExprSyntax lang keyText key)
      (hPower : 9 ≤ exprBindingPower receiver) :
      ExprSyntax lang (base ++ "[" ++ keyText ++ "]")
        (.index receiver key)
  | tsNonNull {base : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts base value)
      (hPower : 9 ≤ exprBindingPower value) :
      ExprSyntax .ts (base ++ "!") (.nonNull value)
  | tsPostIncrement {name : String}
      (hName : ExpressionIdentifier .ts name) :
      ExprSyntax .ts (name ++ "++") (.postIncrement name)
  | sub {lang : TargetLang} {leftText rightText : String}
      {left right : TargetExpr}
      (hLeft : ExprSyntax lang leftText left)
      (hRight : ExprSyntax lang rightText right)
      (hLeftPower : 6 ≤ exprBindingPower left)
      (hRightPower : 6 < exprBindingPower right)
      (hRightmost : RightmostSubOperand rightText) :
      ExprSyntax lang (leftText ++ " - " ++ rightText) (.binary .sub left right)
  | gt {lang : TargetLang} {leftText rightText : String}
      {left right : TargetExpr}
      (hLeft : ExprSyntax lang leftText left)
      (hRight : ExprSyntax lang rightText right)
      (hLeftPower : 5 ≤ exprBindingPower left)
      (hRightPower : 5 < exprBindingPower right)
      (hPythonLeft : lang = .python → 5 < exprBindingPower left) :
      ExprSyntax lang (leftText ++ " > " ++ rightText) (.binary .gt left right)
  | ge {lang : TargetLang} {leftText rightText : String}
      {left right : TargetExpr}
      (hLeft : ExprSyntax lang leftText left)
      (hRight : ExprSyntax lang rightText right)
      (hLeftPower : 5 ≤ exprBindingPower left)
      (hRightPower : 5 < exprBindingPower right)
      (hPythonLeft : lang = .python → 5 < exprBindingPower left) :
      ExprSyntax lang (leftText ++ " >= " ++ rightText) (.binary .ge left right)
  | formatted {lang : TargetLang} {source content : String} {parts : TargetExpr}
      (hWrap : FormatWrapper lang source content)
      (hParts : FormatSyntax lang content parts)
      (hNonempty : parts != .empty) :
      ExprSyntax lang source (.formatted parts)

inductive ArgumentSyntax : TargetLang → String → TargetExpr → Prop where
  | empty (lang : TargetLang) : ArgumentSyntax lang "" .empty
  | one {lang : TargetLang} {source : String} {value : TargetExpr}
      (hNonempty : source.isEmpty = false)
      (hValue : ExprSyntax lang source value) :
      ArgumentSyntax lang source (.sequence value .empty)
  | more {lang : TargetLang} {firstText gap restText : String}
      {tokens : List SourceToken} {first rest : TargetExpr}
      (hFirstNonempty : firstText.isEmpty = false)
      (hLex : Lexes lang (firstText ++ "," ++ gap ++ restText) tokens)
      (hComma : firstTopLevelComma tokens = some firstText.length)
      (hGap : gap.toList.all Char.isWhitespace = true)
      (hFirst : ExprSyntax lang firstText first)
      (hRest : ArgumentSyntax lang restText rest) :
      ArgumentSyntax lang (firstText ++ "," ++ gap ++ restText)
        (.sequence first rest)
end

theorem ArgumentSyntax.empty_only {lang source expr}
    (h : ArgumentSyntax lang source expr) (hSource : source = "") :
    expr = .empty := by
  cases h with
  | empty => rfl
  | one hNonempty _ =>
      have hz : ("" : String).isEmpty = true := by decide
      rw [hSource, hz] at hNonempty
      cases hNonempty
  | @more lang firstText gap restText tokens first rest hLex hComma hGap hFirst hRest =>
      have hLen := congrArg String.length hSource
      have hCommaLength : ("," : String).length = 1 := by decide
      simp [String.length_append, hCommaLength] at hLen

/-- `.empty` represents a list terminator, never a runtime expression. -/
theorem ExprSyntax.no_empty {lang source} :
    ¬ ExprSyntax lang source .empty := by
  intro h
  cases h

theorem ExprSyntax.no_empty_callee {lang source args} :
    ¬ ExprSyntax lang source (.call .empty args) := by
  intro h
  cases h with
  | call _ _ _ hCallee _ _ => exact no_empty hCallee

theorem ArgumentSyntax.no_empty_first {lang source rest} :
    ¬ ArgumentSyntax lang source (.sequence .empty rest) := by
  intro h
  cases h with
  | one _ hValue => exact ExprSyntax.no_empty hValue
  | more _ _ _ _ hFirst _ => exact ExprSyntax.no_empty hFirst

theorem ExprSyntax.no_empty_property_receiver {lang source name} :
    ¬ ExprSyntax lang source (.property .empty name) := by
  intro h
  cases h with
  | property _ hBase _ _ _ => exact no_empty hBase

theorem ExprSyntax.no_empty_optional_receiver {source name} :
    ¬ ExprSyntax .ts source (.optionalProperty .empty name) := by
  intro h
  cases h with
  | tsOptionalProperty _ hBase _ _ => exact no_empty hBase

theorem ExprSyntax.no_empty_index_receiver {lang source key} :
    ¬ ExprSyntax lang source (.index .empty key) := by
  intro h
  cases h with
  | index _ hBase _ _ => exact no_empty hBase

/-- A comparison cannot be the unparenthesized left operand of subtraction;
    this is a grammar fact, not a preference of the executable validator. -/
theorem ExprSyntax.no_sub_after_gt {lang source a b c} :
    ¬ ExprSyntax lang source (.binary .sub (.binary .gt a b) c) := by
  intro h
  cases h with
  | sub _ _ hPower _ _ =>
      simp [exprBindingPower] at hPower

inductive ExprDerives : TargetLang → String → SourceSpan → TargetExpr → Prop where
  | ofSyntax {lang : TargetLang} {source : String} {span : SourceSpan}
      {expr : TargetExpr}
      (hBounds : span.start ≤ span.stop ∧ span.stop ≤ source.length)
      (hSyntax : ExprSyntax lang (span.text source) expr) :
      ExprDerives lang source span expr

inductive SurfaceControl where
  | module | function | body | loop | switch
  deriving DecidableEq, Repr

/-- K-02's six runtime module bindings have explicit erased TS annotations.
    The annotation text is an exact restricted grammar terminal; the RHS is
    still independently derived as executable expression syntax. -/
def tsModuleType : String → Option String
  | "world" => some "WorldData"
  | "contextDefaults" => some "Readonly<Record<string, number | string>>"
  | "contextDefinitions" =>
      some "Record<string, { readonly type: \"integer\" | \"string\"; readonly min?: number; readonly max?: number }>"
  | "stateDefinitions" =>
      some "readonly { readonly id: string; readonly terminal?: boolean }[]"
  | "invariantDefinitions" =>
      some "readonly { readonly id: string; readonly predicate: string }[]"
  | "transitionDefinitions" =>
      some "readonly { readonly id: string; readonly from: string; readonly to: string; readonly guard: string | boolean; readonly directive: string | null; readonly effects: readonly string[] }[]"
  | _ => none

/-- A source-level sequence is right-nested: its first item (and the child
    of a final wrapper) is one statement, never another sibling sequence.
    Without this premise the same `a; b; c;` bytes derive two ASTs. -/
def SingleStatement : TargetStmt → Prop
  | .sequence _ _ | .empty => False
  | _ => True

/-- Statement lists and single statements occupy different grammar sorts. -/
def statementControl : TargetStmt → SurfaceControl
  | .empty | .sequence _ _ => .body
  | _ => .function

theorem SingleStatement.control {stmt : TargetStmt} (h : SingleStatement stmt) :
    statementControl stmt = .function := by
  cases stmt <;> simp_all [SingleStatement, statementControl]

/-- Adjacent significant lines own a suite opener only if the next line
    is strictly deeper. The first line is supplied at its enclosing indent;
    later lines retain their absolute source indentation. -/
def pythonLineIndent (line : String) : Nat :=
  (line.toList.takeWhile (· == ' ')).length

def pythonSignificantLine (line : String) : Bool :=
  let content := line.toList.dropWhile (· == ' ')
  !content.isEmpty && content.head? != some '#'

def pythonSuiteHeaders : List String → Bool
  | [] => true
  | [last] => !last.endsWith ":"
  | first :: next :: rest =>
      (!first.endsWith ":" || pythonLineIndent first < pythonLineIndent next) &&
        pythonSuiteHeaders (next :: rest)

/-- A suite cannot swallow a dedented line or a header without its body.
    Blank physical lines do not satisfy a pending suite opener. -/
def suiteLinesWithin (indent bodySource : String) : Bool :=
  let lines := (indent ++ bodySource).splitSourceOn "\n"
  lines.all (fun line => line.isEmpty || line.startsWith indent) &&
    let significant := lines.filter pythonSignificantLine
    !significant.isEmpty && pythonSuiteHeaders significant

/-- The supported TS writable receiver slice excludes optional chains through
    postfix accesses/calls and erased casts. Parentheses are erased by the AST,
    so parenthesized optional receivers are conservatively outside this slice.
    Index keys and call arguments are independent expressions, not receivers. -/
def WritableReceiverChain : TargetExpr → Prop
  | .optionalProperty _ _ => False
  | .property receiver _ | .index receiver _ | .call receiver _
  | .nonNull receiver | .typeCast receiver _ => WritableReceiverChain receiver
  | _ => True

/-- Only source expressions with actual writable target syntax become lvalues.
    Internal checker fields are not surface assignment targets. -/
inductive AssignmentTargetSyntax : TargetLang → String → AssignTarget → Prop where
  | local {lang source name}
      (hName : ExpressionIdentifier lang name)
      (hText : source = name) : AssignmentTargetSyntax lang source (.local name)
  | property {lang source receiver name}
      (hExpr : ExprSyntax lang source (.property receiver name))
      (hWritable : lang = .ts → WritableReceiverChain receiver) :
      AssignmentTargetSyntax lang source (.property receiver name)
  | index {lang source receiver key}
      (hExpr : ExprSyntax lang source (.index receiver key))
      (hWritable : lang = .ts → WritableReceiverChain receiver) :
      AssignmentTargetSyntax lang source (.index receiver key)

def statementTerminator : TargetLang → String
  | .ts => ";"
  | .python => ""

inductive StmtSyntax : TargetLang → SurfaceControl → String → TargetStmt → Prop where
  | empty (lang : TargetLang) (control : SurfaceControl) :
      StmtSyntax lang control "" .empty
  | assignment {lang targetSource valueSource target value}
      (hTarget : AssignmentTargetSyntax lang targetSource target)
      (hValue : ExprSyntax lang valueSource value) :
      StmtSyntax lang .function
        (targetSource ++ " = " ++ valueSource ++ statementTerminator lang)
        (.assign target value)
  | tsDo {exprSource : String} {expr : TargetExpr}
      (hExpr : ExprSyntax .ts exprSource expr) :
      StmtSyntax .ts .function (exprSource ++ ";") (.doExpr expr)
  | pythonDo {exprSource : String} {expr : TargetExpr}
      (hExpr : ExprSyntax .python exprSource expr) :
      StmtSyntax .python .function exprSource (.doExpr expr)
  | tsFunctionLet {name exprSource : String} {mutable : Bool}
      {expr : TargetExpr}
      (hName : ExpressionIdentifier .ts name)
      (hExpr : ExprSyntax .ts exprSource expr) :
      StmtSyntax .ts .function
        ((if mutable then "let " else "const ") ++ name ++ " = " ++
          exprSource ++ ";") (.letLocal name mutable expr)
  | pythonFunctionAssign {name exprSource : String} {expr : TargetExpr}
      (hName : ExpressionIdentifier .python name)
      (hExpr : ExprSyntax .python exprSource expr) :
      StmtSyntax .python .function (name ++ " = " ++ exprSource)
        (.assign (.local name) expr)
  | pythonAugmentAdd {name exprSource : String} {expr : TargetExpr}
      (hName : ExpressionIdentifier .python name)
      (hExpr : ExprSyntax .python exprSource expr) :
      StmtSyntax .python .function (name ++ " += " ++ exprSource)
        (.augment (.local name) .add expr)
  | pythonRaise {valueSource : String} {value : TargetExpr}
      (hValue : ExprSyntax .python valueSource value) :
      StmtSyntax .python .function ("raise " ++ valueSource)
        (.throwValue value)
  | pythonReturn {valueSource : String} {value : TargetExpr}
      (hValue : ExprSyntax .python valueSource value) :
      StmtSyntax .python .function ("return " ++ valueSource)
        (.returnValue value)
  | pythonIfThen {conditionSource bodySource : String}
      {condition : TargetExpr} {body : TargetStmt}
      (hCondition : ExprSyntax .python conditionSource condition)
      (hSuite : suiteLinesWithin "        " bodySource = true)
      (hBody : StmtSyntax .python .body bodySource body) :
      StmtSyntax .python .function
        ("if " ++ conditionSource ++ ":\n        " ++ bodySource)
        (.ifThenElse condition body .empty)
  | pythonIfThenIndented {conditionSource bodySource indent : String}
      {condition : TargetExpr} {body : TargetStmt}
      (hIndentLength : 4 ≤ indent.length)
      (hIndentSteps : indent.length % 4 = 0)
      (hIndentSpaces : indent.toList.all (· == ' ') = true)
      (hCondition : ExprSyntax .python conditionSource condition)
      (hSuite : suiteLinesWithin indent bodySource = true)
      (hBody : StmtSyntax .python .body bodySource body) :
      StmtSyntax .python .function
        ("if " ++ conditionSource ++ ":\n" ++ indent ++ bodySource)
        (.ifThenElse condition body .empty)
  | pythonSequence {firstSource restSource : String}
      {first rest : TargetStmt}
      (hSingle : SingleStatement first)
      (hFirst : StmtSyntax .python .function firstSource first)
      (hRest : StmtSyntax .python .body restSource rest) :
      StmtSyntax .python .body (firstSource ++ "\n    " ++ restSource)
        (.sequence first rest)
  | pythonFinal {source : String} {last : TargetStmt}
      (hSingle : SingleStatement last)
      (hLast : StmtSyntax .python .function source last) :
      StmtSyntax .python .body source (.sequence last .empty)
  | pythonModuleAssign {name valueSource : String} {value : TargetExpr}
      (hName : IdentifierText name)
      (hValue : ExprSyntax .python valueSource value) :
      StmtSyntax .python .module (name ++ " = " ++ valueSource)
        (.assign (.local name) value)
  | tsThrow {valueSource : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts valueSource value) :
      StmtSyntax .ts .function ("throw " ++ valueSource ++ ";")
        (.throwValue value)
  | tsReturn {valueSource : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts valueSource value) :
      StmtSyntax .ts .function ("return " ++ valueSource ++ ";")
        (.returnValue value)
  | tsIfThen {conditionSource bodySource : String}
      {condition : TargetExpr} {body : TargetStmt}
      (hCondition : ExprSyntax .ts conditionSource condition)
      (hSingle : SingleStatement body)
      (hBody : StmtSyntax .ts .function bodySource body) :
      StmtSyntax .ts .function
        ("if (" ++ conditionSource ++ ") " ++ bodySource)
        (.ifThenElse condition body .empty)
  | tsSequence {firstSource restSource : String}
      {first rest : TargetStmt}
      (hSingle : SingleStatement first)
      (hFirst : StmtSyntax .ts .function firstSource first)
      (hRest : StmtSyntax .ts .body restSource rest) :
      StmtSyntax .ts .body (firstSource ++ "\n  " ++ restSource)
        (.sequence first rest)
  | tsFinal {source : String} {last : TargetStmt}
      (hSingle : SingleStatement last)
      (hLast : StmtSyntax .ts .function source last) :
      StmtSyntax .ts .body source (.sequence last .empty)
  | tsModuleConst {name typeSource valueSource : String} {value : TargetExpr}
      (hType : tsModuleType name = some typeSource)
      (hValue : ExprSyntax .ts valueSource value) :
      StmtSyntax .ts .module
        ("const " ++ name ++ ": " ++ typeSource ++ " = " ++ valueSource ++ ";")
        (.letLocal name false value)
  | tsNamedImport {moduleName name alias : String}
      (hName : IdentifierText name) (hAlias : IdentifierText alias) :
      StmtSyntax .ts .module
        ("import { " ++ name ++ " as " ++ alias ++ " } from \"" ++
          moduleName ++ "\";")
        (.fromImport moduleName name alias)
  | pythonImport {moduleName : String}
      (hModule : IdentifierText moduleName) :
      StmtSyntax .python .module ("import " ++ moduleName)
        (.importModule moduleName moduleName)
  | pythonFromImport {moduleName name : String}
      (hModule : IdentifierText moduleName) (hName : IdentifierText name) :
      StmtSyntax .python .module
        ("from " ++ moduleName ++ " import " ++ name)
        (.fromImport moduleName name name)
  | nonlocal {name : String} (hName : IdentifierText name) :
      StmtSyntax .python .function ("nonlocal " ++ name) (.nonlocalNames [name])
  | switchBreak :
      StmtSyntax .ts .switch "break;" (.breakTarget "switch")
  | loopBreakTS :
      StmtSyntax .ts .loop "break;" (.breakTarget "loop")
  | loopBreakPython :
      StmtSyntax .python .loop "break" (.breakTarget "loop")

theorem StmtSyntax.no_nested_sequence_first {lang source first rest tail} :
    ¬ StmtSyntax lang .body source
      (.sequence (.sequence first rest) tail) := by
  intro h
  cases h <;> simp [SingleStatement] at *

theorem StmtSyntax.no_unbraced_ts_sequence {source condition first rest} :
    ¬ StmtSyntax .ts .function source
      (.ifThenElse condition (.sequence first rest) .empty) := by
  intro h
  cases h <;> simp [SingleStatement] at *

/-- Absolute indentation before an owned source span. No parser or AST
    candidate supplies this column. -/
def sourceLinePrefix (source : String) (start : Nat) : List Char :=
  ((source.toList.take start).reverse.takeWhile (· != '\n')).reverse

def sourceColumn (source : String) (start : Nat) : Nat :=
  (sourceLinePrefix source start).length

def statementLayoutCheck (lang : TargetLang) (source : String) (span : SourceSpan) : Bool :=
  if lang == .python && !(span.text source).isEmpty then
    (sourceLinePrefix source span.start).all (· == ' ') &&
    suiteLinesWithin (String.mk (List.replicate (sourceColumn source span.start) ' '))
      (span.text source)
  else true

inductive StmtDerives : TargetLang → SurfaceControl → String → SourceSpan → TargetStmt → Prop where
  | ofSyntax {lang : TargetLang} {control : SurfaceControl}
      {source : String} {span : SourceSpan} {stmt : TargetStmt}
      (hBounds : span.start ≤ span.stop ∧ span.stop ≤ source.length)
      (hSyntax : StmtSyntax lang control (span.text source) stmt)
      (hLayout : statementLayoutCheck lang source span = true) :
      StmtDerives lang control source span stmt

/-- A module function owns its header and constituent body. Additional
    parameter/type productions are added only for emitted forms; the body is
    always derived through `StmtSyntax`, never assigned ideal behavior. -/
inductive FunctionSyntax : TargetLang → String → TargetFunction → Prop where
  | pythonAnyToBool {name param bodySource : String} {body : TargetStmt}
      (hName : IdentifierText name) (hParam : IdentifierText param)
      (hBody : StmtSyntax .python .body bodySource body)
      (hLayout : suiteLinesWithin "    " bodySource = true) :
      FunctionSyntax .python
        ("def " ++ name ++ "(" ++ param ++
          ": Any) -> bool:\n    " ++ bodySource)
        ⟨name, [⟨param, none⟩], body⟩
  | tsUnknownToBool {name param bodySource : String} {body : TargetStmt}
      (hName : IdentifierText name) (hParam : IdentifierText param)
      (hBody : StmtSyntax .ts .body bodySource body) :
      FunctionSyntax .ts
        ("function " ++ name ++ "(" ++ param ++
          ": unknown): boolean {\n  " ++ bodySource ++ "\n}")
        ⟨name, [⟨param, none⟩], body⟩

inductive FunctionDerives : TargetLang → String → SourceSpan →
    TargetFunction → Prop where
  | ofSyntax {lang : TargetLang} {source : String}
      {span : SourceSpan} {function : TargetFunction}
      (hBounds : span.start ≤ span.stop ∧ span.stop ≤ source.length)
      (hSyntax : FunctionSyntax lang (span.text source) function) :
      FunctionDerives lang source span function

def functionHeader (lang : TargetLang) (function : TargetFunction) : Option String :=
  match function.params with
  | [⟨param, none⟩] => some (match lang with
      | .ts => "function " ++ function.qualifiedName ++ "(" ++ param ++
          ": unknown): boolean {\n  "
      | .python => "def " ++ function.qualifiedName ++ "(" ++ param ++
          ": Any) -> bool:\n    ")
  | _ => none

def functionTrailer : TargetLang → String
  | .ts => "\n}"
  | .python => ""

inductive FunctionBodyLocated (lang : TargetLang) (span bodySpan : SourceSpan)
    (function : TargetFunction) : Prop where
  | ofHeader {header : String}
      (hHeader : functionHeader lang function = some header)
      (hStart : bodySpan.start = span.start + header.length)
      (hStop : bodySpan.stop + (functionTrailer lang).length = span.stop) :
      FunctionBodyLocated lang span bodySpan function

/-- Type-only imports own source characters but contribute no runtime AST
    statement. The listed names are checked identifiers, not an opaque body. -/
def renderTypeNames : List String → String
  | [] => ""
  | [name] => name
  | name :: rest => name ++ ", " ++ renderTypeNames rest

inductive TypeNames : List String → Prop where
  | one {name : String} (hName : IdentifierText name) : TypeNames [name]
  | more {name : String} {rest : List String}
      (hName : IdentifierText name) (hRest : TypeNames rest) :
      TypeNames (name :: rest)

def emittedWorldDataTypeAlias : String :=
  "type WorldData = { readonly context: Readonly<Record<string, { readonly type: \"integer\" | \"string\"; readonly min?: number; readonly max?: number }>>; readonly states: readonly { readonly id: string; readonly terminal?: boolean }[]; readonly invariants: readonly { readonly id: string; readonly predicate: string }[]; readonly transitions: readonly { readonly id: string; readonly from: string; readonly to: string; readonly guard: string | boolean; readonly directive: string | null; readonly effects: readonly string[] }[] };"

inductive ErasedSyntax : TargetLang → String → Prop where
  | tsWorldDataAlias : ErasedSyntax .ts emittedWorldDataTypeAlias
  | tsImportType {names : List String} {moduleName : String}
      (hNames : TypeNames names)
      (hModule : StringLiteralSyntax .ts
        ("\"" ++ moduleName ++ "\"") moduleName) :
      ErasedSyntax .ts
        ("import type { " ++ renderTypeNames names ++
          " } from \"" ++ moduleName ++ "\";")

inductive ErasedDerives : TargetLang → String → SourceSpan → Prop where
  | ofSyntax {lang : TargetLang} {source : String} {span : SourceSpan}
      (hBounds : span.start ≤ span.stop ∧ span.stop ≤ source.length)
      (hSyntax : ErasedSyntax lang (span.text source)) :
      ErasedDerives lang source span

/-- Candidate declarations carry explicit source ownership. The candidate is
    untrusted; the inductive relation below requires a constituent derivation
    for every executable statement and for every erased declaration. -/
inductive SourceItem where
  | runtime (control : SurfaceControl) (span : SourceSpan) (stmt : TargetStmt)
  | functionDecl (span bodySpan : SourceSpan) (function : TargetFunction)
  | tsTypeImport (span : SourceSpan) (names : List String) (moduleName : String)
  | tsWorldDataType (span : SourceSpan)
  deriving DecidableEq, Repr

def SourceItem.span : SourceItem → SourceSpan
  | .runtime _ span _ => span
  | .functionDecl span _ _ => span
  | .tsTypeImport span _ _ => span
  | .tsWorldDataType span => span

inductive ItemDerives : TargetLang → String → SourceItem → Prop where
  | runtime {lang : TargetLang} {source : String} {control : SurfaceControl}
      {span : SourceSpan} {stmt : TargetStmt}
      (hStmt : StmtDerives lang control source span stmt) :
      ItemDerives lang source (.runtime control span stmt)
  | functionDecl {lang : TargetLang} {source : String}
      {span bodySpan : SourceSpan} {function : TargetFunction}
      (hFunction : FunctionDerives lang source span function)
      (hBody : StmtDerives lang .body source bodySpan function.body)
      (hWithin : span.start ≤ bodySpan.start ∧
        bodySpan.stop ≤ span.stop)
      (hLocated : FunctionBodyLocated lang span bodySpan function) :
      ItemDerives lang source (.functionDecl span bodySpan function)
  | tsTypeImport {source : String} {span : SourceSpan}
      {names : List String} {moduleName : String}
      (hNames : TypeNames names)
      (hModule : StringLiteralSyntax .ts
        ("\"" ++ moduleName ++ "\"") moduleName)
      (hText : span.text source =
        "import type { " ++ renderTypeNames names ++
          " } from \"" ++ moduleName ++ "\";")
      (hErased : ErasedDerives .ts source span) :
      ItemDerives .ts source (.tsTypeImport span names moduleName)
  | tsWorldDataType {source : String} {span : SourceSpan}
      (hErased : ErasedDerives .ts source span) :
      ItemDerives .ts source (.tsWorldDataType span)

inductive ItemsDerive : TargetLang → String → List SourceItem → Prop where
  | nil (lang : TargetLang) (source : String) : ItemsDerive lang source []
  | cons {lang : TargetLang} {source : String}
      {item : SourceItem} {rest : List SourceItem}
      (hItem : ItemDerives lang source item)
      (hRest : ItemsDerive lang source rest) :
      ItemsDerive lang source (item :: rest)

inductive OrderedItems : List SourceItem → Prop where
  | nil : OrderedItems []
  | single (item : SourceItem) : OrderedItems [item]
  | cons {first second : SourceItem} {rest : List SourceItem}
      (hOrder : first.span.stop ≤ second.span.start)
      (hRest : OrderedItems (second :: rest)) :
      OrderedItems (first :: second :: rest)

def TokenWithinItem (token : SourceToken) (item : SourceItem) : Prop :=
  item.span.start ≤ token.start ∧ token.stop ≤ item.span.stop

def NontriviaOwned (tokens : List SourceToken) (items : List SourceItem)
    (prefixStop : Nat) : Prop :=
  ∀ token, token ∈ tokens → token.stop ≤ prefixStop →
    token.kind ≠ .spacing → token.kind ≠ .comment →
      ∃ item, item ∈ items ∧ TokenWithinItem token item

/-- Partial progress carrier: lexical coverage is for the whole source while
    item ownership is only through `prefixStop`. It cannot certify a program
    until every remaining executable declaration is likewise derived. -/
inductive PrefixDerives (lang : TargetLang) (source : String)
    (prefixStop : Nat) : Prop where
  | ofItems {tokens : List SourceToken} {items : List SourceItem}
      (hLexes : Lexes lang source tokens)
      (hSyntax : ItemsDerive lang source items)
      (hOrder : OrderedItems items)
      (hOwnership : NontriviaOwned tokens items prefixStop) :
      PrefixDerives lang source prefixStop

end Harmonia.Applications.Kadmos.Generated
