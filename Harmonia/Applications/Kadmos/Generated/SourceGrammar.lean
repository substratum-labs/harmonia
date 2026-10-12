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

inductive FormatSyntax : TargetLang → String → TargetExpr → Prop where
  | empty (lang : TargetLang) : FormatSyntax lang "" .empty
  | literal {lang : TargetLang} {text : String}
      (hNonempty : text.isEmpty = false)
      (hNoHole : splitFirstFormat text (formatOpen lang) = none) :
      FormatSyntax lang text (.formatPart text .empty .empty)
  | hole {lang : TargetLang} {headText name tail : String} {rest : TargetExpr}
      (hNoHole : splitFirstFormat headText (formatOpen lang) = none)
      (hName : IdentifierText name)
      (hRest : FormatSyntax lang tail rest) :
      FormatSyntax lang (headText ++ formatOpen lang ++ name ++ "}" ++ tail)
        (.formatPart headText (.local name) rest)

inductive FormatWrapper : TargetLang → String → String → Prop where
  | ts (content : String) : FormatWrapper .ts ("`" ++ content ++ "`") content
  | pythonDouble (content : String) :
      FormatWrapper .python ("f\"" ++ content ++ "\"") content
  | pythonSingle (content : String) :
      FormatWrapper .python ("f'" ++ content ++ "'") content

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

mutual
/-- Source productions, independent of the executable decoder. Argument
    sequences have their own sort: a bare expression cannot also be an
    argument-list AST for the same source. -/
inductive ExprSyntax : TargetLang → String → TargetExpr → Prop where
  | empty (lang : TargetLang) : ExprSyntax lang "" .empty
  | call {lang : TargetLang} {calleeText argsText : String}
      {callee args : TargetExpr} {tokens : List SourceToken}
      (hLex : Lexes lang (calleeText ++ "(" ++ argsText ++ ")") tokens)
      (hOpen : finalCallOpen tokens = some calleeText.length)
      (hCalleeNonempty : calleeText.isEmpty = false)
      (hCallee : ExprSyntax lang calleeText callee)
      (hArgs : ArgumentSyntax lang argsText args) :
      ExprSyntax lang (calleeText ++ "(" ++ argsText ++ ")") (.call callee args)
  | tsTypeof {valueText : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts valueText value) :
      ExprSyntax .ts ("typeof " ++ valueText) (.unary .typeof value)
  | tsStrictNe {leftText rightText : String} {left right : TargetExpr}
      (hLeft : ExprSyntax .ts leftText left)
      (hRight : ExprSyntax .ts rightText right) :
      ExprSyntax .ts (leftText ++ " !== " ++ rightText)
        (.binary .strictNe left right)
  | pythonIsNot {leftText rightText : String} {left right : TargetExpr}
      (hLeft : ExprSyntax .python leftText left)
      (hRight : ExprSyntax .python rightText right) :
      ExprSyntax .python (leftText ++ " is not " ++ rightText)
        (.binary .isNotIdentity left right)
  | tsNew {valueText : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts valueText value) :
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
      (hName : PropertyIdentifier lang name) :
      ExprSyntax lang (base ++ "." ++ name) (.property receiver name)
  | tsOptionalProperty {base name : String} {receiver : TargetExpr}
      (hBaseNonempty : base.isEmpty = false)
      (hBase : ExprSyntax .ts base receiver)
      (hName : IdentifierText name) :
      ExprSyntax .ts (base ++ "?." ++ name)
        (.optionalProperty receiver name)
  | index {lang : TargetLang} {base keyText : String}
      {receiver key : TargetExpr}
      (hBaseNonempty : base.isEmpty = false)
      (hBase : ExprSyntax lang base receiver)
      (hKey : ExprSyntax lang keyText key) :
      ExprSyntax lang (base ++ "[" ++ keyText ++ "]")
        (.index receiver key)
  | tsNonNull {base : String} {value : TargetExpr}
      (hValue : ExprSyntax .ts base value) :
      ExprSyntax .ts (base ++ "!") (.nonNull value)
  | sub {lang : TargetLang} {leftText rightText : String}
      {left right : TargetExpr}
      (hLeft : ExprSyntax lang leftText left)
      (hRight : ExprSyntax lang rightText right)
      (hRightmost : RightmostSubOperand rightText) :
      ExprSyntax lang (leftText ++ " - " ++ rightText) (.binary .sub left right)
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

theorem ExprSyntax.no_empty_callee {lang source args} :
    ¬ ExprSyntax lang source (.call .empty args) := by
  intro h
  cases h with
  | call hLex hOpen hNonempty hCallee hArgs =>
      cases hCallee with
      | empty =>
          have hz : ("" : String).isEmpty = true := by decide
          rw [hz] at hNonempty
          cases hNonempty

theorem ArgumentSyntax.no_empty_first {lang source rest} :
    ¬ ArgumentSyntax lang source (.sequence .empty rest) := by
  intro h
  cases h with
  | one hNonempty hValue =>
      cases hValue with
      | empty =>
          have hz : ("" : String).isEmpty = true := by decide
          rw [hz] at hNonempty
          cases hNonempty
  | more hNonempty hLex hComma hGap hFirst hRest =>
      cases hFirst with
      | empty =>
          have hz : ("" : String).isEmpty = true := by decide
          rw [hz] at hNonempty
          cases hNonempty

theorem ExprSyntax.no_empty_property_receiver {lang source name} :
    ¬ ExprSyntax lang source (.property .empty name) := by
  intro h
  cases h with
  | property hNonempty hBase hName =>
      cases hBase with
      | empty =>
          have hz : ("" : String).isEmpty = true := by decide
          rw [hz] at hNonempty
          cases hNonempty

theorem ExprSyntax.no_empty_optional_receiver {source name} :
    ¬ ExprSyntax .ts source (.optionalProperty .empty name) := by
  intro h
  cases h with
  | tsOptionalProperty hNonempty hBase hName =>
      cases hBase with
      | empty =>
          have hz : ("" : String).isEmpty = true := by decide
          rw [hz] at hNonempty
          cases hNonempty

theorem ExprSyntax.no_empty_index_receiver {lang source key} :
    ¬ ExprSyntax lang source (.index .empty key) := by
  intro h
  cases h with
  | index hNonempty hBase hKey =>
      cases hBase with
      | empty =>
          have hz : ("" : String).isEmpty = true := by decide
          rw [hz] at hNonempty
          cases hNonempty

inductive ExprDerives : TargetLang → String → SourceSpan → TargetExpr → Prop where
  | ofSyntax {lang : TargetLang} {source : String} {span : SourceSpan}
      {expr : TargetExpr}
      (hBounds : span.start ≤ span.stop ∧ span.stop ≤ source.length)
      (hSyntax : ExprSyntax lang (span.text source) expr) :
      ExprDerives lang source span expr

inductive SurfaceControl where
  | module | function | loop | switch
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

inductive StmtSyntax : TargetLang → SurfaceControl → String → TargetStmt → Prop where
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
      (hBody : StmtSyntax .python .function bodySource body) :
      StmtSyntax .python .function
        ("if " ++ conditionSource ++ ":\n        " ++ bodySource)
        (.ifThenElse condition body .empty)
  | pythonSequence {firstSource restSource : String}
      {first rest : TargetStmt}
      (hFirst : StmtSyntax .python .function firstSource first)
      (hRest : StmtSyntax .python .function restSource rest) :
      StmtSyntax .python .function (firstSource ++ "\n    " ++ restSource)
        (.sequence first rest)
  | pythonFinal {source : String} {last : TargetStmt}
      (hLast : StmtSyntax .python .function source last) :
      StmtSyntax .python .function source (.sequence last .empty)
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
      (hBody : StmtSyntax .ts .function bodySource body) :
      StmtSyntax .ts .function
        ("if (" ++ conditionSource ++ ") " ++ bodySource)
        (.ifThenElse condition body .empty)
  | tsSequence {firstSource restSource : String}
      {first rest : TargetStmt}
      (hFirst : StmtSyntax .ts .function firstSource first)
      (hRest : StmtSyntax .ts .function restSource rest) :
      StmtSyntax .ts .function (firstSource ++ "\n  " ++ restSource)
        (.sequence first rest)
  | tsFinal {source : String} {last : TargetStmt}
      (hLast : StmtSyntax .ts .function source last) :
      StmtSyntax .ts .function source (.sequence last .empty)
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

inductive StmtDerives : TargetLang → SurfaceControl → String → SourceSpan → TargetStmt → Prop where
  | ofSyntax {lang : TargetLang} {control : SurfaceControl}
      {source : String} {span : SourceSpan} {stmt : TargetStmt}
      (hBounds : span.start ≤ span.stop ∧ span.stop ≤ source.length)
      (hSyntax : StmtSyntax lang control (span.text source) stmt) :
      StmtDerives lang control source span stmt

/-- A module function owns its header and constituent body. Additional
    parameter/type productions are added only for emitted forms; the body is
    always derived through `StmtSyntax`, never assigned ideal behavior. -/
inductive FunctionSyntax : TargetLang → String → TargetFunction → Prop where
  | pythonAnyToBool {name param bodySource : String} {body : TargetStmt}
      (hName : IdentifierText name) (hParam : IdentifierText param)
      (hBody : StmtSyntax .python .function bodySource body) :
      FunctionSyntax .python
        ("def " ++ name ++ "(" ++ param ++
          ": Any) -> bool:\n    " ++ bodySource)
        ⟨name, [⟨param, none⟩], body⟩
  | tsUnknownToBool {name param bodySource : String} {body : TargetStmt}
      (hName : IdentifierText name) (hParam : IdentifierText param)
      (hBody : StmtSyntax .ts .function bodySource body) :
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
      (hBody : StmtDerives lang .function source bodySpan function.body)
      (hWithin : span.start ≤ bodySpan.start ∧
        bodySpan.stop ≤ span.stop) :
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
