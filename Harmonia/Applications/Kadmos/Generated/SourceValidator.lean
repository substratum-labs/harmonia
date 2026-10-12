import Harmonia.Applications.Kadmos.Generated.SourceGrammar
import Harmonia.Applications.Kadmos.Generated.SourceLexicalValidator

set_option maxHeartbeats 1000000

namespace Harmonia.Applications.Kadmos.Generated

private def joinProperty : List String → String
  | [] => ""
  | [last] => last
  | first :: rest => first ++ "." ++ joinProperty rest

private def splitProperty (source : String) : Option (String × String) :=
  match (source.splitSourceOn ".").reverse with
  | name :: first :: rest => some (joinProperty (first :: rest).reverse, name)
  | _ => none

private def joinOptionalProperty : List String → String
  | [] => ""
  | [last] => last
  | first :: rest => first ++ "?." ++ joinOptionalProperty rest

private def splitOptionalProperty (source : String) : Option (String × String) :=
  match (source.splitSourceOn "?.").reverse with
  | name :: first :: rest =>
      some (joinOptionalProperty (first :: rest).reverse, name)
  | _ => none

private def joinIndexBase : List String → String
  | [] => ""
  | [last] => last
  | first :: rest => first ++ "[" ++ joinIndexBase rest

private def splitIndex (source : String) : Option (String × String) :=
  match (source.splitSourceOn "[").reverse with
  | withClose :: first :: rest =>
      match withClose.toList.reverse with
      | ']' :: reversedKey =>
          some (joinIndexBase (first :: rest).reverse,
            String.mk reversedKey.reverse)
      | _ => none
  | _ => none

private def splitSub (source : String) : Option (String × String) :=
  match source.splitSourceOn " - " with
  | [left, right] => some (left, right)
  | _ => none

private def splitStrictNe (source : String) : Option (String × String) :=
  match source.splitSourceOn " !== " with
  | [left, right] => some (left, right)
  | _ => none

private def splitPythonIsNot (source : String) : Option (String × String) :=
  match source.splitSourceOn " is not " with
  | [left, right] => some (left, right)
  | _ => none

private def afterSourcePrefix (source head : String) : Option String :=
  if source.startsWith head then
    some (String.mk (source.toList.drop head.length))
  else none

def validateFormatText (lang : TargetLang) (source : String) : TargetExpr → Bool
  | .empty => source == ""
  | .formatPart text .empty .empty =>
      !text.isEmpty && source == text &&
        (splitFirstFormat text (formatOpen lang)).isNone
  | .formatPart headText (.local name) rest =>
      match splitFirstFormat source (formatOpen lang) with
      | none => false
      | some (before, afterOpen) =>
          match splitFirstFormat afterOpen "}" with
          | none => false
          | some (holeText, tail) =>
              before == headText && holeText == name &&
                source == headText ++ formatOpen lang ++ name ++ "}" ++ tail &&
                (splitFirstFormat headText (formatOpen lang)).isNone &&
                identifierTextCheck name && validateFormatText lang tail rest
  | _ => false

theorem validateFormatText_sound (lang : TargetLang) (source : String)
    (parts : TargetExpr) (h : validateFormatText lang source parts = true) :
    FormatSyntax lang source parts := by
  induction parts generalizing source with
  | empty =>
      simp [validateFormatText] at h
      subst source
      exact .empty lang
  | formatPart text value rest ihValue ihRest =>
      cases value with
      | empty =>
          cases rest <;> simp [validateFormatText] at h
          rcases h with ⟨⟨hNonempty, hEq⟩, hNoHole⟩
          subst source
          exact .literal hNonempty hNoHole
      | «local» name =>
          simp only [validateFormatText] at h
          cases hs1 : splitFirstFormat source (formatOpen lang) with
          | none => simp [hs1] at h
          | some firstParts =>
              rcases firstParts with ⟨before, afterOpen⟩
              cases hs2 : splitFirstFormat afterOpen "}" with
              | none => simp [hs1, hs2] at h
              | some secondParts =>
                  rcases secondParts with ⟨holeText, tail⟩
                  simp only [hs1, hs2, Bool.and_eq_true, beq_iff_eq] at h
                  rcases h with ⟨⟨⟨⟨⟨hBefore, hName⟩, hEq⟩, hNoHole⟩,
                    hIdent⟩, hRest⟩
                  have hNo : splitFirstFormat text (formatOpen lang) = none := by
                    cases hn : splitFirstFormat text (formatOpen lang) with
                    | none => rfl
                    | some value => simp [hn] at hNoHole
                  subst source
                  exact .hole hNo (identifierTextCheck_sound hIdent) (ihRest tail hRest)
      | _ => simp [validateFormatText] at h
  | _ => simp [validateFormatText] at h

private def wrapperContent (lang : TargetLang) (source : String) : Option String :=
  match lang, source.toList with
  | .ts, '`' :: rest =>
      match rest.reverse with
      | '`' :: inside => some (String.mk inside.reverse)
      | _ => none
  | .python, 'f' :: '"' :: rest =>
      match rest.reverse with
      | '"' :: inside => some (String.mk inside.reverse)
      | _ => none
  | .python, 'f' :: '\'' :: rest =>
      match rest.reverse with
      | '\'' :: inside => some (String.mk inside.reverse)
      | _ => none
  | _, _ => none

private def wrapperRebuild (lang : TargetLang) (content : String) : String :=
  if lang == .ts then "`" ++ content ++ "`"
  else "f\"" ++ content ++ "\""

private def stripFinalParen (source : String) : Option String :=
  match source.toList.reverse with
  | ')' :: inside => some (String.mk inside.reverse)
  | _ => none

private def stripFinalBang (source : String) : Option String :=
  match source.toList.reverse with
  | '!' :: inside => some (String.mk inside.reverse)
  | _ => none

private def stripFinalSemicolon (source : String) : Option String :=
  match source.toList.reverse with
  | ';' :: inside => some (String.mk inside.reverse)
  | _ => none

private def tsModuleValueText (source name typeSource : String) : Option String :=
  stripFinalSemicolon (String.mk (source.toList.drop
    ("const " ++ name ++ ": " ++ typeSource ++ " = ").length))

private def argumentCommaPieces (source : String) (comma : Nat) :
    String × String × String :=
  let first := SourceSpan.text source ⟨0, comma⟩
  let after := SourceSpan.suffix source (comma + 1)
  let gap := String.mk (after.toList.takeWhile Char.isWhitespace)
  let rest := String.mk (after.toList.drop gap.length)
  (first, gap, rest)

private def finalCallPieces (source : String) (openPos : Nat) :
    Option (String × String) := do
  let callee := SourceSpan.text source ⟨0, openPos⟩
  let args ← stripFinalParen (SourceSpan.suffix source (openPos + 1))
  return (callee, args)

mutual
/-- AST-guided source check: source text, rather than the raw decoder,
    determines these operator boundaries. -/
def validateExprText (lang : TargetLang) (source : String) : TargetExpr → Bool
  | .empty => source == ""
  | .call callee args =>
      match tokenizeSource lang source with
      | .error _ => false
      | .ok tokens =>
          match finalCallOpen tokens with
          | none => false
          | some openPos =>
              match finalCallPieces source openPos with
              | none => false
              | some (calleeText, argsText) =>
                  validateLexes lang source tokens &&
                  openPos == calleeText.length &&
                  !calleeText.isEmpty &&
                  source == calleeText ++ "(" ++ argsText ++ ")" &&
                  validateExprText lang calleeText callee &&
                  validateArgumentText lang argsText args
  | .bool value =>
      source == (if lang == .ts then
        (if value then "true" else "false")
        else (if value then "True" else "False"))
  | .null => source == (if lang == .ts then "null" else "None")
  | .undefined => lang == .ts && source == "undefined"
  | .integer n =>
      match source.toNat? with
      | some value => n == Int.ofNat value
      | none => false
  | .decimal literal =>
      source == literal && numberTokenCheck source && source.toList.contains '.'
  | .string value => validateStringLiteral lang source value
  | .local name =>
      if lang == .ts && name == "this" then source == "this"
      else expressionIdentifierCheck lang name && source == name
  | .property receiver name =>
      match splitProperty source with
      | some (base, field) =>
          !base.isEmpty && propertyIdentifierCheck lang field && field == name &&
            source == base ++ "." ++ field && validateExprText lang base receiver
      | none => false
  | .optionalProperty receiver name =>
      if lang == .ts then
        match splitOptionalProperty source with
        | some (base, field) =>
            !base.isEmpty && identifierTextCheck field && field == name &&
              source == base ++ "?." ++ field &&
              validateExprText .ts base receiver
        | none => false
      else false
  | .index receiver key =>
      match splitIndex source with
      | some (base, keyText) =>
          !base.isEmpty && source == base ++ "[" ++ keyText ++ "]" &&
            validateExprText lang base receiver &&
            validateExprText lang keyText key
      | none => false
  | .nonNull value =>
      if lang == .ts then
        match stripFinalBang source with
        | some base => source == base ++ "!" &&
            validateExprText .ts base value
        | none => false
      else false
  | .binary .sub left right =>
      match splitSub source with
      | some (leftText, rightText) =>
          source == leftText ++ " - " ++ rightText &&
            validateExprText lang leftText left &&
            validateExprText lang rightText right &&
            (rightText.splitSourceOn " - ") == [rightText]
      | none => false
  | .formatted parts =>
      match wrapperContent lang source with
      | none => false
      | some content =>
          source == wrapperRebuild lang content &&
            parts != .empty && validateFormatText lang content parts
  | _ => false

def validateArgumentText (lang : TargetLang) (source : String) : TargetExpr → Bool
  | .empty => source == ""
  | .sequence value rest =>
      match rest with
      | .empty => !source.isEmpty && validateExprText lang source value
      | _ =>
          match tokenizeSource lang source with
          | .error _ => false
          | .ok tokens =>
              match firstTopLevelComma tokens with
              | none => false
              | some comma =>
                  let (firstText, gap, restText) :=
                    argumentCommaPieces source comma
                  !firstText.isEmpty && validateLexes lang source tokens &&
                    comma == firstText.length &&
                    source == firstText ++ "," ++ gap ++ restText &&
                    gap.toList.all Char.isWhitespace &&
                    validateExprText lang firstText value &&
                    validateArgumentText lang restText rest
  | _ => false
end

def validateExprSpan (lang : TargetLang) (source : String)
    (span : SourceSpan) (expr : TargetExpr) : Bool :=
  span.start ≤ span.stop && span.stop ≤ source.length &&
    validateExprText lang (span.text source) expr

private theorem validateExprAndArgument_sound (lang : TargetLang) (expr : TargetExpr) :
    (∀ source, validateExprText lang source expr = true → ExprSyntax lang source expr) ∧
    (∀ source, validateArgumentText lang source expr = true →
      ArgumentSyntax lang source expr) := by
  induction expr with
  | empty =>
      constructor
      · intro source h
        simp [validateExprText] at h
        subst source
        exact .empty lang
      · intro source h
        simp [validateArgumentText] at h
        subst source
        exact .empty lang
  | sequence value rest ihValue ihRest =>
      constructor
      · intro source h
        simp [validateExprText] at h
      · intro source h
        cases rest with
        | empty =>
            simp only [validateArgumentText, Bool.and_eq_true,
              Bool.not_eq_true] at h
            exact .one (by simpa using h.1) (ihValue.1 source h.2)
        | sequence next tail =>
            simp only [validateArgumentText] at h
            cases ht : tokenizeSource lang source with
            | error error => simp [ht] at h
            | ok tokens =>
                cases hc : firstTopLevelComma tokens with
                | none => simp [ht, hc] at h
                | some comma =>
                    rcases hp : argumentCommaPieces source comma with
                      ⟨firstText, gap, restText⟩
                    simp only [ht, hc, hp, Bool.and_eq_true, beq_iff_eq] at h
                    rcases h with ⟨⟨⟨⟨⟨⟨hFirstNonempty, hLex⟩, hOffset⟩,
                      hSource⟩, hGap⟩, hFirst⟩, hTail⟩
                    have hLexDerived : Lexes lang
                        (firstText ++ "," ++ gap ++ restText) tokens := by
                      rw [← hSource]
                      exact validateLexes_sound hLex
                    have hComma : firstTopLevelComma tokens =
                        some firstText.length := by
                      simpa only [hOffset] using hc
                    have hDerived : ArgumentSyntax lang
                        (firstText ++ "," ++ gap ++ restText)
                        (.sequence value (.sequence next tail)) :=
                      .more (by simpa using hFirstNonempty)
                        hLexDerived hComma hGap
                        (ihValue.1 firstText hFirst)
                        (ihRest.2 restText hTail)
                    exact hSource.symm ▸ hDerived
        | _ =>
            simp only [validateArgumentText] at h
            cases ht : tokenizeSource lang source with
            | error _ => simp [ht] at h
            | ok tokens =>
                cases hc : firstTopLevelComma tokens with
                | none => simp [ht, hc] at h
                | some _ => simp [ht, hc] at h
  | call callee args ihCallee ihArgs =>
      constructor
      · intro source h
        simp only [validateExprText] at h
        cases ht : tokenizeSource lang source with
        | error _ => simp [ht] at h
        | ok tokens =>
            cases ho : finalCallOpen tokens with
            | none => simp [ht, ho] at h
            | some openPos =>
                cases hp : finalCallPieces source openPos with
                | none => simp [ht, ho, hp] at h
                | some parts =>
                    rcases parts with ⟨calleeText, argsText⟩
                    simp only [ht, ho, hp, Bool.and_eq_true,
                      beq_iff_eq] at h
                    rcases h with ⟨⟨⟨⟨⟨hLex, hOffset⟩, hNonempty⟩,
                      hSource⟩, hCallee⟩, hArgs⟩
                    have hLexDerived : Lexes lang
                        (calleeText ++ "(" ++ argsText ++ ")") tokens := by
                      rw [← hSource]
                      exact validateLexes_sound hLex
                    have hOpen : finalCallOpen tokens =
                        some calleeText.length := by
                      simpa only [hOffset] using ho
                    subst source
                    exact .call hLexDerived hOpen
                      (by simpa using hNonempty)
                      (ihCallee.1 calleeText hCallee)
                      (ihArgs.2 argsText hArgs)
      · intro source h
        simp [validateArgumentText] at h
  | bool value =>
      constructor
      · intro source h
        cases lang <;> simp [validateExprText] at h
        · subst source; exact .tsBool value
        · subst source; exact .pythonBool value
      · intro source h
        simp [validateArgumentText] at h
  | null =>
      constructor
      · intro source h
        cases lang <;> simp [validateExprText] at h
        · subst source; exact .tsNull
        · subst source; exact .pythonNone
      · intro source h
        simp [validateArgumentText] at h
  | undefined =>
      constructor
      · intro source h
        simp [validateExprText] at h
        rcases h with ⟨rfl, rfl⟩
        exact .tsUndefined
      · intro source h
        simp [validateArgumentText] at h
  | integer n =>
      constructor
      · intro source h
        simp only [validateExprText] at h
        cases hv : source.toNat? with
        | none => simp [hv] at h
        | some value =>
            simp only [hv, beq_iff_eq] at h
            subst n
            exact .numeral hv
      · intro source h
        simp [validateArgumentText] at h
  | decimal literal =>
      constructor
      · intro source h
        simp only [validateExprText, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨⟨hSource, hNumber⟩, hDot⟩
        subst literal
        exact .decimal hNumber hDot
      · intro source h
        simp [validateArgumentText] at h
  | string value =>
      constructor
      · intro source h
        simp only [validateExprText] at h
        exact .string (validateStringLiteral_sound h)
      · intro source h
        simp [validateArgumentText] at h
  | «local» name =>
      constructor
      · intro source h
        cases hc : (lang == .ts && name == "this") with
        | true =>
            simp only [validateExprText, hc, beq_iff_eq] at h
            have hPair : lang = .ts ∧ name = "this" := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hc
            rcases hPair with ⟨rfl, rfl⟩
            simp at h
            subst source
            exact .tsThis
        | false =>
            simp only [validateExprText, hc, Bool.false_eq_true, ite_false,
              Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨hne, heq⟩
            subst source
            exact ExprSyntax.local (expressionIdentifierCheck_sound hne)
      · intro source h
        simp [validateArgumentText] at h
  | property receiver name ih =>
      constructor
      · intro source h
        simp only [validateExprText] at h
        cases hs : splitProperty source with
        | none => simp [hs] at h
        | some parts =>
            rcases parts with ⟨base, field⟩
            simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨⟨⟨⟨hBaseNonempty, hne⟩, heq⟩, hconcat⟩, hrec⟩
            subst source
            subst field
            exact .property (by simpa using hBaseNonempty)
              (ih.1 base hrec) (propertyIdentifierCheck_sound hne)
      · intro source h
        simp [validateArgumentText] at h
  | optionalProperty receiver name ih =>
      constructor
      · intro source h
        cases lang with
        | python => simp [validateExprText] at h
        | ts =>
            simp only [validateExprText, beq_self_eq_true, ↓reduceIte] at h
            cases hs : splitOptionalProperty source with
            | none => simp [hs] at h
            | some parts =>
                rcases parts with ⟨base, field⟩
                simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
                rcases h with ⟨⟨⟨⟨hBaseNonempty, hName⟩, hEq⟩, hSource⟩,
                  hBase⟩
                subst source
                subst field
                exact .tsOptionalProperty (by simpa using hBaseNonempty)
                  (ih.1 base hBase)
                  (identifierTextCheck_sound hName)
      · intro source h
        simp [validateArgumentText] at h
  | index receiver key ihReceiver ihKey =>
      constructor
      · intro source h
        simp only [validateExprText] at h
        cases hs : splitIndex source with
        | none => simp [hs] at h
        | some parts =>
            rcases parts with ⟨base, keyText⟩
            simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨⟨⟨hBaseNonempty, hSource⟩, hBase⟩, hKey⟩
            subst source
            exact .index (by simpa using hBaseNonempty)
              (ihReceiver.1 base hBase)
              (ihKey.1 keyText hKey)
      · intro source h
        simp [validateArgumentText] at h
  | nonNull value ih =>
      constructor
      · intro source h
        cases lang with
        | python => simp [validateExprText] at h
        | ts =>
            simp only [validateExprText, beq_self_eq_true, ↓reduceIte] at h
            cases hs : stripFinalBang source with
            | none => simp [hs] at h
            | some base =>
                simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
                rcases h with ⟨hSource, hValue⟩
                subst source
                exact .tsNonNull (ih.1 base hValue)
      · intro source h
        simp [validateArgumentText] at h
  | binary op left right ihLeft ihRight =>
      constructor
      · intro source h
        cases op <;> simp [validateExprText] at h
        case sub =>
          cases hs : splitSub source with
          | none => simp [hs] at h
          | some parts =>
              rcases parts with ⟨leftText, rightText⟩
              simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨⟨hconcat, hleft⟩, hright⟩, hRightmost⟩
              subst source
              exact .sub (ihLeft.1 leftText hleft) (ihRight.1 rightText hright)
                (by simpa [RightmostSubOperand] using hRightmost)
      · intro source h
        simp [validateArgumentText] at h
  | formatted parts ih =>
      constructor
      · intro source h
        simp only [validateExprText] at h
        cases hw : wrapperContent lang source with
        | none => simp [hw] at h
        | some content =>
            simp only [hw, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨⟨hRebuild, hNonempty⟩, hParts⟩
            cases lang with
            | ts =>
                simp [wrapperRebuild] at hRebuild
                subst source
                exact .formatted (.ts content)
                  (validateFormatText_sound .ts content parts hParts)
                  (by simpa using hNonempty)
            | python =>
                simp [wrapperRebuild] at hRebuild
                subst source
                exact .formatted (.pythonDouble content)
                  (validateFormatText_sound .python content parts hParts)
                  (by simpa using hNonempty)
      · intro source h
        simp [validateArgumentText] at h
  | _ =>
      constructor
      · intro source h
        simp [validateExprText] at h
      · intro source h
        simp [validateArgumentText] at h

theorem validateExprText_sound (lang : TargetLang) (source : String)
    (expr : TargetExpr) (h : validateExprText lang source expr = true) :
    ExprSyntax lang source expr :=
  (validateExprAndArgument_sound lang expr).1 source h

theorem validateArgumentText_sound (lang : TargetLang) (source : String)
    (args : TargetExpr) (h : validateArgumentText lang source args = true) :
    ArgumentSyntax lang source args :=
  (validateExprAndArgument_sound lang args).2 source h

/-- Form-specific checks avoid unfolding the whole recursive expression
    checker when a selected AST constructor is already known. -/
def validateTSTypeofValue (source : String) (value : TargetExpr) : Bool :=
  match afterSourcePrefix source "typeof " with
  | some valueText => source == "typeof " ++ valueText &&
      validateExprText .ts valueText value
  | none => false

theorem validateTSTypeofValue_sound {source value}
    (h : validateTSTypeofValue source value = true) :
    ExprSyntax .ts source (.unary .typeof value) := by
  unfold validateTSTypeofValue at h
  cases hp : afterSourcePrefix source "typeof " with
  | none => simp [hp] at h
  | some valueText =>
      simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hSource, hValue⟩
      subst source
      exact .tsTypeof (validateExprText_sound .ts valueText value hValue)

def validateTSStrictNeTypeofValue (source : String)
    (value right : TargetExpr) : Bool :=
  match splitStrictNe source with
  | some (leftText, rightText) =>
      source == leftText ++ " !== " ++ rightText &&
        validateTSTypeofValue leftText value &&
        validateExprText .ts rightText right
  | none => false

theorem validateTSStrictNeTypeofValue_sound {source value right}
    (h : validateTSStrictNeTypeofValue source value right = true) :
    ExprSyntax .ts source
      (.binary .strictNe (.unary .typeof value) right) := by
  unfold validateTSStrictNeTypeofValue at h
  cases hs : splitStrictNe source with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨leftText, rightText⟩
      simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨hSource, hLeft⟩, hRight⟩
      subst source
      exact .tsStrictNe (validateTSTypeofValue_sound hLeft)
        (validateExprText_sound .ts rightText right hRight)

def validateTSNewValue (source : String) (value : TargetExpr) : Bool :=
  match afterSourcePrefix source "new " with
  | some valueText => source == "new " ++ valueText &&
      validateExprText .ts valueText value
  | none => false

theorem validateTSNewValue_sound {source value}
    (h : validateTSNewValue source value = true) :
    ExprSyntax .ts source (.newExpr value) := by
  unfold validateTSNewValue at h
  cases hp : afterSourcePrefix source "new " with
  | none => simp [hp] at h
  | some valueText =>
      simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hSource, hValue⟩
      subst source
      exact .tsNew (validateExprText_sound .ts valueText value hValue)

def validatePythonIsNotValues (source : String)
    (left right : TargetExpr) : Bool :=
  match splitPythonIsNot source with
  | some (leftText, rightText) =>
      source == leftText ++ " is not " ++ rightText &&
        validateExprText .python leftText left &&
        validateExprText .python rightText right
  | none => false

theorem validatePythonIsNotValues_sound {source left right}
    (h : validatePythonIsNotValues source left right = true) :
    ExprSyntax .python source (.binary .isNotIdentity left right) := by
  unfold validatePythonIsNotValues at h
  cases hs : splitPythonIsNot source with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨leftText, rightText⟩
      simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨hSource, hLeft⟩, hRight⟩
      subst source
      exact .pythonIsNot
        (validateExprText_sound .python leftText left hLeft)
        (validateExprText_sound .python rightText right hRight)

theorem validateExprSpan_sound {lang source span expr}
    (h : validateExprSpan lang source span expr = true) :
    ExprDerives lang source span expr := by
  simp [validateExprSpan] at h
  exact .ofSyntax h.1
    (validateExprText_sound lang (span.text source) expr h.2)

/-- Function bodies choose a source production by the low-level AST node;
    these branches still validate every operand through `ExprSyntax`. -/
def validateFunctionExpr (lang : TargetLang) (source : String)
    (expr : TargetExpr) : Bool :=
  match lang, expr with
  | .ts, .binary .strictNe (.unary .typeof value) right =>
      validateTSStrictNeTypeofValue source value right
  | .python, .binary .isNotIdentity left right =>
      validatePythonIsNotValues source left right
  | .ts, .newExpr value => validateTSNewValue source value
  | _, _ => validateExprText lang source expr

theorem validateFunctionExpr_sound {lang source expr}
    (h : validateFunctionExpr lang source expr = true) :
    ExprSyntax lang source expr := by
  cases lang with
  | ts =>
      cases expr with
      | binary op left right =>
          cases op <;> simp only [validateFunctionExpr] at h
          case strictNe =>
            cases left with
            | unary unaryOp value =>
                cases unaryOp <;> simp only [validateFunctionExpr] at h
                case typeof => exact validateTSStrictNeTypeofValue_sound h
                all_goals exact validateExprText_sound .ts source _ h
            | _ => exact validateExprText_sound .ts source _ h
          all_goals exact validateExprText_sound .ts source _ h
      | newExpr value => exact validateTSNewValue_sound h
      | _ => exact validateExprText_sound .ts source _ h
  | python =>
      cases expr with
      | binary op left right =>
          cases op <;> simp only [validateFunctionExpr] at h
          case isNotIdentity => exact validatePythonIsNotValues_sound h
          all_goals exact validateExprText_sound .python source _ h
      | _ => exact validateExprText_sound .python source _ h

private def joinSourceWith (separator : String) : List String → String
  | [] => ""
  | [last] => last
  | first :: rest => first ++ separator ++ joinSourceWith separator rest

private def splitLastFormat (source separator : String) :
    Option (String × String) :=
  match (source.splitSourceOn separator).reverse with
  | last :: first :: rest =>
      some (joinSourceWith separator (first :: rest).reverse, last)
  | _ => none

def validateStmtText (lang : TargetLang) (control : SurfaceControl)
    (source : String) : TargetStmt → Bool
  | .sequence first rest =>
      if rest == .empty then
        control == .function &&
          validateStmtText lang .function source first
      else if control == .function then
        let delimiter := if lang == .ts then "\n  " else "\n    "
        let parts := if lang == .ts then splitFirstFormat source delimiter
          else splitLastFormat source delimiter
        match parts with
        | some (firstText, restText) =>
            source == firstText ++ delimiter ++ restText &&
              validateStmtText lang .function firstText first &&
              validateStmtText lang .function restText rest
        | none => false
      else false
  | .ifThenElse cond yes no =>
      if no == .empty && control == .function then
        match lang with
        | .ts =>
            match afterSourcePrefix source "if (" with
            | some remaining =>
                match splitFirstFormat remaining ") " with
                | some (conditionText, bodyText) =>
                    source == "if (" ++ conditionText ++ ") " ++ bodyText &&
                      validateFunctionExpr .ts conditionText cond &&
                      validateStmtText .ts .function bodyText yes
                | none => false
            | none => false
        | .python =>
            match afterSourcePrefix source "if " with
            | some remaining =>
                match splitFirstFormat remaining ":\n        " with
                | some (conditionText, bodyText) =>
                    source == "if " ++ conditionText ++ ":\n        " ++ bodyText &&
                      validateFunctionExpr .python conditionText cond &&
                      validateStmtText .python .function bodyText yes
                | none => false
            | none => false
      else false
  | .returnValue value =>
      if control == .function then
        match lang with
        | .ts =>
            match afterSourcePrefix source "return " with
            | some withClose =>
                match stripFinalSemicolon withClose with
                | some valueText =>
                    source == "return " ++ valueText ++ ";" &&
                      validateFunctionExpr .ts valueText value
                | none => false
            | none => false
        | .python =>
            match afterSourcePrefix source "return " with
            | some valueText =>
                source == "return " ++ valueText &&
                  validateFunctionExpr .python valueText value
            | none => false
      else false
  | .throwValue value =>
      if control == .function then
        match lang with
        | .ts =>
            match afterSourcePrefix source "throw " with
            | some withClose =>
                match stripFinalSemicolon withClose with
                | some valueText =>
                    source == "throw " ++ valueText ++ ";" &&
                      validateFunctionExpr .ts valueText value
                | none => false
            | none => false
        | .python =>
            match afterSourcePrefix source "raise " with
            | some valueText =>
                source == "raise " ++ valueText &&
                  validateFunctionExpr .python valueText value
            | none => false
      else false
  | .assign (.local name) value =>
      match afterSourcePrefix source (name ++ " = ") with
      | some valueSource =>
          lang == .python && control == .module &&
            identifierTextCheck name &&
            source == name ++ " = " ++ valueSource &&
            validateExprText .python valueSource value
      | none => false
  | .letLocal name mutable value =>
      lang == .ts && control == .module && !mutable &&
        match tsModuleType name with
      | none => false
      | some typeSource =>
          let head := "const " ++ name ++ ": " ++ typeSource ++ " = "
          match tsModuleValueText source name typeSource with
          | none => false
          | some valueSource =>
              source == head ++ valueSource ++ ";" &&
                validateExprText .ts valueSource value
  | .importModule moduleName alias =>
      lang == .python && control == .module &&
        identifierTextCheck moduleName && alias == moduleName &&
        source == "import " ++ moduleName
  | .fromImport moduleName name alias =>
      match lang with
      | .ts =>
          control == .module && identifierTextCheck name &&
            identifierTextCheck alias &&
            source == "import { " ++ name ++ " as " ++ alias ++
              " } from \"" ++ moduleName ++ "\";"
      | .python =>
          control == .module && identifierTextCheck moduleName &&
            identifierTextCheck name && alias == name &&
            source == "from " ++ moduleName ++ " import " ++ name
  | .nonlocalNames [name] =>
      lang == .python && control == .function &&
        identifierTextCheck name && source == "nonlocal " ++ name
  | .breakTarget target =>
      match lang, control with
      | .ts, .switch => source == "break;" && target == "switch"
      | .ts, .loop => source == "break;" && target == "loop"
      | .python, .loop => source == "break" && target == "loop"
      | _, _ => false
  | _ => false

def validateStmtSpan (lang : TargetLang) (control : SurfaceControl)
    (source : String) (span : SourceSpan) (stmt : TargetStmt) : Bool :=
  span.start ≤ span.stop && span.stop ≤ source.length &&
    validateStmtText lang control (span.text source) stmt

theorem validateStmtText_sound (lang : TargetLang) (control : SurfaceControl)
    (source : String) (stmt : TargetStmt)
    (h : validateStmtText lang control source stmt = true) :
    StmtSyntax lang control source stmt := by
  induction stmt generalizing source control with
  | sequence first rest ihFirst ihRest =>
      by_cases hr : rest = .empty
      · subst rest
        simp only [validateStmtText, beq_self_eq_true, ↓reduceIte,
          Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨hControl, hFirst⟩
        subst control
        cases lang with
        | ts => exact .tsFinal (ihFirst .function source hFirst)
        | python => exact .pythonFinal (ihFirst .function source hFirst)
      · cases lang <;> cases control <;>
          simp [validateStmtText, hr] at h
        case neg.ts.function =>
          cases hs : splitFirstFormat source "\n  " with
          | none => simp [hs] at h
          | some parts =>
              rcases parts with ⟨firstText, restText⟩
              simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨hSource, hFirst⟩, hRest⟩
              subst source
              exact .tsSequence (ihFirst .function firstText hFirst)
                (ihRest .function restText hRest)
        case neg.python.function =>
          cases hs : splitLastFormat source "\n    " with
          | none => simp [hs] at h
          | some parts =>
              rcases parts with ⟨firstText, restText⟩
              simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨hSource, hFirst⟩, hRest⟩
              subst source
              exact .pythonSequence (ihFirst .function firstText hFirst)
                (ihRest .function restText hRest)
  | ifThenElse condition yes no ihYes ihNo =>
      by_cases hn : no = .empty
      · subst no
        cases lang <;> cases control <;>
          simp [validateStmtText] at h
        case pos.ts.function =>
          cases hp : afterSourcePrefix source "if (" with
          | none => simp [hp] at h
          | some remaining =>
              cases hs : splitFirstFormat remaining ") " with
              | none => simp [hp, hs] at h
              | some parts =>
                  rcases parts with ⟨conditionText, bodyText⟩
                  simp only [hp, hs, Bool.and_eq_true, beq_iff_eq] at h
                  rcases h with ⟨⟨hSource, hCond⟩, hBody⟩
                  subst source
                  exact .tsIfThen (validateFunctionExpr_sound hCond)
                    (ihYes .function bodyText hBody)
        case pos.python.function =>
          cases hp : afterSourcePrefix source "if " with
          | none => simp [hp] at h
          | some remaining =>
              cases hs : splitFirstFormat remaining ":\n        " with
              | none => simp [hp, hs] at h
              | some parts =>
                  rcases parts with ⟨conditionText, bodyText⟩
                  simp only [hp, hs, Bool.and_eq_true, beq_iff_eq] at h
                  rcases h with ⟨⟨hSource, hCond⟩, hBody⟩
                  subst source
                  exact .pythonIfThen (validateFunctionExpr_sound hCond)
                    (ihYes .function bodyText hBody)
      · simp [validateStmtText, hn] at h
  | assign target value =>
      cases target with
      | «local» name =>
          simp only [validateStmtText] at h
          cases hp : afterSourcePrefix source (name ++ " = ") with
          | none => simp [hp] at h
          | some valueSource =>
              simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨⟨⟨hLang, hControl⟩, hName⟩, hSource⟩,
                hValue⟩
              subst lang
              subst control
              subst source
              exact .pythonModuleAssign (identifierTextCheck_sound hName)
                (validateExprText_sound .python valueSource value hValue)
      | _ => simp [validateStmtText] at h
  | letLocal name mutable value =>
      simp only [validateStmtText, Bool.and_eq_true] at h
      rcases h with ⟨⟨⟨hLang, hControl⟩, hMutable⟩, hRest⟩
      have hLangEq : lang = .ts := by simpa using hLang
      have hControlEq : control = .module := by simpa using hControl
      have hMutableEq : mutable = false := by simpa using hMutable
      subst lang
      subst control
      subst mutable
      cases ht : tsModuleType name with
        | none => simp [ht] at hRest
        | some typeSource =>
            simp only [ht] at hRest
            cases hv : tsModuleValueText source name typeSource with
            | none => simp [hv] at hRest
            | some valueSource =>
                simp only [hv, Bool.and_eq_true, beq_iff_eq] at hRest
                rcases hRest with ⟨hSource, hValue⟩
                subst source
                exact .tsModuleConst ht
                  (validateExprText_sound .ts valueSource value hValue)
  | importModule moduleName alias =>
      simp only [validateStmtText, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨⟨hLang, hControl⟩, hModule⟩, hAlias⟩, hSource⟩
      subst lang
      subst control
      subst alias
      subst source
      exact .pythonImport (identifierTextCheck_sound hModule)
  | fromImport moduleName name alias =>
      cases lang with
      | ts =>
          simp only [validateStmtText, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with ⟨⟨⟨hControl, hName⟩, hAlias⟩, hSource⟩
          subst control
          subst source
          exact .tsNamedImport (identifierTextCheck_sound hName)
            (identifierTextCheck_sound hAlias)
      | python =>
          simp only [validateStmtText, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with ⟨⟨⟨⟨hControl, hModule⟩, hName⟩, hAlias⟩, hSource⟩
          subst control
          subst alias
          subst source
          exact .pythonFromImport (identifierTextCheck_sound hModule)
            (identifierTextCheck_sound hName)
  | nonlocalNames names =>
      cases names with
      | nil => simp [validateStmtText] at h
      | cons name rest =>
          cases rest with
          | nil =>
              simp only [validateStmtText, Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨⟨hLang, hControl⟩, hName⟩, hSource⟩
              subst lang
              subst control
              subst source
              exact .nonlocal (identifierTextCheck_sound hName)
          | cons other tail => simp [validateStmtText] at h
  | breakTarget target =>
      cases lang <;> cases control <;> simp [validateStmtText] at h
      all_goals
        rcases h with ⟨rfl, rfl⟩
        first | exact .loopBreakTS | exact .switchBreak | exact .loopBreakPython
  | returnValue value =>
      cases lang <;> cases control <;> simp [validateStmtText] at h
      case ts.function =>
        cases hp : afterSourcePrefix source "return " with
        | none => simp [hp] at h
        | some withClose =>
            cases hs : stripFinalSemicolon withClose with
            | none => simp [hp, hs] at h
            | some valueText =>
                simp only [hp, hs, Bool.and_eq_true, beq_iff_eq] at h
                rcases h with ⟨hSource, hValue⟩
                subst source
                exact .tsReturn (validateFunctionExpr_sound hValue)
      case python.function =>
        cases hp : afterSourcePrefix source "return " with
        | none => simp [hp] at h
        | some valueText =>
            simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨hSource, hValue⟩
            subst source
            exact .pythonReturn (validateFunctionExpr_sound hValue)
  | throwValue value =>
      cases lang <;> cases control <;> simp [validateStmtText] at h
      case ts.function =>
        cases hp : afterSourcePrefix source "throw " with
        | none => simp [hp] at h
        | some withClose =>
            cases hs : stripFinalSemicolon withClose with
            | none => simp [hp, hs] at h
            | some valueText =>
                simp only [hp, hs, Bool.and_eq_true, beq_iff_eq] at h
                rcases h with ⟨hSource, hValue⟩
                subst source
                exact .tsThrow (validateFunctionExpr_sound hValue)
      case python.function =>
        cases hp : afterSourcePrefix source "raise " with
        | none => simp [hp] at h
        | some valueText =>
            simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨hSource, hValue⟩
            subst source
            exact .pythonRaise (validateFunctionExpr_sound hValue)
  | _ => simp [validateStmtText] at h

theorem validateStmtSpan_sound {lang control source span stmt}
    (h : validateStmtSpan lang control source span stmt = true) :
    StmtDerives lang control source span stmt := by
  simp [validateStmtSpan] at h
  exact .ofSyntax h.1
    (validateStmtText_sound lang control (span.text source) stmt h.2)

def validateTypeNames : List String → Bool
  | [] => false
  | [name] => identifierTextCheck name
  | name :: rest => identifierTextCheck name && validateTypeNames rest

theorem validateTypeNames_sound {names}
    (h : validateTypeNames names = true) : TypeNames names := by
  induction names with
  | nil => simp [validateTypeNames] at h
  | cons name rest ih =>
      cases rest with
      | nil =>
          exact .one (identifierTextCheck_sound h)
      | cons second tail =>
          simp only [validateTypeNames, Bool.and_eq_true] at h
          exact .more (identifierTextCheck_sound h.1) (ih h.2)

/-- Type-only import candidate data is checked against its owned source span;
    it cannot silently replace the runtime `node:util` value import. -/
def validateErasedTypeImport (lang : TargetLang) (source : String)
    (span : SourceSpan) (names : List String) (moduleName : String) : Bool :=
  span.start ≤ span.stop && span.stop ≤ source.length &&
    lang == .ts && validateTypeNames names &&
    validateStringLiteral .ts ("\"" ++ moduleName ++ "\"") moduleName &&
    span.text source ==
      "import type { " ++ renderTypeNames names ++
        " } from \"" ++ moduleName ++ "\";"

theorem validateErasedTypeImport_sound {lang source span names moduleName}
    (h : validateErasedTypeImport lang source span names moduleName = true) :
    ErasedDerives lang source span := by
  simp only [validateErasedTypeImport, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hStart, hStop⟩, hLang⟩, hNames⟩, hModule⟩, hSource⟩
  subst lang
  have hSyntax : ErasedSyntax .ts (span.text source) := by
    simpa only [hSource] using
      (ErasedSyntax.tsImportType (validateTypeNames_sound hNames)
        (validateStringLiteral_sound hModule))
  exact .ofSyntax ⟨(by simpa using hStart), (by simpa using hStop)⟩ hSyntax

/-- The K-02 WorldData alias is runtime-erased and has no TargetStmt field.
    Its exact admitted type text is a grammar terminal for this pinned subset;
    this rule is not used for any function, helper, or executable declaration. -/
def validateErasedWorldDataAlias (lang : TargetLang) (source : String)
    (span : SourceSpan) : Bool :=
  span.start ≤ span.stop && span.stop ≤ source.length &&
    lang == .ts && span.text source == emittedWorldDataTypeAlias

theorem validateErasedWorldDataAlias_sound {lang source span}
    (h : validateErasedWorldDataAlias lang source span = true) :
    ErasedDerives lang source span := by
  simp only [validateErasedWorldDataAlias, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨hStart, hStop⟩, hLang⟩, hSource⟩
  subst lang
  have hSyntax : ErasedSyntax .ts (span.text source) := by
    simpa only [hSource] using ErasedSyntax.tsWorldDataAlias
  exact .ofSyntax ⟨(by simpa using hStart), (by simpa using hStop)⟩ hSyntax

/-- The two currently certified boolean helpers use different source-level
    headers. Their bodies remain recursive statement derivations. -/
def validateFunctionText (lang : TargetLang) (source bodySource : String)
    (function : TargetFunction) : Bool :=
  match function.params with
  | [⟨param, none⟩] =>
      identifierTextCheck function.qualifiedName &&
      identifierTextCheck param &&
      validateStmtText lang .function bodySource function.body &&
      (match lang with
       | .ts =>
           source == "function " ++ function.qualifiedName ++ "(" ++ param ++
             ": unknown): boolean {\n  " ++ bodySource ++ "\n}"
       | .python =>
           source == "def " ++ function.qualifiedName ++ "(" ++ param ++
             ": Any) -> bool:\n    " ++ bodySource)
  | _ => false

theorem validateFunctionText_sound {lang source bodySource function}
    (h : validateFunctionText lang source bodySource function = true) :
    FunctionSyntax lang source function ∧
      StmtSyntax lang .function bodySource function.body := by
  cases function with
  | mk name params body =>
      cases params with
      | nil => simp [validateFunctionText] at h
      | cons first rest =>
          cases rest with
          | cons second tail => simp [validateFunctionText] at h
          | nil =>
              cases first with
              | mk param defaultValue =>
                  cases defaultValue with
                  | some value => simp [validateFunctionText] at h
                  | none =>
                      cases lang with
                      | ts =>
                          simp only [validateFunctionText,
                            Bool.and_eq_true, beq_iff_eq] at h
                          rcases h with ⟨⟨⟨hName, hParam⟩, hBody⟩, hSource⟩
                          subst source
                          have hStmt := validateStmtText_sound .ts .function
                            bodySource body hBody
                          exact ⟨.tsUnknownToBool
                            (identifierTextCheck_sound hName)
                            (identifierTextCheck_sound hParam) hStmt, hStmt⟩
                      | python =>
                          simp only [validateFunctionText,
                            Bool.and_eq_true, beq_iff_eq] at h
                          rcases h with ⟨⟨⟨hName, hParam⟩, hBody⟩, hSource⟩
                          subst source
                          have hStmt := validateStmtText_sound .python .function
                            bodySource body hBody
                          exact ⟨.pythonAnyToBool
                            (identifierTextCheck_sound hName)
                            (identifierTextCheck_sound hParam) hStmt, hStmt⟩

def validateFunctionItem (lang : TargetLang) (source : String)
    (span bodySpan : SourceSpan) (function : TargetFunction) : Bool :=
  span.start ≤ span.stop && span.stop ≤ source.length &&
  bodySpan.start ≤ bodySpan.stop && bodySpan.stop ≤ source.length &&
  span.start ≤ bodySpan.start && bodySpan.stop ≤ span.stop &&
  validateFunctionText lang (span.text source) (bodySpan.text source) function

theorem validateFunctionItem_sound {lang source span bodySpan function}
    (h : validateFunctionItem lang source span bodySpan function = true) :
    ItemDerives lang source (.functionDecl span bodySpan function) := by
  simp only [validateFunctionItem, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hStart, hStop⟩, hBodyStart⟩,
    hBodyStop⟩, hWithinStart⟩, hWithinStop⟩, hText⟩
  obtain ⟨hFunction, hBody⟩ := validateFunctionText_sound hText
  exact .functionDecl
    (.ofSyntax ⟨(by simpa using hStart), (by simpa using hStop)⟩
      hFunction)
    (.ofSyntax ⟨(by simpa using hBodyStart), (by simpa using hBodyStop)⟩
      hBody)
    ⟨(by simpa using hWithinStart), (by simpa using hWithinStop)⟩

def validateSourceItem (lang : TargetLang) (source : String) :
    SourceItem → Bool
  | .runtime control span stmt =>
      validateStmtSpan lang control source span stmt
  | .functionDecl span bodySpan function =>
      validateFunctionItem lang source span bodySpan function
  | .tsTypeImport span names moduleName =>
      validateErasedTypeImport lang source span names moduleName
  | .tsWorldDataType span =>
      validateErasedWorldDataAlias lang source span

theorem validateSourceItem_sound {lang source item}
    (h : validateSourceItem lang source item = true) :
    ItemDerives lang source item := by
  cases item with
  | runtime control span stmt =>
      exact .runtime (validateStmtSpan_sound h)
  | functionDecl span bodySpan function =>
      exact validateFunctionItem_sound h
  | tsTypeImport span names moduleName =>
      simp only [validateSourceItem, validateErasedTypeImport,
        Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨⟨⟨hStart, hStop⟩, hLang⟩, hNames⟩, hModule⟩, hText⟩
      subst lang
      have hErased : ErasedDerives .ts source span :=
        validateErasedTypeImport_sound (by
          simp only [validateErasedTypeImport, Bool.and_eq_true,
            beq_iff_eq]
          exact ⟨⟨⟨⟨⟨hStart, hStop⟩, trivial⟩, hNames⟩, hModule⟩, hText⟩)
      exact .tsTypeImport (validateTypeNames_sound hNames)
        (validateStringLiteral_sound hModule) hText hErased
  | tsWorldDataType span =>
      have hLang : lang = .ts := by
        simp only [validateSourceItem, validateErasedWorldDataAlias,
          Bool.and_eq_true, beq_iff_eq] at h
        exact h.1.2
      subst lang
      exact .tsWorldDataType (validateErasedWorldDataAlias_sound h)

def validateSourceItems (lang : TargetLang) (source : String) :
    List SourceItem → Bool
  | [] => true
  | item :: rest =>
      validateSourceItem lang source item && validateSourceItems lang source rest

theorem validateSourceItems_sound {lang source items}
    (h : validateSourceItems lang source items = true) :
    ItemsDerive lang source items := by
  induction items with
  | nil => exact .nil lang source
  | cons item rest ih =>
      simp only [validateSourceItems, Bool.and_eq_true] at h
      exact .cons (validateSourceItem_sound h.1) (ih h.2)

def validateOrderedItems : List SourceItem → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      first.span.stop ≤ second.span.start &&
        validateOrderedItems (second :: rest)

theorem validateOrderedItems_sound {items}
    (h : validateOrderedItems items = true) : OrderedItems items := by
  induction items with
  | nil => exact .nil
  | cons first rest ih =>
      cases rest with
      | nil => exact .single first
      | cons second tail =>
          simp only [validateOrderedItems, Bool.and_eq_true] at h
          exact .cons (by simpa using h.1) (ih h.2)

private theorem allCheck_sound {α : Type} {items : List α} {check : α → Bool}
    (h : items.all check = true) :
    ∀ item, item ∈ items → check item = true := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      intro item hMember
      simp only [List.mem_cons] at hMember
      rcases hMember with rfl | hTail
      · exact h.1
      · exact ih h.2 item hTail

private theorem anyCheck_witness {α : Type} {items : List α} {check : α → Bool}
    (h : items.any check = true) :
    ∃ item, item ∈ items ∧ check item = true := by
  induction items with
  | nil => simp at h
  | cons first rest ih =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      rcases h with hFirst | hRest
      · exact ⟨first, by simp, hFirst⟩
      · obtain ⟨item, hMember, hCheck⟩ := ih hRest
        exact ⟨item, by simp [hMember], hCheck⟩

def tokenWithinItemCheck (token : SourceToken) (item : SourceItem) : Bool :=
  item.span.start ≤ token.start && token.stop ≤ item.span.stop

def validateNontriviaOwned (tokens : List SourceToken)
    (items : List SourceItem) (prefixStop : Nat) : Bool :=
  tokens.all (fun token =>
    token.stop > prefixStop || token.kind == .spacing ||
    token.kind == .comment ||
    items.any (tokenWithinItemCheck token))

theorem validateNontriviaOwned_sound {tokens items prefixStop}
    (h : validateNontriviaOwned tokens items prefixStop = true) :
    NontriviaOwned tokens items prefixStop := by
  intro token hMember hStop hSpace hComment
  have hToken := allCheck_sound h token hMember
  simp only [validateNontriviaOwned, Bool.or_eq_true] at hToken
  have hNotBeyond : (token.stop > prefixStop) = false := by
    simpa using Nat.not_lt.mpr hStop
  have hNotSpace : (token.kind == TokenKind.spacing) = false := by
    simpa using hSpace
  have hNotComment : (token.kind == TokenKind.comment) = false := by
    simpa using hComment
  have hOwned : items.any (tokenWithinItemCheck token) = true := by
    simpa [hNotBeyond, hNotSpace, hNotComment] using hToken
  obtain ⟨item, hIn, hWithin⟩ := anyCheck_witness hOwned
  simp only [tokenWithinItemCheck, Bool.and_eq_true] at hWithin
  exact ⟨item, hIn, (by simpa using hWithin.1), (by simpa using hWithin.2)⟩

end Harmonia.Applications.Kadmos.Generated
