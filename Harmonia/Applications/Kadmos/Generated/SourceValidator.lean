import Harmonia.Applications.Kadmos.Generated.SourceGrammar

set_option maxHeartbeats 1000000

namespace Harmonia.Applications.Kadmos.Generated

private def splitProperty (source : String) : Option (String × String) :=
  match source.splitSourceOn "." with
  | [base, name] => some (base, name)
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

def identifierTextCheck (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first == '_' || first == '$') &&
        rest.all (fun c => c.isAlphanum || c == '_' || c == '$')

theorem identifierTextCheck_sound {name : String}
    (h : identifierTextCheck name = true) : IdentifierText name := by
  unfold identifierTextCheck at h
  cases hs : name.toList with
  | nil =>
      have hdata : name.data = [] := by simpa [String.toList] using hs
      simp [hdata] at h
  | cons first rest =>
      simp only [hs, Bool.and_eq_true] at h
      exact ⟨first, rest, hs, h.1, h.2⟩

def decodeSurfaceChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: escaped :: rest => do
      let decoded ← surfaceEscape escaped
      return decoded :: (← decodeSurfaceChars rest)
  | '\\' :: [] => none
  | c :: rest => do
      return c :: (← decodeSurfaceChars rest)

theorem decodeSurfaceChars_sound {source decoded}
    (h : decodeSurfaceChars source = some decoded) :
    DecodesChars source decoded := by
  match source with
  | [] =>
      simp [decodeSurfaceChars] at h
      subst decoded
      exact .empty
  | c :: rest =>
      by_cases hc : c = '\\'
      · subst c
        cases rest with
        | nil => simp [decodeSurfaceChars] at h
        | cons escaped tail =>
            cases he : surfaceEscape escaped with
            | none => simp [decodeSurfaceChars, he] at h
            | some decodedChar =>
                cases hr : decodeSurfaceChars tail with
                | none => simp [decodeSurfaceChars, he, hr] at h
                | some decodedRest =>
                    simp [decodeSurfaceChars, he, hr] at h
                    subst decoded
                    exact .escape he (decodeSurfaceChars_sound hr)
      · cases hr : decodeSurfaceChars rest with
        | none => simp [decodeSurfaceChars, hc, hr] at h
        | some decodedRest =>
            simp [decodeSurfaceChars, hc, hr] at h
            subst decoded
            exact .plain (by simpa using hc) (decodeSurfaceChars_sound hr)
termination_by source.length

private def quoteParts (source : String) : Option (Char × String) :=
  match source.toList with
  | quote :: tail =>
      match tail.reverse with
      | last :: revInside =>
          if last == quote then some (quote, String.mk revInside.reverse)
          else none
      | [] => none
  | [] => none

private def quoteAllowed (quote : Char) : Bool :=
  quote == '"' || quote == '\''

private def quotedStringCheck (source value : String) : Bool :=
  match quoteParts source with
  | none => false
  | some (quote, inside) =>
      quoteAllowed quote &&
      source == String.singleton quote ++ inside ++ String.singleton quote &&
      quotedTail quote (inside.toList ++ [quote]) &&
      decodeSurfaceChars inside.toList == some value.toList

private def rawStringCheck (source value : String) : Bool :=
  match quoteParts (source.drop 1) with
  | none => false
  | some (quote, inside) =>
      quoteAllowed quote &&
      source == "r" ++ String.singleton quote ++ inside ++ String.singleton quote &&
      quotedTail quote (inside.toList ++ [quote]) &&
      value == inside

def validateStringLiteral (lang : TargetLang) (source value : String) : Bool :=
  match lang with
  | .ts => quotedStringCheck source value
  | .python =>
      if source.startsWith "r\"" || source.startsWith "r'" then
        rawStringCheck source value
      else quotedStringCheck source value

private theorem quotedStringCheck_sound {source value}
    (h : quotedStringCheck source value = true) :
    StringLiteralSyntax lang source value := by
  unfold quotedStringCheck at h
  cases hp : quoteParts source with
  | none => simp [hp] at h
  | some parts =>
      rcases parts with ⟨quote, inside⟩
      simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨hQuote, hSource⟩, hClose⟩, hDecoded⟩
      exact .quoted hSource hQuote hClose (decodeSurfaceChars_sound hDecoded)

private theorem rawStringCheck_sound {source value}
    (h : rawStringCheck source value = true) :
    StringLiteralSyntax .python source value := by
  unfold rawStringCheck at h
  cases hp : quoteParts (source.drop 1) with
  | none => simp [hp] at h
  | some parts =>
      rcases parts with ⟨quote, inside⟩
      simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨hQuote, hSource⟩, hClose⟩, hValue⟩
      subst value
      exact .rawPython hSource hQuote hClose

theorem validateStringLiteral_sound {lang source value}
    (h : validateStringLiteral lang source value = true) :
    StringLiteralSyntax lang source value := by
  cases lang with
  | ts => exact quotedStringCheck_sound h
  | python =>
      simp only [validateStringLiteral] at h
      split at h
      · exact rawStringCheck_sound h
      · exact quotedStringCheck_sound h

def tokenFormCheck (lang : TargetLang) (token : SourceToken) : Bool :=
  match token.kind with
  | .spacing => token.text.toList.all Char.isWhitespace && !token.text.isEmpty
  | .identifier => identifierTextCheck token.text
  | .numeral =>
      numberTokenCheck token.text
  | .quoted =>
      match token.text.toList with
      | quote :: tail =>
          (quote == '"' || quote == '\'' || quote == '`') && quotedTail quote tail
      | [] => false
  | .regex => lang == .ts && regexTokenCheck token.text
  | .comment =>
      ((lang == .python && token.text.startsWith "#") ||
       (lang == .ts && token.text.startsWith "//")) &&
      !token.text.toList.contains '\n'
  | .punctuation => punctuationCharCheck token.text

theorem tokenFormCheck_sound {lang token}
    (h : tokenFormCheck lang token = true) : SurfaceTokenForm lang token := by
  unfold tokenFormCheck at h
  cases hk : token.kind with
  | spacing =>
      simp only [hk, Bool.and_eq_true, Bool.not_eq_true] at h
      exact .spacing hk h.1 (by simpa using h.2)
  | identifier =>
      simp only [hk] at h
      exact .identifier hk (identifierTextCheck_sound h)
  | numeral =>
      simp only [hk] at h
      exact .numeral hk h
  | quoted =>
      simp only [hk] at h
      cases ht : token.text.toList with
      | nil =>
          have hdata : token.text.data = [] := by simpa [String.toList] using ht
          simp [hdata] at h
      | cons quote tail =>
          simp only [ht, Bool.and_eq_true] at h
          exact .quoted hk ht h.1 h.2
  | regex =>
      simp only [hk, Bool.and_eq_true, beq_iff_eq] at h
      cases h.1
      exact .regex hk h.2
  | comment =>
      simp only [hk, Bool.and_eq_true, Bool.not_eq_true] at h
      exact .comment hk h.1 h.2
  | punctuation =>
      simp only [hk] at h
      exact .punctuation hk h

/-- Independently checks absolute offsets and complete character ownership
    for a candidate token stream. It does not call `tokenizeSource`. -/
def validateLexesAt (lang : TargetLang) (remaining : String) (offset : Nat) :
    List SourceToken → Bool
  | [] => remaining == ""
  | first :: tail =>
      first.start == offset &&
      first.stop == offset + first.text.length &&
      !first.text.isEmpty &&
      tokenFormCheck lang first &&
      String.mk (remaining.toList.take first.text.length) == first.text &&
      tokenBoundaryCheck first
        (String.mk (remaining.toList.drop first.text.length)) &&
      validateLexesAt lang
        (String.mk (remaining.toList.drop first.text.length)) first.stop tail

theorem validateLexesAt_sound {lang remaining offset tokens}
    (h : validateLexesAt lang remaining offset tokens = true) :
    LexesAt lang remaining offset tokens := by
  induction tokens generalizing remaining offset with
  | nil =>
      simp [validateLexesAt] at h
      subst remaining
      exact .empty lang offset
  | cons first tail ih =>
      simp only [validateLexesAt, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨⟨⟨⟨hStart, hStop⟩, hNonempty⟩, hForm⟩, hPrefix⟩,
        hBoundary⟩, hRest⟩
      exact .token hStart hStop (by simpa using hNonempty)
        (tokenFormCheck_sound hForm) hPrefix hBoundary (ih hRest)

/-- A second independent check rejects an otherwise well-spanned token trace
    when it selects punctuation in a comment/regex position or vice versa. -/
def validatePriorityAt (lang : TargetLang) (prior : Option SourceToken)
    (remaining : String) : List SourceToken → Bool
  | [] => remaining == ""
  | first :: tail =>
      tokenPriorityCheck lang prior remaining first &&
      validatePriorityAt lang
        (if first.kind == .spacing then prior else some first)
        (String.mk (remaining.toList.drop first.text.length)) tail

theorem validatePriorityAt_sound {lang prior remaining tokens}
    (h : validatePriorityAt lang prior remaining tokens = true) :
    PriorityAt lang prior remaining tokens := by
  induction tokens generalizing prior remaining with
  | nil =>
      simp [validatePriorityAt] at h
      subst remaining
      exact .empty lang prior
  | cons first tail ih =>
      simp only [validatePriorityAt, Bool.and_eq_true] at h
      exact .token h.1 (ih h.2)

def validateCanonicalAt (lang : TargetLang) (prior : Option SourceToken)
    (remaining : String) (offset : Nat) : List SourceToken → Bool
  | [] => remaining == ""
  | first :: tail =>
      canonicalLexicalHead lang prior remaining offset == some first &&
      validateCanonicalAt lang
        (if first.kind == .spacing then prior else some first)
        (String.mk (remaining.toList.drop first.text.length)) first.stop tail

theorem validateCanonicalAt_sound {lang prior remaining offset tokens}
    (h : validateCanonicalAt lang prior remaining offset tokens = true) :
    CanonicalAt lang prior remaining offset tokens := by
  induction tokens generalizing prior remaining offset with
  | nil =>
      simp [validateCanonicalAt] at h
      subst remaining
      exact .empty lang prior offset
  | cons first tail ih =>
      simp only [validateCanonicalAt, Bool.and_eq_true] at h
      have hHead : canonicalLexicalHead lang prior remaining offset = some first := by
        simpa only [beq_iff_eq] using h.1
      exact .token hHead (ih h.2)

def validateLexes (lang : TargetLang) (source : String)
    (tokens : List SourceToken) : Bool :=
  validateLexesAt lang source 0 tokens &&
    validatePriorityAt lang none source tokens &&
    validateCanonicalAt lang none source 0 tokens

theorem validateLexes_sound {lang source tokens}
    (h : validateLexes lang source tokens = true) : Lexes lang source tokens := by
  simp only [validateLexes, Bool.and_eq_true] at h
  exact .ofTrace (validateLexesAt_sound h.1.1)
    (validatePriorityAt_sound h.1.2)
    (validateCanonicalAt_sound h.2)

def locatedLinesSource : List LocatedSourceLine → String
  | [] => ""
  | [last] => last.raw
  | first :: rest => first.raw ++ "\n" ++ locatedLinesSource rest

def validateLineList (offset : Nat) : List LocatedSourceLine → Bool
  | [] => false
  | [last] =>
      last.start == offset && last.stop == offset + last.raw.length &&
      !last.terminated && !last.raw.toList.contains '\n'
  | first :: rest =>
      first.start == offset && first.stop == offset + first.raw.length &&
      first.terminated && !first.raw.toList.contains '\n' &&
      validateLineList (offset + first.raw.length + 1) rest

def validateLinesAt (source : String) (offset : Nat)
    (lines : List LocatedSourceLine) : Bool :=
  source == locatedLinesSource lines && validateLineList offset lines

theorem validateLineList_sound {offset lines}
    (h : validateLineList offset lines = true) :
    LinesAt (locatedLinesSource lines) offset lines := by
  induction lines generalizing offset with
  | nil => simp [validateLineList] at h
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [validateLineList, Bool.and_eq_true, beq_iff_eq,
            Bool.not_eq_true] at h
          cases first with
          | mk start stop raw terminated =>
              rcases h with ⟨⟨⟨hStart, hStop⟩, hTerm⟩, hNoNewline⟩
              have hTermFalse : terminated = false := by simpa using hTerm
              have hNo : raw.toList.contains '\n' = false := by simpa using hNoNewline
              dsimp at hStart hStop
              subst start
              subst stop
              subst terminated
              simpa [locatedLinesSource] using
                (LinesAt.final (source := raw) (offset := offset) hNo)
      | cons second tail =>
          simp only [validateLineList, Bool.and_eq_true, beq_iff_eq,
            Bool.not_eq_true] at h
          cases first with
          | mk start stop raw terminated =>
              rcases h with ⟨⟨⟨⟨hStart, hStop⟩, hTerm⟩, hNoNewline⟩, hRest⟩
              have hNo : raw.toList.contains '\n' = false := by simpa using hNoNewline
              dsimp at hStart hStop hTerm
              subst start
              subst stop
              subst terminated
              simpa [locatedLinesSource] using
                (LinesAt.next (head := raw)
                  (rest := locatedLinesSource (second :: tail))
                  (offset := offset) hNo (ih hRest))

theorem validateLinesAt_sound {source offset lines}
    (h : validateLinesAt source offset lines = true) :
    LinesAt source offset lines := by
  simp only [validateLinesAt, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1]
  exact validateLineList_sound h.2

private def locateLineParts (offset : Nat) : List String → List LocatedSourceLine
  | [] => []
  | [last] => [⟨offset, offset + last.length, last, false⟩]
  | first :: rest =>
      ⟨offset, offset + first.length, first, true⟩ ::
        locateLineParts (offset + first.length + 1) rest

/-- Candidate line spans for the second validator; `validateLinesAt` checks
    them against the independent line relation before they are trusted. -/
def locateSourceLines (source : String) : List LocatedSourceLine :=
  locateLineParts 0 (source.splitSourceOn "\n")

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

private def stripFinalSemicolon (source : String) : Option String :=
  match source.toList.reverse with
  | ';' :: inside => some (String.mk inside.reverse)
  | _ => none

private def tsModuleValueText (source name typeSource : String) : Option String :=
  stripFinalSemicolon (String.mk (source.toList.drop
    ("const " ++ name ++ ": " ++ typeSource ++ " = ").length))

/-- AST-guided source check: source text, rather than the raw decoder,
    determines these operator boundaries. -/
def validateExprText (lang : TargetLang) (source : String) : TargetExpr → Bool
  | .empty => source == ""
  | .sequence value .empty => validateExprText lang source value
  | .call callee args =>
      match splitFirstFormat source "(" with
      | none => false
      | some (calleeText, afterOpen) =>
          match stripFinalParen afterOpen with
          | none => false
          | some argsText =>
              source == calleeText ++ "(" ++ argsText ++ ")" &&
              validateExprText lang calleeText callee &&
              validateExprText lang argsText args
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
  | .local name => identifierTextCheck name && source == name
  | .property receiver name =>
      match splitProperty source with
      | some (base, field) =>
          identifierTextCheck field && field == name &&
            source == base ++ "." ++ field && validateExprText lang base receiver
      | none => false
  | .binary .sub left right =>
      match splitSub source with
      | some (leftText, rightText) =>
          source == leftText ++ " - " ++ rightText &&
            validateExprText lang leftText left && validateExprText lang rightText right
      | none => false
  | .formatted parts =>
      match wrapperContent lang source with
      | none => false
      | some content =>
          source == wrapperRebuild lang content &&
            parts != .empty && validateFormatText lang content parts
  | _ => false

def validateExprSpan (lang : TargetLang) (source : String)
    (span : SourceSpan) (expr : TargetExpr) : Bool :=
  span.start ≤ span.stop && span.stop ≤ source.length &&
    validateExprText lang (span.text source) expr

theorem validateExprText_sound (lang : TargetLang) (source : String)
    (expr : TargetExpr) (h : validateExprText lang source expr = true) :
    ExprSyntax lang source expr := by
  induction expr generalizing source with
  | empty =>
      simp [validateExprText] at h
      subst source
      exact .empty lang
  | sequence value rest ihValue ihRest =>
      cases rest <;> simp [validateExprText] at h
      exact .singleArgument (ihValue source h)
  | call callee args ihCallee ihArgs =>
      simp only [validateExprText] at h
      cases hs : splitFirstFormat source "(" with
      | none => simp [hs] at h
      | some parts =>
          rcases parts with ⟨calleeText, afterOpen⟩
          cases hp : stripFinalParen afterOpen with
          | none => simp [hs, hp] at h
          | some argsText =>
              simp only [hs, hp, Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨hSource, hCallee⟩, hArgs⟩
              subst source
              exact .call (ihCallee calleeText hCallee) (ihArgs argsText hArgs)
  | bool value =>
      cases lang <;> simp [validateExprText] at h
      · subst source; exact .tsBool value
      · subst source; exact .pythonBool value
  | null =>
      cases lang <;> simp [validateExprText] at h
      · subst source; exact .tsNull
      · subst source; exact .pythonNone
  | undefined =>
      simp [validateExprText] at h
      rcases h with ⟨rfl, rfl⟩
      exact .tsUndefined
  | integer n =>
      simp only [validateExprText] at h
      cases hv : source.toNat? with
      | none => simp [hv] at h
      | some value =>
          simp only [hv, beq_iff_eq] at h
          subst n
          exact .numeral hv
  | decimal literal =>
      simp only [validateExprText, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨hSource, hNumber⟩, hDot⟩
      subst literal
      exact .decimal hNumber hDot
  | string value =>
      simp only [validateExprText] at h
      exact .string (validateStringLiteral_sound h)
  | «local» name =>
      simp [validateExprText] at h
      rcases h with ⟨hne, heq⟩
      subst source
      exact ExprSyntax.local (identifierTextCheck_sound hne)
  | property receiver name ih =>
      simp only [validateExprText] at h
      cases hs : splitProperty source with
      | none => simp [hs] at h
      | some parts =>
          rcases parts with ⟨base, field⟩
          simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with ⟨⟨⟨hne, heq⟩, hconcat⟩, hrec⟩
          subst source
          subst field
          exact .property (ih base hrec) (identifierTextCheck_sound hne)
  | binary op left right ihLeft ihRight =>
      cases op <;> simp [validateExprText] at h
      case sub =>
        cases hs : splitSub source with
        | none => simp [hs] at h
        | some parts =>
            rcases parts with ⟨leftText, rightText⟩
            simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨⟨hconcat, hleft⟩, hright⟩
            subst source
            exact .sub (ihLeft leftText hleft) (ihRight rightText hright)
  | formatted parts ih =>
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
  | _ => simp [validateExprText] at h

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

def validateStmtText (lang : TargetLang) (control : SurfaceControl)
    (source : String) : TargetStmt → Bool
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
  cases stmt with
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

def validateSourceItem (lang : TargetLang) (source : String) :
    SourceItem → Bool
  | .runtime control span stmt =>
      validateStmtSpan lang control source span stmt
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
