import Harmonia.Applications.Kadmos.Generated.SourceLexical

set_option maxHeartbeats 1000000

namespace Harmonia.Applications.Kadmos.Generated

def identifierTextCheck (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first == '_' || first == '$') &&
        rest.all (fun c => c.isAlphanum || c == '_' || c == '$')

def expressionIdentifierCheck (lang : TargetLang) (name : String) : Bool :=
  identifierTextCheck name && !(expressionReserved lang).contains name

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

theorem expressionIdentifierCheck_sound {lang name}
    (h : expressionIdentifierCheck lang name = true) :
    ExpressionIdentifier lang name := by
  simp only [expressionIdentifierCheck, Bool.and_eq_true, Bool.not_eq_true] at h
  exact ⟨identifierTextCheck_sound h.1, by
    simpa [List.contains_eq_mem] using h.2⟩

def propertyIdentifierCheck (lang : TargetLang) (name : String) : Bool :=
  match lang with
  | .ts =>
      if name.startsWith "#" then
        let plain := String.mk (name.toList.drop 1)
        name == "#" ++ plain && identifierTextCheck plain
      else identifierTextCheck name
  | .python => expressionIdentifierCheck .python name

theorem propertyIdentifierCheck_sound {lang name}
    (h : propertyIdentifierCheck lang name = true) :
    PropertyIdentifier lang name := by
  cases lang with
  | ts =>
      simp only [propertyIdentifierCheck] at h
      split at h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact h.1 ▸ .tsPrivate (identifierTextCheck_sound h.2)
      · exact .tsPlain (identifierTextCheck_sound h)
  | python =>
      exact .python (expressionIdentifierCheck_sound h)

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

def validatePrefixLineList (offset : Nat) : List LocatedSourceLine → Bool
  | [] => true
  | first :: rest =>
      first.start == offset && first.stop == offset + first.raw.length &&
      first.terminated && !first.raw.toList.contains '\n' &&
      validatePrefixLineList (offset + first.raw.length + 1) rest

def validatePrefixLinesAt (source : String) (offset : Nat)
    (lines : List LocatedSourceLine) : Bool :=
  source == prefixLinesSource lines && validatePrefixLineList offset lines

theorem validatePrefixLineList_sound {offset lines}
    (h : validatePrefixLineList offset lines = true) :
    PrefixLinesAt (prefixLinesSource lines) offset lines := by
  induction lines generalizing offset with
  | nil => exact .empty offset
  | cons first rest ih =>
      simp only [validatePrefixLineList, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true] at h
      rcases h with ⟨⟨⟨⟨hStart, hStop⟩, hTerm⟩, hNoNewline⟩, hRest⟩
      cases first with
      | mk start stop raw terminated =>
          dsimp at hStart hStop hTerm
          subst start
          subst stop
          subst terminated
          have hNo : raw.toList.contains '\n' = false := by
            simpa using hNoNewline
          simpa [prefixLinesSource] using
            (PrefixLinesAt.next (head := raw)
              (rest := prefixLinesSource rest) (offset := offset)
              hNo (ih hRest))

theorem validatePrefixLinesAt_sound {source offset lines}
    (h : validatePrefixLinesAt source offset lines = true) :
    PrefixLinesAt source offset lines := by
  simp only [validatePrefixLinesAt, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1]
  exact validatePrefixLineList_sound h.2

def validateChunkedLines (remaining : String) (offset : Nat) :
    List LocatedLineChunk → Bool
  | [] => remaining == ""
  | chunk :: rest =>
      String.mk (remaining.toList.take chunk.text.length) == chunk.text &&
      validatePrefixLinesAt chunk.text offset chunk.lines &&
      validateChunkedLines
        (String.mk (remaining.toList.drop chunk.text.length))
        (offset + chunk.text.length) rest

theorem validateChunkedLines_sound {remaining offset chunks}
    (h : validateChunkedLines remaining offset chunks = true) :
    ChunkedLines remaining offset chunks := by
  induction chunks generalizing remaining offset with
  | nil =>
      simp [validateChunkedLines] at h
      subst remaining
      exact .empty offset
  | cons chunk rest ih =>
      simp only [validateChunkedLines, Bool.and_eq_true,
        beq_iff_eq] at h
      rcases h with ⟨⟨hPrefix, hChunk⟩, hRest⟩
      have hSource : remaining = chunk.text ++
          String.mk (remaining.toList.drop chunk.text.length) := by
        calc
          remaining = String.mk (remaining.toList.take chunk.text.length) ++
              String.mk (remaining.toList.drop chunk.text.length) :=
            SourceSpan.prefix_drop remaining chunk.text.length
          _ = chunk.text ++
              String.mk (remaining.toList.drop chunk.text.length) := by
            rw [hPrefix]
      cases chunk with
      | mk text lines =>
          dsimp at hPrefix hChunk hRest hSource
          have hDerived : ChunkedLines
              (text ++ String.mk (remaining.toList.drop text.length)) offset
              (⟨text, lines⟩ :: rest) :=
            .cons (validatePrefixLinesAt_sound hChunk) (ih hRest)
          exact Eq.mp
            (congrArg (fun value =>
              ChunkedLines value offset (⟨text, lines⟩ :: rest)) hSource.symm)
            hDerived

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

def shiftSourceLines (offset : Nat) (lines : List LocatedSourceLine) :
    List LocatedSourceLine :=
  lines.map (fun line =>
    { line with start := offset + line.start, stop := offset + line.stop })

end Harmonia.Applications.Kadmos.Generated
