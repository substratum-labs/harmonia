import Harmonia.Applications.Kadmos.Generated.TargetSyntax

namespace Harmonia.Applications.Kadmos.Generated

/-- Half-open character interval in an emitted source file. -/
structure SourceSpan where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

def SourceSpan.text (source : String) (span : SourceSpan) : String :=
  String.mk ((source.toList.drop span.start).take (span.stop - span.start))

theorem SourceSpan.prefix_then_slice (source : String) (middle stop : Nat)
    (hOrder : middle ≤ stop) :
    (SourceSpan.text source ⟨0, middle⟩) ++
      (SourceSpan.text source ⟨middle, stop⟩) =
      SourceSpan.text source ⟨0, stop⟩ := by
  unfold SourceSpan.text
  have hAdd : middle + (stop - middle) = stop := Nat.add_sub_of_le hOrder
  simp only [Nat.sub_zero, List.drop_zero]
  change String.mk
      (List.take middle source.toList ++
        List.take (stop - middle) (List.drop middle source.toList)) =
    String.mk (List.take stop source.toList)
  congr 1
  calc
    List.take middle source.toList ++
        List.take (stop - middle) (List.drop middle source.toList) =
      List.take (middle + (stop - middle)) source.toList :=
        (List.take_add source.toList middle (stop - middle)).symm
    _ = List.take stop source.toList := by rw [hAdd]

theorem SourceSpan.whole (source : String) :
    SourceSpan.text source ⟨0, source.length⟩ = source := by
  cases source with
  | mk data =>
      simp [SourceSpan.text, String.length, List.take_length]

theorem SourceSpan.prefix_length (source : String) (stop : Nat)
    (hStop : stop ≤ source.length) :
    (SourceSpan.text source ⟨0, stop⟩).length = stop := by
  cases source with
  | mk data =>
      have hLength : stop ≤ data.length := by
        simpa [String.length] using hStop
      simp [SourceSpan.text, String.length, List.length_take,
        Nat.min_eq_left hLength]

def SourceSpan.suffix (source : String) (start : Nat) : String :=
  String.mk (source.toList.drop start)

theorem SourceSpan.suffix_zero (source : String) :
    SourceSpan.suffix source 0 = source := by
  cases source
  rfl

theorem SourceSpan.suffix_split (source : String) (start stop : Nat)
    (hOrder : start ≤ stop) :
    SourceSpan.suffix source start =
      SourceSpan.text source ⟨start, stop⟩ ++
        SourceSpan.suffix source stop := by
  unfold SourceSpan.suffix SourceSpan.text
  have hAdd : start + (stop - start) = stop := Nat.add_sub_of_le hOrder
  have hDrop : (source.toList.drop start).drop (stop - start) =
      source.toList.drop stop := by
    simp [List.drop_drop, hAdd]
  change String.mk (source.toList.drop start) =
    String.mk ((source.toList.drop start).take (stop - start) ++
      source.toList.drop stop)
  rw [← hDrop]
  exact congrArg String.mk
    (List.take_append_drop (stop - start) (source.toList.drop start)).symm

theorem SourceSpan.suffix_end (source : String) :
    SourceSpan.suffix source source.length = "" := by
  cases source with
  | mk data => simp [SourceSpan.suffix, String.length]

theorem SourceSpan.prefix_drop (source : String) (count : Nat) :
    source = String.mk (source.toList.take count) ++
      String.mk (source.toList.drop count) := by
  cases source with
  | mk data =>
      change String.mk data =
        String.mk (data.take count ++ data.drop count)
      exact congrArg String.mk (List.take_append_drop count data).symm

/-- Surface identifier grammar, stated without reference to the decoder. -/
def IdentifierText (name : String) : Prop :=
  ∃ first rest, name.toList = first :: rest ∧
    (first.isAlpha || first == '_' || first == '$') = true ∧
    rest.all (fun c => c.isAlphanum || c == '_' || c == '$') = true

/-- A name in expression position cannot be a language literal or keyword.
    Property keys and declaration binders use `IdentifierText` separately. -/
def expressionReserved : TargetLang → List String
  | .ts => ["true", "false", "null", "undefined", "this", "new", "typeof",
      "if", "else", "return", "throw", "switch", "case", "default",
      "while", "for", "break", "continue", "const", "let", "function",
      "class", "import", "export", "void", "delete", "instanceof", "in"]
  | .python => ["True", "False", "None", "and", "or", "not", "is", "in",
      "if", "else", "elif", "for", "while", "return", "raise", "try",
      "except", "finally", "def", "class", "lambda", "yield", "await",
      "async", "import", "from", "as", "with", "nonlocal", "global",
      "pass", "break", "continue", "del"]

def ExpressionIdentifier (lang : TargetLang) (name : String) : Prop :=
  IdentifierText name ∧ name ∉ expressionReserved lang

/-- A TS property may be private or use a keyword spelling; Python dotted
    properties use the expression-identifier category. -/
inductive PropertyIdentifier : TargetLang → String → Prop where
  | tsPlain {name : String} (hName : IdentifierText name) :
      PropertyIdentifier .ts name
  | tsPrivate {name : String} (hName : IdentifierText name) :
      PropertyIdentifier .ts ("#" ++ name)
  | python {name : String} (hName : ExpressionIdentifier .python name) :
      PropertyIdentifier .python name

/-- In the current binary subtraction fragment the rightmost surface
    delimiter owns the outer node, giving left association. Full program
    syntax will refine this to token-level top-level delimiter ownership. -/
def RightmostSubOperand (rightText : String) : Prop :=
  rightText.splitSourceOn " - " = [rightText]

def numberTokenCheck (source : String) : Bool :=
  match source.splitSourceOn "." with
  | [whole] => !whole.isEmpty && whole.toList.all Char.isDigit
  | [whole, fraction] =>
      !whole.isEmpty && !fraction.isEmpty &&
        whole.toList.all Char.isDigit && fraction.toList.all Char.isDigit
  | _ => false

def punctuationCharCheck (source : String) : Bool :=
  match source.toList with
  | [c] =>
      32 ≤ c.toNat && c.toNat ≤ 126 &&
        !(c.isAlphanum || c.isWhitespace || c == '_' || c == '$' ||
          c == '"' || c == '\'' || c == '`')
  | _ => false

def quotedTail (quote : Char) : List Char → Bool
  | [] => false
  | [last] => last == quote
  | '\\' :: _ :: rest => quotedTail quote rest
  | c :: rest => c != quote && quotedTail quote rest

/-- First unescaped slash outside a character class closes a TS regex. The
    suffix is the flag run, not another expression or comment token. -/
def regexAfterClose (inClass : Bool) : List Char → Option (List Char)
  | [] => none
  | '\\' :: _ :: rest => regexAfterClose inClass rest
  | '[' :: rest => regexAfterClose true rest
  | ']' :: rest => regexAfterClose false rest
  | '/' :: rest => if inClass then regexAfterClose inClass rest else some rest
  | _ :: rest => regexAfterClose inClass rest

def regexTokenCheck (source : String) : Bool :=
  match source.toList with
  | '/' :: body =>
      match regexAfterClose false body with
      | some flags => flags.all Char.isAlpha
      | none => false
  | _ => false

def surfaceEscape : Char → Option Char
  | '"' => some '"'
  | '\'' => some '\''
  | '\\' => some '\\'
  | '/' => some '/'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | _ => none

inductive DecodesChars : List Char → List Char → Prop where
  | empty : DecodesChars [] []
  | plain {c : Char} {source decoded : List Char}
      (hNotEscape : c != '\\')
      (hRest : DecodesChars source decoded) :
      DecodesChars (c :: source) (c :: decoded)
  | escape {e decodedChar : Char} {source decoded : List Char}
      (hDecode : surfaceEscape e = some decodedChar)
      (hRest : DecodesChars source decoded) :
      DecodesChars ('\\' :: e :: source) (decodedChar :: decoded)

inductive StringLiteralSyntax : TargetLang → String → String → Prop where
  | quoted {lang : TargetLang} {source : String} {quote : Char} {inside value : String}
      (hSource : source = String.singleton quote ++ inside ++ String.singleton quote)
      (hQuote : quote == '"' || quote == '\'')
      (hClose : quotedTail quote (inside.toList ++ [quote]) = true)
      (hDecode : DecodesChars inside.toList value.toList) :
      StringLiteralSyntax lang source value
  | rawPython {source : String} {quote : Char} {inside : String}
      (hSource : source =
        "r" ++ String.singleton quote ++ inside ++ String.singleton quote)
      (hQuote : quote == '"' || quote == '\'')
      (hClose : quotedTail quote (inside.toList ++ [quote]) = true) :
      StringLiteralSyntax .python source inside

/-- The token-kind rules make literal/trivia ownership explicit. Maximality and
    the expression-context rule for regex are checked at the trace boundary. -/
inductive SurfaceTokenForm : TargetLang → SourceToken → Prop where
  | spacing {lang : TargetLang} {token : SourceToken}
      (hKind : token.kind = .spacing)
      (hChars : token.text.toList.all Char.isWhitespace = true)
      (hNonempty : token.text.isEmpty = false) :
      SurfaceTokenForm lang token
  | identifier {lang : TargetLang} {token : SourceToken}
      (hKind : token.kind = .identifier)
      (hIdent : IdentifierText token.text) :
      SurfaceTokenForm lang token
  | numeral {lang : TargetLang} {token : SourceToken}
      (hKind : token.kind = .numeral)
      (hNumber : numberTokenCheck token.text = true) :
      SurfaceTokenForm lang token
  | quoted {lang : TargetLang} {token : SourceToken} {quote : Char} {tail : List Char}
      (hKind : token.kind = .quoted)
      (hText : token.text.toList = quote :: tail)
      (hQuote : quote == '"' || quote == '\'' || quote == '`')
      (hTail : quotedTail quote tail = true) :
      SurfaceTokenForm lang token
  | regex {token : SourceToken}
      (hKind : token.kind = .regex)
      (hShape : regexTokenCheck token.text = true) :
      SurfaceTokenForm .ts token
  | comment {lang : TargetLang} {token : SourceToken}
      (hKind : token.kind = .comment)
      (hPrefix : (lang == .python && token.text.startsWith "#") ||
        (lang == .ts && token.text.startsWith "//"))
      (hNoNewline : !token.text.toList.contains '\n') :
      SurfaceTokenForm lang token
  | punctuation {lang : TargetLang} {token : SourceToken}
      (hKind : token.kind = .punctuation)
      (hPunct : punctuationCharCheck token.text = true) :
      SurfaceTokenForm lang token

/-- End-of-token maximality for run-shaped tokens. -/
def tokenBoundaryCheck (token : SourceToken) (after : String) : Bool :=
  match token.kind, after.toList with
  | .spacing, c :: _ => !c.isWhitespace
  | .identifier, c :: _ => !(c.isAlphanum || c == '_' || c == '$')
  | .numeral, c :: d :: _ =>
      !c.isDigit && !(c == '.' && d.isDigit)
  | .numeral, c :: _ => !c.isDigit
  | .comment, c :: _ => c == '\n'
  | .regex, c :: _ => !c.isAlpha
  | _, _ => true

/-- Scanner priority is a source-language lexical rule. It is stated apart
    from the raw `scan` decoder: comments outrank slash, then regex is selected
    only at expression-start positions. -/
def regexStartAllowed (prior : Option SourceToken) : Bool :=
  match prior with
  | none => true
  | some token =>
      token.kind == .punctuation &&
        (["=", "(", "!", ",", ":"] : List String).contains token.text

def tokenPriorityCheck (lang : TargetLang) (prior : Option SourceToken)
    (remaining : String) (token : SourceToken) : Bool :=
  match remaining.toList with
  | [] => false
  | c :: cs =>
      if c == '"' || c == '\'' || c == '`' then token.kind == .quoted
      else if c.isWhitespace then token.kind == .spacing
      else if c.isAlpha || c == '_' || c == '$' then token.kind == .identifier
      else if c.isDigit then token.kind == .numeral
      else if (lang == .python && c == '#') ||
              (lang == .ts && c == '/' && cs.head? == some '/') then
        token.kind == .comment
      else if lang == .ts && c == '/' && regexStartAllowed prior then
        token.kind == .regex
      else token.kind == .punctuation

/-- Select the shortest quote-terminated prefix. Escape pairs remain owned by
    the same token. This is a determinism witness for the lexical grammar, not
    the raw decoder's `scanQuote` implementation. -/
def firstQuotedPrefix (quote : Char) (reversePrefix : List Char) :
    List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c == quote then some ((c :: reversePrefix).reverse, rest)
      else if c == '\\' then
        match rest with
        | [] => none
        | escaped :: tail =>
            firstQuotedPrefix quote (escaped :: c :: reversePrefix) tail
      else firstQuotedPrefix quote (c :: reversePrefix) rest

def firstRegexPrefix (inClass : Bool) (reversePrefix : List Char) :
    List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c == '\\' then
        match rest with
        | [] => none
        | escaped :: tail =>
            firstRegexPrefix inClass (escaped :: c :: reversePrefix) tail
      else if c == '[' then firstRegexPrefix true (c :: reversePrefix) rest
      else if c == ']' then firstRegexPrefix false (c :: reversePrefix) rest
      else if c == '/' && !inClass then
        let flags := rest.takeWhile Char.isAlpha
        some (String.mk ((c :: reversePrefix).reverse ++ flags) |>.toList,
          rest.dropWhile Char.isAlpha)
      else firstRegexPrefix inClass (c :: reversePrefix) rest

def firstNumeralPrefix (first : Char) (rest : List Char) : List Char :=
  let digits := rest.takeWhile Char.isDigit
  match rest.dropWhile Char.isDigit with
  | '.' :: fractionFirst :: tail =>
      if fractionFirst.isDigit then
        first :: digits ++ ['.', fractionFirst] ++ tail.takeWhile Char.isDigit
      else first :: digits
  | _ => first :: digits

/-- A deterministic *lexical* head reconstructed from the independent
    character rules. No expression, statement, or program AST is parsed here. -/
def canonicalLexicalHead (lang : TargetLang) (prior : Option SourceToken)
    (remaining : String) (offset : Nat) : Option SourceToken := do
  let c :: rest := remaining.toList | none
  let (kind, spelling) ←
    if c == '"' || c == '\'' || c == '`' then do
      let (chunk, _) ← firstQuotedPrefix c [c] rest
      pure (TokenKind.quoted, String.mk chunk)
    else if c.isWhitespace then
      pure (.spacing, String.mk (c :: rest.takeWhile Char.isWhitespace))
    else if c.isAlpha || c == '_' || c == '$' then
      pure (.identifier,
        String.mk (c :: rest.takeWhile
          (fun x => x.isAlphanum || x == '_' || x == '$')))
    else if c.isDigit then
      pure (.numeral, String.mk (firstNumeralPrefix c rest))
    else if (lang == .python && c == '#') ||
            (lang == .ts && c == '/' && rest.head? == some '/') then
      pure (.comment, String.mk (c :: rest.takeWhile (· != '\n')))
    else if lang == .ts && c == '/' && regexStartAllowed prior then do
      let (chunk, _) ← firstRegexPrefix false [c] rest
      pure (.regex, String.mk chunk)
    else pure (.punctuation, String.singleton c)
  pure ⟨kind, spelling, offset, offset + spelling.length⟩

inductive CanonicalAt : TargetLang → Option SourceToken → String → Nat →
    List SourceToken → Prop where
  | empty (lang : TargetLang) (prior : Option SourceToken) (offset : Nat) :
      CanonicalAt lang prior "" offset []
  | token {lang : TargetLang} {prior : Option SourceToken}
      {remaining : String} {offset : Nat} {first : SourceToken}
      {tail : List SourceToken}
      (hHead : canonicalLexicalHead lang prior remaining offset = some first)
      (hRest : CanonicalAt lang
        (if first.kind == .spacing then prior else some first)
        (String.mk (remaining.toList.drop first.text.length)) first.stop tail) :
      CanonicalAt lang prior remaining offset (first :: tail)

inductive PriorityAt : TargetLang → Option SourceToken → String →
    List SourceToken → Prop where
  | empty (lang : TargetLang) (prior : Option SourceToken) :
      PriorityAt lang prior "" []
  | token {lang : TargetLang} {prior : Option SourceToken}
      {remaining : String} {first : SourceToken} {tail : List SourceToken}
      (hPriority : tokenPriorityCheck lang prior remaining first = true)
      (hRest : PriorityAt lang
        (if first.kind == .spacing then prior else some first)
        (String.mk (remaining.toList.drop first.text.length)) tail) :
      PriorityAt lang prior remaining (first :: tail)

/-- A lexical trace consumes the entire source with absolute offsets. The
    token-kind and maximal-munch productions are separate refinements. -/
inductive LexesAt : TargetLang → String → Nat → List SourceToken → Prop where
  | empty (lang : TargetLang) (offset : Nat) : LexesAt lang "" offset []
  | token {lang : TargetLang} {remaining : String} {offset : Nat}
      {first : SourceToken} {tail : List SourceToken}
      (hStart : first.start = offset)
      (hStop : first.stop = offset + first.text.length)
      (hNonempty : !first.text.isEmpty)
      (hForm : SurfaceTokenForm lang first)
      (hPrefix : String.mk (remaining.toList.take first.text.length) = first.text)
      (hBoundary : tokenBoundaryCheck first
        (String.mk (remaining.toList.drop first.text.length)) = true)
      (hRest : LexesAt lang
        (String.mk (remaining.toList.drop first.text.length)) first.stop tail) :
      LexesAt lang remaining offset (first :: tail)

inductive Lexes : TargetLang → String → List SourceToken → Prop where
  | ofTrace {lang : TargetLang} {source : String} {tokens : List SourceToken}
      (h : LexesAt lang source 0 tokens)
      (hPriority : PriorityAt lang none source tokens)
      (hCanonical : CanonicalAt lang none source 0 tokens) :
      Lexes lang source tokens

theorem CanonicalAt.unique {lang prior source offset left right}
    (hLeft : CanonicalAt lang prior source offset left)
    (hRight : CanonicalAt lang prior source offset right) : left = right := by
  induction hLeft generalizing right with
  | empty =>
      cases hRight with
      | empty => rfl
      | token hHead _ => simp [canonicalLexicalHead] at hHead
  | token hHead hRest ih =>
      cases hRight with
      | empty => simp [canonicalLexicalHead] at hHead
      | token hOther hOtherRest =>
          rw [hHead] at hOther
          cases hOther
          exact congrArg (_ :: ·) (ih hOtherRest)

theorem Lexes.unique {lang source left right}
    (hLeft : Lexes lang source left) (hRight : Lexes lang source right) :
    left = right := by
  cases hLeft with
  | ofTrace _ _ leftCanonical =>
      cases hRight with
      | ofTrace _ _ rightCanonical =>
          exact CanonicalAt.unique leftCanonical rightCanonical

/-- Delimiters inside validated quote/regex tokens are atomic. A comma is an
    argument separator only when no parenthesis, bracket or brace is open. -/
def firstTopLevelCommaAux : List String → List SourceToken → Option Nat
  | _, [] => none
  | stack, token :: rest =>
      match token.text with
      | "(" => firstTopLevelCommaAux (")" :: stack) rest
      | "[" => firstTopLevelCommaAux ("]" :: stack) rest
      | "{" => firstTopLevelCommaAux ("}" :: stack) rest
      | ")" | "]" | "}" =>
          match stack with
          | expected :: tail =>
              if token.text == expected then firstTopLevelCommaAux tail rest
              else none
          | [] => none
      | "," =>
          if stack.isEmpty then some token.start
          else firstTopLevelCommaAux stack rest
      | _ => firstTopLevelCommaAux stack rest

def firstTopLevelComma (tokens : List SourceToken) : Option Nat :=
  firstTopLevelCommaAux [] tokens

/-- Physical line spans preserve blank lines, indentation, and the newline
    separator instead of relying on the decoder's offset-free `PythonLine`. -/
structure LocatedSourceLine where
  start : Nat
  stop : Nat
  raw : String
  terminated : Bool
  deriving DecidableEq, Repr

inductive LinesAt : String → Nat → List LocatedSourceLine → Prop where
  | final {source : String} {offset : Nat}
      (hNoNewline : source.toList.contains '\n' = false) :
      LinesAt source offset [⟨offset, offset + source.length, source, false⟩]
  | next {head rest : String} {offset : Nat} {tail : List LocatedSourceLine}
      (hNoNewline : head.toList.contains '\n' = false)
      (hRest : LinesAt rest (offset + head.length + 1) tail) :
      LinesAt (head ++ "\n" ++ rest) offset
        (⟨offset, offset + head.length, head, true⟩ :: tail)

/-- A chunk ending at a physical newline. These compose without creating a
    spurious empty final line at each chunk boundary. -/
inductive PrefixLinesAt : String → Nat → List LocatedSourceLine → Prop where
  | empty (offset : Nat) : PrefixLinesAt "" offset []
  | next {head rest : String} {offset : Nat}
      {tail : List LocatedSourceLine}
      (hNoNewline : head.toList.contains '\n' = false)
      (hRest : PrefixLinesAt rest (offset + head.length + 1) tail) :
      PrefixLinesAt (head ++ "\n" ++ rest) offset
        (⟨offset, offset + head.length, head, true⟩ :: tail)

def prefixLinesSource : List LocatedSourceLine → String
  | [] => ""
  | first :: rest => first.raw ++ "\n" ++ prefixLinesSource rest

structure LocatedLineChunk where
  text : String
  lines : List LocatedSourceLine
  deriving DecidableEq, Repr

/-- Full-source indentation ownership by bounded chunks. Each chunk has a
    constituent line derivation; the recursive source equation leaves no gap. -/
inductive ChunkedLines : String → Nat → List LocatedLineChunk → Prop where
  | empty (offset : Nat) : ChunkedLines "" offset []
  | cons {chunkText rest : String} {offset : Nat}
      {lines : List LocatedSourceLine} {tail : List LocatedLineChunk}
      (hChunk : PrefixLinesAt chunkText offset lines)
      (hRest : ChunkedLines rest (offset + chunkText.length) tail) :
      ChunkedLines (chunkText ++ rest) offset
        (⟨chunkText, lines⟩ :: tail)

theorem prefixLinesSource_append (left right : List LocatedSourceLine) :
    prefixLinesSource (left ++ right) =
      prefixLinesSource left ++ prefixLinesSource right := by
  induction left with
  | nil => simp [prefixLinesSource]
  | cons first rest ih =>
      simp [prefixLinesSource, ih, String.append_assoc]

theorem PrefixLinesAt.append {left right : String} {offset : Nat}
    {leftLines rightLines : List LocatedSourceLine}
    (hLeft : PrefixLinesAt left offset leftLines)
    (hRight : PrefixLinesAt right (offset + left.length) rightLines) :
    PrefixLinesAt (left ++ right) offset (leftLines ++ rightLines) := by
  induction hLeft with
  | empty => simpa using hRight
  | @next head rest offset tail hNoNewline hRest ih =>
      have hRightRest : PrefixLinesAt right
          ((offset + head.length + 1) + rest.length) rightLines := by
        have hNl : ("\n" : String).length = 1 := by decide
        simpa [String.length_append, hNl, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hRight
      have hTail := ih hRightRest
      simpa [String.append_assoc] using
        (PrefixLinesAt.next (head := head)
          (rest := rest ++ right) (offset := offset)
          hNoNewline hTail)

def flattenedChunkLines : List LocatedLineChunk → List LocatedSourceLine
  | [] => []
  | chunk :: rest => chunk.lines ++ flattenedChunkLines rest

/-- Chunk boundaries are only a proof engineering device. The result is a
    single independent line derivation for the complete emitted source. -/
theorem ChunkedLines.toPrefixLinesAt {source : String} {offset : Nat}
    {chunks : List LocatedLineChunk}
    (h : ChunkedLines source offset chunks) :
    PrefixLinesAt source offset (flattenedChunkLines chunks) := by
  induction h with
  | empty => exact .empty _
  | cons hChunk hRest ih =>
      simpa [flattenedChunkLines] using PrefixLinesAt.append hChunk ih

theorem PrefixLinesAt.toLinesAt {source : String} {offset : Nat}
    {lines : List LocatedSourceLine}
    (h : PrefixLinesAt source offset lines) :
    LinesAt source offset
      (lines ++ [⟨offset + source.length, offset + source.length, "", false⟩]) := by
  induction h with
  | @empty offset =>
      simpa using (LinesAt.final (source := "") (offset := offset) (by decide))
  | @next head rest offset tail hNoNewline hRest ih =>
      have hNl : ("\n" : String).length = 1 := by decide
      have hTail : LinesAt rest (offset + head.length + 1)
          (tail ++ [⟨offset + (head ++ "\n" ++ rest).length,
            offset + (head ++ "\n" ++ rest).length, "", false⟩]) := by
        simpa [String.length_append, hNl, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using ih
      simpa using LinesAt.next hNoNewline hTail

end Harmonia.Applications.Kadmos.Generated
