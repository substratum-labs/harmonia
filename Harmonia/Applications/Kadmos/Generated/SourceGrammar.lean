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

mutual
/-- Source productions, independent of the executable decoder. Argument
    sequences have their own sort: a bare expression cannot also be an
    argument-list AST for the same source. -/
inductive ExprSyntax : TargetLang → String → TargetExpr → Prop where
  | empty (lang : TargetLang) : ExprSyntax lang "" .empty
  | call {lang : TargetLang} {calleeText argsText : String}
      {callee args : TargetExpr}
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
      (hBase : ExprSyntax lang base receiver)
      (hName : PropertyIdentifier lang name) :
      ExprSyntax lang (base ++ "." ++ name) (.property receiver name)
  | tsOptionalProperty {base name : String} {receiver : TargetExpr}
      (hBase : ExprSyntax .ts base receiver)
      (hName : IdentifierText name) :
      ExprSyntax .ts (base ++ "?." ++ name)
        (.optionalProperty receiver name)
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
      (hValue : ExprSyntax lang source value) :
      ArgumentSyntax lang source (.sequence value .empty)
  | more {lang : TargetLang} {firstText gap restText : String}
      {tokens : List SourceToken} {first rest : TargetExpr}
      (hLex : Lexes lang (firstText ++ "," ++ gap ++ restText) tokens)
      (hComma : firstTopLevelComma tokens = some firstText.length)
      (hGap : gap.toList.all Char.isWhitespace = true)
      (hFirst : ExprSyntax lang firstText first)
      (hRest : ArgumentSyntax lang restText rest) :
      ArgumentSyntax lang (firstText ++ "," ++ gap ++ restText)
        (.sequence first rest)
end

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
  | tsTypeImport (span : SourceSpan) (names : List String) (moduleName : String)
  | tsWorldDataType (span : SourceSpan)
  deriving DecidableEq, Repr

def SourceItem.span : SourceItem → SourceSpan
  | .runtime _ span _ => span
  | .tsTypeImport span _ _ => span
  | .tsWorldDataType span => span

inductive ItemDerives : TargetLang → String → SourceItem → Prop where
  | runtime {lang : TargetLang} {source : String} {control : SurfaceControl}
      {span : SourceSpan} {stmt : TargetStmt}
      (hStmt : StmtDerives lang control source span stmt) :
      ItemDerives lang source (.runtime control span stmt)
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
