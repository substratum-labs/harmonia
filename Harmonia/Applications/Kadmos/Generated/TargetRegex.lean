import Harmonia.Applications.Kadmos.Generated.TargetMachine

namespace Harmonia.Applications.Kadmos.Generated

def pythonTokenPattern : String :=
  "\\s+|=>|==|!=|>=|<=|&&|\\|\\||[()+\\-*/<>!.]|\\d+(?:\\.\\d+)?|[A-Za-z_][A-Za-z_0-9]*|'(?:[^'\\\\]|\\\\.)*'"

def pythonNamePattern : String := "[A-Za-z_][A-Za-z_0-9]*\\Z"
def pythonEffectPattern : String :=
  "([A-Za-z_][A-Za-z_0-9]*)\\s*=\\s*(.+)\\Z"

private def regexSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def identStart (c : Char) : Bool := c.isAlpha || c == '_'
private def identRest (c : Char) : Bool := c.isAlphanum || c == '_'

def identifierFullMatch (source : String) : Bool :=
  match source.toList with
  | [] => false
  | first :: rest => identStart first && rest.all identRest

def effectFullMatch (source : String) : Option MatchValue := do
  let chars := source.toList
  let before := chars.takeWhile (· != '=')
  let after ← match chars.dropWhile (· != '=') with
    | '=' :: rest => some rest
    | _ => none
  let nameChars := (before.reverse.dropWhile
    (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')).reverse
  let name := String.mk nameChars
  if !identifierFullMatch name then none
  let rhs := String.mk (after.dropWhile
    (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'))
  if rhs.isEmpty then none
  some ⟨source, 0, chars.length, [some name, some rhs]⟩

private def quotedTail (acc : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | '\'' :: rest => some (('\'' :: acc).reverse, rest)
  | '\\' :: escaped :: rest => quotedTail (escaped :: '\\' :: acc) rest
  | '\\' :: [] => none
  | c :: rest => quotedTail (c :: acc) rest

private def tokenChars : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if regexSpace c then
        let tail := rest.takeWhile regexSpace
        some (c :: tail, rest.dropWhile regexSpace)
      else if c == '\'' then quotedTail ['\''] rest
      else if c.isDigit then
        let digits := rest.takeWhile Char.isDigit
        let after := rest.dropWhile Char.isDigit
        match after with
        | '.' :: d :: more =>
            if d.isDigit then
              let fraction := more.takeWhile Char.isDigit
              some (c :: digits ++ ['.', d] ++ fraction,
                more.dropWhile Char.isDigit)
            else some (c :: digits, after)
        | _ => some (c :: digits, after)
      else if identStart c then
        let tail := rest.takeWhile identRest
        some (c :: tail, rest.dropWhile identRest)
      else
        match c, rest with
        | '=', '>' :: after => some (['=', '>'], after)
        | '=', '=' :: after => some (['=', '='], after)
        | '!', '=' :: after => some (['!', '='], after)
        | '>', '=' :: after => some (['>', '='], after)
        | '<', '=' :: after => some (['<', '='], after)
        | '&', '&' :: after => some (['&', '&'], after)
        | '|', '|' :: after => some (['|', '|'], after)
        | _, _ =>
            if ['(', ')', '+', '-', '*', '/', '<', '>', '!', '.'].contains c then
              some ([c], rest)
            else none

def tokenMatchAt (source : String) (offset : Nat) : Option MatchValue := do
  if offset > source.toList.length then none
  let (chars, _) ← tokenChars (source.toList.drop offset)
  if chars.isEmpty then none
  else some ⟨String.mk chars, offset, offset + chars.length, []⟩

private def tokenizeWorldExprAux (fuel offset : Nat) (source : String)
    (acc : List String) : Option (List String) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if offset == source.toList.length then some acc.reverse
      else
        match tokenMatchAt source offset with
        | none => none
        | some result =>
            if result.stop ≤ offset then none
            else if result.full.toList.all regexSpace then
              tokenizeWorldExprAux fuel result.stop source acc
            else tokenizeWorldExprAux fuel result.stop source (result.full :: acc)

def tokenizeWorldExpr (source : String) : Option (List String) :=
  tokenizeWorldExprAux (source.toList.length + 1) 0 source []

end Harmonia.Applications.Kadmos.Generated
