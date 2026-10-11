import Init

namespace Harmonia.Applications.Kadmos.Generated

inductive TargetJSON where
  | empty
  | null | bool (value : Bool) | integer (value : Int) | string (value : String)
  | array (items : TargetJSON) | valueItem (value rest : TargetJSON)
  | object (fields : TargetJSON) | keyVal (key : String) (value rest : TargetJSON)
  deriving DecidableEq, Repr

inductive JSONError where
  | syntax | duplicateKey | unsupportedNumber | unsafeNumber | invalidString
  deriving DecidableEq, Repr

private def jsonSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def skipSpace (chars : List Char) : List Char :=
  chars.dropWhile jsonSpace

private def parseQuoted : List Char → List Char → Except JSONError (String × List Char)
  | _, [] => .error .invalidString
  | acc, '"' :: rest => .ok (String.mk acc.reverse, rest)
  | acc, '\\' :: escaped :: rest => do
      let decoded ← match escaped with
        | '"' => .ok '"' | '\\' => .ok '\\' | '/' => .ok '/'
        | 'n' => .ok '\n' | 'r' => .ok '\r' | 't' => .ok '\t'
        | 'b' => .ok '\x08' | 'f' => .ok '\x0c'
        | _ => .error .invalidString
      parseQuoted (decoded :: acc) rest
  | _, '\\' :: [] => .error .invalidString
  | acc, c :: rest =>
      if c.toNat < 32 then .error .invalidString
      else parseQuoted (c :: acc) rest

private def decimalNat (chars : List Char) : Nat :=
  chars.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

private def parseNumber (chars : List Char) : Except JSONError (TargetJSON × List Char) := do
  let negative := chars.head? == some '-'
  let digitsInput := if negative then chars.drop 1 else chars
  let digits := digitsInput.takeWhile Char.isDigit
  if digits.isEmpty then throw .syntax
  if digits.length > 1 && digits.head? == some '0' then throw .syntax
  let remaining := digitsInput.drop digits.length
  if remaining.head? == some '.' || remaining.head? == some 'e' ||
      remaining.head? == some 'E' then throw .unsupportedNumber
  let natural := decimalNat digits
  if natural > 9007199254740991 then throw .unsafeNumber
  let value := Int.ofNat natural
  if negative && value == 0 then throw .unsupportedNumber
  return (.integer (if negative then -value else value), remaining)

mutual

private def parseValue (fuel : Nat) (chars : List Char) :
    Except JSONError (TargetJSON × List Char) :=
  match fuel, skipSpace chars with
  | 0, _ => .error .syntax
  | _, [] => .error .syntax
  | _ + 1, '"' :: rest => do
      let (value, tail) ← parseQuoted [] rest
      return (.string value, tail)
  | fuel + 1, '[' :: rest => do
      let (items, tail) ← parseArrayValues fuel rest
      return (.array items, tail)
  | fuel + 1, '{' :: rest => do
      let (fields, tail) ← parseObjectValues fuel [] rest
      return (.object fields, tail)
  | _, 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest)
  | _, 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest)
  | _, 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
  | _, chars => parseNumber chars

private def parseArrayValues (fuel : Nat) (chars : List Char) :
    Except JSONError (TargetJSON × List Char) :=
  match fuel, skipSpace chars with
  | 0, _ => .error .syntax
  | _, ']' :: rest => .ok (.empty, rest)
  | fuel + 1, body => do
      let (value, tail) ← parseValue fuel body
      match skipSpace tail with
      | ']' :: rest => return (.valueItem value .empty, rest)
      | ',' :: rest =>
          let (others, final) ← parseArrayValues fuel rest
          if others == .empty then throw .syntax
          return (.valueItem value others, final)
      | _ => throw .syntax

private def parseObjectValues (fuel : Nat) (keys : List String) (chars : List Char) :
    Except JSONError (TargetJSON × List Char) :=
  match fuel, skipSpace chars with
  | 0, _ => .error .syntax
  | _, '}' :: rest => .ok (.empty, rest)
  | fuel + 1, '"' :: rest => do
      let (key, afterKey) ← parseQuoted [] rest
      if keys.contains key then throw .duplicateKey
      let afterColon ← match skipSpace afterKey with
        | ':' :: tail => .ok tail
        | _ => .error .syntax
      let (value, tail) ← parseValue fuel afterColon
      match skipSpace tail with
      | '}' :: final => return (.keyVal key value .empty, final)
      | ',' :: remaining =>
          let (others, final) ← parseObjectValues fuel (key :: keys) remaining
          if others == .empty then throw .syntax
          return (.keyVal key value others, final)
      | _ => throw .syntax
  | _, _ => .error .syntax

end

def parseTargetJSON (source : String) : Except JSONError TargetJSON := do
  let (value, tail) ← parseValue (source.toList.length * 2 + 1) source.toList
  if (skipSpace tail).isEmpty then return value
  else throw .syntax

end Harmonia.Applications.Kadmos.Generated
