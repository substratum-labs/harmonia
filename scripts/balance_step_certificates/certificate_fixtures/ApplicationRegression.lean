import Init
open Lean
set_option maxRecDepth 200000
set_option autoImplicit false
private def packName (s : String) : Name :=
  (s.splitOn "|").foldl (fun n p => if p.startsWith "s" then Name.str n (p.drop 1) else if p.startsWith "n" then Name.num n (p.drop 1).toNat! else n) Name.anonymous
private def packSyntax (rows : String) (params : Array Syntax) : MacroM (TSyntax `term) := do
  let mut nodes : Array Syntax := #[]
  for row in rows.splitOn "\n" do
    let payload := row.drop 1
    let node ← match row.get? 0 with
      | some 'n' => pure <| Id.run do
          let parts := payload.splitOn ":"
          let cs := if parts[1]! == "" then #[] else (parts[1]!.splitOn ",").toArray.map (fun s => nodes[s.toNat!]!)
          let kind := packName parts[0]!
          -- A former local function may now be a family application.
          -- Keep its explicit head and concatenate the exact argument arrays.
          if kind == `Lean.Parser.Term.explicit && cs[1]!.isOfKind `Lean.Parser.Term.app then
            return cs[1]!
          if kind == `Lean.Parser.Term.app && cs[0]!.isOfKind `Lean.Parser.Term.app then
            return Syntax.node .none kind #[cs[0]![0], mkNullNode (cs[0]![1].getArgs ++ cs[1]!.getArgs)]
          return Syntax.node .none kind cs
      | some 'p' => pure params[payload.toNat!]!
      | some 'i' => pure (mkIdent (packName payload)).raw
      | some 'g' => do
          let parts := payload.splitOn ":"
          let f : TSyntax `term := ⟨(mkIdent (Name.mkSimple parts[0]!)).raw⟩
          let args : Array (TSyntax `term) := if parts[1]! == "" then #[] else (parts[1]!.splitOn ",").toArray.map (fun s => ⟨params[s.toNat!]!⟩)
          if args.isEmpty then pure f.raw else do
            let t ← `(@$f $args*)
            pure t.raw
      | some 'a' => pure (Syntax.atom .none payload)
      | _ => pure Syntax.missing
    nodes := nodes.push node
  return ⟨nodes.back!⟩
macro "pack_term" rows:str "[" ps:term,* "]" : term => packSyntax rows.getString (ps.getElems.map (·.raw))

private def packAux2653 (b n : Int) := fun (x : Nat) => b + n + Int.ofNat x
private def packAux646 : Nat := 3
def functionReferenceRegression (b n : Int) : Int :=
 pack_term "a@\ngpackAux2653:0,1\nn|sLean|sParser|sTerm|sexplicit:0,1\ngpackAux646:\nn|snull:3\nn|sLean|sParser|sTerm|sapp:2,4" [b, n]
theorem functionReferenceRegression_eq (b n : Int) : functionReferenceRegression b n = b + n + 3 := rfl
private def packAux8 (n : Nat) (h : n = n) := fun {α : Type} (x : α) => (@Subtype.mk α (fun _ => n = n) x h)
def implicitArgumentRegression (n : Nat) (h : n = n) := pack_term "a@\ngpackAux8:0,1\nn|sLean|sParser|sTerm|sexplicit:0,1\ni|sNat\np0\nn|snull:3,4\nn|sLean|sParser|sTerm|sapp:2,5" [n, h]
theorem implicitArgumentRegression_eq (n : Nat) (h : n = n) : (implicitArgumentRegression n h).1 = n := rfl
#print axioms functionReferenceRegression_eq
#print axioms implicitArgumentRegression_eq
