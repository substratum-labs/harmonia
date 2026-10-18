import Init
open Lean
set_option maxRecDepth 200000
private def prefixDagNamesText : String := "|sLean|sParser|sTerm|slet\n|sLean|sParser|sTerm|sletDecl\n|sLean|sParser|sTerm|sletIdDecl\n|sprefixDagLocal1\n|snull\n|sLean|sParser|sTerm|sapp\n|sLean|sParser|sTerm|sexplicit\n|sLean|sParser|sTerm|sexplicitUniv\n|sProd\n|snum\n|sInt\n|sprefixDagLocal2\n|sLean|sParser|sTerm|sfun\n|sLean|sParser|sTerm|sbasicFun\n|sLean|sParser|sTerm|stypeAscription\n|sprefixDagLocal0\n|sprefixDagLocal4\n|sprefixDagLocal3\n|sProd|smk\n|sprefixDagLocal7\n|sprefixDagLocal5\n|scongrArg\n|sprefixDagLocal6\n|sprefixDagLocal8\n|sfunext"
private def prefixDagNames : Array Name := (prefixDagNamesText.splitOn "\n").toArray.map fun row => (row.splitOn "|").foldl (fun n p => if p.startsWith "s" then Name.str n (p.drop 1) else if p.startsWith "n" then Name.num n (p.drop 1).toNat! else n) Name.anonymous
private def prefixDagRows : String := "alet\ni3\nn4:\na:=\na@\ni8\na.{\na0\nn9:7\na,\nn4:8,9,8\na}\nn7:5,6,10,11\nn6:4,12\ni10\nn4:14,14\nn5:13,15\nn2:1,2,2,3,16\nn1:17\na;\ni11\nafun\na(\ni15\na:\nn4:14\na)\nn14:22,23,24,25,26\nn4:27\na=>\nn13:28,2,29,1\nn12:21,30\nn2:20,2,2,3,31\nn1:32\ni16\ni17\nn14:22,35,24,25,26\nn4:36\ni18\nn7:38,6,10,11\nn6:4,39\np0\nn4:14,14,41,35\nn5:40,42\nn13:37,2,29,43\nn12:21,44\nn2:34,2,2,3,45\nn1:46\ni19\ni20\nn14:22,49,24,25,26\nn4:50\ni21\na1\nn9:53\nn4:54,9,54\nn7:52,6,55,11\nn6:4,56\ni22\nn14:22,58,24,25,26\nn4:59\nn4:14,14,58,49\nn5:40,61\nn13:60,2,29,62\nn12:21,63\np1\nn4:14,1,41,41,64,65\nn5:57,66\nn13:51,2,29,67\nn12:21,68\nn2:48,2,2,3,69\nn1:70\ni23\ni24\nn7:73,6,55,11\nn6:4,74\nn4:14,20,34,34,48\nn5:75,76\nn2:72,2,2,3,77\nn1:78\nn0:0,79,19,72\nn0:0,71,19,80\nn0:0,47,19,81\nn0:0,33,19,82\nn0:0,18,19,83"
private def prefixDagSyntax (params : Array Syntax) : Syntax := Id.run do
  let mut nodes : Array Syntax := #[]
  for row in prefixDagRows.splitOn "\n" do
    let payload := row.drop 1
    let node := match row.get? 0 with
      | some 'n' => let parts := payload.splitOn ":"; let k := prefixDagNames[parts[0]!.toNat!]!; let cs := if parts[1]! == "" then #[] else (parts[1]!.splitOn ",").toArray.map (fun s => nodes[s.toNat!]!); Syntax.node .none k cs
      | some 'p' => params[payload.toNat!]!
      | some 'i' => (mkIdent prefixDagNames[payload.toNat!]!).raw
      | some 'a' => Syntax.atom .none payload
      | _ => Syntax.missing
    nodes := nodes.push node
  return nodes[84]!
macro "prefix_dag_certificate" "[" ps:term,* "]" : term => return ⟨prefixDagSyntax (ps.getElems.map (·.raw))⟩
