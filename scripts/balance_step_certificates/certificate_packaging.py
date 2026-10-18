"""Lift only the serialized outer lets to ordinary private definition families.
No proof transformation: every original RHS syntax node is retained. Declaration
result types are inferred by Lean; all binder types present in the source remain.
"""
from pathlib import Path
import ast, re, json, hashlib, functools

PRELUDE = r'''open Lean
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
'''

def read_table(path):
    source=Path(path).read_text()
    lines=source.splitlines()
    names=ast.literal_eval(next(l.split(':= ',1)[1] for l in lines if re.match(r'private def \w+NamesText',l))).split('\n')
    rows=ast.literal_eval(next(l.split(':= ',1)[1] for l in lines if re.match(r'private def \w+Rows :',l))).split('\n')
    root=int(re.search(r'return nodes\[(\d+)\]!', source)[1])
    nodes=[]
    for i,row in enumerate(rows):
        if row.startswith('n'):
            k,cs=row[1:].split(':'); cs=list(map(int,filter(None,cs.split(','))))
            assert all(0<=c<i for c in cs), 'syntax child must refer to an earlier nonnegative row'
            assert 0<=int(k)<len(names), 'syntax kind name index out of range'
            nodes.append(('n',int(k),cs))
        elif row[0] in 'ip':
            value=int(row[1:]);assert value>=0, 'negative name/parameter index'
            if row[0]=='i':assert value<len(names), 'identifier name index out of range'
            nodes.append((row[0],value))
        else:
            assert row[0]=='a' or row=='m', 'unknown syntax row tag'
            nodes.append((row[0],row[1:]))
    assert 0<=root<len(nodes), 'root index out of range'
    return source,names,nodes,root

def load_schema(path):
    schema=json.loads(Path(path).read_text())
    fields=schema['parameters'];names=[p['name'] for p in fields]
    assert len(names)==len(set(names)), 'duplicate root parameter'
    params=[(p['name'],p['type']) for p in fields];deps=[]
    for i,p in enumerate(fields):
        required=p.get('type_dependencies',[])
        assert len(required)==len(set(required)), 'duplicate parameter type dependency'
        assert all(n in names for n in required), 'unknown parameter type dependency'
        positions=[names.index(n) for n in required]
        assert all(j<i for j in positions), 'parameter type dependencies must precede their binder'
        deps.append(sum(1<<j for j in positions))
    return schema,params,deps

class Packager:
    def __init__(self,path,params,type_deps,aux_prefix='packAux',macro_name='pack_term',intern_names=False,intern_kinds=False):
        self.source,self.names,self.nodes,self.root=read_table(path)
        self.params=params;self.type_deps=type_deps
        self.aux_prefix=aux_prefix;self.macro_name=macro_name
        self.intern_names=intern_names
        self.intern_kinds=intern_kinds
        assert not (intern_names and intern_kinds), 'choose one name encoding'
        kind_indices=sorted({n[1] for n in self.nodes if n[0]=='n'})
        self.kind_names=[self.names[i] for i in kind_indices]
        self.kind_ids={n:i for i,n in enumerate(kind_indices)}
        self.entries=[]; cur=self.root
        while self.kind(cur)=='|sLean|sParser|sTerm|slet':
            children=self.nodes[cur][2]; assert len(children)==4
            decl=self.nodes[children[1]]; assert self.kind(children[1])=='|sLean|sParser|sTerm|sletDecl'
            inner=decl[2][0]; assert self.kind(inner)=='|sLean|sParser|sTerm|sletIdDecl'
            bits=self.nodes[inner][2]; assert len(bits)==5
            name=self.nodes[bits[0]]; assert name[0]=='i'
            assert not self.nodes[bits[1]][2] and not self.nodes[bits[2]][2], 'outer binding unexpectedly typed/parameterized'
            self.entries.append((name[1],bits[4])); cur=children[3]
        self.body=cur
        self.globals={n:i for i,(n,v) in enumerate(self.entries)}
        assert len(self.globals)==len(self.entries)
        self.masks={}; self.reachable=set();self.depths={}
        for i,(name,rhs) in enumerate(self.entries):
            mask=self.dependencies(rhs,i)
            while True:
                oldmask=mask
                for p in range(len(params)):
                    if mask>>p&1:mask|=type_deps[p]
                if mask==oldmask:break
            self.masks[name]=mask
        self.dependencies(self.body,len(self.entries))
    def kind(self,i):
        n=self.nodes[i]
        return self.names[n[1]] if n[0]=='n' else None
    @functools.cache
    def dependencies(self,node,limit):
        n=self.nodes[node]; self.reachable.add(node)
        if n[0]=='p': return 1<<n[1]
        if n[0]=='i' and n[1] in self.globals:
            assert self.globals[n[1]]<limit, 'forward global reference'
            return self.masks[n[1]]
        mask=0
        if n[0]=='n':
            for c in n[2]:mask |= self.dependencies(c,limit)
        return mask
    def table(self,root):
        out=[];memo={}
        def visit(i):
            if i in memo:return memo[i]
            n=self.nodes[i]
            if n[0]=='n':
                cs=[visit(c) for c in n[2]]
                kind=str(n[1]) if self.intern_names else str(self.kind_ids[n[1]]) if self.intern_kinds else self.names[n[1]]
                row='n'+kind+':'+','.join(map(str,cs))
            elif n[0]=='i' and n[1] in self.globals:
                row='g'+('' if self.intern_names or self.intern_kinds else self.aux_prefix)+str(self.globals[n[1]])+':'+','.join(str(p) for p in range(len(self.params)) if self.masks[n[1]]>>p&1)
            elif n[0]=='i':row='i'+(str(n[1]) if self.intern_names else self.names[n[1]])
            else:row=n[0]+str(n[1])
            j=len(out);memo[i]=j;out.append(row);return j
        visit(root)
        return json.dumps('\n'.join(out),ensure_ascii=False)
    def term(self,rhs,mask):
        args=', '.join(p[0] if mask>>i&1 else '_' for i,p in enumerate(self.params))
        return self.macro_name+' '+self.table(rhs)+' ['+args+']'
    def declarations(self,limit=None):
        out=[]
        for i,(name,rhs) in enumerate(self.entries[:limit]):
            mask=self.masks[name]
            binders=' '.join('('+p[0]+' : '+p[1]+')' for j,p in enumerate(self.params) if mask>>j&1)
            out.append(f'private noncomputable def {self.aux_prefix}{i} {binders} :=\n  '+self.term(rhs,mask)+'\n')
        return '\n'.join(out)
    def report(self):
        return {'source_sha256':hashlib.sha256(self.source.encode()).hexdigest(),'entries':len(self.entries),'nodes':len(self.nodes),'global_identifiers_rewritten':len(self.globals),'intern_names':self.intern_names,'intern_kinds':self.intern_kinds,'kind_names':len(self.kind_names),'mode':'private noncomputable def, inferred result types; all RHS syntax preserved','parameter_masks':{str(m):list(self.masks.values()).count(m) for m in set(self.masks.values())}}

def packaging_prelude(p):
    if not p.intern_names and not p.intern_kinds:return PRELUDE
    table=p.kind_names if p.intern_kinds else p.names
    names='private def packNamesText : String := '+json.dumps('\n'.join(table),ensure_ascii=False)+'\n'
    names+='private def packNames : Array Name := (packNamesText.splitOn "\\n").toArray.map packName\n'
    prelude=PRELUDE.replace('private def packSyntax',names+'private def packSyntax',1)
    prelude=prelude.replace('let kind := packName parts[0]!','let kind := packNames[parts[0]!.toNat!]!')
    if p.intern_names:prelude=prelude.replace('(mkIdent (packName payload)).raw','(mkIdent packNames[payload.toNat!]!).raw')
    prelude=prelude.replace('Name.mkSimple parts[0]!','Name.mkSimple ('+json.dumps(p.aux_prefix)+' ++ parts[0]!)')
    return prelude
