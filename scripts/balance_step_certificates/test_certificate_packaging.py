from pathlib import Path
import ast,hashlib,json,re,tempfile,unittest
from certificate_packaging import Packager,read_table,load_schema
from emit_private_certificate import emit
from verify_certificate_roundtrip import verify

FIX=Path(__file__).resolve().parent/'certificate_fixtures'

class CertificatePackagingTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.out=Path(self.tmp.name)
  self.input=FIX/'TypedToy.input.lean';self.schema=FIX/'toy-schema.json';self.template=FIX/'toy-template.lean.in'
 def schema_changed(self,change):
  data=json.loads(self.schema.read_text());change(data);p=self.out/'schema.json';p.write_text(json.dumps(data));return p
 def rows_changed(self,change):
  source=self.input.read_text();match=re.search(r'(private def \w+Rows : String := )(.*)',source)
  rows=ast.literal_eval(match[2]).split('\n');change(rows)
  source=source[:match.start(2)]+json.dumps('\n'.join(rows))+source[match.end(2):]
  p=self.out/'mutated.lean';p.write_text(source);return p
 def test_raw_and_interned_exact_syntax_roundtrip(self):
  a=verify(self.input,self.schema);b=verify(self.input,self.schema,True)
  self.assertEqual(a['root_sha256'],b['root_sha256']);self.assertEqual(a['entries_checked'],5)
  for intern in [False,True]:
   target=self.out/('interned.lean' if intern else 'raw.lean')
   report=emit(self.input,self.schema,self.template,target,intern_names=intern)
   self.assertEqual(report['entries'],5);self.assertIn('macro "fixture_term"',target.read_text())
 def test_kind_only_encoding_preserves_exact_identifiers_and_proof(self):
  a=verify(self.input,self.schema);b=verify(self.input,self.schema,intern_kinds=True)
  self.assertEqual(a['root_sha256'],b['root_sha256'])
  output=self.out/'kinds.lean';report=emit(self.input,self.schema,self.template,output,intern_kinds=True)
  self.assertTrue(report['intern_kinds']);self.assertLess(report['kind_names'],40)
  self.assertIn('i|sprefixDagLocal',output.read_text())
 def test_local_binders_are_not_rewritten_as_global_families(self):
  _,params,deps=load_schema(self.schema);p=Packager(self.input,params,deps)
  local_ids={i for i,n in enumerate(p.names) if 'prefixDagLocal' in n and i not in p.globals}
  emitted='\n'.join(json.loads(p.table(rhs)) for _,rhs in p.entries)
  self.assertTrue(local_ids)
  for i in local_ids:self.assertIn('i'+p.names[i]+'\n',emitted+'\n')
 def test_changed_universe_atom_rejected_by_input_hash(self):
  p=self.rows_changed(lambda rows:rows.__setitem__(rows.index('a0'),'a1'))
  with self.assertRaisesRegex(AssertionError,'frozen schema input'):emit(p,self.schema,self.template,self.out/'bad.lean')
 def test_negative_and_forward_row_references_rejected(self):
  for bad in [-1,999999]:
   with self.subTest(reference=bad):
    def mutate(rows):
     i=next(i for i,r in enumerate(rows) if r.startswith('n') and r.split(':')[1]);rows[i]=rows[i].split(':')[0]+':'+str(bad)
    p=self.rows_changed(mutate)
    with self.assertRaisesRegex(AssertionError,'earlier nonnegative row'):read_table(p)
 def test_bad_kind_index_rejected(self):
  def mutate(rows):
   i=next(i for i,r in enumerate(rows) if r.startswith('n'));rows[i]='n999999:'+rows[i].split(':')[1]
  p=self.rows_changed(mutate)
  with self.assertRaisesRegex(AssertionError,'kind name index'):read_table(p)
 def test_unknown_forward_duplicate_type_dependencies_rejected(self):
  cases=[('unknown',lambda s:s['parameters'][1].update(type_dependencies=['ghost'])),('precede',lambda s:s['parameters'][0].update(type_dependencies=['h'])),('duplicate',lambda s:s['parameters'][1].update(type_dependencies=['n','n']))]
  for message,mutation in cases:
   with self.subTest(case=message):
    p=self.schema_changed(mutation)
    with self.assertRaisesRegex(AssertionError,message):load_schema(p)
 def test_out_of_range_parameter_slot_rejected(self):
  p=self.rows_changed(lambda rows:rows.__setitem__(rows.index('p1'),'p2'))
  schema=self.schema_changed(lambda s:s.update(certificate_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
  with self.assertRaisesRegex(AssertionError,'parameter slot out of range'):emit(p,schema,self.template,self.out/'bad.lean')
 def test_missing_template_marker_rejected(self):
  p=self.out/'bad-template';p.write_text(self.template.read_text().replace('{{CERTIFICATE_TERM}}','True.intro'))
  with self.assertRaisesRegex(AssertionError,'template marker count'):emit(self.input,self.schema,p,self.out/'bad.lean')
 def test_type_only_root_dependency_is_retained(self):
  source=self.input.read_text()
  names=['|sLean|sParser|sTerm|slet','|sLean|sParser|sTerm|sletDecl','|sLean|sParser|sTerm|sletIdDecl','|sproofAlias','|snull']
  rows=['alet','i3','n4:','a:=','p1','n2:1,2,2,3,4','n1:5','a;','n0:0,6,7,1']
  for suffix,data in [('NamesText',names),('Rows',rows)]:
   match=re.search(r'(private def \w+'+suffix+r' : String := )(.*)',source)
   source=source[:match.start(2)]+json.dumps('\n'.join(data))+source[match.end(2):]
  source=re.sub(r'return nodes\[\d+\]!', 'return nodes[8]!',source)
  p=self.out/'type-only.lean';p.write_text(source)
  schema=self.schema_changed(lambda s:s.update(certificate_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
  _,params,deps=load_schema(schema);packed=Packager(p,params,deps)
  self.assertEqual(packed.masks[3],3)
  template=self.out/'type-only-template';template.write_text(self.template.read_text().replace('(fun x : Int => (n, x)) = (fun x : Int => (n, x))','n = n'))
  output=self.out/'type-only-output.lean';emit(p,schema,template,output)
  self.assertIn('(n : Int) (h : n = n)',output.read_text())
 def test_unique_product_helper_names_do_not_change_proof_digest(self):
  schema=self.schema_changed(lambda s:s.update(aux_prefix='uniqueAux',macro_name='unique_cert',helper_prefix='uniquePack'))
  baseline=verify(self.input,self.schema,True);renamed=verify(self.input,schema,True)
  self.assertEqual(baseline['root_sha256'],renamed['root_sha256'])
  output=self.out/'renamed.lean';emit(self.input,schema,self.template,output,intern_names=True)
  text=output.read_text();self.assertIn('macro "unique_cert"',text);self.assertIn('private noncomputable def uniqueAux',text)

if __name__=='__main__':unittest.main()
