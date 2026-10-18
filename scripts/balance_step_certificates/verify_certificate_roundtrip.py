"""Independent structural acceptance test; takes explicit certificate/schema paths.
This verifies exact Syntax content and parameter application lists, not kernel validity.
"""
from pathlib import Path
import argparse, functools, hashlib, json
from certificate_packaging import Packager,load_schema

def verify(certificate,schema_path,intern_names=False,intern_kinds=False):
 schema,params,deps=load_schema(schema_path)
 p=Packager(certificate,params,deps,aux_prefix=schema.get('aux_prefix','packAux'),intern_names=intern_names,intern_kinds=intern_kinds)
 assert hashlib.sha256(p.source.encode()).hexdigest()==schema['certificate_sha256']
 def digest(x):return hashlib.sha256(json.dumps(x,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
 @functools.cache
 def original(i):
  n=p.nodes[i]
  if n[0]=='n':return digest(['n',p.names[n[1]],[original(c) for c in n[2]]])
  if n[0]=='i':return digest(['i',p.names[n[1]]])
  return digest(list(n))
 def check(root):
  rows=json.loads(p.table(root)).split('\n');hashes=[];depths=[]
  for row in rows:
   k,payload=row[0],row[1:]
   if k=='n':
    name,cs=payload.split(':');cs=list(map(int,filter(None,cs.split(','))))
    if intern_names:name=p.names[int(name)]
    if intern_kinds:name=p.kind_names[int(name)]
    assert all(c<len(hashes) for c in cs)
    value=['n',name,[hashes[c] for c in cs]];depth=1+max([depths[c] for c in cs],default=0)
   elif k=='g':
    name,args=payload.split(':');index=int(name if intern_names or intern_kinds else name.removeprefix(p.aux_prefix));original_name=p.entries[index][0]
    actual=list(map(int,filter(None,args.split(','))))
    assert actual==[j for j in range(len(params)) if p.masks[original_name]>>j&1]
    value=['i',p.names[original_name]];depth=3 if actual else 1
   elif k=='p':value=['p',int(payload)];depth=1
   elif k=='i' and intern_names:value=['i',p.names[int(payload)]];depth=1
   else:value=[k,payload];depth=1
   hashes.append(digest(value));depths.append(depth)
  assert hashes[-1]==original(root), ('syntax content changed',root)
  return depths[-1]
 maximum=max(check(rhs) for _,rhs in p.entries);check(p.body)
 return {'status':'structural round-trip PASS; not kernel acceptance','intern_names':intern_names,'intern_kinds':intern_kinds,'entries_checked':len(p.entries),'maximum_rewritten_rhs_depth':maximum,'root_sha256':original(p.body),'certificate_sha256':hashlib.sha256(p.source.encode()).hexdigest()}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--certificate',required=True);ap.add_argument('--schema',required=True);ap.add_argument('--output',required=True)
 group=ap.add_mutually_exclusive_group();group.add_argument('--intern-names',action='store_true');group.add_argument('--intern-kinds',action='store_true');a=ap.parse_args()
 report=verify(a.certificate,a.schema,a.intern_names,a.intern_kinds);Path(a.output).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
