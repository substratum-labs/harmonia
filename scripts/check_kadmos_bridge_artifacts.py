#!/usr/bin/env python3
"""T-395 exact tracked parser/artifact bytes; external parser provenance is separate."""
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
sys.dont_write_bytecode = True
S = 9007199254740991
PIN = 'fda8c6e42825b35afe5484a4af9d84d9d206ba9a'
class ArtifactError(ValueError): pass

def sha(data): return hashlib.sha256(data).hexdigest()
def read(path): return path.read_bytes()
def strict_json(data):
    def number(token):
        if token == '-0': raise ArtifactError('negative zero numeric token')
        value = int(token)
        if abs(value) > S: raise ArtifactError('unsafe numeric token')
        return value
    def pairs(items):
        result = {}
        for key,value in items:
            if key in result: raise ArtifactError(f'duplicate JSON key: {key}')
            result[key] = value
        return result
    def bad_float(token): raise ArtifactError(f'noninteger numeric token: {token}')
    try: return json.loads(data,parse_int=number,parse_float=bad_float,
                           parse_constant=bad_float,object_pairs_hook=pairs)
    except (ValueError,UnicodeError) as exc:
        if isinstance(exc,ArtifactError): raise
        raise ArtifactError(f'invalid JSON: {exc}') from exc

def object_keys(v,required,optional,label):
    if type(v) is not dict: raise ArtifactError(f'{label}: expected object')
    missing=set(required)-set(v)
    extra=set(v)-set(required)-set(optional)
    if missing or extra: raise ArtifactError(f'{label}: missing={sorted(missing)}, unknown={sorted(extra)}')
def string(v,label):
    if type(v) is not str: raise ArtifactError(f'{label}: expected string')
def integer(v,label):
    if type(v) is not int or abs(v)>S: raise ArtifactError(f'{label}: expected safe integer')
def array(v,label):
    if type(v) is not list: raise ArtifactError(f'{label}: expected array')
def validate_world(w):
    object_keys(w,('version','name','states','context','invariants','transitions'),('description',),'world')
    if w['version']!='kadmos.world.v0': raise ArtifactError('version')
    string(w['name'],'name')
    if 'description' in w: string(w['description'],'description')
    array(w['states'],'states')
    for st in w['states']:
        object_keys(st,('id',),('initial','terminal','description'),'state')
        string(st['id'],'state.id')
        for key in ('initial','terminal'):
            if key in st and type(st[key]) is not bool: raise ArtifactError(f'state.{key}: expected boolean')
        if 'description' in st: string(st['description'],'state.description')
    if type(w['context']) is not dict: raise ArtifactError('context: expected object')
    for name,v in w['context'].items():
        if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name) is None:
            raise ArtifactError(f'context name: {name}')
        object_keys(v,('type',),('min','max','default','unit'),'context entry')
        string(v['type'],'context.type')
        for key in ('min','max','default'):
            if key in v: integer(v[key],f'context.{key}')
        if 'unit' in v: string(v['unit'],'context.unit')
    array(w['invariants'],'invariants')
    for inv in w['invariants']:
        object_keys(inv,('id','predicate'),('description',),'invariant')
        string(inv['id'],'invariant.id'); string(inv['predicate'],'invariant.predicate')
        if 'description' in inv: string(inv['description'],'invariant.description')
    array(w['transitions'],'transitions')
    for tr in w['transitions']:
        object_keys(tr,('id','from','to','guard','effects','directive'),(),'transition')
        for key in ('id','from','to'): string(tr[key],f'transition.{key}')
        if type(tr['guard']) not in (str,bool): raise ArtifactError('transition.guard type')
        array(tr['effects'],'effects')
        for effect in tr['effects']: string(effect,'effect')
        if tr['directive'] is not None: string(tr['directive'],'directive')

def check_artifacts(root):
    root=Path(root).resolve();base=root/'conformance/kadmos-ir-bridge'
    profile_bytes=read(base/'profiles.json'); parsed_bytes=read(base/'parsed.json')
    vectors_bytes=read(base/'evaluate-vectors.json'); provenance=strict_json(read(base/'provenance.json'))
    profiles=strict_json(profile_bytes); parsed=strict_json(parsed_bytes); vectors=strict_json(vectors_bytes)
    object_keys(profiles,('balance','order_phase'),(),'profiles')
    object_keys(parsed,('balance','order_phase'),(),'parsed')
    for id,fields in profiles.items():
        array(fields,f'profile {id}')
        if len(fields)!=len(set(fields)): raise ArtifactError('duplicate profile field')
        for f in fields:
            string(f,'profile field')
            if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',f) is None:
                raise ArtifactError('profile field spelling')
    for world in parsed.values(): validate_world(world)
    array(vectors,'evaluate vectors')
    for v in vectors:
        object_keys(v,('id','expression','environment','outcome'),(),'vector')
        string(v['id'],'vector.id')
        if type(v['expression']) not in (str,bool): raise ArtifactError('vector expression')
        if type(v['environment']) is not dict: raise ArtifactError('vector environment')
        if type(v['outcome']) is not dict or set(v['outcome']) not in ({'value'},{'error'}):
            raise ArtifactError('vector outcome')
    object_keys(provenance,('kadmosCommit','exporterVersion','checkerVersion','yamlSha256',
      'profilesSha256','parsedSha256','evaluateVectorsSha256','fixturesLeanSha256','parserCommand'),(),'provenance')
    if provenance['kadmosCommit']!=PIN or provenance['exporterVersion']!='1' or provenance['checkerVersion']!='1':
        raise ArtifactError('version or commit drift')
    expected={'profilesSha256':sha(profile_bytes),'parsedSha256':sha(parsed_bytes),
      'evaluateVectorsSha256':sha(vectors_bytes),
      'fixturesLeanSha256':sha(read(root/'Harmonia/Applications/Kadmos/Bridge/Fixtures.lean'))}
    yamlhash={id:sha(read(base/(id+'.world.yaml'))) for id in ('balance','order_phase')}
    if provenance['yamlSha256']!=yamlhash: raise ArtifactError('YAML hash drift')
    for k,v in expected.items():
        if provenance[k]!=v: raise ArtifactError(f'{k} drift')
    canonical=json.dumps(parsed,ensure_ascii=False,separators=(',',':')).encode()+b'\n'
    if canonical!=parsed_bytes: raise ArtifactError('parsed JSON byte drift')
    with tempfile.TemporaryDirectory(prefix='t395-artifact-') as tmp:
        cmd=['node',str(root/'tools/export_kadmos_ir_bridge.mjs'),'--from-parsed',str(base/'parsed.json'),
             '--out',tmp,'--check']
        result=subprocess.run(cmd,cwd=root,capture_output=True,text=True)
        if result.returncode: raise ArtifactError(f'exporter drift: {result.stderr.strip()}')
    return {'parsedSha256':expected['parsedSha256'],'fixturesLeanSha256':expected['fixturesLeanSha256']}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    if args.self_test:
        import unittest, test_kadmos_bridge_audit
        suite=unittest.defaultTestLoader.loadTestsFromModule(test_kadmos_bridge_audit)
        sys.exit(0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1)
    try: print('BRIDGE ARTIFACT PASS:',check_artifacts(args.root))
    except ArtifactError as exc: print('BRIDGE ARTIFACT REJECTED:',exc,file=sys.stderr);sys.exit(1)
