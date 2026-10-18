"""Portable ordinary-Lean certificate packaging. Only Python stdlib is needed.
Requires sibling certificate_packaging.py; takes explicit input/schema/template/output.
Templates contain exactly one of each {{PACKAGING_PRELUDE}},
{{PRIVATE_DECLARATIONS}}, {{CERTIFICATE_TERM}}. No product paths are hardcoded.
"""
from pathlib import Path
import argparse, hashlib, json, re
from certificate_packaging import Packager, packaging_prelude, load_schema


def emit(certificate, schema_path, template_path, output, imports_path=None,intern_names=False,intern_kinds=False):
    schema,params,deps=load_schema(schema_path)
    template=Path(template_path).read_text()
    aux=schema.get('aux_prefix','packAux'); macro=schema.get('macro_name','pack_term')
    helper=schema.get('helper_prefix','pack')
    assert all(re.fullmatch('[A-Za-z][A-Za-z0-9_]*',s) for s in [aux,macro,helper]), 'invalid helper name'
    p=Packager(certificate,params,deps,aux_prefix=aux,macro_name=macro,intern_names=intern_names,intern_kinds=intern_kinds)
    rawsha=hashlib.sha256(p.source.encode()).hexdigest()
    assert rawsha==schema['certificate_sha256'], 'certificate differs from frozen schema input'
    actual_slots={n[1] for n in p.nodes if n[0]=='p'}
    assert actual_slots<=set(range(len(params))), ('parameter slot out of range', actual_slots)
    prelude=packaging_prelude(p).replace('packName',helper+'Name').replace('packSyntax',helper+'Syntax').replace('pack_term',macro)
    substitutions={
        '{{PACKAGING_PRELUDE}}':prelude,
        '{{PRIVATE_DECLARATIONS}}':p.declarations(),
        '{{CERTIFICATE_TERM}}':p.term(p.body,(1<<len(params))-1),
    }
    for marker,value in substitutions.items():
        assert template.count(marker)==1, ('template marker count',marker)
        template=template.replace(marker,value)
    if imports_path:
        mapping=json.loads(Path(imports_path).read_text())
        template='\n'.join('import '+mapping.get(line[7:],line[7:]) if line.startswith('import ') else line for line in template.split('\n'))
    assert not re.search(r'\b(?:sorry|admit|sorryAx|unsafe|native_decide|axiom)\b',template), 'forbidden source token'
    assert not re.search(r'^import (?:Lean|Std)(?:\.|\s|$)',template,re.M), 'consumer must use Init/project imports'
    target=Path(output);target.write_text(template)
    report=p.report()
    report.update({'output_sha256':hashlib.sha256(template.encode()).hexdigest(),'schema_sha256':hashlib.sha256(Path(schema_path).read_bytes()).hexdigest(),'template_sha256':hashlib.sha256(Path(template_path).read_bytes()).hexdigest(),'bytes':len(template.encode()),'imports':re.findall(r'^import .*$',template,re.M),'status':'generated; normal Lean kernel check still required'})
    target.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    for flag in ['certificate','schema','template','output']:ap.add_argument('--'+flag,required=True)
    ap.add_argument('--imports')
    group=ap.add_mutually_exclusive_group()
    group.add_argument('--intern-names',action='store_true')
    group.add_argument('--intern-kinds',action='store_true')
    a=ap.parse_args();print(json.dumps(emit(a.certificate,a.schema,a.template,a.output,a.imports,a.intern_names,a.intern_kinds)))
