"""Check exact product regeneration and syntax preservation, without running Lean."""
from pathlib import Path
import json
import tempfile

from emit_private_certificate import emit
from verify_certificate_roundtrip import verify


def main():
    directory = Path(__file__).resolve().parent
    root = directory.parents[1]
    specs = json.loads((directory / 'certificates.json').read_text())
    assert specs, 'no certificates configured'
    with tempfile.TemporaryDirectory(prefix='balance-step-certificates-') as scratch:
        for spec in specs:
            name = spec['name']
            certificate = directory / f'{name}.input.lean'
            schema = directory / f'{name}-schema.json'
            template = directory / f'{name}-template.lean.in'
            output = Path(scratch) / f'{name}.lean'
            report = emit(certificate, schema, template, output,
                          intern_names=spec['intern_names'],
                          intern_kinds=spec.get('intern_kinds', False))
            assert output.read_bytes() == (root / spec['product']).read_bytes(), (
                f'{name}: regenerated product differs')
            structure = verify(certificate, schema, spec['intern_names'],
                               spec.get('intern_kinds', False))
            print(json.dumps({'name': name, 'product_sha256': report['output_sha256'],
                              'byte_identical': True, 'structure': structure}), flush=True)
    print('CERTIFICATE REPRODUCTION PASS; kernel verification is a separate build gate')


if __name__ == '__main__':
    main()
