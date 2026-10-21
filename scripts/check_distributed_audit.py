#!/usr/bin/env python3
"""Check disk/source coverage and keep adversarial modules out of certified roots."""
import argparse
import functools
import re
import subprocess
import sys
import unittest
from pathlib import Path
sys.dont_write_bytecode = True

class AuditInventoryError(ValueError):
    pass

MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
BOUNDARIES = {'import', 'prelude', 'namespace', 'end', 'open', 'def', 'abbrev',
              'theorem', 'lemma', 'axiom', 'structure', 'inductive', 'universe',
              'variable', 'section', 'set_option', 'instance', 'example', 'private',
              'protected', 'noncomputable', 'unsafe', 'elab', 'syntax', 'macro'}
ADVERSARIAL = {'HarmoniaTests.AuditRejection', 'HarmoniaTests.DistributedAuditRejection'}

def scrub(source):
    """Blank nested Lean comments and string literals while preserving newlines."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            stop = source.find('\n', i)
            if stop == -1: stop = len(source)
            out.extend(' ' * (stop - i)); i = stop
        elif source.startswith("'\"'", i):
            # Lean's quote character literal is not the start of a string.
            out.extend('   '); i += 3
        elif source[i] == '"':
            out.append(' '); i += 1
            closed = False
            while i < len(source):
                ch = source[i]; out.append('\n' if ch == '\n' else ' '); i += 1
                if ch == '\\' and i < len(source):
                    out.append(' '); i += 1
                elif ch == '"':
                    closed = True; break
            if not closed: raise AuditInventoryError('unterminated Lean string')
        else:
            out.append(source[i]); i += 1
    if depth: raise AuditInventoryError('unterminated Lean comment')
    return ''.join(out)

def parse_imports(source):
    tokens = re.findall(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*|[^\s]', scrub(source))
    result, i = [], 0
    if tokens[:1] == ['prelude']: i = 1
    while i < len(tokens) and tokens[i] == 'import':
        i += 1
        begin = i
        while i < len(tokens) and MODULE.fullmatch(tokens[i]) and tokens[i] not in BOUNDARIES:
            result.append(tokens[i]); i += 1
        if begin == i: raise AuditInventoryError('empty import declaration')
    return result

def parse_manifest(source):
    clean = scrub(source)
    match = re.search(r'\bdef\s+distributedSourceModules\s*:\s*Array\s+Name\s*:=\s*#\[(.*?)\]', clean, re.S)
    if not match: raise AuditInventoryError('missing or malformed distributed source manifest')
    body = match.group(1)
    names = re.findall(r'`([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)', body)
    residue = re.sub(r'`[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', '', body)
    if re.sub(r'[\s,]', '', residue): raise AuditInventoryError('malformed manifest entry')
    if len(names) != len(set(names)): raise AuditInventoryError('duplicate manifest entry')
    return set(names)

def module_path(root, name):
    return root / (name.replace('.', '/') + '.lean')

def module_name(root, path):
    return '.'.join(path.relative_to(root).with_suffix('').parts)

def adversarial(name):
    return name in ADVERSARIAL or name.startswith('HarmoniaTests.DistributedRejection.')

@functools.lru_cache(maxsize=1)
def lean_prefix():
    proc = subprocess.run(['lean', '--print-prefix'], capture_output=True, text=True, check=True)
    return Path(proc.stdout.strip())

def import_closure(root, initial):
    seen, work = set(), [initial]
    while work:
        name = work.pop()
        if name in seen: continue
        path = module_path(root, name)
        if not path.is_file():
            if name.startswith(('Harmonia.', 'HarmoniaTests.')) or name in {'Harmonia', 'HarmoniaTests'}:
                raise AuditInventoryError(f'missing project import {name}')
            external = lean_prefix() / 'lib' / 'lean' / (name.replace('.', '/') + '.olean')
            if not external.is_file(): raise AuditInventoryError(f'missing external import {name}')
            continue
        seen.add(name)
        work.extend(parse_imports(path.read_text()))
    return seen

def check(root):
    root = Path(root).resolve()
    product = set((root / 'Harmonia' / 'Distributed').rglob('*.lean'))
    product.add(root / 'Harmonia' / 'Distributed.lean')
    product.add(root / 'Harmonia' / 'Examples' / 'Distributed.lean')
    probes = {path for path in (root / 'HarmoniaTests').rglob('*.lean')
              if path.relative_to(root / 'HarmoniaTests').parts[0].startswith('Distributed')}
    inventory = {module_name(root, path) for path in product | probes if not adversarial(module_name(root, path))}
    for path in product:
        if not path.is_file(): raise AuditInventoryError(f'missing required certified file {path.name}')
    manifest = parse_manifest(module_path(root, 'HarmoniaTests.AuditPolicy').read_text())
    if manifest != inventory:
        raise AuditInventoryError(f'manifest mismatch: missing={sorted(inventory-manifest)}, extra={sorted(manifest-inventory)}')
    closure = import_closure(root, 'HarmoniaTests.DistributedAxiomAudit')
    foundation = import_closure(root, 'HarmoniaTests.AxiomAudit')
    for label, modules in [('distributed', closure), ('foundation', foundation)]:
        traps = sorted(n for n in modules if adversarial(n))
        if traps: raise AuditInventoryError(f'{label} adversarial imports: {traps}')
    absent = inventory - closure
    if absent: raise AuditInventoryError(f'unimported certified source modules: {sorted(absent)}')
    # Example source edge is required independently of its declaration namespace.
    traces_imports = parse_imports(module_path(root, 'HarmoniaTests.DistributedTraces').read_text())
    if 'Harmonia.Examples.Distributed' not in traces_imports:
        raise AuditInventoryError('DistributedTraces must import the example source module')
    forbidden = {'Harmonia.Core.Event', 'Harmonia.Core.Network', 'Harmonia.Core.SmallStep'}
    for name in inventory:
        source = module_path(root, name).read_text()
        bad = re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide)\b', scrub(source))
        if bad: raise AuditInventoryError(f'forbidden certified source token {bad.group(1)} in {name}')
    for name in product:
        for imported in import_closure(root, module_name(root, name)):
            if imported in forbidden or imported.startswith(('Harmonia.Protocols.', 'Harmonia.DSL.', 'Harmonia.SMT.', 'Harmonia.Gatekeeper.')):
                raise AuditInventoryError(f'forbidden legacy import {imported}')
    # The local signature is deliberately fixed: no global argument can enter react.
    protocol = scrub(module_path(root, 'Harmonia.Distributed.Protocol').read_text())
    if 'structure Protocol' in protocol:
        match = re.search(r'\breact\s*:\s*(.*?)\n\s*crashReset\s*:', protocol, re.S)
        expected = 'M → D → V → Input M L P C K → D → V → List (Outgoing M L P) → Prop'
        if not match or ' '.join(match.group(1).split()) != expected:
            raise AuditInventoryError('Protocol.react violates restricted input signature')
    return {'certified_modules': len(inventory), 'distributed_closure': len(closure), 'foundation_closure': len(foundation)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    if args.self_test:
        import test_distributed_audit
        suite = unittest.defaultTestLoader.loadTestsFromModule(test_distributed_audit)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    try:
        result = check(args.root)
    except (AuditInventoryError, OSError, subprocess.SubprocessError) as exc:
        print(f'INVENTORY REJECTED: {exc}', file=sys.stderr)
        return 1
    print(f'INVENTORY PASS: {result}')
    return 0

if __name__ == '__main__':
    # Share the CLI module with its self-tests without loading it twice.
    sys.modules['check_distributed_audit'] = sys.modules[__name__]
    raise SystemExit(main())
