#!/usr/bin/env python3
"""T-393 exact application inventory and directional certified-root isolation."""
import argparse
import re
import subprocess
import sys
import unittest
from pathlib import Path
sys.dont_write_bytecode = True
from check_distributed_audit import (AuditInventoryError, scrub, parse_imports, parse_manifest,
    module_name, module_path, import_closure, adversarial, check as check_distributed)

CERTIFIED_TARGETS = ('foundationsTest', 'foundationsAudit', 'distributedTest',
                     'distributedAudit', 'kadmosWorldTest', 'kadmosWorldAudit')
REJECTION_TARGETS = ('foundationsAuditRejection', 'distributedAuditRejection', 'kadmosWorldAuditRejection')
MANDATORY = {'Harmonia.Applications.Kadmos', 'Harmonia.Applications.Kadmos.World',
    'Harmonia.Applications.Kadmos.Interpreter', 'Harmonia.Applications.Kadmos.System',
    'Harmonia.Applications.Kadmos.Balance', 'HarmoniaTests.KadmosWorldIR',
    'HarmoniaTests.KadmosWorldInterpreter', 'HarmoniaTests.KadmosWorldBalance',
    'HarmoniaTests.KadmosWorldAxiomAudit'}
FOUNDATION = {'Harmonia.Core.TransitionSystem', 'Harmonia.Core.Execution',
              'Harmonia.Core.Invariant', 'Harmonia.Core.Refinement'}

def trap(name):
    return adversarial(name) or name == 'HarmoniaTests.KadmosWorldAuditRejection' or name.startswith('HarmoniaTests.KadmosWorldRejection.')

def name_array(body):
    # Reuse the existing strict lexical array parser without altering its policy.
    return parse_manifest('def distributedSourceModules : Array Name := #[' + body + ']')

def literal_end(clean, end, label):
    # A literal array must be the entire declaration RHS, not a prefix of ++/push.
    tail = clean[end:]
    boundary = re.search(r'(?m)^(?:def|abbrev|theorem|lemma|instance|elab|namespace|end|lean_lib|lean_exe|package|import)\b', tail)
    suffix = tail[:boundary.start()] if boundary else tail
    if suffix.strip():
        raise AuditInventoryError(f'nonliteral {label} array suffix')

def application_manifest(source):
    match = re.search(r'\bdef\s+kadmosWorldSourceModules\s*:\s*Array\s+Name\s*:=\s*#\[(.*?)\]', scrub(source), re.S)
    if not match:
        raise AuditInventoryError('missing or malformed Kadmos manifest')
    literal_end(scrub(source), match.end(), "Kadmos manifest")
    return name_array(match.group(1))

def target_roots(source, target):
    clean = scrub(source)
    matches = list(re.finditer(r'\blean_lib\s+' + re.escape(target) + r'\s+where\s+roots\s*:=\s*#\[(.*?)\]', clean, re.S))
    if len(matches) != 1:
        raise AuditInventoryError(f'missing or malformed target roots: {target}')
    literal_end(clean, matches[0].end(), target)
    roots = name_array(matches[0].group(1))
    if not roots:
        raise AuditInventoryError(f'empty target roots: {target}')
    return roots

def root_closure(root, names):
    result = set()
    for name in names:
        result |= import_closure(root, name)
    return result

def check(root):
    root = Path(root).resolve()
    original = check_distributed(root)
    product = set((root / 'Harmonia' / 'Applications').rglob('*.lean'))
    probes = {p for p in (root / 'HarmoniaTests').rglob('*.lean')
              if p.relative_to(root / 'HarmoniaTests').parts[0].startswith('KadmosWorld')}
    for p in product:
        name = module_name(root, p)
        if name != 'Harmonia.Applications.Kadmos' and not name.startswith('Harmonia.Applications.Kadmos.'):
            raise AuditInventoryError(f'unknown application source: {name}')
    inventory = {module_name(root, p) for p in product | probes if not trap(module_name(root, p))}
    if not MANDATORY <= inventory:
        raise AuditInventoryError(f'missing required application source: {sorted(MANDATORY-inventory)}')
    manifest = application_manifest(module_path(root, 'HarmoniaTests.AuditPolicy').read_text())
    if manifest != inventory:
        raise AuditInventoryError(f'Kadmos manifest mismatch: missing={sorted(inventory-manifest)}, extra={sorted(manifest-inventory)}')
    closure = import_closure(root, 'HarmoniaTests.KadmosWorldAxiomAudit')
    if inventory - closure:
        raise AuditInventoryError(f'unimported certified application source: {sorted(inventory-closure)}')
    unexpected = closure - inventory - FOUNDATION - {'HarmoniaTests.AuditPolicy'}
    if unexpected:
        raise AuditInventoryError(f'unknown certified application import: {sorted(unexpected)}')
    audit_closures = {
        'foundation': import_closure(root, 'HarmoniaTests.AxiomAudit'),
        'distributed': import_closure(root, 'HarmoniaTests.DistributedAxiomAudit'),
        'kadmos': closure,
    }
    lake = (root / 'lakefile.lean').read_text()
    for target in CERTIFIED_TARGETS:
        modules = root_closure(root, target_roots(lake, target))
        traps = sorted(n for n in modules if trap(n))
        if traps:
            raise AuditInventoryError(f'{target} adversarial closure: {traps}')
        family = 'foundation' if target.startswith('foundations') else 'distributed' if target.startswith('distributed') else 'kadmos'
        unaudited = modules - audit_closures[family]
        if unaudited:
            raise AuditInventoryError(f'unaudited certified root in {target}: {sorted(unaudited)}')
    for target in REJECTION_TARGETS:
        # Directional: its own traps/shared tooling are allowed; certified roots above
        # must never reach them. Validate that even isolated roots resolve completely.
        modules = root_closure(root, target_roots(lake, target))
        for name in modules:
            if trap(name):
                own = (target == 'foundationsAuditRejection' and name == 'HarmoniaTests.AuditRejection') or (
                    target == 'distributedAuditRejection' and (name == 'HarmoniaTests.DistributedAuditRejection' or name.startswith('HarmoniaTests.DistributedRejection.'))) or (
                    target == 'kadmosWorldAuditRejection' and (name == 'HarmoniaTests.KadmosWorldAuditRejection' or name.startswith('HarmoniaTests.KadmosWorldRejection.')))
                if not own:
                    raise AuditInventoryError(f'{target} foreign adversarial root: {name}')
    for name in inventory:
        source = module_path(root, name).read_text()
        bad = re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide)\b', scrub(source))
        if bad:
            raise AuditInventoryError(f'forbidden certified source token {bad.group(1)} in {name}')
    for p in product:
        for name in import_closure(root, module_name(root, p)):
            if name not in FOUNDATION and name not in inventory:
                raise AuditInventoryError(f'forbidden product import: {name}')
            if name.startswith('HarmoniaTests.'):
                raise AuditInventoryError(f'forbidden product test/audit import: {name}')
        for name in parse_imports(p.read_text()):
            if name != 'Init' and not name.startswith('Init.') and name not in FOUNDATION and not name.startswith('Harmonia.Applications.Kadmos'):
                raise AuditInventoryError(f'forbidden product dependency: {name}')
    return {'certified_application_modules': len(inventory), 'application_closure': len(closure),
            'certified_targets': len(CERTIFIED_TARGETS), 'isolated_targets': len(REJECTION_TARGETS),
            'distributed_inventory': original}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        import test_kadmos_world_audit
        suite = unittest.defaultTestLoader.loadTestsFromModule(test_kadmos_world_audit)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    try:
        result = check(args.root)
    except (AuditInventoryError, OSError, subprocess.SubprocessError) as exc:
        print(f'KADMOS INVENTORY REJECTED: {exc}', file=sys.stderr)
        return 1
    print(f'KADMOS INVENTORY PASS: {result}')
    return 0

if __name__ == '__main__':
    sys.modules['check_kadmos_world_audit'] = sys.modules[__name__]
    raise SystemExit(main())
