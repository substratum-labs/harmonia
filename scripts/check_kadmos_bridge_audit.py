#!/usr/bin/env python3
"""T-395 bridge source/root inventory, composed with unchanged old policy."""
import argparse
import re
import sys
import unittest
from pathlib import Path
sys.dont_write_bytecode = True
from check_kadmos_world_audit import (check as check_old, AuditInventoryError,
    target_roots, root_closure, application_manifest, trap as old_trap, FOUNDATION)
from check_distributed_audit import scrub, module_name, module_path, import_closure

NEW_CERTIFIED=('kadmosBridgeSyntaxTest','kadmosBridgeCertificateTest',
               'kadmosBridgeFixturesTest','kadmosBridgeAudit')
NEW_REJECTION='kadmosBridgeAuditRejection'
EXPECTED={'Harmonia.Applications.Kadmos.Bridge.Syntax',
          'Harmonia.Applications.Kadmos.Bridge.Certificate',
          'Harmonia.Applications.Kadmos.Bridge.Fixtures',
          'HarmoniaTests.KadmosBridgeSyntax',
          'HarmoniaTests.KadmosBridgeCertificate',
          'HarmoniaTests.KadmosBridgeFixtures',
          'HarmoniaTests.KadmosBridgeAxiomAudit'}

def bridge_trap(name):
    return name=='HarmoniaTests.KadmosBridgeAuditRejection' or name.startswith('HarmoniaTests.KadmosBridgeRejection.')

def manifest(text):
    match=re.search(r'\bdef\s+kadmosBridgeSourceModules\s*:\s*Array\s+Name\s*:=\s*#\[(.*?)\]',scrub(text),re.S)
    if not match: raise AuditInventoryError('missing bridge literal manifest')
    rest=scrub(text)[match.end():]
    boundary=re.search(r'(?m)^(?:def|abbrev|theorem|lemma|instance|elab|namespace|end)\b',rest)
    if (rest[:boundary.start()] if boundary else rest).strip():
        raise AuditInventoryError('nonliteral bridge manifest suffix')
    return application_manifest('def kadmosWorldSourceModules : Array Name := #['+match.group(1)+']')

def check(root):
    root=Path(root).resolve()
    previous=check_old(root)
    product={module_name(root,p) for p in (root/'Harmonia/Applications/Kadmos/Bridge').rglob('*.lean')}
    tests={module_name(root,p) for p in (root/'HarmoniaTests').rglob('*.lean')
           if p.relative_to(root/'HarmoniaTests').parts[0].startswith('KadmosBridge')
           and not bridge_trap(module_name(root,p))}
    inventory=product|tests
    trap_sources={module_name(root,p) for p in (root/'HarmoniaTests/KadmosBridgeRejection').rglob('*.lean')}
    expected_traps={'HarmoniaTests.KadmosBridgeRejection.Unused','HarmoniaTests.KadmosBridgeRejection.Unsafe'}
    if trap_sources!=expected_traps:
        raise AuditInventoryError(f'bridge rejection disk mismatch: {sorted(trap_sources^expected_traps)}')
    if inventory!=EXPECTED:
        raise AuditInventoryError(f'bridge disk mismatch: missing={sorted(EXPECTED-inventory)}, extra={sorted(inventory-EXPECTED)}')
    declared=manifest((root/'HarmoniaTests/AuditPolicy.lean').read_text())
    if declared!=inventory: raise AuditInventoryError(f'bridge manifest mismatch: {sorted(inventory-declared)} {sorted(declared-inventory)}')
    closure=import_closure(root,'HarmoniaTests.KadmosBridgeAxiomAudit')
    if inventory-closure: raise AuditInventoryError(f'unimported bridge source: {sorted(inventory-closure)}')
    old_manifest=application_manifest((root/'HarmoniaTests/AuditPolicy.lean').read_text())
    allowed=old_manifest|inventory|FOUNDATION|{'HarmoniaTests.AuditPolicy'}
    if closure-allowed: raise AuditInventoryError(f'unknown bridge audit import: {sorted(closure-allowed)}')
    lake=(root/'lakefile.lean').read_text()
    for target in NEW_CERTIFIED:
        modules=root_closure(root,target_roots(lake,target))
        bad=sorted(n for n in modules if bridge_trap(n) or old_trap(n))
        if bad: raise AuditInventoryError(f'{target} adversarial closure: {bad}')
        if modules-closure: raise AuditInventoryError(f'{target} unaudited certified root: {sorted(modules-closure)}')
    rejected=root_closure(root,target_roots(lake,NEW_REJECTION))
    for name in rejected:
        if old_trap(name): raise AuditInventoryError(f'{NEW_REJECTION} foreign adversarial root: {name}')
        if bridge_trap(name) and name not in {'HarmoniaTests.KadmosBridgeAuditRejection',
              'HarmoniaTests.KadmosBridgeRejection.Unused','HarmoniaTests.KadmosBridgeRejection.Unsafe'}:
            raise AuditInventoryError(f'{NEW_REJECTION} foreign bridge trap: {name}')
    for name in inventory:
        text=module_path(root,name).read_text()
        bad=re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide)\b',scrub(text))
        if bad: raise AuditInventoryError(f'forbidden bridge source token {bad.group(1)} in {name}')
    return {'bridge_modules':len(inventory),'bridge_closure':len(closure),
            'certified_targets':len(NEW_CERTIFIED),'isolated_targets':1,'old':previous}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--self-test',action='store_true')
    a=p.parse_args()
    if a.self_test:
        import test_kadmos_bridge_audit
        suite=unittest.defaultTestLoader.loadTestsFromModule(test_kadmos_bridge_audit)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    try: result=check(a.root)
    except (AuditInventoryError,OSError) as exc:
        print('BRIDGE INVENTORY REJECTED:',exc,file=sys.stderr);return 1
    print('BRIDGE INVENTORY PASS:',result);return 0
if __name__=='__main__': raise SystemExit(main())
