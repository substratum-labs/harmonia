#!/usr/bin/env python3
"""Exact K-02 source, certified-root and rejection-root inventory."""
import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from check_kadmos_world_audit import check as check_world, application_manifest, target_roots
from check_distributed_audit import (AuditInventoryError, scrub, parse_manifest,
    module_name, import_closure, parse_imports)

TEST_TARGETS = (
    'kadmosGeneratedK02LexerTest',
    'kadmosGeneratedK02MachineTest',
    'kadmosGeneratedK02ExpressionParserTest',
    'kadmosGeneratedK02StatementParserTest',
    'kadmosGeneratedK02TSParserTest',
    'kadmosGeneratedK02SemanticsTest',
    'kadmosGeneratedK02ProgramParserTest',
    'kadmosGeneratedK02JSONTest',
    'kadmosGeneratedK02RegexTest',
    'kadmosGeneratedK02BalanceTSParseTest',
    'kadmosGeneratedK02BalancePythonParseTest',
    'kadmosGeneratedK02OrderTSParseTest',
    'kadmosGeneratedK02OrderPythonParseTest',
    'kadmosGeneratedK02CertificateTest',
    'kadmosGeneratedK02BalanceTSCertificateTest',
    'kadmosGeneratedK02BalancePythonCertificateTest',
    'kadmosGeneratedK02BalanceTSStepTest',
)
AUDIT_TARGET = 'kadmosGeneratedK02Audit'
REJECTION_TARGET = 'kadmosGeneratedK02AuditRejection'
AUDIT_ROOT = 'HarmoniaTests.KadmosGeneratedK02AxiomAudit'
REJECTION_ROOT = 'HarmoniaTests.KadmosGeneratedK02AuditRejection'
REJECTION_PREFIX = 'HarmoniaTests.KadmosGeneratedK02Rejection.'
FOUNDATION = {'Harmonia.Core.TransitionSystem', 'Harmonia.Core.Execution',
              'Harmonia.Core.Invariant', 'Harmonia.Core.Refinement'}


def trap(name):
    return name == REJECTION_ROOT or name.startswith(REJECTION_PREFIX)


def generated_manifest(source):
    clean = scrub(source)
    match = re.search(r'\bdef\s+kadmosGeneratedK02SourceModules\s*:\s*Array\s+Name\s*:=\s*#\[(.*?)\]', clean, re.S)
    if not match:
        raise AuditInventoryError('missing generated K-02 manifest')
    tail = clean[match.end():]
    next_decl = re.search(r'(?m)^(?:def|abbrev|theorem|lemma|instance|elab|namespace|end)\b', tail)
    if (tail[:next_decl.start()] if next_decl else tail).strip():
        raise AuditInventoryError('nonliteral generated K-02 manifest suffix')
    return parse_manifest('def distributedSourceModules : Array Name := #[' + match.group(1) + ']')


def check(root):
    root = Path(root).resolve()
    old = check_world(root)
    product_paths = set((root / 'Harmonia/Applications/Kadmos/Generated').rglob('*.lean'))
    test_paths = set((root / 'HarmoniaTests').glob('KadmosGeneratedK02*.lean'))
    product = {module_name(root, path) for path in product_paths}
    tests = {module_name(root, path) for path in test_paths if not trap(module_name(root, path))}
    inventory = product | tests
    policy = (root / 'HarmoniaTests/AuditPolicy.lean').read_text()
    manifest = generated_manifest(policy)
    if manifest != inventory:
        raise AuditInventoryError(f'generated K-02 manifest mismatch: missing={sorted(inventory-manifest)}, extra={sorted(manifest-inventory)}')
    lake = (root / 'lakefile.lean').read_text()
    roots = set()
    for target in TEST_TARGETS:
        named = target_roots(lake, target)
        if any(trap(name) for name in named):
            raise AuditInventoryError(f'{target} reaches a rejection root')
        roots.update(named)
    if roots != tests - {AUDIT_ROOT}:
        raise AuditInventoryError(f'generated K-02 test root mismatch: missing={sorted(tests-{AUDIT_ROOT}-roots)}, extra={sorted(roots-(tests-{AUDIT_ROOT}))}')
    audit_roots = target_roots(lake, AUDIT_TARGET)
    if set(audit_roots) != {'HarmoniaTests.AuditPolicy', AUDIT_ROOT}:
        raise AuditInventoryError('generated K-02 audit roots differ from exact pair')
    closure = import_closure(root, AUDIT_ROOT)
    if inventory - closure:
        raise AuditInventoryError(f'unimported generated K-02 source: {sorted(inventory-closure)}')
    if any(trap(name) for name in closure):
        raise AuditInventoryError('generated K-02 certified closure contains rejection source')
    old_manifest = application_manifest(policy)
    allowed = inventory | old_manifest | FOUNDATION | {'HarmoniaTests.AuditPolicy'}
    if closure - allowed:
        raise AuditInventoryError(f'unknown generated K-02 audit import: {sorted(closure-allowed)}')
    for target in (*TEST_TARGETS, AUDIT_TARGET):
        target_closure = set().union(*(import_closure(root, name) for name in target_roots(lake, target)))
        if any(trap(name) for name in target_closure):
            raise AuditInventoryError(f'{target} includes a rejection trap')
        if target_closure - closure:
            raise AuditInventoryError(f'{target} has unaudited source: {sorted(target_closure-closure)}')
    rejection_roots = set(target_roots(lake, REJECTION_TARGET))
    expected_rejections = {REJECTION_ROOT, REJECTION_PREFIX+'Unused', REJECTION_PREFIX+'Unsafe'}
    if rejection_roots != expected_rejections:
        raise AuditInventoryError('generated K-02 rejection roots differ from exact set')
    rejected_closure = set().union(*(import_closure(root, name) for name in rejection_roots))
    if any(name.startswith('HarmoniaTests.KadmosBridgeRejection.') for name in rejected_closure):
        raise AuditInventoryError('generated K-02 rejection target imports foreign Bridge trap')
    for name in inventory:
        path = root / (name.replace('.', '/') + '.lean')
        clean = scrub(path.read_text())
        bad = re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide)\b', clean)
        if bad:
            raise AuditInventoryError(f'forbidden generated K-02 token {bad.group(1)} in {name}')
    for path in product_paths:
        for imported in parse_imports(path.read_text()):
            if imported.startswith('HarmoniaTests.'):
                raise AuditInventoryError(f'product imports test source: {module_name(root,path)}')
    return {'generated_modules': len(product), 'generated_tests': len(tests),
            'certified_closure': len(closure), 'test_targets': len(TEST_TARGETS),
            'world_inventory': old['certified_application_modules']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        import unittest
        import test_kadmos_generated_k02_audit
        suite = unittest.defaultTestLoader.loadTestsFromModule(test_kadmos_generated_k02_audit)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    try:
        result = check(args.root)
    except (AuditInventoryError, OSError, subprocess.SubprocessError) as error:
        print(f'KADMOS GENERATED K-02 INVENTORY REJECTED: {error}', file=sys.stderr)
        return 1
    print(f'KADMOS GENERATED K-02 INVENTORY PASS: {result}')
    return 0


if __name__ == '__main__':
    sys.modules['check_kadmos_generated_k02_audit'] = sys.modules[__name__]
    raise SystemExit(main())
