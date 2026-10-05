"""Behavioral policy probes on temporary repositories, not production sources."""
import sys
sys.dont_write_bytecode = True
import tempfile
import unittest
from pathlib import Path
from check_distributed_audit import AuditInventoryError, check, parse_imports, parse_manifest

MODULES = [
    'Harmonia.Distributed', 'Harmonia.Distributed.Membership',
    'Harmonia.Distributed.Protocol', 'Harmonia.Distributed.Network',
    'Harmonia.Distributed.Semantics', 'Harmonia.Distributed.Properties',
    'Harmonia.Examples.Distributed', 'HarmoniaTests.DistributedMembership',
    'HarmoniaTests.DistributedNetwork', 'HarmoniaTests.DistributedSteps',
    'HarmoniaTests.DistributedTraces', 'HarmoniaTests.DistributedAxiomAudit',
]

class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for module in MODULES:
            self.write(module, 'namespace NamespaceEscape\nend NamespaceEscape\n')
        self.write('HarmoniaTests.AuditPolicy', self.manifest(MODULES))
        self.write('HarmoniaTests.AxiomAudit', 'import HarmoniaTests.AuditPolicy\n')
        self.write('HarmoniaTests.DistributedAxiomAudit',
                   'import ' + ' '.join(MODULES[:-1]) + ' -- many imports\nimport HarmoniaTests.AuditPolicy\n')
        self.write('HarmoniaTests.DistributedTraces', 'import Harmonia.Examples.Distributed\n')

    def write(self, module, source):
        path = self.root / (module.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)

    def manifest(self, modules):
        return 'def distributedSourceModules : Array Name := #[\n' + ',\n'.join('  `' + m for m in modules) + '\n]\n'

    def test_clean_coverage(self):
        self.assertEqual(check(self.root)['certified_modules'], 12)

    def test_multiline_imports_comments(self):
        self.assertEqual(parse_imports('import A B -- trailing\nimport\n C.D /- outer /- nested -/ -/ E.F\nnamespace X\n'),
                         ['A', 'B', 'C.D', 'E.F'])

    def test_multiline_manifest_comments(self):
        src = self.manifest(MODULES).replace('`Harmonia.Distributed,', '`Harmonia.Distributed, -- trailing\n/- nested /- comment -/ -/\n')
        self.assertEqual(parse_manifest(src), set(MODULES))

    def test_unknown_certified_file(self):
        self.write('HarmoniaTests.DistributedNewProbe', 'namespace Other\nend Other\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_unimported_namespace_escape(self):
        extra = 'Harmonia.Distributed.Escape'
        self.write(extra, 'namespace Different\ntheorem clean : 0 = 0 := rfl\nend Different\n')
        self.write('HarmoniaTests.AuditPolicy', self.manifest(MODULES + [extra]))
        with self.assertRaisesRegex(AuditInventoryError, 'unimported'):
            check(self.root)

    def test_unimported_unused_axiom(self):
        extra = 'Harmonia.Distributed.Hidden'
        self.write(extra, 'namespace Other\naxiom unused : Nat\nend Other\n')
        self.write('HarmoniaTests.AuditPolicy', self.manifest(MODULES + [extra]))
        with self.assertRaisesRegex(AuditInventoryError, 'unimported'):
            check(self.root)

    def test_distributed_adversarial_contamination(self):
        self.write('HarmoniaTests.DistributedRejection.Unused', 'axiom bad : Nat\n')
        self.write('Harmonia.Distributed.Protocol', 'import HarmoniaTests.DistributedRejection.Unused\n')
        with self.assertRaisesRegex(AuditInventoryError, 'adversarial'):
            check(self.root)

    def test_foundation_adversarial_contamination(self):
        self.write('HarmoniaTests.AuditRejection', 'axiom bad : Nat\n')
        self.write('HarmoniaTests.AxiomAudit', 'import HarmoniaTests.AuditRejection\n')
        with self.assertRaisesRegex(AuditInventoryError, 'adversarial'):
            check(self.root)

    def test_missing_import(self):
        self.write('Harmonia.Distributed.Protocol', 'import Harmonia.Distributed.Missing\n')
        with self.assertRaisesRegex(AuditInventoryError, 'missing'):
            check(self.root)

    def test_extra_manifest_entry(self):
        self.write('HarmoniaTests.AuditPolicy', self.manifest(MODULES + ['Missing.Module']))
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_malformed_manifest(self):
        self.write('HarmoniaTests.AuditPolicy', 'def distributedSourceModules := #[]\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_duplicate_manifest_entry(self):
        self.write('HarmoniaTests.AuditPolicy', self.manifest(MODULES + MODULES[:1]))
        with self.assertRaisesRegex(AuditInventoryError, 'duplicate'):
            check(self.root)

    def test_unknown_nested_certified_file(self):
        self.write('HarmoniaTests.DistributedExtra.Hidden', 'namespace Escape\nend Escape\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_unused_unsafe_source_axiom(self):
        self.write('Harmonia.Distributed.Protocol', 'unsafe axiom unused : Nat\n')
        with self.assertRaisesRegex(AuditInventoryError, 'forbidden certified source token axiom'):
            check(self.root)

    def test_protocol_global_argument(self):
        self.write('Harmonia.Distributed.Protocol',
                   'structure Protocol (M D V L P C K : Type) where\n'
                   '  react : State M D V L P → M → D → V → Prop\n'
                   '  crashReset : D → V → V\n')
        with self.assertRaisesRegex(AuditInventoryError, 'restricted input'):
            check(self.root)

    def test_forbidden_legacy_import(self):
        self.write('Harmonia.Core.Network', 'namespace Legacy\nend Legacy\n')
        self.write('Harmonia.Distributed.Protocol', 'import Harmonia.Core.Network\n')
        with self.assertRaisesRegex(AuditInventoryError, 'forbidden legacy'):
            check(self.root)

if __name__ == '__main__':
    unittest.main()
