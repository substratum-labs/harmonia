"""Application policy mutations in disposable repositories, never product files."""
import sys
sys.dont_write_bytecode = True
import unittest
import test_distributed_audit as legacy
from check_kadmos_world_audit import (check, AuditInventoryError, MANDATORY,
    CERTIFIED_TARGETS, REJECTION_TARGETS, application_manifest, target_roots)

class KadmosInventoryTests(unittest.TestCase):
    write = legacy.InventoryTests.write
    manifest = legacy.InventoryTests.manifest

    def setUp(self):
        legacy.InventoryTests.setUp(self)
        self.modules = sorted(MANDATORY)
        for name in self.modules:
            self.write(name, 'namespace Escaped\ntheorem marker : True := True.intro\nend Escaped\n')
        self.write('HarmoniaTests.KadmosWorldAxiomAudit', 'import ' + ' '.join(n for n in self.modules if not n.endswith('AxiomAudit')) + '\nimport HarmoniaTests.AuditPolicy\n')
        self.policy()
        for name in ('Foundations', 'InvariantProbes', 'RefinementProbes'):
            self.write('HarmoniaTests.' + name, 'namespace Clean\nend Clean\n')
        self.write('HarmoniaTests.AxiomAudit', 'import HarmoniaTests.AuditPolicy HarmoniaTests.Foundations HarmoniaTests.InvariantProbes HarmoniaTests.RefinementProbes\n')
        self.roots = {
            'foundationsTest': ['HarmoniaTests.Foundations','HarmoniaTests.InvariantProbes','HarmoniaTests.RefinementProbes'],
            'foundationsAudit': ['HarmoniaTests.AuditPolicy','HarmoniaTests.AxiomAudit'],
            'distributedTest': ['HarmoniaTests.DistributedMembership','HarmoniaTests.DistributedNetwork','HarmoniaTests.DistributedSteps','HarmoniaTests.DistributedTraces'],
            'distributedAudit': ['HarmoniaTests.AuditPolicy','HarmoniaTests.DistributedAxiomAudit'],
            'kadmosWorldTest': ['HarmoniaTests.KadmosWorldIR','HarmoniaTests.KadmosWorldInterpreter','HarmoniaTests.KadmosWorldBalance'],
            'kadmosWorldAudit': ['HarmoniaTests.AuditPolicy','HarmoniaTests.KadmosWorldAxiomAudit'],
            'foundationsAuditRejection': ['HarmoniaTests.AuditRejection'],
            'distributedAuditRejection': ['HarmoniaTests.DistributedAuditRejection'],
            'kadmosWorldAuditRejection': ['HarmoniaTests.KadmosWorldAuditRejection'],
        }
        for name in ('HarmoniaTests.AuditRejection','HarmoniaTests.DistributedAuditRejection','HarmoniaTests.KadmosWorldAuditRejection'):
            self.write(name, 'import HarmoniaTests.AuditPolicy\n')
        for family in ('DistributedRejection', 'KadmosWorldRejection'):
            self.write('HarmoniaTests.'+family+'.Unused', 'namespace Escape\naxiom unused : Nat\nend Escape\n')
        self.write('HarmoniaTests.DistributedAuditRejection', 'import HarmoniaTests.AuditPolicy HarmoniaTests.DistributedRejection.Unused\n')
        self.write('HarmoniaTests.KadmosWorldAuditRejection', 'import HarmoniaTests.AuditPolicy HarmoniaTests.KadmosWorldRejection.Unused\n')
        self.lake()

    def policy(self, modules=None):
        src = self.manifest(legacy.MODULES)
        src += 'def kadmosWorldSourceModules : Array Name := #[' + ','.join('`'+n for n in (modules or self.modules)) + ']\n'
        self.write('HarmoniaTests.AuditPolicy', src)

    def lake(self):
        src = ''.join('lean_lib '+t+' where\n  roots := #['+','.join('`'+n for n in ns)+']\n' for t,ns in self.roots.items())
        (self.root/'lakefile.lean').write_text(src)

    def test_clean_and_isolated_roots(self):
        result = check(self.root)
        self.assertEqual(result['certified_application_modules'], 9)
        self.assertEqual(result['certified_targets'], 6)
        self.assertEqual(result['isolated_targets'], 3)

    def test_new_application_is_not_silently_excluded(self):
        self.write('Harmonia.Applications.Kadmos.Hidden', 'namespace Escape\naxiom unused : Nat\nend Escape\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_unknown_nested_probe(self):
        self.write('HarmoniaTests.KadmosWorldExtra.Hidden', 'namespace Escape\nend Escape\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_unknown_domain_module(self):
        self.write('Harmonia.Applications.Other', 'namespace Escape\nend Escape\n')
        with self.assertRaisesRegex(AuditInventoryError, 'unknown application'):
            check(self.root)

    def test_unimported_namespace_escape(self):
        extra = 'Harmonia.Applications.Kadmos.Escape'
        self.write(extra, 'namespace Foreign\ntheorem clean : True := True.intro\nend Foreign\n')
        self.policy(self.modules+[extra])
        with self.assertRaisesRegex(AuditInventoryError, 'unimported'):
            check(self.root)

    def test_unused_normal_and_unsafe_axioms(self):
        for prefix in ('', 'unsafe '):
            with self.subTest(prefix=prefix):
                self.write('Harmonia.Applications.Kadmos.World', 'namespace Foreign\n'+prefix+'axiom unused : Nat\nend Foreign\n')
                with self.assertRaisesRegex(AuditInventoryError, 'forbidden certified source token axiom'):
                    check(self.root)

    def test_forbidden_proof_tokens(self):
        for token in ('sorry','admit','sorryAx','native_decide'):
            with self.subTest(token=token):
                self.write('HarmoniaTests.KadmosWorldIR', 'theorem bad : True := '+token+'\n')
                with self.assertRaisesRegex(AuditInventoryError, 'forbidden certified source token'):
                    check(self.root)

    def test_comments_and_strings_are_not_proofs(self):
        self.write('Harmonia.Applications.Kadmos.World', '-- axiom sorry\n/- native_decide /- nested -/ -/\ndef text := "sorryAx"\n')
        check(self.root)

    def test_missing_project_import(self):
        self.write('Harmonia.Applications.Kadmos.World', 'import Harmonia.Applications.Kadmos.Absent\n')
        with self.assertRaisesRegex(AuditInventoryError, 'missing project import'):
            check(self.root)

    def test_missing_external_import(self):
        self.write('Harmonia.Applications.Kadmos.World', 'import DoesNotExist.Installed\n')
        with self.assertRaisesRegex(AuditInventoryError, 'missing external import'):
            check(self.root)

    def test_manifest_extra_duplicate_and_malformed(self):
        for src in ('def kadmosWorldSourceModules := #[]',
                    'def kadmosWorldSourceModules : Array Name := #[`A,`A]',
                    'def kadmosWorldSourceModules : Array Name := #[`A + x]'):
            with self.subTest(src=src), self.assertRaises(AuditInventoryError):
                application_manifest(src)
        self.policy(self.modules+['Missing.Module'])
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_multiline_manifest_and_imports(self):
        source = self.manifest(self.modules).replace('distributedSourceModules','kadmosWorldSourceModules')
        source = source.replace('`Harmonia.Applications.Kadmos,','`Harmonia.Applications.Kadmos, -- trailing\n/- nested /- comment -/ -/\n')
        self.assertEqual(application_manifest(source), set(self.modules))
        self.write('HarmoniaTests.KadmosWorldAxiomAudit', 'import\n'+'\n'.join(n+' -- after' for n in self.modules if not n.endswith('AxiomAudit'))+'\nimport HarmoniaTests.AuditPolicy\n')
        check(self.root)

    def test_each_certified_target_rejects_adversarial_root(self):
        for target in CERTIFIED_TARGETS:
            original = self.roots[target][:]
            with self.subTest(target=target):
                self.roots[target].append('HarmoniaTests.KadmosWorldRejection.Unused')
                self.lake()
                with self.assertRaisesRegex(AuditInventoryError, 'adversarial closure'):
                    check(self.root)
                self.roots[target] = original
        self.lake()

    def test_each_certified_target_rejects_import_contamination(self):
        for target in CERTIFIED_TARGETS:
            name = self.roots[target][-1]
            path = self.root/(name.replace('.','/')+'.lean')
            original = path.read_text()
            with self.subTest(target=target):
                path.write_text('import HarmoniaTests.KadmosWorldRejection.Unused\n'+original)
                with self.assertRaises(AuditInventoryError):
                    check(self.root)
                path.write_text(original)

    def test_rejection_roots_allow_shared_tooling_but_not_foreign_traps(self):
        check(self.root)
        self.roots['kadmosWorldAuditRejection'].append('HarmoniaTests.DistributedRejection.Unused')
        self.lake()
        with self.assertRaisesRegex(AuditInventoryError, 'foreign adversarial'):
            check(self.root)

    def test_malformed_unknown_and_duplicate_roots(self):
        for body in ('#[]', '#[`Missing.Root]', '#[`HarmoniaTests.KadmosWorldIR,`HarmoniaTests.KadmosWorldIR]', 'otherFunction'):
            self.lake()
            p = self.root/'lakefile.lean'
            src = p.read_text()
            import re
            src = re.sub(r'lean_lib kadmosWorldTest where\n  roots := #\[.*?\]', 'lean_lib kadmosWorldTest where\n  roots := '+body, src)
            p.write_text(src)
            with self.subTest(body=body), self.assertRaises(AuditInventoryError):
                check(self.root)

    def test_outside_inventory_import_and_root_cannot_escape(self):
        name = 'HarmoniaTests.OutsideKadmosInventory'
        self.write(name, 'namespace Outside\naxiom unused : Nat\nend Outside\n')
        p = self.root/'HarmoniaTests/KadmosWorldIR.lean'
        original = p.read_text()
        p.write_text('import '+name+'\n'+original)
        with self.assertRaisesRegex(AuditInventoryError, 'unknown certified application import'):
            check(self.root)
        p.write_text(original)
        self.roots['kadmosWorldTest'].append(name)
        self.lake()
        with self.assertRaisesRegex(AuditInventoryError, 'unaudited certified root'):
            check(self.root)

    def test_missing_required_disk_source(self):
        (self.root/'Harmonia/Applications/Kadmos/World.lean').unlink()
        with self.assertRaisesRegex(AuditInventoryError, 'missing required application source'):
            check(self.root)

    def test_array_suffixes_are_not_silently_excluded(self):
        p = self.root/'lakefile.lean'
        p.write_text(p.read_text().replace(
            '`HarmoniaTests.KadmosWorldBalance]',
            '`HarmoniaTests.KadmosWorldBalance] ++ #[`HarmoniaTests.KadmosWorldRejection.Unused]'))
        with self.assertRaisesRegex(AuditInventoryError, 'nonliteral'):
            check(self.root)
        with self.assertRaisesRegex(AuditInventoryError, 'nonliteral'):
            application_manifest('def kadmosWorldSourceModules : Array Name := #[`A] ++ #[`B]')

    def test_product_dependency_boundary(self):
        for dependency in ('HarmoniaTests.AuditPolicy','Harmonia.Distributed.Protocol','Harmonia.Core.Network','Lean'):
            with self.subTest(dependency=dependency):
                if dependency == 'Harmonia.Core.Network':
                    self.write(dependency, 'namespace Old\nend Old\n')
                self.write('Harmonia.Applications.Kadmos.World', 'import '+dependency+'\n')
                with self.assertRaisesRegex(AuditInventoryError, 'forbidden product|unknown certified application import'):
                    check(self.root)

if __name__ == '__main__':
    unittest.main()
