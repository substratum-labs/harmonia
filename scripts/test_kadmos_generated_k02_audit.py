"""Generated K-02 inventory mutations in a disposable Lean source tree."""
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
from check_distributed_audit import AuditInventoryError
from check_kadmos_generated_k02_audit import check

SOURCE = Path(__file__).resolve().parents[1]


class GeneratedK02InventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='t398-audit-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for directory in ('Harmonia', 'HarmoniaTests'):
            for source in (SOURCE / directory).rglob('*.lean'):
                target = self.root / source.relative_to(SOURCE)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)
        shutil.copy2(SOURCE / 'lakefile.lean', self.root / 'lakefile.lean')

    def change(self, path, old, new):
        target = self.root / path
        text = target.read_text()
        self.assertIn(old, text)
        target.write_text(text.replace(old, new, 1))

    def test_clean_inventory(self):
        result = check(self.root)
        # The checker above enforces exact file/manifest/root equality. Keep
        # this smoke assertion independent of a historical source count.
        self.assertGreater(result['generated_modules'], 0)
        self.assertGreater(result['generated_tests'], 0)

    def test_generated_audit_cannot_allow_choice(self):
        self.change('HarmoniaTests/AuditPolicy.lean',
                    '"kadmos generated K-02" true "KADMOS GENERATED K-02 AUDIT PASS" false',
                    '"kadmos generated K-02" true "KADMOS GENERATED K-02 AUDIT PASS" true')
        with self.assertRaisesRegex(AuditInventoryError, 'strict axiom policy'):
            check(self.root)

    def test_commented_strict_policy_cannot_mask_allow_choice(self):
        policy = self.root / 'HarmoniaTests/AuditPolicy.lean'
        text = policy.read_text()
        start = text.index('elab "#audit_kadmos_generated_k02"')
        stop = text.index('elab "#audit_kadmos_generated_declaration ', start)
        strict = text[start:stop]
        weakened = strict.replace('AUDIT PASS" false', 'AUDIT PASS" true')
        self.assertNotEqual(strict, weakened)
        policy.write_text(text[:start] + '/-\n' + strict + 'namespace Decoy\nend Decoy\n-/\n' +
                          weakened + text[stop:])
        with self.assertRaisesRegex(AuditInventoryError, 'strict axiom policy'):
            check(self.root)

    def test_nested_product_cannot_escape(self):
        path = self.root / 'Harmonia/Applications/Kadmos/Generated/Nested/Hidden.lean'
        path.parent.mkdir(parents=True)
        path.write_text('namespace Hidden\naxiom unused : Nat\nend Hidden\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_test_module_cannot_escape(self):
        path = self.root / 'HarmoniaTests/KadmosGeneratedK02Unregistered.lean'
        path.write_text('theorem marker : True := True.intro\n')
        with self.assertRaisesRegex(AuditInventoryError, 'manifest'):
            check(self.root)

    def test_missing_certified_import_is_rejected(self):
        self.change('HarmoniaTests/KadmosGeneratedK02AxiomAudit.lean',
                    'import HarmoniaTests.KadmosGeneratedK02BalanceTSStep\n', '')
        with self.assertRaisesRegex(AuditInventoryError, 'unimported'):
            check(self.root)

    def test_certified_root_rejects_own_trap(self):
        self.change('lakefile.lean',
                    'roots := #[`HarmoniaTests.KadmosGeneratedK02Lexer]',
                    'roots := #[`HarmoniaTests.KadmosGeneratedK02Lexer, '
                    '`HarmoniaTests.KadmosGeneratedK02Rejection.Unused]')
        with self.assertRaisesRegex(AuditInventoryError, 'rejection root'):
            check(self.root)

    def test_rejection_root_set_is_exact(self):
        self.change('lakefile.lean',
                    '`HarmoniaTests.KadmosGeneratedK02Rejection.Unsafe,\n'
                    '    `HarmoniaTests.KadmosGeneratedK02AuditRejection]',
                    '`HarmoniaTests.KadmosGeneratedK02AuditRejection]')
        with self.assertRaisesRegex(AuditInventoryError, 'rejection roots'):
            check(self.root)

    def test_python_line_stack_option_is_exact(self):
        self.change('lakefile.lean',
                    'moreLeanArgs := #["--tstack=131072"]',
                    'moreLeanArgs := #["-DtrustLevel=1"]')
        with self.assertRaisesRegex(AuditInventoryError, 'stack option'):
            check(self.root)

    def test_commented_python_line_stack_option_is_rejected(self):
        self.change('lakefile.lean',
                    'moreLeanArgs := #["--tstack=131072"]',
                    '-- moreLeanArgs := #["--tstack=131072"]')
        with self.assertRaisesRegex(AuditInventoryError, 'stack option'):
            check(self.root)

    def test_unused_axiom_is_rejected(self):
        path = self.root / 'Harmonia/Applications/Kadmos/Generated/TargetObservation.lean'
        path.write_text(path.read_text() + '\nnamespace Escape\naxiom unused : Nat\nend Escape\n')
        with self.assertRaisesRegex(AuditInventoryError, 'forbidden certified source token axiom'):
            check(self.root)


if __name__ == '__main__':
    unittest.main()
