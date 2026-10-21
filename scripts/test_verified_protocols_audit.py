"""Hostile inventory, source, policy, import, and output mutations for protocol audits."""

import shutil
import tempfile
import unittest
from pathlib import Path

import check_verified_protocols_audit as audit


class VerifiedProtocolsAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        names = ["lakefile.lean", "HarmoniaTests/AuditPolicy.lean",
                 "HarmoniaTests/VerifiedProtocolsAxiomAudit.lean",
                 "HarmoniaTests/VerifiedProtocolsRejection.lean"]
        # Keep the fixtures independent of the protocol's proof implementation.
        for name in names:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT / name, target)
        self.write("Harmonia/VerifiedProtocols.lean",
                   "import Harmonia.VerifiedProtocols.QuorumLease\n")
        self.write("Harmonia/VerifiedProtocols/QuorumLease.lean",
                   "import Init\nnamespace Harmonia.VerifiedProtocols.QuorumLease\n"
                   "theorem witness : True := True.intro\nend Harmonia.VerifiedProtocols.QuorumLease\n")
        self.write("HarmoniaTests/VerifiedProtocolsTest.lean", "import Harmonia.VerifiedProtocols\n")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def mutate(self, name, old, new):
        path = self.root / name
        source = path.read_text()
        self.assertIn(old, source)
        path.write_text(source.replace(old, new, 1))

    def test_baseline(self):
        audit.check_static(self.root)

    def test_unmanifested_protocol_module(self):
        self.write("Harmonia/VerifiedProtocols/Nested/Hidden.lean", "import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_unmanifested_nested_probe(self):
        self.write("HarmoniaTests/VerifiedProtocols/Hidden.lean", "import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_duplicate_manifest_entry(self):
        self.mutate("HarmoniaTests/AuditPolicy.lean", "`HarmoniaTests.VerifiedProtocolsTest,",
                    "`HarmoniaTests.VerifiedProtocolsTest, `HarmoniaTests.VerifiedProtocolsTest,")
        with self.assertRaisesRegex(ValueError, "duplicate verified protocols manifest"):
            audit.check_static(self.root)

    def test_malformed_manifest_entry(self):
        self.mutate("HarmoniaTests/AuditPolicy.lean", "`HarmoniaTests.VerifiedProtocolsTest,",
                    "`HarmoniaTests.VerifiedProtocolsTest, badToken,")
        with self.assertRaisesRegex(ValueError, "malformed verified protocols manifest"):
            audit.check_static(self.root)

    def test_fixture_imported_by_certified_test(self):
        self.write("HarmoniaTests/VerifiedProtocolsTest.lean",
                   "import Harmonia.VerifiedProtocols\nimport HarmoniaTests.VerifiedProtocolsRejection\n")
        with self.assertRaisesRegex(ValueError, "counterexample fixture imported"):
            audit.check_static(self.root)

    def test_unknown_project_import(self):
        self.write("Harmonia/Unknown.lean", "import Init\n")
        self.write("HarmoniaTests/VerifiedProtocolsTest.lean",
                   "import Harmonia.VerifiedProtocols\nimport Harmonia.Unknown\n")
        with self.assertRaisesRegex(ValueError, "unknown certified import"):
            audit.check_static(self.root)

    def test_unknown_test_import(self):
        self.write("HarmoniaTests/Unknown.lean", "import Init\n")
        self.write("HarmoniaTests/VerifiedProtocolsTest.lean",
                   "import Harmonia.VerifiedProtocols HarmoniaTests.Unknown\n")
        with self.assertRaisesRegex(ValueError, "unknown certified import"):
            audit.check_static(self.root)

    def test_unknown_external_import(self):
        self.write("HarmoniaTests/VerifiedProtocolsTest.lean",
                   "import Harmonia.VerifiedProtocols Lean\n")
        with self.assertRaisesRegex(ValueError, "unknown certified import"):
            audit.check_static(self.root)

    def test_transitive_unknown_import(self):
        self.write("Harmonia/Core/Hidden.lean", "import Harmonia.Unknown\n")
        self.write("HarmoniaTests/VerifiedProtocolsTest.lean",
                   "import Harmonia.VerifiedProtocols Harmonia.Core.Hidden\n")
        with self.assertRaisesRegex(ValueError, "unknown certified import"):
            audit.check_static(self.root)

    def test_forbidden_tokens(self):
        path = self.root / "Harmonia/VerifiedProtocols/QuorumLease.lean"
        baseline = path.read_text()
        for token in ("sorry", "admit", "sorryAx", "axiom", "native_decide", "unsafe", "Classical.choice"):
            with self.subTest(token=token):
                path.write_text(baseline + "\n" + token + "\n")
                with self.assertRaisesRegex(ValueError, "forbidden certified source token"):
                    audit.check_static(self.root)
        path.write_text(baseline + '\n/- sorry /- axiom -/ Classical.choice -/\n-- unsafe\n')
        audit.check_static(self.root)

    def test_duplicate_target(self):
        path = self.root / "lakefile.lean"
        path.write_text(path.read_text() + "\nlean_lib verifiedProtocolsTest where\n  roots := #[`HarmoniaTests.VerifiedProtocolsTest]\n")
        with self.assertRaisesRegex(ValueError, "duplicate Lake target"):
            audit.check_static(self.root)

    def test_rejection_in_certified_roots(self):
        self.mutate("lakefile.lean", "roots := #[`HarmoniaTests.VerifiedProtocolsTest]",
                    "roots := #[`HarmoniaTests.VerifiedProtocolsTest, `HarmoniaTests.VerifiedProtocolsRejection]")
        with self.assertRaisesRegex(ValueError, "incorrect roots"):
            audit.check_static(self.root)

    def test_uncovered_manifest_module(self):
        self.write("HarmoniaTests/VerifiedProtocols/Extra.lean", "import Init\n")
        self.mutate("HarmoniaTests/AuditPolicy.lean", "`HarmoniaTests.VerifiedProtocolsTest,",
                    "`HarmoniaTests.VerifiedProtocolsTest, `HarmoniaTests.VerifiedProtocols.Extra,")
        with self.assertRaisesRegex(ValueError, "uncovered certified"):
            audit.check_static(self.root)

    def test_missing_audit_invocation(self):
        self.mutate("HarmoniaTests/VerifiedProtocolsAxiomAudit.lean", "#audit_verified_protocols", "-- removed")
        with self.assertRaisesRegex(ValueError, "missing verified protocols audit invocation"):
            audit.check_static(self.root)

    def test_weakened_policy(self):
        self.mutate("HarmoniaTests/AuditPolicy.lean", 'true "VERIFIED PROTOCOLS AUDIT PASS" false',
                    'true "VERIFIED PROTOCOLS AUDIT PASS" true')
        with self.assertRaisesRegex(ValueError, "modified verified protocols audit command"):
            audit.check_static(self.root)

    def test_weakened_selector(self):
        self.mutate("HarmoniaTests/AuditPolicy.lean",
                    "verifiedProtocolsSourceModules.contains (sourceModule env n)", "false")
        with self.assertRaisesRegex(ValueError, "modified verified protocols declaration selector"):
            audit.check_static(self.root)

    def test_output_whitelist(self):
        valid = ("VERIFIED PROTOCOLS AUDIT PASS: 3 theorems; 4 declarations; "
                 "observed axioms [propext, Quot.sound]; whitelist [propext, Quot.sound]")
        self.assertEqual(audit.audit_summary(valid), valid)
        for hostile in (valid.replace("[propext, Quot.sound];", "[Classical.choice];"),
                        "warning: unexpected\n" + valid, valid + "\nerror: unexpected",
                        valid.replace("whitelist [propext, Quot.sound]", "whitelist []")):
            with self.subTest(output=hostile), self.assertRaises(ValueError):
                audit.audit_summary(hostile)


if __name__ == "__main__":
    unittest.main()
