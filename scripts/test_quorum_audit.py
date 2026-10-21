"""Hostile mutations for the quorum audit inventory and isolation checks."""

import shutil
import tempfile
import unittest
from pathlib import Path

import check_quorum_audit as audit


class QuorumAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in (
            "lakefile.lean", "Harmonia/Theorems/Quorum.lean",
            "HarmoniaTests/AuditPolicy.lean", "HarmoniaTests/QuorumTest.lean",
            "HarmoniaTests/QuorumAxiomAudit.lean", "HarmoniaTests/QuorumRejection.lean",
        ):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT / name, target)

    def test_new_theorem_source_must_enter_manifest(self):
        (self.root / "Harmonia/Theorems/QuorumExtra.lean").write_text("import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_nested_quorum_probe_must_enter_manifest(self):
        nested = self.root / "HarmoniaTests/Quorum/Hidden.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_manifest_rejects_extra_tokens_and_duplicates(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        source = policy.read_text()
        policy.write_text(source.replace("`HarmoniaTests.QuorumTest,",
                                         "`HarmoniaTests.QuorumTest, garbage,"))
        with self.assertRaisesRegex(ValueError, "malformed quorum manifest"):
            audit.check_static(self.root)
        policy.write_text(source.replace("`HarmoniaTests.QuorumTest,",
                                         "`HarmoniaTests.QuorumTest, `HarmoniaTests.QuorumTest,"))
        with self.assertRaisesRegex(ValueError, "duplicate quorum manifest"):
            audit.check_static(self.root)

    def test_certified_import_rejects_fixture(self):
        test = self.root / "HarmoniaTests/QuorumTest.lean"
        test.write_text("import HarmoniaTests.QuorumRejection\n" + test.read_text())
        with self.assertRaisesRegex(ValueError, "counterexample fixture imported"):
            audit.check_static(self.root)

    def test_certified_import_rejects_unknown_project_module(self):
        (self.root / "HarmoniaTests/Hidden.lean").write_text("import Init\n")
        test = self.root / "HarmoniaTests/QuorumTest.lean"
        test.write_text("import HarmoniaTests.Hidden\n" + test.read_text())
        with self.assertRaisesRegex(ValueError, "unknown certified import"):
            audit.check_static(self.root)


if __name__ == "__main__":
    unittest.main()
