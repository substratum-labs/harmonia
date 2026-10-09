"""Five hostile source and import mutations for the CAP audit inventory."""

import shutil
import tempfile
import unittest
from pathlib import Path

import check_cap_audit as audit


class CAPAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in (
            "lakefile.lean", "Harmonia/Theorems/CAP.lean",
            "Harmonia/Core/TransitionSystem.lean", "Harmonia/Core/Execution.lean",
            "HarmoniaTests/AuditPolicy.lean", "HarmoniaTests/CAPTest.lean",
            "HarmoniaTests/CAPAxiomAudit.lean", "HarmoniaTests/CAPRejection.lean",
        ):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT / name, target)

    def test_new_cap_source_requires_manifest(self):
        nested = self.root / "Harmonia/Theorems/CAP/Hidden.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_nested_cap_probe_requires_manifest(self):
        nested = self.root / "HarmoniaTests/CAP/Hidden.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_manifest_rejects_duplicate(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        policy.write_text(policy.read_text().replace("`HarmoniaTests.CAPTest,",
            "`HarmoniaTests.CAPTest, `HarmoniaTests.CAPTest,"))
        with self.assertRaisesRegex(ValueError, "duplicate CAP manifest"):
            audit.check_static(self.root)

    def test_certified_import_rejects_fixture(self):
        test = self.root / "HarmoniaTests/CAPTest.lean"
        test.write_text("import HarmoniaTests.CAPRejection\n" + test.read_text())
        with self.assertRaisesRegex(ValueError, "counterexample fixture imported"):
            audit.check_static(self.root)

    def test_certified_source_rejects_axiom(self):
        source = self.root / "Harmonia/Theorems/CAP.lean"
        source.write_text(source.read_text() + "\naxiom hidden : True\n")
        with self.assertRaisesRegex(ValueError, "forbidden certified source token axiom"):
            audit.check_static(self.root)


if __name__ == "__main__":
    unittest.main()
