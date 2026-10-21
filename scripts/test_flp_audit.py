"""Hostile source and import mutations for the FLP audit inventory."""

import shutil
import tempfile
import unittest
from pathlib import Path

import check_flp_audit as audit


class FLPAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        names = [
            "lakefile.lean",
            "Harmonia/Core/TransitionSystem.lean", "Harmonia/Core/Execution.lean",
            "HarmoniaTests/AuditPolicy.lean", "HarmoniaTests/FLPTest.lean",
            "HarmoniaTests/FLPAxiomAudit.lean", "HarmoniaTests/FLPRejection.lean",
        ]
        names.extend(str(path.relative_to(audit.ROOT)) for path in
                     (audit.ROOT / "Harmonia/Theorems").glob("FLP*.lean"))
        for name in names:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT / name, target)

    def test_new_flp_source_requires_manifest(self):
        nested = self.root / "Harmonia/Theorems/FLP/Hidden.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_nested_flp_probe_requires_manifest(self):
        nested = self.root / "HarmoniaTests/FLP/Hidden.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("import Init\n")
        with self.assertRaisesRegex(ValueError, "manifest mismatch"):
            audit.check_static(self.root)

    def test_manifest_rejects_duplicate(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        policy.write_text(policy.read_text().replace("`HarmoniaTests.FLPTest,",
            "`HarmoniaTests.FLPTest, `HarmoniaTests.FLPTest,"))
        with self.assertRaisesRegex(ValueError, "duplicate FLP manifest"):
            audit.check_static(self.root)

    def test_certified_import_rejects_fixture(self):
        test = self.root / "HarmoniaTests/FLPTest.lean"
        test.write_text("import HarmoniaTests.FLPRejection\n" + test.read_text())
        with self.assertRaisesRegex(ValueError, "counterexample fixture imported"):
            audit.check_static(self.root)

    def test_certified_source_rejects_axiom(self):
        source = self.root / "Harmonia/Theorems/FLP.lean"
        source.write_text(source.read_text() + "\naxiom hidden : True\n")
        with self.assertRaisesRegex(ValueError, "forbidden certified source token axiom"):
            audit.check_static(self.root)

    def test_certified_source_rejects_classical_choice(self):
        source = self.root / "Harmonia/Theorems/FLP.lean"
        source.write_text(source.read_text() +
                          "\nnoncomputable def hidden : Nat := Classical.choice (show Nonempty Nat from ⟨0⟩)\n")
        with self.assertRaisesRegex(ValueError, "forbidden certified source token Classical.choice"):
            audit.check_static(self.root)


if __name__ == "__main__":
    unittest.main()
