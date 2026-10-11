"""Hostile source mutations for the causal audit gate."""

import shutil
import tempfile
import unittest
from pathlib import Path

import check_causal_audit as audit


class CausalAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in (
            "lakefile.lean", "HarmoniaTests/AuditPolicy.lean",
            "HarmoniaTests/CausalTest.lean", "HarmoniaTests/CausalAxiomAudit.lean",
            "HarmoniaTests/CausalRejection.lean", "Harmonia/Theorems/Causal.lean",
            "Harmonia/Theorems/Lamport.lean", "Harmonia/Theorems/VectorClock.lean",
        ):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT / name, target)

    def mutate(self, name: str, addition: str) -> None:
        path = self.root / name
        path.write_text(path.read_text() + addition)

    def test_rejects_sorry(self):
        self.mutate("Harmonia/Theorems/Causal.lean", "\ntheorem bad : True := by sorry\n")
        with self.assertRaisesRegex(ValueError, "forbidden certified source token sorry"):
            audit.check_static(self.root)

    def test_rejects_classical_choice(self):
        self.mutate("Harmonia/Theorems/Lamport.lean", "\ndef bad := Classical.choice\n")
        with self.assertRaisesRegex(ValueError, "Classical.choice"):
            audit.check_static(self.root)

    def test_rejects_unsafe(self):
        self.mutate("Harmonia/Theorems/VectorClock.lean", "\nunsafe def bad : Nat := 0\n")
        with self.assertRaisesRegex(ValueError, "forbidden certified source token unsafe"):
            audit.check_static(self.root)

    def test_rejects_broader_whitelist(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        policy.write_text(policy.read_text().replace(
            "unless ax == ``propext || ax == ``Quot.sound do\n      throwError \"CAUSAL",
            "unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do\n      throwError \"CAUSAL"))
        with self.assertRaisesRegex(ValueError, "causal whitelist"):
            audit.check_static(self.root)

    def test_rejects_missing_manifest_entry(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        policy.write_text(policy.read_text().replace("`Harmonia.Theorems.VectorClock, `HarmoniaTests.CausalTest,",
                                                   "`HarmoniaTests.CausalTest,"))
        with self.assertRaisesRegex(ValueError, "causal manifest mismatch"):
            audit.check_static(self.root)


if __name__ == "__main__":
    unittest.main()
