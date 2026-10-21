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
            "lakefile.lean", ".github/workflows/foundations.yml",
            "HarmoniaTests/AuditPolicy.lean",
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

    def test_rejects_unqualified_classical_choice(self):
        self.mutate("Harmonia/Theorems/Lamport.lean", "\nopen Classical\ndef bad := choice\n")
        with self.assertRaisesRegex(ValueError, "choice"):
            audit.check_static(self.root)

    def test_rejects_second_import_on_same_line(self):
        path = self.root / "Harmonia/Theorems/VectorClock.lean"
        path.write_text(path.read_text().replace(
            "import Harmonia.Theorems.Causal", "import Harmonia.Theorems.Causal Lean"))
        with self.assertRaisesRegex(ValueError, "nonstandard causal import"):
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

    def test_rejects_dead_whitelist_bypass(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        policy.write_text(policy.read_text().replace(
            "  let axioms ← collectAxioms n\n  for ax in axioms do\n    unless ax == ``propext",
            "  let axioms := #[]\n  for ax in axioms do\n    unless ax == ``propext"))
        with self.assertRaisesRegex(ValueError, "causal audit policy body changed"):
            audit.check_static(self.root)

    def test_rejects_missing_manifest_entry(self):
        policy = self.root / "HarmoniaTests/AuditPolicy.lean"
        policy.write_text(policy.read_text().replace("`Harmonia.Theorems.VectorClock, `HarmoniaTests.CausalTest,",
                                                   "`HarmoniaTests.CausalTest,"))
        with self.assertRaisesRegex(ValueError, "causal manifest mismatch"):
            audit.check_static(self.root)


if __name__ == "__main__":
    unittest.main()
