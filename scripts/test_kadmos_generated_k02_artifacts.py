#!/usr/bin/env python3
"""Hostile byte and admitted-world probes for the pinned K-02 export."""
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from check_kadmos_generated_k02_artifacts import ArtifactError, check_artifacts

ROOT = Path(__file__).resolve().parents[1]


class K02Artifacts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="t398-artifact-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "conformance").mkdir()
        shutil.copytree(ROOT / "conformance/kadmos-ir-bridge",
                        self.root / "conformance/kadmos-ir-bridge")
        shutil.copytree(ROOT / "conformance/kadmos-generated-k02",
                        self.root / "conformance/kadmos-generated-k02")
        fixture = self.root / 'Harmonia/Applications/Kadmos/Generated/Fixtures.lean'
        fixture.parent.mkdir(parents=True)
        shutil.copyfile(ROOT / 'Harmonia/Applications/Kadmos/Generated/Fixtures.lean', fixture)

    def check_rejects(self, path, before, after):
        data = path.read_bytes()
        self.assertIn(before, data)
        path.write_bytes(data.replace(before, after, 1))
        with self.assertRaises(ArtifactError):
            check_artifacts(self.root)

    def test_clean(self):
        check_artifacts(self.root)

    def test_rehashed_effect_mutation(self):
        path = self.root / "conformance/kadmos-generated-k02/balance/world_checker.ts"
        self.check_rejects(path, b'balance - event.amount', b'balance + event.amount')

    def test_python_effect_mutation(self):
        path = self.root / "conformance/kadmos-generated-k02/balance/world_checker.py"
        self.check_rejects(path, b'balance - event.amount', b'balance + event.amount')

    def test_default_json_mutation(self):
        path = self.root / "conformance/kadmos-generated-k02/balance/world_checker.ts"
        self.check_rejects(path, b'\\"balance\\":100', b'\\"balance\\":101')

    def test_world_json_mutation(self):
        path = self.root / "conformance/kadmos-generated-k02/balance/world_checker.ts"
        self.check_rejects(path, b'event.amount > 0', b'event.amount >= 0')

    def test_python_world_order_mutation(self):
        path = self.root / "conformance/kadmos-generated-k02/balance/world_checker.py"
        self.check_rejects(path, b'\\"version\\":\\"kadmos.world.v0\\",\\"name\\"',
                           b'\\"name\\":\\"BalanceWorld\\",\\"version\\"')

    def test_old_bridge_record_mutation(self):
        path = self.root / "conformance/kadmos-ir-bridge/parsed.json"
        self.check_rejects(path, b'event.amount > 0', b'event.amount >= 0')

    def test_manifest_rehash_cannot_authorize_mutation(self):
        path = self.root / "conformance/kadmos-generated-k02/balance/world_checker.ts"
        data = path.read_bytes().replace(b'balance - event.amount',
                                         b'balance + event.amount', 1)
        path.write_bytes(data)
        manifest_path = self.root / "conformance/kadmos-generated-k02/provenance.json"
        manifest = json.loads(manifest_path.read_text())
        import hashlib
        manifest["files"]["balance/world_checker.ts"] = hashlib.sha256(data).hexdigest()
        manifest_path.write_text(json.dumps(manifest) + "\n")
        with self.assertRaises(ArtifactError):
            check_artifacts(self.root)


if __name__ == "__main__":
    unittest.main()
