"""T-395 artifact and audit mutations in disposable copies."""
import sys
sys.dont_write_bytecode = True
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from shutil import copytree, copy2
from check_kadmos_bridge_artifacts import check_artifacts, ArtifactError, strict_json, validate_world
from check_kadmos_bridge_audit import check, AuditInventoryError

SOURCE = Path(__file__).resolve().parents[1]
class BridgePolicyTests(unittest.TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for dirname in ('Harmonia','HarmoniaTests','conformance','tools'):
            copytree(SOURCE/dirname,self.root/dirname)
        copy2(SOURCE/'lakefile.lean',self.root/'lakefile.lean')
        copytree(SOURCE/'scripts',self.root/'scripts')
    def test_clean(self):
        check_artifacts(self.root)
        check(self.root)
    def test_hash_drift(self):
        p=self.root/'conformance/kadmos-ir-bridge/balance.world.yaml'
        p.write_text(p.read_text()+'\n')
        with self.assertRaises(ArtifactError): check_artifacts(self.root)
    def test_unregistered_bridge_source(self):
        p=self.root/'Harmonia/Applications/Kadmos/Bridge/Hidden.lean'
        p.write_text('namespace Escaped\naxiom unused : Nat\nend Escaped\n')
        with self.assertRaises(AuditInventoryError): check(self.root)

    def test_each_artifact_byte_drift(self):
        paths=['balance.world.yaml','order_phase.world.yaml','parsed.json','profiles.json',
               'evaluate-vectors.json','provenance.json']
        for name in paths:
            with self.subTest(name=name):
                p=self.root/'conformance/kadmos-ir-bridge'/name
                original=p.read_bytes();p.write_bytes(original+b' ')
                with self.assertRaises(ArtifactError): check_artifacts(self.root)
                p.write_bytes(original)
        p=self.root/'Harmonia/Applications/Kadmos/Bridge/Fixtures.lean'
        p.write_text(p.read_text()+'\n')
        with self.assertRaises(ArtifactError): check_artifacts(self.root)
    def test_strict_parser_schema_and_numbers(self):
        for raw in (b'{"x":-0}',b'{"x":1.5}',b'{"x":9007199254740992}',b'{"x":1,"x":2}'):
            with self.subTest(raw=raw), self.assertRaises(ArtifactError): strict_json(raw)
        import json
        world=json.loads((self.root/'conformance/kadmos-ir-bridge/parsed.json').read_text())['balance']
        world['states'][0]['terminal']=None
        with self.assertRaisesRegex(ArtifactError,'boolean'): validate_world(world)
        del world['states'][0]['terminal']
        world['fields']=['amount']
        with self.assertRaisesRegex(ArtifactError,'unknown'): validate_world(world)
        del world['fields']
        del world['transitions'][0]['directive']
        with self.assertRaisesRegex(ArtifactError,'missing'): validate_world(world)
    def test_escaped_and_unsafe_axioms(self):
        p=self.root/'Harmonia/Applications/Kadmos/Bridge/Syntax.lean'
        source=p.read_text()
        for prefix in ('','unsafe '):
            with self.subTest(prefix=prefix):
                p.write_text(source+'\nnamespace Escaped\n'+prefix+'axiom unused : Nat\nend Escaped\n')
                with self.assertRaisesRegex(AuditInventoryError,'forbidden .* source token axiom'): check(self.root)
        p.write_text(source)
    def test_indirect_axiom_import_and_trap_root(self):
        outside=self.root/'HarmoniaTests/OutsideBridge.lean'
        outside.write_text('namespace Escape\naxiom bad : True\nend Escape\n')
        p=self.root/'HarmoniaTests/KadmosBridgeSyntax.lean';source=p.read_text()
        p.write_text('import HarmoniaTests.OutsideBridge\n'+source)
        with self.assertRaisesRegex(AuditInventoryError,'unknown bridge audit import'): check(self.root)
        p.write_text(source)
        lake=self.root/'lakefile.lean';text=lake.read_text()
        lake.write_text(text.replace('roots := #[`HarmoniaTests.KadmosBridgeSyntax]',
          'roots := #[`HarmoniaTests.KadmosBridgeSyntax, `HarmoniaTests.KadmosBridgeRejection.Unused]'))
        with self.assertRaisesRegex(AuditInventoryError,'adversarial closure'): check(self.root)
    def test_nested_bridge_probe_inventory(self):
        path=self.root/'HarmoniaTests/KadmosBridgeExtra/Hidden.lean'
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text('namespace Escape\ntheorem marker : True := True.intro\nend Escape\n')
        with self.assertRaisesRegex(AuditInventoryError,'bridge disk mismatch'): check(self.root)
    def test_unregistered_rejection_fixture(self):
        path=self.root/'HarmoniaTests/KadmosBridgeRejection/Hidden.lean'
        path.write_text('namespace Trap\naxiom hidden : Nat\nend Trap\n')
        with self.assertRaisesRegex(AuditInventoryError,'rejection disk mismatch'): check(self.root)
    def test_exported_name_cannot_inject_lean(self):
        import json,subprocess
        parsed=self.root/'conformance/kadmos-ir-bridge/parsed.json'
        obj=json.loads(parsed.read_text());obj['balance']['name']='\"; axiom forged : False'
        parsed.write_text(json.dumps(obj,separators=(',',':'))+'\n')
        out=self.root/'generated';result=subprocess.run(['node',str(self.root/'tools/export_kadmos_ir_bridge.mjs'),
            '--from-parsed',str(parsed),'--out',str(out)],capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stderr)
        emitted=(out/'Fixtures.lean').read_text()
        self.assertIn('\\\"; axiom forged',emitted)
        self.assertNotRegex(emitted,r'(?m)^axiom forged')
