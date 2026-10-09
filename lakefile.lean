import Lake
open Lake DSL

package "harmonia" where
  version := v!"0.1.0"
  keywords := #["distributed-systems", "formal-methods", "lean4", "consensus"]

lean_lib «Harmonia» where
  -- Root library for Harmonia formal specification and verification

@[default_target]
lean_exe "harmonia" where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #["-fuse-ld=/usr/bin/ld"] else #[]

-- Proof elaboration targets; certified audit and adversarial fixtures are separate.
lean_lib foundationsTest where
  roots := #[`HarmoniaTests.Foundations, `HarmoniaTests.InvariantProbes,
    `HarmoniaTests.RefinementProbes]

lean_lib foundationsAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.AxiomAudit]

-- Deliberate axiom/sorryAx fixtures: never a root of foundationsAudit.
lean_lib foundationsAuditRejection where
  roots := #[`HarmoniaTests.AuditRejection]

lean_lib distributedTest where
  roots := #[`HarmoniaTests.DistributedMembership, `HarmoniaTests.DistributedNetwork, `HarmoniaTests.DistributedSteps, `HarmoniaTests.DistributedTraces]

lean_lib distributedAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.DistributedAxiomAudit]
lean_lib distributedAuditRejection where
  roots := #[`HarmoniaTests.DistributedRejection.Unused, `HarmoniaTests.DistributedRejection.Unsafe, `HarmoniaTests.DistributedAuditRejection]

lean_lib kadmosWorldTest where
  roots := #[`HarmoniaTests.KadmosWorldIR, `HarmoniaTests.KadmosWorldInterpreter, `HarmoniaTests.KadmosWorldBalance]

lean_lib kadmosWorldAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.KadmosWorldAxiomAudit]

lean_lib kadmosWorldAuditRejection where
  roots := #[`HarmoniaTests.KadmosWorldRejection.Unused,
    `HarmoniaTests.KadmosWorldRejection.Unsafe, `HarmoniaTests.KadmosWorldAuditRejection]

lean_lib kadmosBridgeSyntaxTest where
  roots := #[`HarmoniaTests.KadmosBridgeSyntax]

lean_lib kadmosBridgeCertificateTest where
  roots := #[`HarmoniaTests.KadmosBridgeCertificate]

lean_lib kadmosBridgeFixturesTest where
  roots := #[`HarmoniaTests.KadmosBridgeFixtures]

lean_lib kadmosBridgeAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.KadmosBridgeAxiomAudit]
lean_lib kadmosBridgeAuditRejection where
  roots := #[`HarmoniaTests.KadmosBridgeRejection.Unused,
    `HarmoniaTests.KadmosBridgeRejection.Unsafe, `HarmoniaTests.KadmosBridgeAuditRejection]

lean_lib quorumTest where
  roots := #[`HarmoniaTests.QuorumTest]

lean_lib quorumAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.QuorumAxiomAudit]

lean_lib quorumAuditRejection where
  roots := #[`HarmoniaTests.QuorumRejection]
