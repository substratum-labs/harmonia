import Lake
open Lake DSL

package "harmonia" where
  version := v!"0.1.0"
  keywords := #["distributed-systems", "formal-methods", "lean4", "consensus"]

@[default_target]
lean_lib «Harmonia» where
  -- Certified root library for Harmonia formal specification and verification

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

lean_lib quorumTest where
  roots := #[`HarmoniaTests.QuorumTest]

lean_lib quorumAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.QuorumAxiomAudit]

lean_lib quorumAuditRejection where
  roots := #[`HarmoniaTests.QuorumRejection]

lean_lib capTest where
  roots := #[`HarmoniaTests.CAPTest]

lean_lib capAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.CAPAxiomAudit]

lean_lib capAuditRejection where
  roots := #[`HarmoniaTests.CAPRejection]

lean_lib flpTest where
  roots := #[`HarmoniaTests.FLPTest]

lean_lib flpAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.FLPAxiomAudit]

lean_lib flpAuditRejection where
  roots := #[`HarmoniaTests.FLPRejection]

lean_lib causalTest where
  roots := #[`HarmoniaTests.CausalTest]

lean_lib causalAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.CausalAxiomAudit]

lean_lib causalAuditRejection where
  roots := #[`HarmoniaTests.CausalRejection]

lean_lib verifiedProtocolsTest where
  roots := #[`HarmoniaTests.VerifiedProtocolsTest]

lean_lib verifiedProtocolsAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.VerifiedProtocolsAxiomAudit]

lean_lib verifiedProtocolsAuditRejection where
  roots := #[`HarmoniaTests.VerifiedProtocolsRejection]
