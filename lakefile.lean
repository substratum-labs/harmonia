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

-- Proof elaboration targets; adversarial audit fixtures remain isolated.
lean_lib foundationsTest where
  roots := #[`HarmoniaTests.Foundations, `HarmoniaTests.InvariantProbes,
    `HarmoniaTests.RefinementProbes]

lean_lib foundationsAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.AxiomAudit, `HarmoniaTests.AuditRejection]
