import Lake
open Lake DSL

package "harmonia" where
  version := v!"0.1.0"
  keywords := #["distributed-systems", "formal-methods", "lean4", "consensus"]

lean_lib «Harmonia» where
  -- Root library for Harmonia formal specification and verification
  -- Canonical execution certificates need a larger native thread stack.
  -- This changes resource capacity, not proof trust or execution fuel.
  moreLeanArgs := #["--tstack=131072"]

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

lean_lib kadmosGeneratedK02LexerTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Lexer]

lean_lib kadmosGeneratedK02SourceGrammarTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02SourceGrammar]

lean_lib kadmosGeneratedK02SourceLexTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02SourceLex]

lean_lib kadmosGeneratedK02SourceValidatorTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02SourceValidator]

lean_lib kadmosGeneratedK02SourceModuleTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02SourceModule]

lean_lib kadmosGeneratedK02PythonBooleanSyntaxTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02PythonBooleanSyntax]

lean_lib kadmosGeneratedK02StatementCertificateTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02StatementCertificate]

lean_lib kadmosGeneratedK02PythonLinesTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02PythonLines01,
    `HarmoniaTests.KadmosGeneratedK02PythonLines02,
    `HarmoniaTests.KadmosGeneratedK02PythonLinesAll,
    `HarmoniaTests.KadmosGeneratedK02PythonOrderLinesAll]
  -- The closed 19 KB source-line certificates need a larger Lean thread
  -- stack; this changes resource capacity, not proof trust or reduction mode.
  moreLeanArgs := #["--tstack=131072"]

lean_lib kadmosGeneratedK02SimulationTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Simulation]

lean_lib kadmosGeneratedK02ClosedProgramsTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02ClosedPrograms]
  moreLeanArgs := #["--tstack=131072"]

lean_lib kadmosGeneratedK02ConstructorProofTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02ConstructorProof,
    `HarmoniaTests.KadmosGeneratedK02ConstructorProofTS,
    `HarmoniaTests.KadmosGeneratedK02ConstructorProofPython]

lean_lib kadmosGeneratedK02BalanceStepProofTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02BalanceStepProof,
    `HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases,
    `HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS,
    `HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython]

lean_lib kadmosGeneratedK02MachineTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Machine]

lean_lib kadmosGeneratedK02ExpressionParserTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02ExpressionParser]

lean_lib kadmosGeneratedK02StatementParserTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02StatementParser]

lean_lib kadmosGeneratedK02TSParserTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02TSParser]

lean_lib kadmosGeneratedK02SemanticsTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Semantics]

lean_lib kadmosGeneratedK02ProgramParserTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02ProgramParser]

lean_lib kadmosGeneratedK02BalanceTSParseTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02BalanceTSParse]

lean_lib kadmosGeneratedK02BalancePythonParseTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02BalancePythonParse]

lean_lib kadmosGeneratedK02OrderTSParseTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02OrderTSParse]

lean_lib kadmosGeneratedK02OrderPythonParseTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02OrderPythonParse]

lean_lib kadmosGeneratedK02CertificateTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Certificate]

lean_lib kadmosGeneratedK02BalanceTSCertificateTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02BalanceTSCertificate]

lean_lib kadmosGeneratedK02BalancePythonCertificateTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02BalancePythonCertificate]

lean_lib kadmosGeneratedK02BalanceTSStepTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02BalanceTSStep]

lean_lib kadmosGeneratedK02Audit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.KadmosGeneratedK02AxiomAudit]

lean_lib kadmosGeneratedK02AuditRejection where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Rejection.Unused,
    `HarmoniaTests.KadmosGeneratedK02Rejection.Unsafe,
    `HarmoniaTests.KadmosGeneratedK02AuditRejection]

lean_lib kadmosGeneratedK02JSONTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02JSON]

lean_lib kadmosGeneratedK02RegexTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Regex]

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

lean_lib kadmosGeneratedK02CorrespondenceTest where
  roots := #[`HarmoniaTests.KadmosGeneratedK02Correspondence]
  moreLeanArgs := #["--tstack=131072"]

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

