/- Build-time audit tooling, separate from the generic proof kernel API. -/
import Lean
open Lean Elab Command

namespace HarmoniaAudit

def allowed (n : Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

def checkDeclaration (n : Name) (allowChoice : Bool := true) :
    CommandElabM (Array Name) := do
  unless (← getEnv).contains n do
    throwError "axiom audit declaration does not exist: {n}"
  let axioms ← collectAxioms n
  for ax in axioms do
    unless allowed ax && (allowChoice || ax != ``Classical.choice) do
      throwError "axiom audit rejected {n}: {ax}"
  return axioms

def theoremNames (env : Environment) (select : Name → Bool) : Array Name :=
  (env.constants.toList.filterMap fun (n, info) =>
    match info with
    | .thmInfo _ => if select n then some n else none
    | _ => none).toArray.qsort (fun a b => a.toString < b.toString)

/-- Select by source module too: changing a theorem's namespace cannot evade
coverage. All new generic Core, examples and formal probe modules are included. -/
def foundationDeclaration (env : Environment) (n : Name) : Bool := Id.run do
  if (`Harmonia.Foundation).isPrefixOf n then return true
  let some idx := env.getModuleIdxFor? n | return false
  let m := env.header.moduleNames[idx.toNat]!
  return ((`Harmonia.Core).isPrefixOf m &&
      !(#[`Harmonia.Core.Event, `Harmonia.Core.Network, `Harmonia.Core.SmallStep]).contains m) ||
    m == `Harmonia.Examples.Foundation ||
    ((`HarmoniaTests).isPrefixOf m &&
      m != `HarmoniaTests.AuditPolicy && m != `HarmoniaTests.AuditRejection)

def sourceModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

def distributedSourceModules : Array Name := #[
  `Harmonia.Distributed, `Harmonia.Distributed.Membership,
  `Harmonia.Distributed.Protocol, `Harmonia.Distributed.Network,
  `Harmonia.Distributed.Semantics, `Harmonia.Distributed.Properties,
  `Harmonia.Examples.Distributed, `HarmoniaTests.DistributedMembership,
  `HarmoniaTests.DistributedNetwork, `HarmoniaTests.DistributedSteps,
  `HarmoniaTests.DistributedTraces, `HarmoniaTests.DistributedAxiomAudit]

def distributedDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.Distributed).isPrefixOf n ||
  (`Harmonia.Distributed).isPrefixOf (sourceModule env n) ||
  distributedSourceModules.contains (sourceModule env n)

def kadmosWorldSourceModules : Array Name := #[
  `Harmonia.Applications.Kadmos, `Harmonia.Applications.Kadmos.World,
  `Harmonia.Applications.Kadmos.Interpreter, `Harmonia.Applications.Kadmos.System,
  `Harmonia.Applications.Kadmos.Balance, `Harmonia.Applications.Kadmos.Bridge.Syntax,
  `Harmonia.Applications.Kadmos.Bridge.Certificate,
  `Harmonia.Applications.Kadmos.Bridge.Fixtures,
  `Harmonia.Applications.Kadmos.Generated.BalanceModel,
  `Harmonia.Applications.Kadmos.Generated.Fixtures,
  `Harmonia.Applications.Kadmos.Generated.SourceGrammar,
  `Harmonia.Applications.Kadmos.Generated.SourceLexical,
  `Harmonia.Applications.Kadmos.Generated.SourceLexicalValidator,
  `Harmonia.Applications.Kadmos.Generated.SourceStatementCertificate,
  `Harmonia.Applications.Kadmos.Generated.SourceValidator,
  `Harmonia.Applications.Kadmos.Generated.TargetCertificate,
  `Harmonia.Applications.Kadmos.Generated.TargetExpressionParser,
  `Harmonia.Applications.Kadmos.Generated.TargetJSON,
  `Harmonia.Applications.Kadmos.Generated.TargetMachine,
  `Harmonia.Applications.Kadmos.Generated.TargetObservation,
  `Harmonia.Applications.Kadmos.Generated.TargetProgramParser,
  `Harmonia.Applications.Kadmos.Generated.TargetRegex,
  `Harmonia.Applications.Kadmos.Generated.TargetSemantics,
  `Harmonia.Applications.Kadmos.Generated.TargetStatementParser,
  `Harmonia.Applications.Kadmos.Generated.TargetSyntax,
  `Harmonia.Applications.Kadmos.Generated.TargetTSStatementParser,
  `HarmoniaTests.KadmosWorldIR,
  `HarmoniaTests.KadmosWorldInterpreter, `HarmoniaTests.KadmosWorldBalance,
  `HarmoniaTests.KadmosWorldAxiomAudit]

def kadmosWorldDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.Applications.Kadmos).isPrefixOf n ||
  (`Harmonia.Applications.Kadmos).isPrefixOf (sourceModule env n) ||
  kadmosWorldSourceModules.contains (sourceModule env n)

/-- Shared scan: source axioms first, even unused; unsafe compiler placeholders
are exempt only from the auxiliary scan, never theorem dependency checks. -/
def auditSelected (select : Name → Bool) (label : String) (allObserved : Bool := false)
    (summaryPrefix : String := "DISTRIBUTED AUDIT PASS")
    (allowChoice : Bool := true) : CommandElabM Unit := do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, info) in declarations do
    if select n then
      match info with
      | .axiomInfo _ =>
        let range ← findDeclarationRanges? n
        unless info.isUnsafe && range.isNone do discard <| checkDeclaration n allowChoice
      | _ => pure ()
  let names := theoremNames env select
  if names.isEmpty then throwError "axiom audit found no {label} theorems"
  let mut observed : Array Name := #[]
  let mut count := 0
  for (n, info) in declarations do
    if select n && !info.isUnsafe then
      let axioms ← checkDeclaration n allowChoice
      count := count + 1
      if allObserved then
        for ax in axioms do
          if !observed.contains ax then observed := observed.push ax
  for n in names do
    let axioms ← checkDeclaration n allowChoice
    for ax in axioms do
      if !observed.contains ax then observed := observed.push ax
    logInfo m!"{n}: {axioms}"
  let whitelist := if allowChoice then
    "[propext, Quot.sound, Classical.choice]" else "[propext, Quot.sound]"
  if allObserved then
    logInfo m!"{summaryPrefix}: {names.size} theorems; {count} declarations; observed axioms {observed}; whitelist {whitelist}"
  else
    logInfo m!"AUDIT PASS: {names.size} theorems; observed axioms {observed}; whitelist {whitelist}"

end HarmoniaAudit

elab "#audit_declaration " n:ident : command => do
  discard <| HarmoniaAudit.checkDeclaration n.getId

elab "#audit_namespace " n:ident : command => do
  let env ← getEnv
  let names := HarmoniaAudit.theoremNames env (n.getId.isPrefixOf ·)
  if names.isEmpty then throwError "axiom audit found no theorems in {n.getId}"
  for name in names do discard <| HarmoniaAudit.checkDeclaration name

elab "#audit_foundations" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (HarmoniaAudit.foundationDeclaration env) "foundation"

elab "#audit_distributed" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (HarmoniaAudit.distributedDeclaration env) "distributed" true

elab "#audit_module " n:ident : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (fun name => HarmoniaAudit.sourceModule env name == n.getId) "source module" true

elab "#audit_kadmos_world" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (HarmoniaAudit.kadmosWorldDeclaration env) "kadmos world" true
    "KADMOS WORLD AUDIT PASS"

namespace HarmoniaAudit

def kadmosBridgeSourceModules : Array Name := #[
  `Harmonia.Applications.Kadmos.Bridge.Syntax,
  `Harmonia.Applications.Kadmos.Bridge.Certificate,
  `Harmonia.Applications.Kadmos.Bridge.Fixtures,
  `HarmoniaTests.KadmosBridgeSyntax,
  `HarmoniaTests.KadmosBridgeCertificate,
  `HarmoniaTests.KadmosBridgeFixtures,
  `HarmoniaTests.KadmosBridgeAxiomAudit]

def kadmosBridgeDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.Applications.Kadmos.Bridge).isPrefixOf n ||
  (`Harmonia.Applications.Kadmos.Bridge).isPrefixOf (sourceModule env n) ||
  kadmosBridgeSourceModules.contains (sourceModule env n)
end HarmoniaAudit

elab "#audit_kadmos_bridge" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (HarmoniaAudit.kadmosBridgeDeclaration env) "kadmos bridge" true
    "KADMOS BRIDGE AUDIT PASS"

namespace HarmoniaAudit

def kadmosGeneratedK02SourceModules : Array Name := #[
  `Harmonia.Applications.Kadmos.Generated.BalanceModel,
  `Harmonia.Applications.Kadmos.Generated.Fixtures,
  `Harmonia.Applications.Kadmos.Generated.SourceGrammar,
  `Harmonia.Applications.Kadmos.Generated.SourceLexical,
  `Harmonia.Applications.Kadmos.Generated.SourceLexicalValidator,
  `Harmonia.Applications.Kadmos.Generated.SourceStatementCertificate,
  `Harmonia.Applications.Kadmos.Generated.SourceValidator,
  `Harmonia.Applications.Kadmos.Generated.TargetCertificate,
  `Harmonia.Applications.Kadmos.Generated.TargetExpressionParser,
  `Harmonia.Applications.Kadmos.Generated.TargetJSON,
  `Harmonia.Applications.Kadmos.Generated.TargetMachine,
  `Harmonia.Applications.Kadmos.Generated.TargetObservation,
  `Harmonia.Applications.Kadmos.Generated.TargetProgramParser,
  `Harmonia.Applications.Kadmos.Generated.TargetRegex,
  `Harmonia.Applications.Kadmos.Generated.TargetSemantics,
  `Harmonia.Applications.Kadmos.Generated.TargetStatementParser,
  `Harmonia.Applications.Kadmos.Generated.TargetSyntax,
  `Harmonia.Applications.Kadmos.Generated.TargetTSStatementParser,
  `HarmoniaTests.KadmosGeneratedK02Lexer,
  `HarmoniaTests.KadmosGeneratedK02SourceGrammar,
  `HarmoniaTests.KadmosGeneratedK02SourceLex,
  `HarmoniaTests.KadmosGeneratedK02SourceModule,
  `HarmoniaTests.KadmosGeneratedK02SourceValidator,
  `HarmoniaTests.KadmosGeneratedK02PythonBooleanSyntax,
  `HarmoniaTests.KadmosGeneratedK02StatementCertificate,
  `HarmoniaTests.KadmosGeneratedK02PythonLines01,
  `HarmoniaTests.KadmosGeneratedK02PythonLines02,
  `HarmoniaTests.KadmosGeneratedK02PythonLinesAll,
  `HarmoniaTests.KadmosGeneratedK02PythonOrderLinesAll,
  `HarmoniaTests.KadmosGeneratedK02Machine,
  `HarmoniaTests.KadmosGeneratedK02ExpressionParser,
  `HarmoniaTests.KadmosGeneratedK02StatementParser,
  `HarmoniaTests.KadmosGeneratedK02TSParser,
  `HarmoniaTests.KadmosGeneratedK02Semantics,
  `HarmoniaTests.KadmosGeneratedK02ProgramParser,
  `HarmoniaTests.KadmosGeneratedK02JSON,
  `HarmoniaTests.KadmosGeneratedK02Regex,
  `HarmoniaTests.KadmosGeneratedK02BalanceTSParse,
  `HarmoniaTests.KadmosGeneratedK02BalancePythonParse,
  `HarmoniaTests.KadmosGeneratedK02OrderTSParse,
  `HarmoniaTests.KadmosGeneratedK02OrderPythonParse,
  `HarmoniaTests.KadmosGeneratedK02Certificate,
  `HarmoniaTests.KadmosGeneratedK02BalanceTSCertificate,
  `HarmoniaTests.KadmosGeneratedK02BalancePythonCertificate,
  `HarmoniaTests.KadmosGeneratedK02BalanceTSStep,
  `HarmoniaTests.KadmosGeneratedK02AxiomAudit]

def kadmosGeneratedK02Declaration (env : Environment) (n : Name) : Bool :=
  kadmosGeneratedK02SourceModules.contains (sourceModule env n)

end HarmoniaAudit

elab "#audit_kadmos_generated_k02" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (HarmoniaAudit.kadmosGeneratedK02Declaration env)
    "kadmos generated K-02" true "KADMOS GENERATED K-02 AUDIT PASS" false

elab "#audit_kadmos_generated_declaration " n:ident : command => do
  discard <| HarmoniaAudit.checkDeclaration n.getId false

namespace HarmoniaAudit

def quorumSourceModules : Array Name := #[
  `Harmonia.Theorems.Quorum, `HarmoniaTests.QuorumTest,
  `HarmoniaTests.QuorumAxiomAudit]

def quorumDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.Quorum).isPrefixOf n ||
  quorumSourceModules.contains (sourceModule env n)

end HarmoniaAudit

elab "#audit_quorum" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected (HarmoniaAudit.quorumDeclaration env) "quorum" true
    "QUORUM AUDIT PASS"

namespace HarmoniaAudit

def capSourceModules : Array Name := #[
  `Harmonia.Theorems.CAP, `HarmoniaTests.CAPTest,
  `HarmoniaTests.CAPAxiomAudit]

def capDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.CAP).isPrefixOf n ||
  capSourceModules.contains (sourceModule env n)

def checkCapDeclaration (n : Name) : CommandElabM (Array Name) := do
  unless (← getEnv).contains n do
    throwError "CAP audit declaration does not exist: {n}"
  let axioms ← collectAxioms n
  for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound do
      throwError "CAP audit rejected {n}: {ax}"
  return axioms

def auditCap : CommandElabM Unit := do
  let env ← getEnv
  let select := capDeclaration env
  let declarations := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let names := theoremNames env select
  if names.isEmpty then throwError "CAP audit found no theorems"
  let mut observed : Array Name := #[]
  let mut count := 0
  for (n, info) in declarations do
    if select n then
      match info with
      | .axiomInfo _ =>
        let range ← findDeclarationRanges? n
        unless info.isUnsafe && range.isNone do
          discard <| checkCapDeclaration n
      | _ => pure ()
      unless info.isUnsafe do
        let axioms ← checkCapDeclaration n
        count := count + 1
        for ax in axioms do
          if !observed.contains ax then observed := observed.push ax
  logInfo m!"CAP AUDIT PASS: {names.size} theorems; {count} declarations; observed axioms {observed}; whitelist [propext, Quot.sound]"

end HarmoniaAudit

elab "#audit_cap" : command => HarmoniaAudit.auditCap
