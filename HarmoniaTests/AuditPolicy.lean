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
  let mut count : Nat := 0
  for (n, info) in declarations do
    if select n && !info.isUnsafe then
      let axioms ← collectAxioms n
      for ax in axioms do
        unless allowed ax && (allowChoice || ax != ``Classical.choice) do
          throwError "axiom audit rejected {n}: {ax}"
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
  let mut count : Nat := 0
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

namespace HarmoniaAudit

def flpSourceModules : Array Name := #[
  `Harmonia.Theorems.FLP, `Harmonia.Theorems.FLPInitial,
  `Harmonia.Theorems.FLPIndistinguishability,
  `Harmonia.Theorems.FLPInputs, `Harmonia.Theorems.FLPExtension,
  `Harmonia.Theorems.FLPBounds,
  `HarmoniaTests.FLPTest,
  `HarmoniaTests.FLPAxiomAudit]

def flpDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.FLP).isPrefixOf n ||
  flpSourceModules.contains (sourceModule env n)

def checkFlpDeclaration (n : Name) : CommandElabM (Array Name) := do
  unless (← getEnv).contains n do
    throwError "FLP audit declaration does not exist: {n}"
  let axioms ← collectAxioms n
  for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound do
      throwError "FLP audit rejected {n}: {ax}"
  return axioms

def auditFlp : CommandElabM Unit := do
  let env ← getEnv
  let select := flpDeclaration env
  let declarations := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let names := theoremNames env select
  if names.isEmpty then throwError "FLP audit found no theorems"
  let mut observed : Array Name := #[]
  let mut count : Nat := 0
  for (n, info) in declarations do
    if select n then
      let range ← findDeclarationRanges? n
      if info.isUnsafe && range.isSome then
        throwError "FLP audit rejected unsafe source declaration {n}"
      match info with
      | .axiomInfo _ =>
        if range.isSome then
          discard <| checkFlpDeclaration n
      | _ => pure ()
      unless info.isUnsafe do
        let axioms ← checkFlpDeclaration n
        count := count + 1
        for ax in axioms do
          if !observed.contains ax then observed := observed.push ax
  logInfo m!"FLP AUDIT PASS: {names.size} theorems; {count} declarations; observed axioms {observed}; whitelist [propext, Quot.sound]"

end HarmoniaAudit

elab "#audit_flp" : command => HarmoniaAudit.auditFlp

namespace HarmoniaAudit

def verifiedProtocolsSourceModules : Array Name := #[
  `Harmonia.VerifiedProtocols,
  `Harmonia.VerifiedProtocols.QuorumLease,
  `Harmonia.VerifiedProtocols.TwoPhaseCommit,
  `Harmonia.VerifiedProtocols.BFTQuorumCommit,
  `HarmoniaTests.VerifiedProtocolsTest,
  `HarmoniaTests.VerifiedProtocolsAxiomAudit
]

def verifiedProtocolsDeclaration (env : Environment) (n : Name) : Bool :=
  verifiedProtocolsSourceModules.contains (sourceModule env n)

end HarmoniaAudit

elab "#audit_verified_protocols" : command => do
  let env ← getEnv
  HarmoniaAudit.auditSelected
    (HarmoniaAudit.verifiedProtocolsDeclaration env) "verified protocols"
    true "VERIFIED PROTOCOLS AUDIT PASS" false

namespace HarmoniaAudit

def causalSourceModules : Array Name := #[
  `Harmonia.Theorems.Causal, `Harmonia.Theorems.Lamport,
  `Harmonia.Theorems.VectorClock, `HarmoniaTests.CausalTest,
  `HarmoniaTests.CausalAxiomAudit]

def causalDeclaration (env : Environment) (n : Name) : Bool :=
  (`Harmonia.Causal).isPrefixOf n ||
  causalSourceModules.contains (sourceModule env n)

def checkCausalDeclaration (n : Name) : CommandElabM (Array Name) := do
  unless (← getEnv).contains n do
    throwError "CAUSAL audit declaration does not exist: {n}"
  let axioms ← collectAxioms n
  for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound do
      throwError "CAUSAL audit rejected {n}: {ax}"
  return axioms

def auditCausal : CommandElabM Unit := do
  let env ← getEnv
  let select := causalDeclaration env
  let declarations := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let names := theoremNames env select
  if names.isEmpty then throwError "CAUSAL audit found no theorems"
  let mut observed : Array Name := #[]
  let mut count : Nat := 0
  for (n, info) in declarations do
    if select n then
      let range ← findDeclarationRanges? n
      if info.isUnsafe && range.isSome then
        throwError "CAUSAL audit rejected unsafe source declaration {n}"
      match info with
      | .axiomInfo _ =>
        if range.isSome then
          discard <| checkCausalDeclaration n
      | _ => pure ()
      unless info.isUnsafe do
        let axioms ← checkCausalDeclaration n
        count := count + 1
        for ax in axioms do
          if !observed.contains ax then observed := observed.push ax
  logInfo m!"CAUSAL AUDIT PASS: {names.size} theorems; {count} declarations; observed axioms {observed}; whitelist [propext, Quot.sound]"

end HarmoniaAudit

elab "#audit_causal" : command => HarmoniaAudit.auditCausal

elab "#audit_causal_declaration " n:ident : command => do
  discard <| HarmoniaAudit.checkCausalDeclaration n.getId
