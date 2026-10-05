/- Build-time audit tooling, separate from the generic proof kernel API. -/
import Lean
open Lean Elab Command

namespace HarmoniaAudit

def allowed (n : Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

def checkDeclaration (n : Name) : CommandElabM (Array Name) := do
  unless (← getEnv).contains n do
    throwError "axiom audit declaration does not exist: {n}"
  let axioms ← collectAxioms n
  for ax in axioms do
    unless allowed ax do
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
def auditSelected (select : Name → Bool) (label : String) (allObserved : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, info) in declarations do
    if select n then
      match info with
      | .axiomInfo _ =>
        let range ← findDeclarationRanges? n
        unless info.isUnsafe && range.isNone do discard <| checkDeclaration n
      | _ => pure ()
  let names := theoremNames env select
  if names.isEmpty then throwError "axiom audit found no {label} theorems"
  let mut observed : Array Name := #[]
  let mut count := 0
  for (n, info) in declarations do
    if select n && !info.isUnsafe then
      let axioms ← checkDeclaration n
      count := count + 1
      if allObserved then
        for ax in axioms do
          if !observed.contains ax then observed := observed.push ax
  for n in names do
    let axioms ← checkDeclaration n
    for ax in axioms do
      if !observed.contains ax then observed := observed.push ax
    logInfo m!"{n}: {axioms}"
  if allObserved then
    logInfo m!"DISTRIBUTED AUDIT PASS: {names.size} theorems; {count} declarations; observed axioms {observed}; whitelist [propext, Quot.sound, Classical.choice]"
  else
    logInfo m!"AUDIT PASS: {names.size} theorems; observed axioms {observed}; whitelist [propext, Quot.sound, Classical.choice]"

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
