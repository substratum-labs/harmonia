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
  let select := HarmoniaAudit.foundationDeclaration env
  let names := HarmoniaAudit.theoremNames env select
  if names.isEmpty then throwError "axiom audit found no foundation theorems"
  -- Check safe definitions and axioms too. Compiler-only unsafe
  -- specializations are not logical declarations; theorem dependencies
  -- are always checked without this filter.
  for (n, info) in env.constants.toList do
    if select n && !info.isUnsafe then discard <| HarmoniaAudit.checkDeclaration n
  let mut observed : Array Name := #[]
  for n in names do
    let axioms ← HarmoniaAudit.checkDeclaration n
    for ax in axioms do
      if !observed.contains ax then observed := observed.push ax
    logInfo m!"{n}: {axioms}"
  logInfo m!"AUDIT PASS: {names.size} theorems; observed axioms {observed}; whitelist [propext, Quot.sound, Classical.choice]"
