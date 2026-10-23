import Harmonia.Theorems.CAP
import HarmoniaTests.AuditPolicy

open Harmonia.CAP Harmonia.Foundation

-- A connected system shares one register across both sides of the cut.
private def connected : TransitionSystem Nat (Side × Op Nat) (Resp Nat) where
  init _ := True
  step before action response after :=
    (register Nat).step before action.2 response after

-- With cross-component communication, G2 can read the completed G1 write.
example : Execution connected 0
    [((.left, .write 1), .ok), ((.right, .read), .val 1)] 1 := by
  apply Execution.cons (m := 1)
  · left; exact ⟨1, rfl, rfl, rfl⟩
  apply Execution.cons (m := 1)
  · right; exact ⟨rfl, rfl, rfl⟩
  exact .nil

namespace CAPAuditTrap
axiom falseEvidence : False
theorem tainted : True := False.elim falseEvidence
/-- error: axiom audit rejected CAPAuditTrap.tainted: CAPAuditTrap.falseEvidence -/
#guard_msgs in
#audit_declaration CAPAuditTrap.tainted
axiom unused : True
/-- error: axiom audit rejected CAPAuditTrap.unused: CAPAuditTrap.unused -/
#guard_msgs in
#audit_declaration CAPAuditTrap.unused
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem placeholder : True := sorryAx True false
/-- error: axiom audit rejected CAPAuditTrap.placeholder: sorryAx -/
#guard_msgs in
#audit_declaration CAPAuditTrap.placeholder
end CAPAuditTrap

namespace Harmonia.CAP.AuditTrap
theorem tainted : True := False.elim CAPAuditTrap.falseEvidence
end Harmonia.CAP.AuditTrap
/-- error: CAP audit rejected Harmonia.CAP.AuditTrap.tainted: CAPAuditTrap.falseEvidence -/
#guard_msgs in
#audit_cap
