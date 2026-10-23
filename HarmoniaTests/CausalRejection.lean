import Harmonia.Theorems.Lamport
import HarmoniaTests.AuditPolicy

open Harmonia.Causal

-- The scalar converse would turn the independent witness into causality.
/-- error: Type mismatch
  Lamport.scalar_incomplete.right.left
has type
  ¬HappensBefore Lamport.independentTrace 0 1
but is expected to have type
  HappensBefore Lamport.independentTrace 0 1 -/
#guard_msgs in
example : HappensBefore Lamport.independentTrace 0 1 := by
  exact Lamport.scalar_incomplete.2.1

namespace Harmonia.Causal.AuditTrap
axiom foreign : False
theorem tainted : True := False.elim foreign
/-- error: CAUSAL audit rejected Harmonia.Causal.AuditTrap.foreign: Harmonia.Causal.AuditTrap.foreign -/
#guard_msgs in
#audit_causal
end Harmonia.Causal.AuditTrap

namespace Harmonia.Causal.AuditTrap

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem placeholder : True := sorryAx True false
/-- error: CAUSAL audit rejected Harmonia.Causal.AuditTrap.placeholder: sorryAx -/
#guard_msgs in
#audit_causal_declaration Harmonia.Causal.AuditTrap.placeholder

theorem chosen : True := Classical.choice ⟨trivial⟩
/-- error: CAUSAL audit rejected Harmonia.Causal.AuditTrap.chosen: Classical.choice -/
#guard_msgs in
#audit_causal_declaration Harmonia.Causal.AuditTrap.chosen

end Harmonia.Causal.AuditTrap
