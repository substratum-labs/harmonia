import Harmonia.Theorems.Lamport
import HarmoniaTests.AuditPolicy

open Harmonia.Causal

-- The scalar converse would turn the independent witness into causality.
/-- error: type mismatch
  Lamport.scalar_incomplete.right.left
has type
  ¬HappensBefore Lamport.independentTrace 0 1 : Prop
but is expected to have type
  HappensBefore Lamport.independentTrace 0 1 : Prop -/
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
