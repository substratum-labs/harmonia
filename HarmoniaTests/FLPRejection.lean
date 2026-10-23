import Harmonia.Theorems.FLP
import HarmoniaTests.AuditPolicy

namespace FLPAuditTrap
axiom falseEvidence : False
theorem tainted : True := False.elim falseEvidence
/-- error: axiom audit rejected FLPAuditTrap.tainted: FLPAuditTrap.falseEvidence -/
#guard_msgs in
#audit_declaration FLPAuditTrap.tainted
axiom unused : True
/-- error: axiom audit rejected FLPAuditTrap.unused: FLPAuditTrap.unused -/
#guard_msgs in
#audit_declaration FLPAuditTrap.unused
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem placeholder : True := sorryAx True false
/-- error: axiom audit rejected FLPAuditTrap.placeholder: sorryAx -/
#guard_msgs in
#audit_declaration FLPAuditTrap.placeholder
end FLPAuditTrap

namespace Harmonia.FLP.AuditChoice
noncomputable def chosen {α : Type} (h : Nonempty α) : α := Classical.choice h
end Harmonia.FLP.AuditChoice
/-- error: FLP audit rejected Harmonia.FLP.AuditChoice.chosen: Classical.choice -/
#guard_msgs in
#audit_flp
