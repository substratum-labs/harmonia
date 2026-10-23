/- Adversarial fixtures only. Never imported by the certified foundation audit. -/
import HarmoniaTests.AuditPolicy
namespace AuditFixtures
axiom protocol : True
theorem indirect : True := protocol
/-- error: axiom audit rejected AuditFixtures.indirect: AuditFixtures.protocol -/
#guard_msgs in
#audit_declaration AuditFixtures.indirect

-- Direct construction deliberately tests detection without a sorry tactic.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem contaminated : True := sorryAx True false
/-- error: axiom audit rejected AuditFixtures.contaminated: sorryAx -/
#guard_msgs in
#audit_declaration AuditFixtures.contaminated
end AuditFixtures

namespace Harmonia.Foundation.AuditTrap
theorem newlyAdded : True := AuditFixtures.protocol
end Harmonia.Foundation.AuditTrap
/-- error: axiom audit rejected Harmonia.Foundation.AuditTrap.newlyAdded: AuditFixtures.protocol -/
#guard_msgs in
#audit_namespace Harmonia.Foundation.AuditTrap

-- The full audit must discover a newly added theorem automatically, without
-- adding its name to an audit list.
/-- error: axiom audit rejected Harmonia.Foundation.AuditTrap.newlyAdded: AuditFixtures.protocol -/
#guard_msgs in
#audit_foundations

/-- error: axiom audit declaration does not exist: AuditFixtures.absent -/
#guard_msgs in
#audit_declaration AuditFixtures.absent

/-- error: axiom audit found no theorems in MissingNamespace -/
#guard_msgs in
#audit_namespace MissingNamespace
