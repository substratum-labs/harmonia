import HarmoniaTests.AuditPolicy
import HarmoniaTests.KadmosWorldRejection.Unused
import HarmoniaTests.KadmosWorldRejection.Unsafe
namespace KadmosAuditFixtures
axiom protocol : True
theorem indirect : True := protocol
/-- error: axiom audit rejected KadmosAuditFixtures.indirect: KadmosAuditFixtures.protocol -/
#guard_msgs in
#audit_declaration KadmosAuditFixtures.indirect
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem contaminated : True := sorryAx True false
/-- error: axiom audit rejected KadmosAuditFixtures.contaminated: sorryAx -/
#guard_msgs in
#audit_declaration KadmosAuditFixtures.contaminated
end KadmosAuditFixtures
/-- error: axiom audit rejected KadmosRenamedTrap.unused: KadmosRenamedTrap.unused -/
#guard_msgs in
#audit_module HarmoniaTests.KadmosWorldRejection.Unused
/-- error: axiom audit rejected KadmosRenamedUnsafe.unused: KadmosRenamedUnsafe.unused -/
#guard_msgs in
#audit_module HarmoniaTests.KadmosWorldRejection.Unsafe
/-- error: axiom audit found no source module theorems -/
#guard_msgs in
#audit_module MissingKadmosSource
/-- error: axiom audit declaration does not exist: KadmosAuditFixtures.absent -/
#guard_msgs in
#audit_declaration KadmosAuditFixtures.absent
/-- error: axiom audit found no theorems in MissingKadmosNamespace -/
#guard_msgs in
#audit_namespace MissingKadmosNamespace
namespace Harmonia.Applications.Kadmos.AuditTrap
theorem newlyAdded : True := KadmosAuditFixtures.protocol
end Harmonia.Applications.Kadmos.AuditTrap
/-- error: axiom audit rejected Harmonia.Applications.Kadmos.AuditTrap.newlyAdded: KadmosAuditFixtures.protocol -/
#guard_msgs in
#audit_kadmos_world
