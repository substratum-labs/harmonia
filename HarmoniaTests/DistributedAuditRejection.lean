import HarmoniaTests.AuditPolicy
import HarmoniaTests.DistributedRejection.Unused
import HarmoniaTests.DistributedRejection.Unsafe
namespace DistributedAuditFixtures
axiom protocol : True
theorem indirect : True := protocol
/-- error: axiom audit rejected DistributedAuditFixtures.indirect: DistributedAuditFixtures.protocol -/
#guard_msgs in
#audit_declaration DistributedAuditFixtures.indirect
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem contaminated : True := sorryAx True false
/-- error: axiom audit rejected DistributedAuditFixtures.contaminated: sorryAx -/
#guard_msgs in
#audit_declaration DistributedAuditFixtures.contaminated
end DistributedAuditFixtures
/-- error: axiom audit rejected RenamedTrap.unused: RenamedTrap.unused -/
#guard_msgs in
#audit_module HarmoniaTests.DistributedRejection.Unused
/-- error: axiom audit rejected RenamedUnsafe.unused: RenamedUnsafe.unused -/
#guard_msgs in
#audit_module HarmoniaTests.DistributedRejection.Unsafe
/-- error: axiom audit found no source module theorems -/
#guard_msgs in
#audit_module MissingSourceModule
/-- error: axiom audit declaration does not exist: DistributedAuditFixtures.absent -/
#guard_msgs in
#audit_declaration DistributedAuditFixtures.absent
/-- error: axiom audit found no theorems in MissingDistributedNamespace -/
#guard_msgs in
#audit_namespace MissingDistributedNamespace
namespace Harmonia.Distributed.AuditTrap
theorem newlyAdded : True := DistributedAuditFixtures.protocol
end Harmonia.Distributed.AuditTrap
/-- error: axiom audit rejected Harmonia.Distributed.AuditTrap.newlyAdded: DistributedAuditFixtures.protocol -/
#guard_msgs in
#audit_namespace Harmonia.Distributed.AuditTrap
/-- error: axiom audit rejected Harmonia.Distributed.AuditTrap.newlyAdded: DistributedAuditFixtures.protocol -/
#guard_msgs in
#audit_distributed
