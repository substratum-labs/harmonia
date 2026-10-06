import HarmoniaTests.AuditPolicy
import HarmoniaTests.KadmosBridgeRejection.Unused
import HarmoniaTests.KadmosBridgeRejection.Unsafe
namespace KadmosBridgeRejection
axiom protocol : True
theorem indirect : True := protocol
/-- error: axiom audit rejected KadmosBridgeRejection.indirect: KadmosBridgeRejection.protocol -/
#guard_msgs in
#audit_declaration KadmosBridgeRejection.indirect
/-- error: axiom audit rejected KadmosBridgeEscapedTrap.unused: KadmosBridgeEscapedTrap.unused -/
#guard_msgs in
#audit_module HarmoniaTests.KadmosBridgeRejection.Unused
/-- error: axiom audit rejected KadmosBridgeEscapedUnsafe.unused: KadmosBridgeEscapedUnsafe.unused -/
#guard_msgs in
#audit_module HarmoniaTests.KadmosBridgeRejection.Unsafe
end KadmosBridgeRejection
