import HarmoniaTests.AuditPolicy
import HarmoniaTests.KadmosGeneratedK02Rejection.Unused
import HarmoniaTests.KadmosGeneratedK02Rejection.Unsafe

namespace KadmosGeneratedK02Rejection
axiom protocol : True
theorem indirect : True := protocol

/-- error: axiom audit rejected KadmosGeneratedK02Rejection.indirect: KadmosGeneratedK02Rejection.protocol -/
#guard_msgs in
#audit_declaration KadmosGeneratedK02Rejection.indirect

/-- error: axiom audit rejected KadmosGeneratedK02EscapedTrap.unused: KadmosGeneratedK02EscapedTrap.unused -/
#guard_msgs in
#audit_module HarmoniaTests.KadmosGeneratedK02Rejection.Unused

/-- error: axiom audit rejected KadmosGeneratedK02EscapedUnsafe.unused: KadmosGeneratedK02EscapedUnsafe.unused -/
#guard_msgs in
#audit_module HarmoniaTests.KadmosGeneratedK02Rejection.Unsafe
theorem choice_dependency (h : Nonempty Nat) : ∃ _ : Nat, True :=
  ⟨Classical.choice h, True.intro⟩

/-- error: axiom audit rejected KadmosGeneratedK02Rejection.choice_dependency: Classical.choice -/
#guard_msgs in
#audit_kadmos_generated_declaration KadmosGeneratedK02Rejection.choice_dependency

end KadmosGeneratedK02Rejection
