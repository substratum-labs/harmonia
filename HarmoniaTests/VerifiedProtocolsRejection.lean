import HarmoniaTests.AuditPolicy

/- Isolated hostile declarations; never imported by a certified protocol module. -/
namespace VerifiedProtocolsAuditTrap
axiom falseEvidence : False
theorem tainted : True := False.elim falseEvidence
/-- error: axiom audit rejected VerifiedProtocolsAuditTrap.tainted: VerifiedProtocolsAuditTrap.falseEvidence -/
#guard_msgs in
#audit_declaration VerifiedProtocolsAuditTrap.tainted
axiom unused : True
/-- error: axiom audit rejected VerifiedProtocolsAuditTrap.unused: VerifiedProtocolsAuditTrap.unused -/
#guard_msgs in
#audit_declaration VerifiedProtocolsAuditTrap.unused
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem placeholder : True := sorryAx True false
/-- error: axiom audit rejected VerifiedProtocolsAuditTrap.placeholder: sorryAx -/
#guard_msgs in
#audit_declaration VerifiedProtocolsAuditTrap.placeholder

noncomputable def chosen {α : Type} (h : Nonempty α) : α := Classical.choice h
theorem choiceAuditWitness : True := True.intro
/-- error: axiom audit rejected VerifiedProtocolsAuditTrap.chosen: Classical.choice -/
#guard_msgs in
run_cmd do
  HarmoniaAudit.auditSelected
    (fun n => n == ``VerifiedProtocolsAuditTrap.chosen ||
      n == ``VerifiedProtocolsAuditTrap.choiceAuditWitness) "verified protocols rejection"
    true "VERIFIED PROTOCOLS REJECTION" false
end VerifiedProtocolsAuditTrap
