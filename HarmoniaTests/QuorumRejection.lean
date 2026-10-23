import Harmonia.Theorems.Quorum
import HarmoniaTests.AuditPolicy

open Harmonia.Quorum

-- CFT f = 1: a one-node quorum can avoid a two-node quorum in a three-node universe.
example : ([0] : List Nat).length ≤ 1 ∧
    ([1, 2] : List Nat).length ≥ 2 ∧
    (inter [0] [1, 2]).length = 0 := by decide

-- BFT f = 1: two quorums of size 2 can be disjoint in a four-node universe.
example : ([0, 1] : List Nat).length ≤ 2 ∧
    ([2, 3] : List Nat).length ≥ 2 ∧
    (inter [0, 1] [2, 3]).length = 0 := by decide

namespace QuorumAuditTrap
axiom falseEvidence : False
theorem tainted : True := False.elim falseEvidence
/-- error: axiom audit rejected QuorumAuditTrap.tainted: QuorumAuditTrap.falseEvidence -/
#guard_msgs in
#audit_declaration QuorumAuditTrap.tainted
axiom unused : True
/-- error: axiom audit rejected QuorumAuditTrap.unused: QuorumAuditTrap.unused -/
#guard_msgs in
#audit_declaration QuorumAuditTrap.unused
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem placeholder : True := sorryAx True false
/-- error: axiom audit rejected QuorumAuditTrap.placeholder: sorryAx -/
#guard_msgs in
#audit_declaration QuorumAuditTrap.placeholder
end QuorumAuditTrap

namespace Harmonia.Quorum.AuditTrap
theorem tainted : True := False.elim QuorumAuditTrap.falseEvidence
end Harmonia.Quorum.AuditTrap
/-- error: axiom audit rejected Harmonia.Quorum.AuditTrap.tainted: QuorumAuditTrap.falseEvidence -/
#guard_msgs in
#audit_quorum
