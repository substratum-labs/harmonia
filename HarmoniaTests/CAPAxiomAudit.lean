import Harmonia.Theorems.CAP
import HarmoniaTests.CAPTest
import HarmoniaTests.AuditPolicy

#audit_cap
#audit_declaration Harmonia.CAP.lift_left
#audit_declaration Harmonia.CAP.lift_right
#audit_declaration Harmonia.CAP.partition_replay
#audit_declaration Harmonia.CAP.cap_impossibility
