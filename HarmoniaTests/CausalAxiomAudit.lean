import Harmonia.Theorems.Causal
import Harmonia.Theorems.Lamport
import Harmonia.Theorems.VectorClock
import HarmoniaTests.CausalTest
import HarmoniaTests.AuditPolicy

#audit_causal
#check Harmonia.Causal.happensBefore_irrefl
#check Harmonia.Causal.Lamport.Clocking.sound
#check Harmonia.Causal.Lamport.scalar_incomplete
#check Harmonia.Causal.Vector.Clocking.iff_happensBefore
#check Harmonia.Causal.Vector.Clocking.concurrent_iff_incomparable
#check Harmonia.Causal.Lamport.total_irrefl
#check Harmonia.Causal.Lamport.total_trans
#check Harmonia.Causal.Lamport.total_trichotomy
#check Harmonia.Causal.Lamport.total_extends_causality
#check Harmonia.Causal.Vector.Canonical.iff_happensBefore
#check Harmonia.Causal.Vector.Canonical.OperationalHistory.clock_tick
#check Harmonia.Causal.Vector.Canonical.OperationalHistory.operational_iff
#check Harmonia.Causal.Vector.Canonical.concurrent_iff_incomparable
