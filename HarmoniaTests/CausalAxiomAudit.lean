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
