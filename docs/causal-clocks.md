# Causal clocks model (T-402)

`Trace` is a finite, duplicate-free list of Nat event IDs. IDs enumerate an
acyclic execution. Local edges connect successive events on one process and
must increase the ID; matching message send/receive pairs must also increase
the ID. `HappensBefore` is the inductive transitive closure of those two edge
kinds, restricted to listed events. The local adjacency claim is supplied by
the trace constructor; the type checks node agreement and forward order but
does not reconstruct adjacency from the event list.

`Lamport.Clocking` supplies the pre-event local scalar, attached message
scalars, and the tick/merge rules. Its `local_precedes` field requires an
edge's earlier event clock to be included in the successor's pre-event clock.
The clock condition follows from these rules. The strict total extension
orders by `(clock, node ID, event ID)`. Event IDs are unique, so the final tie
breaker is total. The explicit two-event execution has scalar clocks 1 and 2
but no causal edge.

`Vector.Clocking` supplies a finite `Fin N → Nat` vector, pre-event vector,
message vector, componentwise merge, and increment of the current node's
component. The strong isomorphism applies to events listed in a trace. In
addition to the update rule, it assumes two history invariants: local ranks
order events on each process (`process_prefix`), and a positive observed
component has an actual latest event on that process in the causal past
(`component_frontier`). `rank_self` links an event's own component to its
rank. These fields express vector provenance; the theorem derives the
causal implication from them. The library does **not** prove that arbitrary
recorded ticks establish those invariants. A concrete independent two-node
clocking in `CausalTest.lean` inhabits the model and demonstrates vector
incomparability for concurrency.

All certified modules import only Lean Init or the causal theorem modules.
The dedicated audit checks all causal declarations against `[propext,
Quot.sound]`, rejects source `unsafe`, and isolates deliberately invalid
claims in `CausalRejection.lean`. No solver result or finite exploration is
claimed as a kernel proof; the kernel checks the stated conditional theorems.
Legacy 2PC, SMT, and C experiments have no asserted correspondence here.
