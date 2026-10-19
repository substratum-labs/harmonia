# Causal clocks model (T-402)

`Trace` is a finite, duplicate-free list of Nat event IDs. IDs enumerate an
acyclic execution. Program order is defined directly by membership, equal
node ID, and increasing event ID. Matching message sends and receives must
increase the ID; each message ID has at most one send in the trace.
`HappensBefore` is the inductive transitive closure of program and message
order. It only relates listed events.

`Lamport.Clocking` supplies the pre-event local scalar, attached message
scalars, and the tick/merge rules. Its `local_precedes` field requires all
prior events on a process to be included in the successor's pre-event
register. The clock condition follows from these rules. The strict total
extension orders by `(clock, node ID, event ID)`. Event IDs are unique, so
the final tie breaker is total. The explicit two-event execution has scalar
clocks 1 and 2 but no causal edge.

`VectorClock` is `Fin N → Nat`. The operational `Clocking` interface supplies
local ranks, causal component frontiers, pre-event vectors, message payloads,
componentwise merge, and increment. Its isomorphism theorem is conditional
on the history invariants. The stronger `Canonical` construction computes
component values as the greatest process rank in each event's finite causal
past. Its soundness, completeness, and concurrency theorems derive from
program order, causal reachability, and strictly increasing process ranks;
they do not assume a clock comparison or a component frontier. A witnessed
send/receive execution instantiates this construction.

`Canonical.OperationalHistory` ties the denotational clock to process
registers and message payloads. It requires that these inputs represent the
strict causal past (`input_eq`) and that an event's local rank is the next
count (`rank_next`). The kernel then proves the local/receive
`increment (merge ...)` rule and the same happened-before isomorphism. The
two-event send/receive test constructs these inputs and proves both the
update and the causal comparison. The library does not synthesize input
registers or a reachability decision procedure for every arbitrary trace;
those are explicit model inputs, rather than hidden axioms.

All certified theorem modules import only Lean Init or the causal theorem
modules. The dedicated audit checks causal declarations against `[propext,
Quot.sound]`, rejects source `unsafe`, and isolates deliberately invalid
claims in `CausalRejection.lean`. No solver result or finite exploration is
claimed as a kernel proof. Legacy 2PC, SMT, and C experiments have no
asserted correspondence here.
