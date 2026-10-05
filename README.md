# Harmonia (Ἁρμονία)

Harmonia independently develops formal foundations for distributed algorithms
in Lean. Kadmos is an application, rather than the definition of the Core API.
The approved canonical design is
[the foundation-first design](docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md).

Stage one provides kernel-checked generic relational transition systems,
finite labeled executions, reachability, invariant induction, and one-step
observation-preserving forward simulation lifted to executions. State, action
and observation types are parameters; steps may be nondeterministic or disabled.
The new API lives in `Harmonia.Foundation` and uses Lean 4.16.0's standard
library only. See [architecture](ARCHITECTURE.md) and the
[verification receipt](docs/verification/2026-10-04-foundations-stage-one.md)
for exact guarantees, assumptions and RED/GREEN evidence.

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake build
lake build foundationsTest
lake build foundationsAudit
lake build foundationsAuditRejection
```

`lean-toolchain` pins `leanprover/lean4:v4.16.0`. Foundation verification needs
no SMT solver. The audit enumerates every theorem from the imported new modules,
checks transitive dependencies and prints each theorem's axiom set. Isolated
adversarial fixtures verify rejection of custom axioms and `sorryAx`; they are
built only by `foundationsAuditRejection`, not by the certified
`foundationsAudit` target or its module import closure.

The legacy CLI remains available as `lake exe harmonia`; its SMT demonstrations
require Z3. `Event`, `Network`, `SmallStep`, handwritten 2PC, DSL datatype macros,
SMT queries, C exports and Rust experiments remain legacy prototypes. The Lean
2PC model, SMT behavior and C gatekeeper are not proved compiler-connected.
Timestamp comparison in the legacy Event model does not establish message
causality. No FLP/CAP theorem, distributed crash/recovery guarantee, verified
runtime or solver proof reconstruction is claimed by stage one.

Stage two now supplies minimal distributed semantics. Remaining stages are Kadmos application semantics,
and verification/codegen correspondence, followed by evidence-driven expansion.
Forward simulation transfers the stated safety properties; it does not prove
liveness or bisimulation.

The proved simulation requires a related abstract initial state for every
concrete initial state. For every related abstract pre-state and every concrete
step, it requires one abstract step with the mapped observation and a related
successor. Safety transfer additionally requires that the abstract invariant,
through the state relation, implies the concrete property. The exact quantifiers
are documented in [architecture](ARCHITECTURE.md).

Concrete and abstract internal action types may differ; current examples use
identical `Unit` actions. Externally relevant inputs/actions must be represented
in observations or constrained by an application refinement contract. Finite
internal-step/weak matching remains deferred.

## Minimal distributed semantics (T-392)

Use `import Harmonia.Distributed` for the independent layer. It provides checked
finite membership, restricted local protocol inputs, unordered message occurrences,
and fixed crash/omission profiles. Kernel proofs cover network well-formedness,
frames, durable preservation, fresh IDs, same-label representation lifting and
initialized envelope origin. Concrete histories exhibit duplicate/retry delivery,
crash/recovery and nonhead receive. Logical ID equality does not imply payload
equality or exactly-once processing.

```sh
lake build distributedTest distributedAudit distributedAuditRejection
python3 scripts/check_distributed_audit.py --self-test
python3 scripts/check_distributed_audit.py
```

Reliable forbids drop, duplication, crash and recovery; it promises no eventual
delivery. Abstract atomic local updates/publication require later physical IO
refinement. Protocol safety is a separate obligation; no fairness/liveness or
runtime correctness is claimed. See [architecture](ARCHITECTURE.md) and the
[local receipt](docs/verification/2026-10-04-minimal-distributed-semantics.md).
