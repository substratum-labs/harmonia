# Harmonia architecture

The approved canonical specification is
[2026-10-04 minimal formal core design](docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md).
It replaces the earlier roadmap's guarantee claims. Harmonia develops independent
formal foundations; Kadmos instantiates upper layers.

## Implemented stage one

The generic namespace `Harmonia.Foundation` coexists with the legacy modules:

| Module | Interface and guarantee |
| --- | --- |
| `Core/TransitionSystem.lean` | Universe-polymorphic state/action/observation types; `init` predicate and relational `step`; inductive `Reachable` |
| `Core/Execution.lean` | Proof-indexed finite action/observation lists with endpoints; zero steps, append, prefix/suffix splitting, ordered observations and reachability equivalence |
| `Core/Invariant.lean` | `Initially`, all-successor `Preserved`, and reachable-state `invariant` induction |
| `Core/Refinement.lean` | Related initial states and exact one-step matching through an observation map; execution lifting, reachability and abstract safety transfer |
| `Examples/Foundation.lean` | Bounded counter and nondeterministic bookkeeping counter, initial witnesses, bound proofs and a forward simulation |
| `HarmoniaTests/` | Formal regression probes, automatic theorem dependency audit and isolated audit rejection fixtures |

Execution validity alone does not imply initialization. Reachability starts
from an initial-state proof. No global axiom asserts that every system has an
initial state: nonvacuity is exhibited separately for examples. Preservation
quantifies over every legal action, observation and successor. Models choose
step granularity and observations; the Core assumes no executable transition
function, persistence, physical IO atomicity, checker or verdict mechanism.

Simulation preserves the mapped observation list and matches every concrete
step with exactly one abstract step. Abstract action labels are existential;
state correspondence is an explicit relation. This supports reachable-state
safety transfer, not liveness, fairness, bisimulation, reverse matching or
internal-step erasure. Finite-internal-step refinement is deferred.

The new Core imports only its predecessor foundation modules and Lean's implicit
standard prelude. The umbrella `Harmonia.lean` also imports legacy prototypes;
import a specific foundation module for the independent API.

## Planned layers

1. **Distributed:** explicit finite membership, local processing, message
   occurrences and identities, scheduling, crash/recovery and fault profiles.
2. **Applications/Kadmos:** typed action semantics, reference interpreter,
   verdicts, directives, savepoints and local rollback.
3. **Verification:** sound VC generation, bounded exploration with replay,
   solver adapters and separately reported proof reconstruction.
4. **Codegen and adapters:** supported target representations and correspondence
   theorems, then host concurrency/storage/recovery contracts.
5. **Feedback:** revise abstractions and select later applications from evidence.

These stages are unimplemented here. Infinite executions, temporal logic,
fairness and protocol impossibility results require their own semantics and
assumptions; they are not stage-one guarantees.

## Legacy evidence boundary

Legacy `Event/Network/SmallStep`, protocol definitions, DSL macros, SMT queries,
C exports and Rust examples are preserved. The 2PC initial agreement theorem
concerns its handwritten initial model, not all reachable states. SMT UNSAT
is solver evidence, not a Lean kernel proof. Finite exploration is a bounded
check, not arbitrary-state safety. DSL datatype generation does not generate
protocol semantics. No correspondence theorem connects the separate Lean,
SMT and C behaviors. Legacy performance measurements do not prove correctness.

## Verification

```sh
lake build
lake build foundationsTest
lake build foundationsAudit
```

CI runs these commands on Ubuntu and enforces the Lean 4.16.0 pin. The Mac
linker option is restricted to macOS so Linux uses Lean's default linker.
See the [stage-one receipt](docs/verification/2026-10-04-foundations-stage-one.md)
for physical results and the independent-review handoff. The audit's allowed
standard axioms are `propext`, `Quot.sound` and `Classical.choice`; the receipt
reports which actually occur. The adversarial audit module is deliberately
separate from certified proofs.
