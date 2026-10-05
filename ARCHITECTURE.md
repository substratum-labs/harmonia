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

The actual proved forward-simulation interface is:

```lean
structure ForwardSimulation (C : TransitionSystem CS CA CO)
    (B : TransitionSystem BS BA BO) (R : CS → BS → Prop) (obsMap : CO → BO) : Prop where
  initial : ∀ c, C.init c → ∃ b, B.init b ∧ R c b
  matchStep : ∀ c a o c' b, R c b → C.step c a o c' →
    ∃ ba b', B.step b ba (obsMap o) b' ∧ R c' b'
```

For every concrete initial state, `initial` supplies at least one related
abstract initial state. `matchStep` covers **every** concrete pre-state, action,
observation and successor, and **every** abstract pre-state related to that
concrete pre-state. Each such concrete step must have one matching abstract
step with observation `obsMap o` and a related successor. Abstract action `ba`
and successor `b'` are existentially chosen for that obligation; no uniqueness
or determinism is required.

Safety transfer requires both `∀ b, Reachable B b → I b` and
`∀ c b, R c b → I b → J c`; it then establishes `J c` for every reachable
concrete state. The relation-mediated implication is an explicit obligation,
not automatic equality of state predicates.

Concrete and abstract action types `CA` and `BA` may differ. The Core preserves
declared observations, without asserting equality or a map of action labels.
Inputs/actions that are externally relevant must be represented in observations
or constrained by an application refinement contract. The current examples use
identical `Unit` actions. Finite internal-step/weak matching remains deferred;
this interface does not establish liveness or bisimulation.

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
lake build foundationsAuditRejection
```

CI runs these commands on Ubuntu and enforces the Lean 4.16.0 pin. The Mac
linker option is restricted to macOS so Linux uses Lean's default linker.
See the [stage-one receipt](docs/verification/2026-10-04-foundations-stage-one.md)
for physical results and the independent-review handoff. The audit's allowed
standard axioms are `propext`, `Quot.sound` and `Classical.choice`; the receipt
reports which actually occur. `foundationsAudit` has only AuditPolicy and the
certified AxiomAudit as roots; their import closure contains no AuditRejection.
`foundationsAuditRejection` separately elaborates the adversarial fixtures.
Automatic coverage of every new theorem remains in the certified audit.
