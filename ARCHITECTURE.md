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

## Implemented stage two

Import `Harmonia.Distributed` independently of the legacy umbrella.
`Membership` checks an explicit finite list without deduplication; member subtypes
constrain actors and endpoints. Empty configuration is valid, with no actors.
`Protocol` takes only actor, own durable/volatile data and explicit message or
scheduler input. This argument boundary requires fixed-closure discipline; it
is not an epistemic theorem about arbitrary external Lean closures.

`Network` distinguishes application logical IDs from unique Nat transmission
occurrences. Same logical ID may carry different payloads; duplicate copies an
entire envelope under a fresh occurrence ID. Take is a permutation-based
one-occurrence removal, so receive/drop can select any position. Publication
assigns an unbounded monotone supply to a finite outgoing list. This supply is
model bookkeeping, not a central runtime service, and is not protocol input.

`Semantics` defines process, deliver, drop, duplicate, crash and recover labels.
Local processing/delivery require running status; a timeout says nothing about
peers. The fixed profile independently gates each fault. Reliable disables all
four faults, without promising eventual delivery. Crash preserves durable data,
resets volatile data with crashReset D V, and recovery rebuilds V from D only.
Inflight messages survive both. Local durable/volatile update and outgoing
publication are one abstract atomic step, with no physical IO guarantee.

`Properties` proves all-successor network WF via Foundation.invariant, frame
(the delivery actor is recipient), durable preservation, consumption, fresh
duplication, init/WF permutation transport, and same-label finite execution
lifting modulo PoolEq. Exact crash/recovery list preservation makes lifting
existential over related successors. Initialized pending-envelope origin is
proved separately from unique transmission IDs: it records prior envelope
publication, not the allocating step of every occurrence or payload authenticity.
A consumed tid cannot replay in reachable WF states; malformed raw duplicate-tid
pools can admit a second consumption and are shown unreachable.

The single source `Harmonia.Examples.Distributed` has namespace
`Harmonia.Distributed.Examples`; Traces imports it explicitly. Fixtures witness
send/crash/recover/deliver, nonzero volatile loss/rebuild, duplicate and retry
delivery twice, nonhead/reordered receive, other-node frames and scheduler timeout
with a running peer. All histories are finite, with no semantic depth/message
bound. No automatic protocol invariant, fairness/liveness, consensus, crypto,
physical runtime, codegen or legacy correspondence claim is made.

Dedicated verification:

```sh
python3 scripts/check_distributed_audit.py --self-test
python3 scripts/check_distributed_audit.py
lake build distributedTest distributedAudit distributedAuditRejection
```

The shared audit retains stage-one coverage and scans source modules independently
of declaration namespace, all theorem dependencies and unused source axioms.
Unsafe compiler placeholders without declaration ranges are excluded only from
the auxiliary scan. Unsafe source axioms with ranges still reject, as tested;
source inventory also rejects forbidden proof tokens. Inventory detects missing
imports/manifest entries, namespace escape and adversarial imports in either
certified closure. Rejection modules remain isolated. Ubuntu CI includes all
foundation/distributed targets, inventory tests and pinned/running version checks.
Observed local results and review boundary are in the
[stage-two receipt](docs/verification/2026-10-04-minimal-distributed-semantics.md).

## Remaining layers

1. **Applications/Kadmos:** typed action semantics, reference interpreter,
   verdicts, directives, savepoints and local rollback.
2. **Verification:** sound VC generation, bounded exploration with replay,
   solver adapters and separately reported proof reconstruction.
3. **Codegen and adapters:** supported target representations and correspondence
   theorems, then host concurrency/storage/recovery contracts.
4. **Feedback:** revise abstractions and select later applications from evidence.

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
