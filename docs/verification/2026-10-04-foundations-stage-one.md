# T-391 stage-one execution receipt

Worktree: `/Users/yong/.codex/worktrees/16ce/harmonia`.
Branch: `feat/t391-foundations-stage-one`. Baseline: `40f8609`.
Toolchain: `leanprover/lean4:v4.16.0`; standard library only.

## Preflight and rulings

- Ruling: execution receipt doubles as durable task ledger, rather than an
  ephemeral skill workspace; the user requires committed durable evidence.
  Cost if wrong: workflow bookkeeping differs; proof scope is unchanged.
- Ruling: `Harmonia.Foundation` isolates generic modules from legacy semantics;
  executions use proof-indexed lists of action/observation pairs and require
  initial-state evidence separately. Cost if wrong: later API adaptation.
- Ruling: one-step simulation only, as planned; no finite internal-step matching.
  Cost if wrong: later models need a separate weak simulation interface.
- Ruling: coordinator owns independent review and integration, superseding the
  old plan's Grok/agent review step; no reviewers, push or merge here.
- Ruling: hosted CI cannot run without pushing; supply CI and execute its checks
  physically on this Mac. Linux CI remains unobserved until coordinator runs it.

Shared interfaces: Task 1 → 2/3 Execution/Reachable; Task 2 → 3 invariant;
Tasks 1–3 → 4 automatic theorem dependency audit. Exact signatures and probes
are pinned in the plan preflight and test sources.

## Execution evidence

Branch creation: initial sandbox denial (exit 128); authorized Git metadata
escalation succeeded (exit 0). No other project content was read or edited.

Task 1 RED: `lake env lean HarmoniaTests/Foundations.lean` exit 1, missing
`Harmonia/Core/Execution.olean` after baseline `lake build` exit 0 (26 targets).
Initial invocation also lacked baseline artifacts; the second RED isolated the
missing implementation. Probes check actual propositions, including two legal
successors and invalid observation traces.

Task 1 GREEN: `lake build Harmonia` and `lake env lean
HarmoniaTests/Foundations.lean` exit 0; full `lake build` and repeated probe
exit 0. During development, build exit 1 exposed the explicit argument
signature of `List.map_append` in Lean 4.16; supplying `Prod.snd xs ys` resolved
it without changing the API or probes. Task 1 complete.

Task 2 RED: `lake env lean HarmoniaTests/InvariantProbes.lean` exit 1,
missing `Invariant.olean`. Unsafe model has initial 0 and an actual reachable
successor 3; probe negates all-successor preservation of the bound 2.

Task 2 GREEN: full `lake build`, Foundations and InvariantProbes commands exit
0. Intermediate fixture errors: reserved `unsafe` identifier renamed
`unsafeSystem`, and unused Unit action supplied explicitly in the reachable
witness. A shell invocation whose trailing diff check returned 0 still printed
an elaboration error; it was not accepted as GREEN. The subsequent separate
probe and chained build/tests returned 0 with no diagnostics. Task 2 complete.

Task 3 RED: `lake env lean HarmoniaTests/RefinementProbes.lean` exit 1,
missing `Examples/Foundation.olean`. Probes require two-step and empty path
lifting, safety transfer, rejection of a constant wrong observation map, and
failure of simulation to a system with no initial states.

Task 3 GREEN: `lake build Harmonia` plus RefinementProbes exit 0; an unused
binder warning was removed. Full `lake build` and all three probe commands
then exit 0 without new warnings. Task 3 complete. `simulation` is a proved
value of the simulation proposition, not a custom axiom.

Task 4 RED: missing AuditPolicy import initially returned exit 1. With a
nonchecking audit policy stub, `lake build foundationsAudit` returned exit 1
because all three expected rejection diagnostics were absent (the decisive
policy RED). Explicit roots were needed for Lake to build AuditPolicy.
Implemented dependency checks made those fixtures pass. A second policy RED
(exit 1) showed unknown declaration names were silently accepted by Lean's
collector; an existence check made that rejection probe GREEN.

Ruling: safe source definitions/axioms are audited in addition to every theorem.
Compiler-generated unsafe specializations are excluded from the additional
scan: Lean 4.16 creates nonlogical opaque implementation placeholders such as
`List.mapTR.loop._at..._spec_1`. Every theorem's transitive dependency set is
checked without filtering. Cost if wrong: execution-level compiler correctness
is outside this audit; theorem dependency coverage remains complete.

Ruling: preserve the legacy macOS linker option only on macOS, using default
Lean linking on Linux to make the new CI portable. Cost if wrong: Linux linking
will be exposed by coordinator CI; legacy Mac behavior is preserved.

Task 4 audit GREEN: `lake build foundationsAudit` exit 0, 52 theorem
declarations, observed axioms `[propext, Quot.sound]`. `Classical.choice` is
allowed but unobserved. Rejection fixtures test transitive custom protocol
axioms, explicit `sorryAx`, newly-added theorem enumeration, unknown declaration
names and empty theorem namespaces. Their deliberate contaminants are isolated
in AuditRejection, never imported by AxiomAudit or production modules.

## API and exact proof guarantees

`TransitionSystem S A O` is universe-polymorphic and supplies `init : S → Prop`
and `step : S → A → O → S → Prop`. No determinism, decidability, inhabitance
or executability requirement is imposed.

`Execution T s labels t` carries a valid finite path indexed by its endpoints
and `List (A × O)` labels. `nil` has identical endpoints; `cons` requires a real
step. `Execution.append` composes paths, `Execution.split` cuts any prefix
and suffix, and `observations_append` preserves list order. `execution_reachable`
requires an initial-state witness. `reachable_iff_execution` characterizes
reachable states exactly as endpoints of initialized finite paths.

`Initially T I` and `Preserved T I` imply `invariant`: every reachable state
satisfies I. Preservation covers all labeled successors, not a selected branch.

`ForwardSimulation C B R obsMap` requires an abstract related initial state for
every concrete initial state, and one abstract step with mapped observation
for each concrete step from every related pair. `lift` produces a valid abstract
path, a related final state and precisely the mapped observation list.
`reachable` and `transfer_invariant` transfer abstract reachable-state safety.
Action labels may differ; no map of actions is promised.

Examples: counter starts at 0, increments while below 2, emits its successor,
and stays within bound 2. The concrete state pairs that counter with Boolean
bookkeeping, whose next value is unconstrained. `concrete_choices` exhibits two
legal successors; initial witnesses and `simulation` are proved. Regression
models include an unsafe successor 3 (reachable and not preserved), missing
initial states, wrong labels/maps, and zero-step execution/lifting.

## Assumptions and trusted boundary

Generic guarantees are conditional on the supplied init/step predicates and
proofs of invariant/simulation obligations. Example arithmetic and relations
are definitions, with explicit initial witnesses and no protocol axioms.
Lean kernel checking and the standard axioms actually reported by the audit
are the proof boundary. No SMT, finite search, native_decide, Veil, Loom or
mathlib is used. The audit command itself is build tooling, not a kernel proof
of audit implementation correctness; adversarial tests validate its policy.

## Remaining stages and review handoff

Only exact one-step forward simulation is implemented. No finite silent-step
matching, infinite executions, fairness, liveness, temporal framework, reverse
simulation or bisimulation. Distributed nodes/messages/fault/recovery semantics,
Kadmos DSL/checker/savepoint semantics, VC/SMT proof reconstruction, target-code
correspondence and host integration remain future stages. Legacy experiments
remain behaviorally unchanged and unconnected by a correspondence theorem.

Independent review and managed integration are the coordinator's responsibility.
No external reviewer, agents, push, merge or background process is used. Hosted
Linux CI is supplied but has not run in this invocation. Machine-specific
command logs and generated artifacts are outside Git; this receipt records
portable commands, outputs and exit codes.

## Final physical verification

| Command/check | Observed result |
| --- | --- |
| `lake env lean --version` | exit 0; Lean 4.16.0, arm64-apple-darwin |
| `lake build` | exit 0; Build completed successfully |
| `lake build foundationsTest` | exit 0; all three formal regression modules built |
| `lake build foundationsAudit` | exit 0; audit PASS, 52 theorem declarations; rejection fixtures pass |
| `lake env lean HarmoniaTests/AxiomAudit.lean` | exit 0; fresh elaboration, all 52 dependency sets printed, same PASS |
| `lake env lean HarmoniaTests/AuditRejection.lean` | exit 0; all expected diagnostics matched |
| `git diff --check` | exit 0; no whitespace errors |
| Import inspection | only predecessor foundation imports in new Core/example modules |
| Forbidden-proof source scan | rg exit 1 (no matches) in certified new Core, examples and regression proofs |
| Legacy source diff from `40f8609` | empty: Event/Network/SmallStep, Protocols, DSL, SMT, Gatekeeper, Main, examples and toolchain unchanged |

The proof scan excluded the explicitly adversarial AuditRejection fixtures.
Observed standard axioms are `propext` and `Quot.sound`; no `Classical.choice`,
`sorryAx` or custom protocol axiom in the certified audit. Includes generated
structure theorems and proposition-valued field projections, as well as all
named public proof declarations and formal probes; no handpicked theorem list.

## Commits and changed files

- `2e6fa41`: Task 1 relational systems and labeled finite executions; preflight.
- `f593785`: Task 2 all-successor invariant induction and unsafe mutant probes.
- `b97c058`: Task 3 execution lifting, safety transfer and nonvacuous examples.
- Delivery commit containing this receipt: Task 4 audit/CI/documentation, identified
  by final branch HEAD in the executor handoff (avoids a self-referential hash).

Changed files, relative to this worktree:

- `Harmonia/Core/TransitionSystem.lean`
- `Harmonia/Core/Execution.lean`
- `Harmonia/Core/Invariant.lean`
- `Harmonia/Core/Refinement.lean`
- `Harmonia/Examples/Foundation.lean`
- `HarmoniaTests/Foundations.lean`
- `HarmoniaTests/InvariantProbes.lean`
- `HarmoniaTests/RefinementProbes.lean`
- `HarmoniaTests/AuditPolicy.lean`
- `HarmoniaTests/AuditRejection.lean`
- `HarmoniaTests/AxiomAudit.lean`
- `Harmonia.lean`
- `lakefile.lean`
- `README.md`
- `ARCHITECTURE.md`
- `.github/workflows/foundations.yml`
- `docs/superpowers/plans/2026-10-04-generic-transition-foundations.md`
- `docs/verification/2026-10-04-foundations-stage-one.md`

Task 4 complete for the bounded executor scope. Ready for coordinator independent
review; no claim that independent review or hosted CI has already passed.
No deferred minor findings were recorded. No background process remains.
