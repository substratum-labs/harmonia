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

The actual proved `ForwardSimulation` contract is:

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

`lift` produces a valid abstract path, a related final state and precisely the
mapped observation list. `reachable` and `transfer_invariant` use initial-state
matching and the explicit relation-mediated safety obligations above.

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

## Original delivery physical verification (c2ce9e0)

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
- `c2ce9e0`: Task 4 audit/CI/documentation, original stage-one delivery.

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

## Supported source-package review corrections

Resume baseline: `c2ce9e0`, same native worktree and branch. Coordinator reports
independent successful reruns of the original three targets and exact-head Linux
push/PR CI at that commit. Those are coordinator-provided results; this executor
has not accessed remote CI or other projects. Correction-head CI awaits the
coordinator's next run.

Ruling: retain the actual proved API with distinct concrete and abstract action
types, rather than requiring identical action types. `matchStep` universally
covers every related abstract pre-state and every concrete labeled step, and
existentially supplies a single abstract step with the mapped observation and
related successor. Initial matching and relation-mediated safety transfer are
explicit, as detailed above. Current examples use identical Unit actions.
Externally relevant inputs/actions must appear in observations or be constrained
by an application refinement contract; the generic theorem alone does not
certify input/action identity. Cost if this boundary is omitted: an application
could overclaim preservation of behavior it never exposed or constrained.
Finite internal-step/weak refinement, liveness and bisimulation remain deferred.
No proved API or proof changes are made for this ruling.

Audit isolation correction: `foundationsAudit` now has only AuditPolicy and
certified AxiomAudit as roots; `foundationsAuditRejection` builds the adversarial root
separately. AxiomAudit's import closure remains fixture-free, and the automatic
all-new-theorem dependency audit is unchanged. CI and documentation invoke both
commands separately.

Target RED: `lake build foundationsAuditRejection` before implementation returned
exit 1 with `error: unknown target foundationsAuditRejection`.

Disabled clarification: no applicable `(action, observation, successor)` Step
triple at a state; a particular action is disabled when no observation/successor
satisfies its step relation. No new Core outcome enum is introduced.

### Correction verification

Target GREEN: after splitting Lake roots, `lake build foundationsAuditRejection`
returned exit 0 (`Build completed successfully`). The final physical runs on
this correction tree were inspected individually:

| Command/check | Observed result |
| --- | --- |
| `lake build` | exit 0; Build completed successfully |
| `lake build foundationsTest` | exit 0; Build completed successfully |
| `lake build foundationsAudit` | exit 0; certified audit PASS, 52 theorems |
| `lake build foundationsAuditRejection` | exit 0; isolated rejection fixtures pass |
| `lake env lean HarmoniaTests/AxiomAudit.lean` | exit 0; fresh audit PASS, 52 theorems |
| `lake env lean HarmoniaTests/AuditRejection.lean` | exit 0; all expected diagnostics match |
| `git diff --check` | exit 0; no whitespace errors |

Both audit runs report only `[propext, Quot.sound]` in certified theorem
dependencies. The certified module and automatic audit policy are unchanged;
its imports remain Foundations, InvariantProbes, RefinementProbes and AuditPolicy.
No AuditRejection import or root remains in the certified target. Core, examples,
formal proofs, legacy source and `lean-toolchain` have no diff from `c2ce9e0`.

Correction files: lakefile, CI workflow, README, ARCHITECTURE, implementation plan
and this receipt only. The correction commit is the final HEAD named in the
executor handoff. Ready for coordinator final review; no external reviewer,
agents, push, merge or background process was used in this resume.
