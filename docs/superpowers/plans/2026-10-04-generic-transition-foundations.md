# Generic Transition Foundations Implementation Plan

> For agentic workers: execute task by task using superpowers:executing-plans. Yong explicitly authorized actual physical CLI managed execution and reviewed integration. No additional routine approval is needed.

**Goal:** Complete stage one: a generic, nondeterministic labeled transition foundation with kernel-checked safety and observation-preserving refinement.

**Architecture:** A new generic namespace coexists with legacy distributed prototypes. Generic states, actions and observations form a relational system; proof-carrying finite executions connect to reachability. Concrete examples instantiate this foundation without checker APIs.

**Tech Stack:** Lean 4.16.0 and its standard library only. No Veil, Loom, mathlib or solver dependency for this delivery.

**Spec:** `docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md`, approved by Yong; scope limited to stage one.

## Global Constraints

- Preserve legacy protocol/SMT/C source behavior. Correct documentation claims and route to the accepted design.
- Core must not depend on Kadmos, savepoints, verdicts, DSL macros, solver IO or physical storage.
- Transitions may be nondeterministic and disabled. Atomicity is instance-specific.
- No sorry, admit, sorryAx, hidden axioms or native_decide in certified new foundation proofs.
- Work in an isolated native worktree; no secrets, caches or generated artifacts in commits.

## Review Focus

1. Empty initial states must be distinguishable from a nonvacuous example; explicitly exhibit initial states.
2. Multiple enabled successors must remain legal; test a nondeterministic example.
3. Incorrect action or observation labels must not validate a trace; show impossible-label cases.
4. Zero-step and concatenated executions must retain endpoints and observation ordering.
5. State invariants must hold for every legal successor; unsafe mutants must be rejected by proof obligations rather than omitted from the relation.

## Files and interfaces

- `Harmonia/Core/TransitionSystem.lean`: parameterized system with `init : State → Prop` and `step : State → Action → Observation → State → Prop`, plus inductive reachable states.
- `Harmonia/Core/Execution.lean`: finite labeled executions, endpoints, observation sequence, concatenation, prefixes, and correspondence to reachable states.
- `Harmonia/Core/Invariant.lean`: initialization/preservation predicates and generic induction safety theorem.
- `Harmonia/Core/Refinement.lean`: state relation and observation mapping for forward simulation; lift concrete executions and transfer abstract invariants. Begin with one-step matching and document this boundary.
- `Harmonia/Examples/Foundation.lean`: initial witnesses, deterministic/disabled/nondeterministic cases, labeled traces and a concrete-to-abstract refinement.
- `HarmoniaTests/Foundations.lean`: theorem probes including negative cases for wrong labels and unsafe transitions.
- `HarmoniaTests/AxiomAudit.lean`: inspect dependencies of new public theorems, reject sorryAx and unexpected axioms; report standard Lean axioms explicitly.
- `Harmonia.lean`, `lakefile.lean`: expose new modules and dedicated test/audit targets without changing existing demo behavior.
- `README.md`, `ARCHITECTURE.md`: identify legacy demonstrations versus newly proved foundations and exact verification commands.

Public names may be adapted to Lean 4.16.0 during planning preflight; record each change in the execution receipt. Keep interfaces documented and consistent across modules.

## Task 1 System and finite execution

- [x] Write theorem probes before production definitions; run them and record the expected missing-foundation failure.
- [x] Implement the generic relational system, zero-step execution, labeled step extension and concatenation.
- [x] Prove endpoint/observation behavior, valid prefixes and execution/reachability correspondence.
- [x] Demonstrate one initial state, a disabled action, two legal successors, and impossible wrong-label traces.
- [x] Run the test target and `lake build`; commit the independently usable deliverable.

Suggested contract shape:

```lean
structure TransitionSystem (S A O : Type) where
  init : S → Prop
  step : S → A → O → S → Prop
```

Trace test: initial 0 has actions inc and fork; inc emits 1 and reaches 1; fork permits 1 or 2 with explicit observations. A label not in the relation must not form a valid trace. Concatenation of 0→1 and 1→2 must emit the two observations in order.

## Task 2 Invariant principles

- [x] State initialization and all-successor preservation obligations in tests; observe RED before adding the theorem.
- [x] Prove reachable-state invariant preservation by induction.
- [x] Prove the bounded-counter instance with explicit initial witness.
- [x] Include an unsafe successor and prove the preservation obligation fails, so a mutant cannot pass by vacuity.
- [x] Run all foundation tests and build; commit.

Expected safety theorem: initialization and step preservation imply `∀ s, Reachable system s → invariant s`.

## Task 3 Forward refinement

- [x] Test state correspondence and observation mapping for one concrete step and concatenated execution; observe RED.
- [x] Define one-step forward simulation preserving mapped observations.
- [x] Prove execution lifting and abstract invariant transfer.
- [x] Demonstrate a concrete state carrying an extra field and an abstract counter; wrong observation mappings cannot meet the simulation obligation.
- [x] Run all tests and build; commit.

## Task 4 Verification and delivery

- [x] Add an axiom audit over all new named public theorems and examples; prove its failure detection covers sorryAx and a synthetic protocol axiom.
- [x] Add Linux CI using the pinned toolchain and dedicated build/test/audit commands.
- [x] Update README and architecture status without claiming FLP/CAP/quorum, distributed recovery or compiler correctness.
- [x] Run physical Mac build, tests and axiom audit; run CI commands locally; hosted Linux CI awaits coordinator execution.
- [x] Produce `docs/verification/2026-10-04-foundations-stage-one.md` with RED/GREEN evidence, final commands, assumptions, API tour and deferred scopes.
- [x] Deliver a clean committed feature branch for coordinator independent review and managed integration; no external review, push or merge in this invocation.

## Acceptance and next stage

All new theorem proofs must be kernel checked. No state machine test alone substitutes for a proof. CI, source imports and audit must show the new Core has no Kadmos/Veil/solver dependencies. The next stage is minimal distributed semantics; do not start it in this delivery.

## T-391 physical preflight (2026-10-04)

Execution is authorized inline, within this invocation's native worktree. The
coordinator performs independent review and integration: replace the old Grok
review step with delivery for coordinator review. No push means hosted CI cannot
be triggered here; commit the workflow and run its three commands locally.

Exact interfaces (namespace `Harmonia.Foundation`, universe-polymorphic types):
```lean
structure TransitionSystem (S : Type u) (A : Type v) (O : Type w) where
  init : S → Prop
  step : S → A → O → S → Prop
-- Execution T s labels t : Prop; labels : List (A × O).
-- nil : Execution T s [] s
-- cons : T.step s a o m → Execution T m labels t →
--        Execution T s ((a,o)::labels) t
-- Reachable T s : Prop; constructors init and step.
-- observations labels := labels.map Prod.snd
-- Execution.append : Execution T s xs m → Execution T m ys t →
--                    Execution T s (xs ++ ys) t
-- Execution.split : Execution T s (xs ++ ys) t →
--                   ∃ m, Execution T s xs m ∧ Execution T m ys t
-- reachable_iff_execution : Reachable T t ↔
--                   ∃ s labels, T.init s ∧ Execution T s labels t
-- Initially T I := ∀ s, T.init s → I s
-- Preserved T I := ∀ s a o t, I s → T.step s a o t → I t
-- invariant : Initially T I → Preserved T I → ∀ s, Reachable T s → I s
-- ForwardSimulation C B R obsMap : Prop has initial and matchStep fields:
-- initial : ∀ c, C.init c → ∃ b, B.init b ∧ R c b
-- matchStep : ∀ c a o c' b, R c b → C.step c a o c' →
--             ∃ ba b', B.step b ba (obsMap o) b' ∧ R c' b'
-- lift : simulation → R c b → Execution C c labels c' →
--        ∃ b' bs, Execution B b bs b' ∧ R c' b' ∧
--                  observations bs = (observations labels).map obsMap
-- reachable and invariant transfer derived from initial and lift.
```

Dependency preflight: Task 1 produces Execution/Reachable used by Tasks 2/3;
Task 2 produces invariant used by Task 3; Task 4 audits every theorem from Tasks
1–3 and regression modules. Signatures above settle all consumer names.
Use proof-indexed label lists (no executable interpreter promised), separate
initial-state evidence, and exact one-step matching; no silent-step erasure.

Actual task probes are committed in `HarmoniaTests/Foundations.lean`,
`InvariantProbes.lean` and `RefinementProbes.lean`. Each is run before its
production module exists, then unchanged on GREEN. Zero-step endpoints,
append observation order, prefix splitting, reachability correspondence,
unsafe preservation failure, missing initial states, nondeterministic choices,
wrong action/observation, and mapped execution lifting are explicit propositions.
Audit acceptance uses an automatic environment theorem enumeration and an exact
standard axiom whitelist, plus isolated detection tests for a synthetic axiom
and `sorryAx` (neither admitted to the certified foundation).

- [x] Task 1: run `lake env lean HarmoniaTests/Foundations.lean` RED; implement;
  `lake build Harmonia && lake env lean HarmoniaTests/Foundations.lean` GREEN; commit.
- [x] Task 2: run `lake env lean HarmoniaTests/InvariantProbes.lean` RED; implement;
  build and both probes GREEN; commit.
- [x] Task 3: run `lake env lean HarmoniaTests/RefinementProbes.lean` RED; implement;
  build and all probes GREEN; commit.
- [x] Task 4: run audit policy detection tests RED/GREEN; expose
  `lake build foundationsTest` and `lake build foundationsAudit`; add pinned CI;
  document evidence and boundaries; run `lake build`, both targets, diff checks;
  commit delivery for coordinator review.
