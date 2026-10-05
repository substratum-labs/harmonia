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

- [ ] Write theorem probes before production definitions; run them and record the expected missing-foundation failure.
- [ ] Implement the generic relational system, zero-step execution, labeled step extension and concatenation.
- [ ] Prove endpoint/observation behavior, valid prefixes and execution/reachability correspondence.
- [ ] Demonstrate one initial state, a disabled action, two legal successors, and impossible wrong-label traces.
- [ ] Run the test target and `lake build`; commit the independently usable deliverable.

Suggested contract shape:

```lean
structure TransitionSystem (S A O : Type) where
  init : S → Prop
  step : S → A → O → S → Prop
```

Trace test: initial 0 has actions inc and fork; inc emits 1 and reaches 1; fork permits 1 or 2 with explicit observations. A label not in the relation must not form a valid trace. Concatenation of 0→1 and 1→2 must emit the two observations in order.

## Task 2 Invariant principles

- [ ] State initialization and all-successor preservation obligations in tests; observe RED before adding the theorem.
- [ ] Prove reachable-state invariant preservation by induction.
- [ ] Prove the bounded-counter instance with explicit initial witness.
- [ ] Include an unsafe successor and prove the preservation obligation fails, so a mutant cannot pass by vacuity.
- [ ] Run all foundation tests and build; commit.

Expected safety theorem: initialization and step preservation imply `∀ s, Reachable system s → invariant s`.

## Task 3 Forward refinement

- [ ] Test state correspondence and observation mapping for one concrete step and concatenated execution; observe RED.
- [ ] Define one-step forward simulation preserving mapped observations.
- [ ] Prove execution lifting and abstract invariant transfer.
- [ ] Demonstrate a concrete state carrying an extra field and an abstract counter; wrong observation mappings cannot meet the simulation obligation.
- [ ] Run all tests and build; commit.

## Task 4 Verification and delivery

- [ ] Add an axiom audit over all new named public theorems and examples; prove its failure detection covers sorryAx and a synthetic protocol axiom.
- [ ] Add Linux CI using the pinned toolchain and dedicated build/test/audit commands.
- [ ] Update README and architecture status without claiming FLP/CAP/quorum, distributed recovery or compiler correctness.
- [ ] Run physical Mac build, tests and axiom audit; run CI on the exact candidate commit.
- [ ] Produce `docs/verification/2026-10-04-foundations-stage-one.md` with RED/GREEN evidence, final commands, assumptions, API tour and deferred scopes.
- [ ] Obtain independent physical Grok review; fix supported important findings within scope, rerun verification, then deliver a clean feature branch for managed integration.

## Acceptance and next stage

All new theorem proofs must be kernel checked. No state machine test alone substitutes for a proof. CI, source imports and audit must show the new Core has no Kadmos/Veil/solver dependencies. The next stage is minimal distributed semantics; do not start it in this delivery.
