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
