# Harmonia Contributor Instructions

## Purpose and authority

Harmonia independently develops formal foundations for distributed algorithms. Kadmos is an application. The accepted foundation-first design is `docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md`.

Keep generic Core free of checker verdicts, savepoints, Kadmos fields, Veil dependencies and solver IO. State, action and observation are parameters; transitions may be nondeterministic. Distributed and executable application semantics are separate layers.

## Verification

- Keep `lean-toolchain` pinned to `leanprover/lean4:v4.16.0` unless an explicitly approved change upgrades it.
- Run `lake build` and the dedicated formal-foundation test and axiom-audit targets before reporting completion.
- No `sorry`, `admit`, `sorryAx` or unreported protocol axioms in certified foundation proofs.
- Record models, assumptions and observed verification results. Solver UNSAT and finite exploration are not kernel proofs.
- Preserve legacy 2PC/SMT/C experiments; do not claim them behaviorally connected without a correspondence theorem.
- Do not stage `.lake/`, generated binaries, caches, credentials or machine-specific logs.

## Coordination and workspaces

Use a dedicated branch and isolated worktree for implementation. Register task ownership and evidence in `substratum-internal/ledger/projects/harmonia.md` when working in the Substratum workspace. Avoid editing another agent's task or existing uncommitted work.

When the user explicitly authorizes physical managed execution, use actual CLI processes, durable task evidence and an independent reviewer. That authorization covers normal plan execution and reviewed integration; ask only for genuinely missing authority or a blocking decision.
