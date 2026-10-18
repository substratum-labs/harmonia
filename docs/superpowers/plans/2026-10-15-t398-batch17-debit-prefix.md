# T-398 Batch 17 — canonical DEBIT prefix and guard rejection

Base: `6304ef3803f2bbe435941c7b4c3911c53e91aeb4`; branch
`feat/t396-generated-correspondence`; isolated worktree `5b89`.

This executes the user's Batch 17 mission and Task 3 of the accepted
2026-10-11 generated-correspondence plan. The foundation-first design remains
`docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md`.

## Constraints

Prove actual stored-source execution from `balanceCanonicalConstructed lang b`
for `0 ≤ b ≤ S`, `-S ≤ n ≤ S`, `S = 9007199254740991`. Keep the executor,
source fixture bytes, Core/Distributed/legacy layers, Lean 4.16.0 pin and strict
`[propext, Quot.sound]` whitelist unchanged. Product modules import only Init
and the existing project closure; no Lean.Meta, sorry, admit, native decision
oracle, assumed helper success, or new protocol axiom. Native diagnostics only
propose literal models. Kernel checking supplies the proof.

Use actual CLI processes for delegated scratch proof work. The owner alone
integrates product files and commits. Workers own separate scratch files and
never edit product, ledger, branch, index, fixtures or toolchain. All heavy
Lean commands share `/tmp/t398-b17/compiler.lock`; all Lake builds are owner-run,
serial and have at most one explicit target. No push or PR #5 merge.

## Tasks

1. **Owner: shared entry and prefix.** Prove method/closure provenance, actual
   call opening, busy acquisition, snapshots/rollback, admission, actual one-key
   sanitization (TS jsNumber; Python pyInt to exact pyFloat), record/reject,
   transition selection, directive check, environment installation and actual
   source continuation. Retain all allocations and exact frames. Gate: direct
   kernel checking and strict axiom reports for the universal contracts.
2. **TS scratch worker: guard and rejection.** Prove actual guard value for
   every safe signed n and complete n≤0 actual call/rejection. Use constructive
   zero/negative Int cases if useful; never evaluate b−n on the rejected path.
   Gate: exact interpreter equality and physical frame/projection evidence,
   Init-only replay, no assumed successful call. Owner integration required.
3. **Python scratch worker: guard and rejection.** Same as TS, with exact
   float conversion for n.natAbs≤S, fixed tokenizer/Pratt execution and source
   rollback/finally. Gate: kernel-checked Init-only proof; scratch Meta search
   alone is not acceptable. Owner integration required.
4. **Owner: contracts, verification and commit.** Mirror every new public
   theorem/contract as direct examples in both requested regression roots.
   Register exact new modules without weakening inventory/audit. Run the full
   serial single-target suite plus new module targets, normalize and validate
   any syntax certificates, regenerate the exact portable axiom listing,
   update verification scope/evidence, obtain fresh-context read-only actual
   codex exec review of the exact diff and artifacts until zero Critical and
   Important findings, then make a clean local commit. Preserve the worktree
   and branch; do not push or merge.

## Interface preflight

| Producer / consumer | Interface | Finding |
|---|---|---|
| Shared prefix / TS | `StepModels.olean`, `GuardBase.olean`, actual source selectors and canonical b/n models | TS may prove its guard/rejection independently of Python replay packaging. |
| Shared prefix / Python | Same models, `host_float_exact_tag`, exact source body and safe amount bound | The numeric fact must be proved, not assumed as helper success; scratch replay tooling is owner-owned. |
| Language workers / owner | Scratch-only Lean source, exact checked commands/logs, theorem types and axiom sets | Source integration and every Lake build remain single-owner. |
| Runtime proofs / regressions | Every new public declaration, both roots | A theorem checked in only one root is incomplete coverage. |
| Integration / acceptance | Frozen file hashes, serial command intervals, exact sorted axiom pairs, independent review | Failed/interrupted/prototype checks are excluded. |

Ruling: split the independent language proof research into fresh physical CLI
contexts while the owner retains shared replay/integration. This changes the
execution workflow, not the requested theorem scope. If a proposed worker
proof cannot be replayed under Init and the strict whitelist, it is excluded.

## Physical integration ownership transfer

At 17:15 UTC the coordinating parent transferred exclusive product-edit and
Lake-build ownership to the fresh-context integration owner. Scratch workers
retain their separate proof directories and never edit product. The parent
coordinates proof research and owns final independent read-only review and
local commit; the integration owner completes source, examples, serial suite,
listing and verification documentation, then freezes the reviewable result.
This changes execution ownership, not the required proof or acceptance gates.

At 19:10 UTC the coordinating owner resumed exclusive product-edit and
Lake-build ownership. The integration handoff and accepted intermediate
build evidence remain in `/tmp/t398-b17/worker-integration/next-steps.md`.
The remaining Python proof packaging is scratch-only. Bounded independent
scratch replays may overlap under an owner-monitored combined 8 GiB RSS
limit; each replay has a 4 GiB heap cap. Lake builds remain strictly serial,
one target per command. This replaces the earlier scratch resource precaution
without changing kernel trust, theorem scope, or the final verification gates.

At 20:19 UTC the coordinator transferred exclusive product editing to the
fresh integration implementer. Build ownership was enabled at 20:20 UTC,
after the bounded full Python prefix replay exited 0 with exactly
`[propext, Quot.sound]`. Product builds and the final suite use the shared
serial compiler lease, with at most one explicit Lake target per command.
The coordinator retains proof-worker coordination, final independent review
and local commit; the integration implementer does not stage or commit.
Packaging changes require exact syntax round-trip checks and ordinary kernel
acceptance; a compressed equivalent may obtain that acceptance through its
product build. No unaccepted proof or error-recovery artifact enters the
certified claims.
