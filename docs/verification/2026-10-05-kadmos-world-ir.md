# T-393 design-only baseline receipt

Date: 2026-10-05. Owner: actual physical Codex. Independent reviewer: actual Grok,
dispatched by parent; no reviewer result is claimed in this invocation.
Baseline HEAD: `5daf0208c07eafba0540f054291bfeb3d238fcf9` (integrated T-392).
Toolchain: `leanprover/lean4:v4.16.0`.

## Authority and scope

User explicitly authorized native managed design/plan execution, prescribed this slice,
and required a document-only stop for parent preflight. Brainstorming classified this
as architectural; writing-plans produced the requested plan under that authorization.
No routine stage approval was requested. Using-git-worktrees confirmed supplied native
isolation; verification-before-completion checked actual evidence before handoff.
No subagents, product/test/tooling edits, Kadmos/internal edits, push or merge.
Coordinator owns task registry, physical Grok review and eventual integration.

Workspace: `/Users/yong/.codex/worktrees/03e7/harmonia`.
Native thread: `01a10f01-664f-7621-a050-0d3bafda9cbd` (CODEX_THREAD_ID); agent `/root`.
Entry status was clean and HEAD detached. `git rev-parse --git-dir --git-common-dir`
returned distinct worktree/common metadata directories; superproject query was empty.
No nested worktree was created. Branch: `feat/t393-kadmos-world-ir`.
Initial branch creation exited128: shared Git ref lock write was denied by sandbox.
The same authorized command with metadata escalation exited0 and created the branch.
This was a filesystem sandbox denial, not an automatic approval-review rejection.
Delivery HEAD is reported in final handoff, avoiding a self-referential receipt hash.

## Read evidence and semantic decisions

Read Harmonia AGENTS.md; accepted 2026-10-04 minimal-formal-core-design; current
TransitionSystem/Execution/Invariant/Refinement-facing examples and audit APIs;
Distributed Protocol/Semantics/Properties; lakefile, toolchain, inventory checker/tests,
Linux workflow and prior Foundation/Distributed verification receipts.

Read only in Kadmos: src/types/world.ts, src/world_checker.ts,
src/world_expression.ts, src/world_compiler.ts; order_settlement.world.yaml fixture;
relevant compiler-test assertions and generated-checker tests in
tests/test_harness_world_compiler.test.ts. Existing WorldSpec, runtime property
checking and generated checker were confirmed, not treated as missing capabilities.
No Kadmos execution or correspondence verification was performed.

Chosen finite indexed World declarations; expression AST is an explicit supported
subset, not a second domain language. Input fields form a uniform required-safe-int
Lean contract, not a new existing YAML schema. Runtime typing is strict; no Bool/string
coercion. Initial defaults and bounds are checked; successful initialization witness
is required in the public reachable-safety interface. Rejection protects phase+context.
Directive token/proposal matching is included; no directive IO or rejected authorization.
Guard uses pre-state; candidate effects run sequentially at target phase. Invariants
are state-only. Every numeric intermediate is checked, strengthening current JS rules;
future correspondence must establish equivalence only inside that safe subset.

Four independently testable tasks cover IR/evaluation/init, interpreter/property proofs,
Foundation/nonvacuous balance fixtures, and application audit/inventory/CI. General
amount theorems and actual interpret equality underpin the balance examples. Unsafe
effects reject at postchecks; no unconditional action-invariant preservation is claimed.

## Physical serial command results

Commands used actual CLI processes on this Mac. Every Lake process completed before
starting another Lake process, including fresh audits and scratch elaboration. Python
inventory runs did not modify Lean source or overlap another Lake build invocation.
No baseline failure was suppressed and no product source changed to obtain these results.

| Command | Exit | Observed result |
| --- | --- | --- |
| `lake env lean --version` | 0 | Lean4.16.0, arm64-apple-darwin23.6.0, commit128a1e6b0a82, Release |
| `lake build` | 0 | `[36/36] Built harmonia`; Build completed successfully |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | all original targets passed; 52-theorem audit |
| `lake build distributedTest distributedAudit distributedAuditRejection` | 0 | all original targets passed; 336-theorem/594-declaration audit |
| `python3 scripts/check_distributed_audit.py --self-test` | 0 | 16 tests, OK |
| `python3 scripts/check_distributed_audit.py` | 0 | inventory PASS: certified_modules12, distributed_closure16, foundation_closure10 |
| `lake env lean /private/tmp/t393-api-probe.lean` | 0 | checked List.ofFn, Fin.elim0, Except.bind, List.all, Int.add_le_add signatures |
| `lake env lean HarmoniaTests/AxiomAudit.lean` | 0 | fresh AUDIT PASS: 52 theorems; observed [propext, Quot.sound] |
| `lake env lean HarmoniaTests/DistributedAxiomAudit.lean` | 0 | fresh DISTRIBUTED AUDIT PASS: 336 theorems; 594 declarations; observed [propext, Quot.sound, Classical.choice] |
| `lake env lean HarmoniaTests/AuditRejection.lean` | 0 | expected rejection diagnostics matched |
| `lake env lean HarmoniaTests/DistributedAuditRejection.lean` | 0 | expected rejection diagnostics matched |

Foundation observed standard axiom union/count: `[propext, Quot.sound]`, 2.
Distributed observed standard axiom union/count: `[propext, Quot.sound, Classical.choice]`, 3.
Both retain the existing whitelist of those three standard axioms. No certified
sorryAx/custom protocol axiom was reported. Adversarial targets deliberately contain
contaminated declarations and are not certified roots. Fresh audits confirm build
summaries independently of artifact replay. The new Kadmos targets do not exist yet;
there is no application theorem count, observed union or runtime certification result.

Scratch file and command logs are outside the repository and unstaged. The scratch
probe only imported Init, checked installed signatures and elaborated a trivial excluded-
middle range proposition; it is feasibility evidence, not implementation or a certified
application proof. No product scaffolding or prototype was written.

## Trust boundary and preflight risks

1. Fin-indexed tables simplify reference validity but require finite function update/
   decoder lemmas and context extensionality. Full planned signatures/proofs have not
   yet been elaborated together; installed API checks are narrower feasibility evidence.
2. Uniform required integer fields, mandatory nonnegative bounds and state-only
   invariants intentionally restrict existing WorldSpec behavior. Parsing, imported
   World compatibility and host payload/object semantics remain outside certification.
3. Reference interpreter revalidates static initialization each call. This favors proof
   clarity and explicit malformed-spec errors; no runtime performance claim is made.
4. Source-module audit coverage must include escaped namespaces and unused axioms,
   while new traps stay out of every certified import closure. Existing distributed
   inventory/policy must retain their checks unchanged. New policy RED is planned,
   not executed in this document-only call.
5. Kernel safety will depend on actual interpreter branches and runtime postchecks,
   with a nonvacuous initial balance witness. Solver UNSAT/finite exploration are not
   kernel proofs. No solver, physical IO, distributed composition, codegen or target
   correspondence result is claimed; legacy experiments remain unconnected.

No hosted Linux CI or independent Grok preflight/review was run here. Parent dispatches
preflight before any implementation. The bounded planning deliverables are the spec
(under200 lines), plan (under300 lines) and this receipt; line/scope/whitespace checks
and document-only commit identity are reported in the final handoff.

[Spec](../superpowers/specs/2026-10-05-kadmos-world-ir-design.md) ·
[Plan](../superpowers/plans/2026-10-05-kadmos-world-ir.md).

## Document self-review and scope check

Observed CLI exit0: spec165 lines and plan288 lines, below the requested limits;
balanced Markdown fences; no TODO/TBD or trailing whitespace in all three documents.
All requested semantics map to the four task cycles. Self-review sharpened the target-
phase invariant probe, repeated-assignment probe, non-null directive acceptance and
certified Lake-root contamination policy. Public signatures and fixture constructors
agree across spec/plan; no product implementation is represented as already proved.
`git diff --exit-code` against baseline for Harmonia, HarmoniaTests, scripts, CI,
lakefile, lean-toolchain, Main and root Harmonia exited0 with no diff. Git status
showed exactly the three requested new document paths and no unrelated work.
