# T-393 design-only baseline receipt

Date: 2026-10-05. Owner: actual physical Codex. Independent reviewer: actual Grok,
dispatched by parent; first and R2 package preflights returned REVISE. No revised acceptance is claimed.
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

The original planning invocation ran no hosted Linux CI or independent Grok review.
Parent subsequently supplied first preflight REVISE; accepted revised preflight still
precedes implementation. Original spec/plan were under200/under300 lines; coordinator
permits modest plan growth for concrete revision pins. Current counts follow below.

[Spec](../superpowers/specs/2026-10-05-kadmos-world-ir-design.md) ·
[Plan](../superpowers/plans/2026-10-05-kadmos-world-ir.md).

## Original document self-review and scope check

Observed CLI exit0: spec165 lines and plan288 lines, below the requested limits;
balanced Markdown fences; no unresolved placeholders or trailing whitespace in all three documents.
All requested semantics map to the four task cycles. Self-review sharpened the target-
phase invariant probe, repeated-assignment probe, non-null directive acceptance and
certified Lake-root contamination policy. Public signatures and fixture constructors
agree across spec/plan; no product implementation is represented as already proved.
`git diff --exit-code` against baseline for Harmonia, HarmoniaTests, scripts, CI,
lakefile, lean-toolchain, Main and root Harmonia exited0 with no diff. Git status
showed exactly the three requested new document paths and no unrelated work.

## Coordinator-reviewed preflight rulings (document correction only)

Resume HEAD: `442241ff1d27b908075797d25117878a90a8711a`; same native03e7 worktree,
thread and branch; clean at entry. Read `/private/tmp/harmonia-t393-preflight-verdict.md`
completely. Actual Grok returned REVISE, package-only with no tests; coordinator reports
physical reviewer process exit0/374.6s. That timing/exit is supplied evidence, not a
review process run by this executor. Receiving-code-review and writing-plans applied;
managed authority covers these document corrections. No routine approval requested.
Rulings are ledgered here; coordinator retains the internal registry, which is untouched.

1. **Accept late-bounds gap; decline wrong reversal arithmetic.** Add start100/bounds0..S,
   subtract150 then add150 => accepted100, including safe private -50; subtract150 alone
   => rejected(bounds0)/original100. Both reversed constant writes also end100:
   (100+150)-150=100, not -50. Order-sensitive evidence remains x=x+1;y=x versus reversal.
   Keep final40 with invariant min50 as a separate invariant-only rejection.
2. **Clarify audit ambiguity, preserve policy.** The original phrase “three certified
   audit targets” meant foundationsAudit/distributedAudit/kadmosWorldAudit, not the
   Kadmos rejection target. The claimed Critical contradiction was an ambiguous reading,
   not a policy contradiction. Six certified test/audit target closures must be trap-free.
   Isolated rejection targets may import their own traps and shared AuditPolicy or
   Foundation definitions. Isolation is directional: no certified-to-trap import edge;
   banning rejection-to-shared-tooling edges would make the harness impossible. New
   synthetic tests separately reject certified-root contamination and accept correctly
   isolated rejection roots; no original distributed/root rule is weakened.
3. **Accept exact stage pins.** UnknownAction beats phase; wrongPhase beats directive;
   SEND mismatch rejects unauthorizedDirective/none; matching SEND accepts SEND and
   none/none accepts none. Invalid raw type/range precedes false guard in this reference
   contract. Second-write overflow is effectError overflow with whole original State.
   Eager and/or/implies/not overflow pins are explicit; implies computes !left||right
   after evaluating both operands. These are planned probes, not observed new results.
4. **Accept malformedSpec and invariant-error pins.** Interpretation wraps duplicate
   initials, invalid bounds, empty/duplicate action IDs, terminal-source and overflowing
   initial-invariant errors, preserving caller State/none. Missing default0 is legal at
   min0. World0000 initialization returns initialCount; State0 is uninhabited so no
   fake interpretation caller is specified. False and evaluation-error post-invariants
   both report invariant(index); overflowing initial invariant reports initialInvariant.
5. **Accept whole-Result generic balance signatures and witnesses.** debit_accept and
   debit_insufficient retain arbitrary Int amounts with explicit hypotheses and full
   verdict/directive equality; n=b>0 accepts0, debit1 from0 rejects bounds0. Include
   Reachable balance100 and the interpreted 30/20/130 execution ending50.
6. **Accept target-phase proof limitation.** Successful numeric-only effects cannot
   distinguish phase behaviorally; bool stateIs RHS fails at either phase. Actual
   interpret must use runTransitionEffects; prove its runEffects transition.target
   equation by unfolding that used helper. Keep candidate phase1/balance70 invariant
   success versus phase0 failure. No unsupported conditional syntax is introduced.
7. **Accept boundary pins and scoped counts.** Add literal/context S+1 overflow,
   field1 decoder errors, unused required fields, Fin0 decode and a valid World1000
   with unknown-action result. Preserve Foundation52 and Distributed336/594 in separate
   certified environments. Existing selectors may legitimately see imported Foundation
   and probe declarations in a combined application environment; report selector and
   import scope rather than imposing the standalone counts there.

Fin references remain typed; expression sorts remain dynamic, not a static GADT.
Existing WorldSpec/types and runtime semantics remain the alignment baseline. The
Lean input contract and safe-intermediate arithmetic remain narrower, with no parsing,
YAML-schema compatibility or equivalence theorem claimed. Four tasks and the original
bounded slice are retained. No product/test/tool code, dependency or toolchain changed;
no subagents, Kadmos/internal edits, push or merge. Implementation and new policy/probe
execution remain stopped pending accepted revised preflight.

## Revision verification (actual CLI; one Lake process at a time)

| Command/check | Exit | Observed result |
| --- | --- | --- |
| `lake build` | 0 | Build completed successfully |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | original targets passed; separate Foundation52 summary |
| `lake build distributedTest distributedAudit distributedAuditRejection` | 0 | original targets passed; separate Distributed336/594 summary |
| `python3 scripts/check_distributed_audit.py --self-test` | 0 | unchanged 16 policy tests, OK |
| `python3 scripts/check_distributed_audit.py` | 0 | certified_modules12, distributed_closure16, foundation_closure10 |
| `lake env lean HarmoniaTests/AxiomAudit.lean` | 0 | fresh 52 theorems; observed [propext, Quot.sound] |
| `lake env lean HarmoniaTests/DistributedAxiomAudit.lean` | 0 | fresh 336 theorems/594 declarations; observed [propext, Quot.sound, Classical.choice] |
| `git diff --exit-code 442241f -- Harmonia HarmoniaTests scripts .github lakefile.lean lean-toolchain Main.lean Harmonia.lean` | 0 | protected/product/test/tooling trees unchanged |
| `git diff --check` | 0 | no whitespace errors |

New application targets are still absent; the revised probes and policy tests above
are execution obligations. Build summaries can replay artifacts; the two audit commands
freshly elaborated their separate certified roots and confirm the counts independently.
Logs stay in /private/tmp and are unstaged. No combined-environment count is asserted.
Spec180/plan352 lines retain four tasks; the plan grew64 lines for concrete requested
pins under the coordinator's explicit modest-growth allowance. Original line counts in
this receipt describe the first delivery, not the revised package. Final document
self-review, staged three-path scope and correction commit are supplied in handoff.
Revised actual Grok preflight acceptance remains outstanding; stop after docs commit.

Final revision self-review passed after a literal placeholder scan initially flagged a
historical sentence saying placeholders were absent (exit1). Rewording that historical
sentence and rerunning returned exit0 for all documents; no unresolved placeholder was
present. Fence/whitespace checks, four-task count and explicit six-target coverage all
passed; spec remains180 lines and plan352. Final staged/commit scope is documents only.

## R2 sole-blocker proof-method correction

Resume HEAD: `663f4bc437f5d2c411cac6c75610e104d3e9de02`; same native03e7 branch,
clean at entry. Read `/private/tmp/harmonia-t393-preflight-r2-verdict.md` and the
coordinator-checked `/private/tmp/harmonia-t393-fin-context-probe.lean`. R2 returned
REVISE solely because singleton Fin-context updates are propositionally, not
definitionally, equal to constant lambdas. Coordinator's probe exit0 confirmed this;
executor rerun `lake env lean /private/tmp/harmonia-t393-fin-context-probe.lean`
also exited0. Both updated and round-trip contexts use `fail_if_success rfl`, then
funext and Fin.ext with Nat.eq_zero_of_le_zero/Nat.le_of_lt_succ to prove equality.
The outside-product probe checks the proof method, not an implemented interpreter.

Replaced debit30's successful whole-Result rfl with debit_accept at100/30, retaining
balanceState(100-30) and accepted/none. General debit_accept/debit_insufficient still
state whole-Result equalities and use context extensionality. Checked every planned
successful identity: both bounds round trips, n=b, accepted trace steps, phase1/balance70,
and zero-effect/directive-only successes. Reduce round-trip verdict, directive and
context0 first; prove whole State extensionally. Literal context reuse, direct default
initialization, unchanged-state rejection, runEffects projections and helper unfolding
retain rfl only when definitionally true. No numeric projection replaces a whole Result.
Spec and plan pin this method; semantics, four tasks and interpreter-derived Step are
unchanged. No second balance relation, product/test/tool edit or new feature.

Per coordinator instruction, unchanged product suites were not repeated: two serial
baseline rounds already passed. This correction runs only the tiny typed probe and
Git/document checks. Probe file stays outside product and unstaged. R3 acceptance is
pending; stop immediately after committing these three documents. No subagents,
Kadmos/internal edits, push or merge. Managed authorization remains in effect.
Git protected-tree diff and whitespace checks exited0. Document checks passed:
spec184/plan375 lines, balanced fences, four tasks, no successful whole-Result rfl pin.
