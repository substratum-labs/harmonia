# T-392 design/plan and physical baseline receipt

Date: 2026-10-04. Owner: physical Codex. Independent reviewer: physical Grok,
next through parent coordinator; preflight ACCEPT read on implementation resume; final review pending.
Worktree: `/Users/yong/.codex/worktrees/991b/harmonia`.
Branch: `feat/t392-minimal-distributed-semantics`.
Baseline source: `d0b2fa497f69eb702733d3ef87c989c7e31e40db`.
Toolchain pin: `leanprover/lean4:v4.16.0`.

## Authority and boundary

Coordinator scoped the first invocation to design/plan only; the user requested
the full next stage, with managed authorization covering implementation and review. Brainstorming architectural path and writing-plans
used; repeated human approval replaced by the supplied authorization. Native
linked worktree reused according to using-git-worktrees. No subagents, internal
ledger/Kadmos edits, product/test edits, push, PR or merge. Parent coordinator
owns physical Grok preflight, ledger and eventual integration. Only the new
spec, implementation plan and this receipt are committed here.

Read AGENTS.md, approved minimal-formal-core-design, ARCHITECTURE, all four new
Foundation interfaces, Foundation example, Foundations/InvariantProbes/
RefinementProbes, AuditPolicy/AxiomAudit/AuditRejection, Lake targets, toolchain
and existing Linux workflow. Stage-one contracts remain unchanged.

## Workspace and actual command evidence

`git status --short`: empty at entry. Branch initially detached.
`git rev-parse --git-dir --git-common-dir --show-superproject-working-tree`
confirmed different worktree/common Git directories and no superproject, so
this is a supplied linked worktree, not a submodule. No second worktree created.
Initial branch creation exit 128: `Operation not permitted` writing shared Git
ref metadata. Authorized metadata escalation ran the same command, exit 0:
`Switched to a new branch 'feat/t392-minimal-distributed-semantics'`.
This was a filesystem sandbox denial, not an automatic approval rejection.

Physical commands ran through CLI on the Mac, not simulated execution:

| Command | Exit | Observed output |
| --- | --- | --- |
| `lake env lean --version` | 0 | `Lean (version 4.16.0, arm64-apple-darwin23.6.0, commit 128a1e6b0a82, Release)` |
| initial `lake build` | 1 | `failed to write ... Harmonia/Core/TransitionSystem.olean: 2 No such file or directory`; `error: build failed` |
| initial `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | built formal modules and both audit roots; `Build completed successfully.` |
| serial rerun `lake build` | 0 | built remaining objects and executable, `[36/36] Built harmonia`; `Build completed successfully.` |
| serial rerun `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | `AUDIT PASS: 52 theorems; observed axioms [propext, Quot.sound]; whitelist [propext, Quot.sound, Classical.choice]`; `Build completed successfully.` |
| `lake env lean /private/tmp/t392-core-probe.lean` | 0 | checked dependent Nodup constructor, member subtype equality and core permutation signatures; no errors |

The initial two Lake processes accidentally overlapped artifact creation.
The first build failed during an artifact write; no semantic source changed.
Both processes completed before serial reruns. Overlap is a plausible cause,
not a proved diagnosis; final acceptance uses the individually observed serial
exit-zero results. Future executor must run one Lake build process at a time.
The second audit output was replayed by Lake from built artifacts; the initial
audit was newly elaborated and reported the same 52 dependency sets.

Certified stage-one observed axiom union: `[propext, Quot.sound]`.
Classical.choice is whitelisted but unobserved. No custom protocol axiom or
sorryAx in certified theorem dependencies. The isolated adversarial audit target
passed its expected-diagnostic probes; it is not a certified proof root.
No new distributed theorem count exists yet, since no code was implemented.
No hosted Linux run or independent physical Grok result is claimed.

## Core API feasibility probe

Throwaway probe lived outside the repository at `/private/tmp/t392-core-probe.lean`.
It imported `Init.Data.List.Perm`, defined a Config with members.Nodup, checked
`if h : xs.Nodup then some ⟨xs,h⟩ else none`, and inferred DecidableEq for a
membership subtype from DecidableEq on external nodes. It proved permutation
transport of `∃ rest, List.Perm pool (e :: rest)` using symm/trans.
This is feasibility evidence, not product implementation or a distributed proof.

Installed Lean 4.16 sources inspected: Init/Data/List/Basic.lean defines Nodup
and Perm; Init/Data/List/Perm.lean supplies the following actually checked APIs:

- `List.Perm.map f p`: mapped-list permutation.
- `List.Perm.length_eq p`: equal list lengths.
- `List.Perm.nodup_iff`: permutation preserves Nodup.
- `List.nodup_cons`: nodup cons iff head absent and tail nodup.
- `List.Perm.cons_inv`: cancel same head on permuted cons lists.
- `List.Perm.append p₁ p₂`: append congruence.
- `List.mem_map`: membership with source witness.
- Source-read `List.perm_middle`: arbitrary-prefix occurrence moves to head.

No web lookup or new dependency needed for these local toolchain APIs. An expanded scratch probe initially failed (exit 1) for
`checked [0,0] = none := by decide` with `failed to synthesize Decidable`.
The same closed proposition proved by `rfl`, and success/empty `.isSome` probes
plus the swap direction passed together on rerun (exit 0). The plan uses the
checked reduction proof and needs no DecidableEq Config instance. Full
Step, invariant, provenance and fixture proof signatures still require actual
elaboration in implementation; the probe does not certify them.

## Design decisions and assumptions

1. Checked explicit member list plus member subtype; reject duplicates, retain
   list exactly, allow empty configuration with no fabricated actor. Two-node
   initial witness is separate acceptance evidence, not vacuous empty-model safety.
2. Protocol relation takes only actor, own D/V and explicit input. Transport
   stamps sender; logical identity and unique occurrence identity are separate.
   Static configuration knowledge allowed; arbitrary externally captured oracles
   are outside the fixed-protocol modeling discipline.
3. List occurrences use permutation-based Take and Publish, exact-one receive/
   drop, monotone unbounded Nat supply, finite output list without a size cap.
   Local processing and publication are one abstract atomic step, with no
   physical storage/network IO guarantee.
4. Crash/recover keep exact pending representation. Self-review caught that
   this makes an iff under independent pre/post permutations too strong.
   Both documents now require symmetric step lifting modulo PoolEq and its
   finite execution lifting; crash/recover choose the reordered input pool as
   their successor. This proves unordered behavior without changing the rules.
5. Fixed profile independently gates drop, duplicate, crash and recover.
   Fault-free reliable profile prohibits loss/duplication and promises no
   eventual delivery. Crash preserves D and resets V; recovery uses D only.
6. WF (unique pending tids, all below next) is proved via Foundation.invariant.
   Separate pending-origin/history theorem excludes transport provenance forging
   from initialized histories. Neither claim establishes protocol safety.
7. Extend shared audit with source-origin selection, unused source axiom checks,
   import inventory, explicit rejection separation and tests of new policy.
   Keep stage-one targets and adversarial probes intact. CI adds distributed
   targets and running-version check; coordinator observes remote Linux results.

Alternatives and exact boundaries are in the spec; file responsibilities,
signatures, test cycles and final command matrix are in the plan. No mathlib,
Veil, Kadmos, SMT, consensus, crypto, infinite execution, fairness/liveness,
extraction or codegen. Legacy experiments remain unmodified and unconnected.

## Review handoff and risks

Physical Grok should review subtype ergonomics, allocation/disjointness proof
complexity, symmetric permutation lifting, publication label completeness,
provenance history and source inventory/unused-axiom audit coverage. Atomic
abstract durable/publication updates require a later implementation refinement;
no physical IO guarantee is intended. Planned statements are obligations, not
already proved results. Independent preflight may revise design before code.

Artifacts:
[spec](../superpowers/specs/2026-10-04-minimal-distributed-semantics-design.md),
[plan](../superpowers/plans/2026-10-04-minimal-distributed-semantics.md).
The delivery commit hash is in the executor handoff; do not insert a self-
referential hash into this receipt. Implementation begins only after coordinator
supplies physical Grok preflight. This invocation stops at committed documents.

## Final design-only verification

After document self-review, commands were repeated on the document-only tree:

| Command/check | Exit | Observed result |
| --- | --- | --- |
| `lake build` | 0 | `Build completed successfully.` |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | same 52-theorem PASS and `[propext, Quot.sound]`; successful completion |
| `lake env lean HarmoniaTests/AxiomAudit.lean` | 0 | fresh elaboration printed all 52 dependency sets and same PASS |
| `lake env lean HarmoniaTests/AuditRejection.lean` | 0 | no diagnostics; all expected rejection messages matched |
| Document self-review | 0 | all requirements mapped to six tasks; corrected step lifting and Config rejection proof; no placeholders, unclosed fences or trailing spaces |

Fresh audit confirms the baseline summary independently of Lake replay.
Final Git staged whitespace/scope checks and commit identity are supplied in
the executor handoff. Product, tests, Foundation contracts, CI and toolchain
are unchanged in this design-only delivery. No background process remains.

## Physical Grok preflight pins (2026-10-04)

Physical Grok ACCEPT was read from `/private/tmp/harmonia-stage-two-preflight-verdict.md`.
This text review is not a kernel proof. Coordinator reports the original review
terminated after 764.1s, exit 143, with no verdict; compact streaming retry
completed after 564.0s, exit 0, ACCEPT. Six pins govern implementation:

1. actorOf deliver is recipient, never sender; process/crash/recover actor,
   drop/duplicate none. Prove/probe this alongside frame.
2. Name PoolEq.symm, PoolEq.init_iff, PoolEq.wf_iff and execution_permutation
   (same labels and related endpoint); prove all, not just prose assertions.
3. Actual Core.Invariant imports Core.Execution, which imports TransitionSystem.
   Parent verification and local source reading resolve the omitted-Core concern.
   Use those imports and real Foundation.Execution.nil/cons, no invented module.
4. One file Harmonia.Examples.Distributed is imported by DistributedTraces.
   Its namespace Harmonia.Distributed.Examples does not determine source origin.
5. Universal wrong-outs negations for both process and deliver, with other
   premises legal. No spent-tid replay in reachable WF pools; malformed raw pools
   may contain duplicate tids and permit a second consumption. Distinguish them.
6. reliable has all four flags false; prove reliable_no_drop, reliable_no_duplicate,
   reliable_no_crash, reliable_no_recover and independent recovery gating.

Global next/tid are mathematical bookkeeping, not a central runtime service,
and are not passed to protocols. No native_decide in certified proofs. Envelope
origin identifies prior envelope publication, not the allocating step of every
tid, and does not authenticate payload claims. Exhibit distinct payloads under
one logical ID. Inventory parser tests multiline manifests, multiple imports,
trailing comments, unknown/unimported namespace-escape files, unused axioms and
adversarial contamination. Fixed-closure discipline and abstract atomic update/
publication assumptions remain explicit; no physical IO or fairness guarantee.

## Implementation progress ledger

Plan: docs/superpowers/plans/2026-10-04-minimal-distributed-semantics.md
Native worktree and branch unchanged; clean at resume from 3afc183.
Ruling: committed receipt is the durable ledger instead of ephemeral skill
workspace — coordinator explicitly requires persistent task progress — no loss
of task identity/evidence across compaction.
Interfaces checked: Task 1 types → 2 network → 3 Step/system → 4 proofs → 5
fixtures → 6 audit. Actual Foundation imports/constructors match the plan.
Task 1: pending. Task 2: pending. Task 3: pending. Task 4: pending.
Task 5: pending. Task 6: pending.

Task 1: complete. RED `lake env lean HarmoniaTests/DistributedMembership.lean`
exit 1: missing Protocol.olean. GREEN `lake build distributedTest foundationsTest
foundationsAudit foundationsAuditRejection` exit 0, source/API and type probes.
Ruling: Lean 4.16 has no #check_fail command — use fail_if_success with typed
have declarations instead — equivalent type rejection without requiring later
Lean syntax; cost if wrong is probe diagnostic ergonomics, not model behavior.
Intermediate build exit 1 identified exactly that unsupported command; no
semantic API change. Checked lists reject duplicates without deduplication;
empty/two-member witnesses and nonmember actor/endpoint rejection pass.

Task 2: complete. RED Network probe exit 1 (missing Network.olean). GREEN
`lake build distributedTest foundationsTest foundationsAudit foundationsAuditRejection`
exit 0. Proved Take length/position/permutation/residual uniqueness, allocation
interval/nodup/bounds/sender and Publish transports. Probe shows logical 7 with
false and true payloads: same logical ID implies no payload equality. Scratch
head-pop and stale-supply mutants exit 1 with the nonhead/type and two-ID
propositions failing; no mutants in source. Ordinary elaboration iterations
resolved reserved `prefix`, core range arithmetic and composition reduction;
core has no assumed nodup_append/map helper, freshness proved structurally.
Omega is kernel-producing core arithmetic, not native_decide or a dependency.
