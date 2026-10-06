# T-395 Stage3b design/plan receipt — 2026-10-06

Status: documents only, awaiting parent's independent physical Grok preflight and ACCEPT before product implementation. Physical owner: Codex, native `--worktree` checkout `/Users/yong/.codex/worktrees/341d/harmonia`, branch `feat/t395-kadmos-ir-bridge`, starting main `b81df540439846b9df3cedc9ee0ca68380677b7b`. Parent retains the internal task ledger, review, publication and integration. No subagents, internal/Kadmos edit, push, PR or merge.

## Source investigation and rulings

Accepted foundation route: `docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md`. Predecessor T-393 design/plan and `docs/verification/2026-10-05-kadmos-world-ir.md` were read; T-394 ledger reference is historical and not renamed. Existing Lean API read: `World.lean`, `Interpreter.lean`, `System.lean`, `Balance.lean`, associated probes and application audit/inventory. Read-only Kadmos at `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`: `src/types/world.ts`, `src/world_expression.ts`, `src/world_compiler.ts`, `src/python_compiler.ts`, `conformance/fixtures/order_settlement.world.yaml`, and `tests/test_harness_world_compiler.test.ts`. No `src/domain_model.ts` or `world_parser.ts` was assumed.

`parseWorldSpec` returns WorldSpec with expression strings and ordered arrays/object context; it does not construct a typed AST. Its identifier check is broader than the formal subset. The evaluator supports additional unary/string/null/property/multiply/divide operators and computes binary boolean operands eagerly, with right-associative implication. Generated TS/Python remain separate programs. T-393 Lean `World` is finite indexed; `interpret` performs actual guard/effect/postcheck sequencing and contains the safe-integer limit, and `Balance.lean` is a handwritten example rather than a source adapter.

Selected approach: actual parser result is exported with original strings and order; a Lean checker parses the restricted expressions, resolves names/profile fields, checks every projection field and confirms the resulting World is initialized. The pinned YAML, parsed JSON, adapter profile and generated Lean data have hash/byte provenance. The kernel establishes properties of the checked raw record and projected `World`, while parser/export serialization, host object behavior and generated TS/Python remain explicit external boundaries. An untrusted direct exporter would be too weak; a general YAML/JS parser in Lean is beyond this stage. Wrong binding/order, silent unsupported syntax, source/target phase confusion, or unsafe cancellation could certify the wrong behavior, so each has a fail-closed probe or stated precondition.

The concrete balance YAML was written only to `/private/tmp/t395-balance.world.yaml` and passed to the pinned checkout's **installed** `dist/src/world_compiler.js` `parseWorldSpec` as a source-shape probe. It returned `BalanceWorld`, Ready, balance 100/[0,S], invariant `balance >= 0`, and `DEBIT` guard `event.amount > 0`, null directive, effect `balance = balance - event.amount`. YAML SHA-256 was `1357baa55f5cc0453a491df264ca75adacad1db580e4bc952dc4adffc900258b`. The installed `dist` binary was not proven to be compiled from the pinned source in this design pass; Task 3 requires private-tmp compilation from pinned source and records final tracked hashes. No product artifact or result was certified by this probe.

## Fresh physical baseline (serial)

Every Lake command completed before the next Lake command started. All processes below returned exit 0. Outputs were observed directly; no new product code or test target was created.

| Command | Observed result |
| --- | --- |
| `lake env lean --version` | Lean 4.16.0, arm64-apple-darwin23.6.0, commit 128a1e6b0a82 |
| `lake build` | 36/36, built `harmonia` |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | built; Foundation audit 52 theorems, `[propext, Quot.sound]` |
| `lake build distributedTest distributedAudit distributedAuditRejection` | built; Distributed audit 336 theorems/594 declarations, `[propext, Quot.sound, Classical.choice]` |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | built; application audit 426 theorems/752 declarations, same three standard axioms |
| `python3 scripts/check_distributed_audit.py --self-test` | 16 tests, OK |
| `python3 scripts/check_distributed_audit.py` | inventory 12 certified modules, distributed closure 16, foundation closure 10 |
| `python3 scripts/check_kadmos_world_audit.py --self-test` | 20 tests, OK |
| `python3 scripts/check_kadmos_world_audit.py` | application inventory 9, audit closure 13, six certified and three isolated targets |
| `lake env lean HarmoniaTests/AxiomAudit.lean` | fresh Foundation 52, `[propext, Quot.sound]` |
| `lake env lean HarmoniaTests/DistributedAxiomAudit.lean` | fresh Distributed 336/594, `[propext, Quot.sound, Classical.choice]` |
| `lake env lean HarmoniaTests/KadmosWorldAxiomAudit.lean` | fresh Kadmos 426/752, `[propext, Quot.sound, Classical.choice]` |

The counts belong to separate import environments. No new bridge target, certificate or Linux run is claimed. Solver UNSAT and finite exploration were not used as proof.

## Document handoff and limits

[Design](../superpowers/specs/2026-10-06-kadmos-ir-bridge-design.md) chooses the supported grammar/profile, full binding contract, source/target phase rules and trust boundary. [Plan](../superpowers/plans/2026-10-06-kadmos-ir-bridge.md) gives four independently testable tasks: source syntax/evaluator, checked projection/kernel transfer, physical parser artifacts/source-bound outcomes, and artifact/audit/Linux isolation. This is a design/plan package only; the parent sends it to Grok and independently judges findings. The executor stops before Task 1 until true preflight ACCEPT.

Before publication, self-review checked coverage of source binding, profile failures, eager/right-associative syntax, name/order/phase/effect mutations, exact balance 30/130 and hostile fixture outcomes, safe-intermediate boundary, audit isolation, and future TS/Python gap. Proof signatures are planned, not yet elaborated; if a theorem cannot be established in Init/Lean 4.16 without weakening the contract, that is a preflight or implementation blocker to report. No request for routine approval is needed under the preserved managed authorization.

Automated document self-review exited 0: balanced fences, no trailing whitespace or unresolved placeholder terms, four tasks, and only the three intended documents present. No product/test/tooling modification was made in this invocation.
