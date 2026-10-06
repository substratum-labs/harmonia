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

## R1 physical Grok preflight correction (documents only)

The first four-turn reviewer attempt ended exit 1 without a valid verdict. Parent retried the actual physical Grok review for 16 turns; it completed exit 0 in 378.2 seconds and wrote `/private/tmp/harmonia-t395-preflight-verdict.md`. The full verdict is **REVISE**, four Important and three Minor findings, no Critical/domain conflict. Parent owns independent judgment and will run R2. This executor read the complete verdict and verified its code references against `World.lean`, `AuditPolicy.lean`, the umbrella import and the old application inventory. No implementation began.

R1 corrections in the same design/plan package:

1. `sourceEval` is mathematical and has no overflow branch. Independent inductive `sourceSafe` covers both eager children, every literal/read and intermediate sum/difference. `lowerExpr_sound` needs this premise. Safe literal tokens `S` and `1` may form `S+1`; the certificate can accept that syntax while unsafe execution rejects. The individually unsafe literal `9007199254740992` fails static certification. Mandatory mathematical `.ok` versus Lean overflow witnesses cover both eager boolean directions and final-safe cancellation.
2. The old application inventory scans all `Harmonia/Applications/**/*.lean`. Its literal `kadmosWorldSourceModules`, umbrella import and old audit import grow incrementally as Syntax, Certificate and Fixtures appear. Its 426/752 audit is the starting count only; Foundation52 and Distributed336/594 remain separate unchanged environments. A distinct Bridge manifest/selector covers all new product/probe/audit modules by scoped namespace or source module, including namespace escapes and unused/indirect axioms, without selecting the entire old Application prefix.
3. Complete RawState/RawVariable/RawInvariant/RawGuard/RawTransition/RawWorld schemas, unknown-key `extras` rejection, guard/effect `Expr p v f` versus invariant `Expr p v 0`, static sorts and explicit source/target/published environment modes are now pinned. Bridge defines computable AST/transition/World equality via `List.ofFn`; it does not edit `World.lean`. `>`/`>=` retain operand order, so source-bound balance proofs compute the exported candidate rather than reusing handwritten `balanceWorld`.
4. The deliverable input is the existing formal `Request f` and `RawPrimitive` decoder. No undefined `CertifiedRequest` or host-object rejection guarantee remains. Fractional/NaN/infinite inputs map to `.invalidNumber` only under a future external adapter assumption; extra runtime properties/accessors/proxies are outside this formal type. Profile JSON extra keys fail artifact checks.

The minor corrections distinguish closed parser probes from a general Kadmos parser theorem, compare invariant ID plus lowered Expr while keeping source text/hash in the raw artifact, and separate original-raw/candidate drift rejection from a consistently regenerated reversed world that may certify but rejects during interpretation. The four task flow remains. Export escaping/injection and strict JSON key/type/numeric checks are explicit failure cases; actual `parseWorldSpec` outputs, differential vectors and Lean data remain separately bound artifacts. No generated TS/Python claim was added.

Parent separately compiled pinned Kadmos TypeScript into `/private/tmp` and reran `parseWorldSpec` with `/private/tmp/harmonia-t395-real-ir-probe.mjs`; parent reports exit 0 and fresh output byte-equal to installed dist for the balance probe. The resulting `/private/tmp/harmonia-t395-balance-worldspec.json` has newline-inclusive SHA-256 `23e1e9a9a047a0497a6fe9ef35673d188fabb60e3833674ce3c5008ab320150d`; YAML SHA-256 remains `1357baa55f5cc0453a491df264ca75adacad1db580e4bc952dc4adffc900258b`. This is parent-supplied physical provenance, not a source-to-Lean semantic proof or a command rerun by this executor.

Only private-tmp Lean feasibility probes were run here. The first `List.ofFn`/Fin2 draft failed to elaborate because unrestricted list indexing lacked a length witness and `interval_cases` was unavailable. The corrected `lake env lean /private/tmp/t395-ofFn-proof-probe.lean` exited 0 on pinned Lean 4.16: `congrArg (fun xs => xs[j.val]?)` followed by `simpa` proves `List.ofFn` injectivity; `by_cases j=0`, `Fin.ext` and `omega` prove a full `Fin 2 → Int` context equality. This is proof-method evidence outside the product, not a Stage3b theorem or a completed-task failure. A separate string escape probe failed on an unsupported `\u{4E2D}` spelling; the plan instead pins escaped ASCII controls and printable UTF-8 with round-trip/injection tests. The unchanged product baseline above was not rerun.

A second private-tmp Lean API probe initially rejected grouped structure fields and unescaped `from`. The corrected `lake env lean /private/tmp/t395-api-shapes-probe.lean` exited 0: individual `Raw*` field declarations, `«from»`, dependent `Expr raw.states.length raw.context.length fieldNames.length`, `raw.states[q].id`, and `(raw.context[j]).1` elaborate under Init/Lean 4.16. The plan now uses those exact spellings. No probe was retained in the worktree.

Final R1 document review: the automated check returned exit 0 for balanced fences, trailing whitespace, unfinished markers, four tasks and explicit R1 coverage terms across the three files. A historical marker in this receipt initially tripped that literal scan; it was replaced with the exact failed `\u{4E2D}` probe spelling and the scan reran clean. Final staged scope/diff and clean-commit evidence are recorded in the handoff, not inferred from the unchanged baseline.

## Remaining R1 self-review premise correction

Parent found an omitted hypothesis before R2, not a new reviewer verdict or completed-task failure. With duplicate raw phase IDs `[A,A]`, lowering `stateEq "A"` by first match chooses `Fin 0`; at phase `Fin 1` source string equality is true while Lean indexed equality is false. Successful lowering and `sourceSafe` alone therefore cannot imply `lowerExpr_sound`. The spec/plan now require `NamesWF raw fieldNames`: no duplicate state IDs, context names or supplied field names, plus exact indexed environment relations. `projectWorld` checks `NamesWF raw raw.fields` before lookup and proves `projectWorld_names_wf`; successful `checkBridge` yields `checkBridge_names_wf`. The invariant `fieldNames=[]` case derives its premise from those checks. Duplicate phase/context/field probes pin the failure boundary without changing semantics.

Parent supplied `/private/tmp/harmonia-t395-duplicate-phase-probe.lean`; this executor reran `lake env lean` on it, exit 0 under Lean 4.16. It checks true string equality versus false `Fin` equality and proves indexed-name injectivity from `List.ofFn` nodup with `List.getElem?_inj` and `Fin.ext`. One unnecessary-`simpa` linter warning was harmless. This private-tmp evidence does not prove the future bridge theorem. Only the three existing documents changed; the prior product baseline was not rerun.
