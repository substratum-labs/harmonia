# T-396 Stage3c investigation and preflight evidence

Status: investigation/design/plan only. No product, test or CI code written. Parent owns actual physical Grok preflight, verdict, publication and integration. No Grok was invoked by this owner; no push, PR or merge. The managed physical CLI worktree for this invocation is `/Users/yong/.codex/worktrees/5b89/harmonia`, branch `feat/t396-generated-correspondence`, start `bcf44916b5cedf351a78e715470c351ddc84a2ad`. The physical Codex thread/session ID is `01a11179-2107-7842-8ea3-adaac2c2993a`; this owner created no virtual agent or Grok thread. The exact final local document commit is reported to the parent after verification.

## Sources and scope read

Read Harmonia `AGENTS.md`, accepted minimal Core design, Stage3a World/Interpreter and Stage3b Bridge design/plan/verification, generated source templates, audit policies and CI. Base `lean-toolchain` is `leanprover/lean4:v4.16.0`. The Kadmos read-only checkout at `/Users/yong/projects/substratum/kadmos` was `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`; its `git status --short` returned no entries. `src/world_compiler.ts` and `src/python_compiler.ts` were read directly, including evaluator, sanitizer, constructor, getters and step. The actual parser and compiler functions were invoked after compiling pinned Kadmos TypeScript source into private tmp. No other repository was edited.

Stage3b supplies `checkBridge raw candidate = .ok candidate`, source expression lowering and the two tracked parsed worlds. It does not establish generated target behavior. The two design goals remain distinct: model properties and generated-code/model behavioral correspondence. Parent self-review rejected the original constructor/getter-only acceptance scope in local commit `e253b774475dde8b7a6d4f814e6bbb57edfe66b5`; this was not a physical Grok REVISE or strike. The corrected acceptance requires a universal generated balance DEBIT step theorem in both TS and Python for all `0≤b≤S`, `safeInt n`, in addition to construction/getters. No such theorem exists yet. R1 later returned REVISE; the correction and parent domain ruling appear below. Design: `docs/superpowers/specs/2026-10-06-generated-implementation-correspondence-design.md`. Plan: `docs/superpowers/plans/2026-10-06-generated-implementation-correspondence.md`.

## Fresh baseline, serial Lake

One shell process ran `lake build`, then each of these 14 pre-existing targets in sequence, with no concurrent Lake process:

```text
foundationsTest foundationsAudit foundationsAuditRejection
distributedTest distributedAudit distributedAuditRejection
kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection
kadmosBridgeSyntaxTest kadmosBridgeCertificateTest kadmosBridgeFixturesTest
kadmosBridgeAudit kadmosBridgeAuditRejection
```

The full sequence exited **0**. `lake build` reported `Build completed successfully.` Every dedicated target reported successful build, including isolated rejection fixtures with their expected diagnostics. The baseline audit output is large; the final shell exit 0 covers every command because `set -e` was active. One existing Bridge source linter suggestion says to use `simp` instead of `simpa`; it is not a failed build. The baseline did not include a fresh `lake env lean` replay of every unchanged audit; prior Stage3b receipt records the exact fresh counts and whitelist. No T-396 proof or new target exists yet.

The same command then ran inventory/artifact self-tests and checks; all exited 0. Observed final Bridge artifact identity: parsed SHA-256 `8dfb3941def3dcc1d25c2d4286f3c9dce47a5404c75b89486e32d791720fd19e`, generated Lean SHA-256 `fe05fc6a76fd0657ce3ad9a71c4ac76e048792cf97458d59d120362791ed4956`. The Bridge policy suite ran 10 tests per invocation and passed. Bridge inventory reported 7 modules/14 import closure, four certified targets and one isolated target; old application inventory 12 modules/16 closure, six certified and three isolated targets; Distributed inventory 12/16/10. These are baseline observations, not fixed future count requirements. Stage3b's fresh receipt separately reported Foundation 52 theorems, Distributed 336 theorems/594 declarations and standard axiom whitelist; this investigation did not recompute those fresh counts.

## Physical generated artifact probe

Command sequence, all output under `/private/tmp/t396-probe`:

```text
/Users/yong/projects/substratum/kadmos/node_modules/.bin/tsc \
  -p /Users/yong/projects/substratum/kadmos/tsconfig.json \
  --outDir /private/tmp/t396-probe/kadmos-js
node --experimental-strip-types /private/tmp/t396-probe/run.mjs
```

The private-tmp Node driver imported the actual freshly compiled `parseWorldSpec`, `compileWorldSpec`, `compileWorldSpecPython`; read the tracked Stage3b YAML; wrote returned `worldCheckerTs`, `portsDts`, `worldCheckerPy`, `portsPy` to private tmp; imported the emitted TS directly using Node 26 type stripping; and ran the emitted Python source with Python 3. Type stripping and host execution are external observations, not kernel evidence. Both commands exited 0. Exact current output fingerprints:

| Fixture | TS SHA-256 / characters | Python SHA-256 / characters |
| --- | --- | --- |
| balance | `1934926af84814aa2e463dd5429f0236a651c9eb1a8527707a203c438917d49d` / 16368 | `3ccec332a536cca1f98043a92d4988e2eec36471b4511f4d0aec9eba0c365c32` / 17906 |
| order_phase | `6495eebd088e782a535b45b852520b314f859937f096d38ed246b654333bc37a` / 16388 | `54a8bc28762d930e90fa2b4078fa2726775f689bcd87e56a5e021bf4ae777c78` / 17962 |

| Emitted program | Constructor/getter | Step sequence (allowed, code, current state, context, directive) |
| --- | --- | --- |
| TS balance | Ready, `{balance:100}` | DEBIT 30 → true, no violation, Ready, 70, null; DEBIT 130 → false, `INVALID_BOUNDS`, Ready, 70, null; DEBIT 20 → true, no violation, Ready, 50, null. Getter remained aligned after each. |
| Python balance | Ready, `{balance:100}` | Same allowed/code/state/context/directive sequence and getter observations. |
| TS order | A, `{x:1,y:0}` | STEP → true, no violation, B, `{x:2,y:2}`, null; getter B/(2,2). |
| Python order | A, `{x:1,y:0}` | Same projected result and getter observation. |

This is nonvacuous finite execution of actual emitted programs, with accept, rejection frame, ordered candidate effects and target-phase invariant behavior. It does not prove these operations for arbitrary inputs. The exact recorded commands depend on private-tmp driver `run.mjs`, which was not staged; the plan requires a deterministic tracked exporter and reproducible test command before certification.

A hostile **emitted source** mutation was made only in private tmp: replace the one embedded effect `balance = balance - event.amount` with `balance = balance + event.amount` in each generated checker, leaving all other text unchanged. Both mutated programs accepted DEBIT 30 but produced Ready/130 rather than Stage3b model Ready/70. Node and Python probes exited 0 and exposed the mismatch. There is no present T-396 certificate to fail; the proposed checker must reject this mutated complete source even if an attacker recomputes a manifest digest. The mutation also shows why a hash of any generated artifact or a handwritten comparison interpreter is insufficient assurance.

## Focused source and boundary feasibility after parent review

The actual Stage3b type was rechecked: `Bridge.checkBridge (raw : RawWorld)` takes `World raw.states.length raw.context.length raw.fields.length raw.transitions.length`. The former proposed `World p v f a` checker interface was invalid without a dimension cast. The corrected design and plan use the dependent dimensions exactly; the balance fixture specializes to `World 1 1 1 1`.

Private-tmp boundary probes ran the **actual emitted checkers** with canonical request `DEBIT`, payload `amount:n`, absent proposed directive and current balance set through the target API. Both languages produced the same projected results:

| b | n | allowed | code | final balance |
| ---: | ---: | --- | --- | ---: |
| 0 | 0 | false | `GUARD_FAILED` | 0 |
| 0 | 1 | false | `INVALID_BOUNDS` | 0 |
| 100 | -1 | false | `GUARD_FAILED` | 100 |
| 100 | 30 | true | none | 70 |
| 100 | 130 | false | `INVALID_BOUNDS` | 100 |
| S | S | true | none | 0 |
| S | -S | false | `GUARD_FAILED` | S |

All returned `Ready` and null directive. Node 26 `--experimental-strip-types` and Python 3 commands exited 0. These finite observations test the chosen domain's boundaries and do not prove its universal behavior. Private-tmp files remain unstaged. The pinned Kadmos source and generated output fingerprints are unchanged from the earlier probe.

## Corrected planned proof and remaining gaps

The new T-396 acceptance theorem must quantify over every `b,n` with `0≤b≤S` and `safeInt n`, and a related **prestore**. A Lean parser must consume exact complete TS/Python emitted source strings, decode data, parse the selected `step` statements and reached evaluator, sanitizer, bounds and invariant helper bodies into a small language AST. Independent target operational semantics executes that AST; there is no atomic idealized helper primitive or reference interpreter call. For `n≤0`, it derives guard rejection/frame; for `0<n≤b`, publication of `b-n`; for `n>b`, bounds rejection/frame. It proves normalized allow/state/context/directive equality with actual Stage3b `interpret balanceCandidate` and target violation-code refinements. Construction/getters remain an initial theorem for both balance and order. The new five-task plan names AST/store/request/observation schemas, dependent checker signature, RED/GREEN and mutation probes, and audit/CI integration.

This is still a **planned** kernel claim, not a completed proof. Exact emitted source strings must be reproduced and bound by an external byte-for-byte exporter check; this serializer boundary is not proved by the Lean theorem. A kernel theorem about the modeled restricted TS/Python source-language operations also relies externally on Node/CPython implementing the specified basic primitive arithmetic/object operations on canonical values. It does **not** assume that Kadmos's user-defined evaluator/sanitizer/bounds/invariant helpers implement an ideal behavior: their selected source bodies and calls must be parsed and executed formally. If any helper branch reached by the canonical request cannot be modeled, there is no step-correctness claim; parent must choose a larger formalization or an explicitly authorized certified-backend architecture.

Outside this first domain remain other action/directive cases, arbitrary/hostile objects and inputs, non-safe arithmetic and error-order cases, reset overrides, error messages/counterexample history, savepoint API, reentrancy, general WorldSpec, order STEP proof, full JS/Python runtime semantics, physical IO and distributed/legacy experiments. Within the selected domain, rejection frame and candidate/check/publication order **are required proof obligations**, not deferred. No solver result or finite physical trace is a kernel proof.

## Physical Grok R1 and parent scope ruling

After local plan commit `f4d9eb81c2f669a21cc1f8a3ec7b0f979a189a50`, parent ran actual physical Grok preflight R1: exit 0, 873.2 seconds, structured success with `is_error=false`, verdict **REVISE**. This is a real Grok verdict. Parent independently accepted the technical corrections below and ruled that route 2 remains viable; there is no architecture conflict. R2 belongs to the parent. No Grok was invoked by this owner in this correction turn.

R1's decisive counterexamples were: copied closure captures leave TS `index`/Python `position` at zero and turn positive DEBITs into guard errors; loop-local `return key` can incorrectly fall through from bounds to invariant failure; treating evaluator `switch` break as loop break makes the order initial invariant's three-operator parse stop early; strict arity rejects actual defaulted helper calls; skipped TS class-field/module initialization makes construction fail; and treating emitted WorldSpec JSON as RawWorld rejects the actual artifact. The review also identified missing reached primitives, Python sanitizer `.pyInt→.pyFloat` conversion, Python globals and `_freeze`/getter alias calls, heap identity/frozen/descriptor state, and insufficient `SourceParses` independence.

**Parent's one-call domain ruling:** restrict the first universal step theorem to incoming `history=[]`, `undo=none`, `busy=false`, one typed `balance=b` in `[0,S]`, canonical own-data/exact-dict request, and safe signed `n`. Retain universal quantification over every such `b,n`. Arbitrary history, tree-size fuel, savepoints and multicall induction are a later slice. This makes the one-record trace/fuel bound independent of `b,n` and avoids the R1 contradiction in which a theorem over arbitrary prior history claimed posthistory `[]`. Rejection proves **logical checker data** unchanged after the executed rollback/finalizer; clone allocations can change object identity and frozen metadata. TS acceptance has pre-call undo plus a frozen one-record history; Python acceptance has no undo and a one-record history with sanitized `.pyFloat n`; both end at Ready with busy false.

The corrected design/plan replace value-snapshot closures with shared mutable cell addresses and fresh recursive frames; define `ControlResult` normal/return/targeted break/continue/exception and `tryCatchFinally` propagation; model an object heap with references, descriptors, prototypes, frozen bits, arrays, sets and mapping proxies; parse module/class initialization and every reached generated helper; distinguish JS call-time omitted/undefined defaults from Python definition-time defaults; and return updated heap with getter values. `SourceParses` is an independent inductive token-span/statement/call relation with deterministic lexical naming and parser soundness/uniqueness; a separate `SurfaceExec` relation and `desugar_preserves` obligation cover reached `.find/.some/.map`, Python `next` and evaluator switch control. The embedded-data checker compares actual fixture-normal-form **WorldSpec JSON**, including omission/key order/guard Boolean/null directive, to a neutral JSONValue before target-language tagging. `checkGenerated` retains exact raw-dependent `World raw.states.length raw.context.length raw.fields.length raw.transitions.length`.

No assumption asserts that Kadmos `evaluateWorld`, `evaluate_world`, sanitizer, bounds or invariant helpers implement an ideal behavior. The plan requires their selected bodies and actual call/control flow to execute under restricted source-language semantics. Basic host primitive contracts and external source-string serialization remain explicit boundaries. A source recognizer that maps an unchanged helper to a single handwritten ideal macro fails acceptance. The universal model cases are to be proved from **`BridgeFixtures.balanceCandidate`**, not the older `Balance.balanceWorld`. Closed `decide +kernel` is for artifact/certificate facts; the `b,n` theorem is symbolic.

## R1 correction self-review and next gate

The revised five-task plan names exact machine, expression, control, heap, request, observation, parser/certificate and theorem interfaces; adds tests for shared index cells, targeted switch/loop exits, default allocation and arity, actual JSON presence, module/global/freezing/tag flow, canonical descriptors/prototypes, lazy expressions, busy/finalizer, logical frame and getter aliasing. The selected domain and theorem postconditions no longer assert physical heap identity or arbitrary-history results. Actual pinned source inspection reconfirmed the emitted TS root JSON has only `version,name,states,context,invariants,transitions`, a `Ready` state with `initial:true`, ordered context definition, `guard` string and `directive:null`; Kadmos remains at `fda8c6e42825b35afe5484a4af9d84d9d206ba9a` and clean. A private-tmp Lean 4.16 declaration probe at `/private/tmp/t396-r1-schema.lean` copied the proposed core syntax/machine/request/observation record shapes (with a minimal illustrative BuiltinId/PrimOp) and `lake env lean /private/tmp/t396-r1-schema.lean` exited 0 with no diagnostics. This checks the basic inductive/record interface shape only; it proves no parser, semantics or correspondence theorem and is not retained. The prior serial baseline/14 targets and physical vectors remain valid because only these three documents changed. No product/test/CI source was written or reverified here.

The principal remaining risk is implementation cost of parsing and executing every reached nested helper with closures and heap effects. The plan's stop condition is explicit: if a reached operation cannot be represented and proved, no step-correctness claim is allowed and parent receives a concrete architecture decision. The R1 correction was a preflight proposal, not completed correspondence. Parent then ran physical Grok R2; its verdict and the second correction are recorded below.

## Physical Grok R2 and parent ruling

Parent ran actual physical Grok preflight R2 after local commit `57dbe3a56829b17ba74d4ebc74e62a0682cfaa26`: exit 0, 624.4 seconds, structured success, verdict **REVISE**. Route 2 remains viable. This is the **second consecutive actual preflight REVISE**; no ACCEPT exists. Parent independently judged the four remaining holes valid and accepted the R1 cell/control/default/JSON/tag/source-grammar/dependent-checker fixes as closed. No Grok call was made by this owner. Parent owns physical R3 and its independent verdict.

The four R2 failures and precise correction are:

1. **Conditions:** the old AST named lazy logical forms but had no executable language truthiness for `if`, `while`, unary `!` or Python `not`. `sourceTruthy lang machine value` now specifies all reached scalar/reference/container cases. Nonempty `"balance"` must select `INVALID_BOUNDS`; absent `invalid`/`violated` and descriptor `get`/`set` are false. Lazy and/or return source operand values; `??` is nullish-only; generated `booleanWorld`/`_boolean` remains a separate parsed strict-Boolean helper.
2. **Closed primitives:** the spec and plan now enumerate `isspace`/`isdigit`/token index, decimal string conversion, `len`, `join("")`, negative quote slice and distinct quote-unescape/whitespace replacements, regex full/group numbering, opaque Python `id` reference identity, `.pyFloat/.pyInt.is_integer`, and one shared `Object.prototype` ref with null-prototype own-data lookup. Each has an arity/tag/result/update contract in the design, with positive and malformed probes in the plan. Python request amount still starts `.pyInt n`, sanitizer creates `.pyFloat n`, numeric evaluation uses `.pyFloat` even for negative guard input, and effect publication stores `.pyInt (b-n)`.
3. **Python instance attributes:** `TargetStore.instanceAttrs` holds `_initial_context`; parsed `__init__` writes `None`, parsed `reset(None)` reads it, then `__init__` stores `dict(self.context)`. Bound Python `self` and TS `this` are implicit receivers, not explicit `ParamSpec` arguments. Getter aliases and reached wrappers remain parsed. The logical checker projection includes attribute data while allowing cloned reference identity.
4. **Quantified one-call prestate:** `balancePreRel lang program b machine` now requires a one-key own enumerable data descriptor with exact numeric tag/value, mutable unfrozen empty TS history array or mutable exact Python list, no undo, busy false, and globals derived from the certified program's module init. The source `Object.entries`/Python `.items()` yields `("balance", definition)` in order; `forDo` with two binders splits that pair into fresh key/definition cells, one binder receives an element, and malformed cardinality raises an error. A constructor witness must **derive** the metadata for default b=100 from actual parsed source; witnesses for every bounded b preserve source-executed canonical module globals/field layout while replacing only the mutable balance data value; they establish a valid current state without claiming public reachability or assuming output. Arbitrary history, savepoints and multicall remain outside this first theorem.

This correction preserves the exact four pinned emitted source strings and fixture-only `emittedWorldData` omission normalization, dependent `checkBridge` dimensions, independent inductive `SourceParses` plus uniqueness and checked desugaring, noncircular target execution, the universal symbolic `b,n` theorem goal and logical rather than physical heap frame. No product/test/CI code exists. The prior serial 14-target baseline and physical boundary probes are unchanged; only these three documents were edited in this correction turn. A private-tmp schema/proof probe and read-only source/API check were run as follows. Parent sends the corrected full design for physical R3; an ACCEPT would authorize implementation, not claim theorem completion.

### R2 correction probes and self-review evidence

`lake env lean /private/tmp/t396-r2-schema.lean` exited **0** with no diagnostics. The throwaway Lean file declares a small reference/value/machine/attribute/pair schema and closes twelve `by decide` probes: TS undefined/object truthiness, Python ordinary-object/empty-dict/nonempty-dict/`"balance"` truthiness, regex full/group 1/group 2 indexing, `_initial_context` attribute lookup, two-member pair destructuring and malformed one-member rejection. A second private-tmp declaration probe, `lake env lean /private/tmp/t396-r2-full-schema.lean`, added the planned `instanceAttrs`, `Intrinsics.objectPrototype`, `Option ObjRef` prototype and distinct TS/Python heap kinds to the earlier core schema; it also exited **0** without diagnostics. These probes test declaration feasibility and the intended small rules only; it is **not** the generated-source parser, actual primitive semantics, or correspondence proof. Nothing from it was copied into product/test/CI source.

Read-only `rg` in pinned Kadmos confirmed `src/python_compiler.ts` uses `match.group().isspace`, `token[0].isdigit`, `id(value)`, `float(value).is_integer`, `_initial_context` write/read, `_EFFECT.fullmatch` with `.group(1/2)`, `getState/getContext` wrappers, and `src/world_compiler.ts` uses `Object.entries`, `Object.prototype`, `tokens.join("")` and whitespace replacement. Kadmos status remained clean at `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`. No Lake baseline target was rerun because the repository source, tests and CI are unchanged since the successful serial 14-target baseline.

Author self-review checked the four R2 failure paths against the schema and plan: `sourceTruthy` is used for conditions and short-circuit operations while strict `booleanWorld` remains parsed; newly listed primitive arities/tags/results and regex group offsets agree with source call sites; `instanceAttrs` and implicit receiver binding cover the Python `__init__→reset→getter` path; and `balancePreRel lang program b machine` ties own enumerable context/global entries and mutable empty history to the certified program without constraining target output. The first theorem still quantifies every bounded `b` and safe `n` for **one call** from empty history/undo. Any unsupported reached primitive remains a stop condition, not an assumed helper theorem. Parent owns physical R3; this author review does not replace it.
