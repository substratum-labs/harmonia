# T-396 Stage3c investigation and preflight evidence

Status: investigation/design/plan only. No product, test or CI code written. Parent owns actual physical Grok preflight, verdict, publication and integration. No Grok was invoked here; no push, PR or merge. The managed physical CLI worktree for this invocation is `/Users/yong/.codex/worktrees/5b89/harmonia`, branch `feat/t396-generated-correspondence`, start `bcf44916b5cedf351a78e715470c351ddc84a2ad`. The physical Codex thread/session ID is `01a11179-2107-7842-8ea3-adaac2c2993a`; no separate virtual agent or Grok thread was created. The exact final local document commit is reported to the parent after verification.

## Sources and scope read

Read Harmonia `AGENTS.md`, accepted minimal Core design, Stage3a World/Interpreter and Stage3b Bridge design/plan/verification, generated source templates, audit policies and CI. Base `lean-toolchain` is `leanprover/lean4:v4.16.0`. The Kadmos read-only checkout at `/Users/yong/projects/substratum/kadmos` was `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`; its `git status --short` returned no entries. `src/world_compiler.ts` and `src/python_compiler.ts` were read directly, including evaluator, sanitizer, constructor, getters and step. The actual parser and compiler functions were invoked after compiling pinned Kadmos TypeScript source into private tmp. No other repository was edited.

Stage3b supplies `checkBridge raw candidate = .ok candidate`, source expression lowering and the two tracked parsed worlds. It does not establish generated target behavior. The two design goals remain distinct: model properties and generated-code/model behavioral correspondence. Parent self-review rejected the original constructor/getter-only acceptance scope in local commit `e253b774475dde8b7a6d4f814e6bbb57edfe66b5`; this was not a physical Grok REVISE or strike. The corrected acceptance requires a universal generated balance DEBIT step theorem in both TS and Python for all `0≤b≤S`, `safeInt n`, in addition to construction/getters. No such theorem exists yet. Design: `docs/superpowers/specs/2026-10-06-generated-implementation-correspondence-design.md`. Plan: `docs/superpowers/plans/2026-10-06-generated-implementation-correspondence.md`.

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

## Corrected design/plan self-review

The previous scope/type defects are addressed in the corrected design: dependent Bridge dimensions, explicit low-level AST/function-call schemas, independent `SourceParses` parser-soundness relation, tagged TS/Python number values and helper-body execution, a prestate-only relation (`Ready`, one bounded balance, empty history, no undo, not busy), three universal model/target cases, both language certificates and concrete nonvacuity witnesses. The plan has five proposed review gates: provenance, source-directed parsing and constructor/getters, independent reached step execution, dependent certificate/universal theorem, and audit/CI. Exact target names are `kadmosGeneratedSyntaxTest`, `kadmosGeneratedConstructorTest`, `kadmosGeneratedSemanticsTest`, `kadmosGeneratedStepTest`, `kadmosGeneratedAudit`, `kadmosGeneratedAuditRejection`; each is defined in the plan. The principal feasibility risk is the generated Pratt evaluator/sanitizer control flow. The plan requires stopping without a code-correctness claim if a reached helper remains opaque. No product, test or CI code has been changed by this correction.

Pending parent gates: send the corrected full design to actual physical Grok, independent verdict, native implementation only after ACCEPT, then hosted Linux and reviewed integration. This document records a concrete proposal and physical investigation, not proof completion.
