# T-396 Stage3c investigation and preflight evidence

Status: investigation/design/plan only. No product, test or CI code written. Parent owns actual physical Grok preflight, verdict, publication and integration. No Grok was invoked here; no push, PR or merge. The managed physical CLI worktree for this invocation is `/Users/yong/.codex/worktrees/5b89/harmonia`, branch `feat/t396-generated-correspondence`, start `bcf44916b5cedf351a78e715470c351ddc84a2ad`. The physical Codex thread/session ID is `01a11179-2107-7842-8ea3-adaac2c2993a`; no separate virtual agent or Grok thread was created. The exact final local document commit is reported to the parent after verification.

## Sources and scope read

Read Harmonia `AGENTS.md`, accepted minimal Core design, Stage3a World/Interpreter and Stage3b Bridge design/plan/verification, generated source templates, audit policies and CI. Base `lean-toolchain` is `leanprover/lean4:v4.16.0`. The Kadmos read-only checkout at `/Users/yong/projects/substratum/kadmos` was `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`; its `git status --short` returned no entries. `src/world_compiler.ts` and `src/python_compiler.ts` were read directly, including evaluator, sanitizer, constructor, getters and step. The actual parser and compiler functions were invoked after compiling pinned Kadmos TypeScript source into private tmp. No other repository was edited.

Stage3b supplies `checkBridge raw candidate = .ok candidate`, source expression lowering and the two tracked parsed worlds. It does not establish generated target behavior. The two design goals remain distinct: model properties and generated-code/model behavioral correspondence. The selected first theorem concerns actual emitted constructor/getter fragments, and explicitly leaves `step` unproved. Design: `docs/superpowers/specs/2026-10-06-generated-implementation-correspondence-design.md`. Plan: `docs/superpowers/plans/2026-10-06-generated-implementation-correspondence.md`.

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

## Exact planned proof and remaining gaps

The proposed kernel theorem, if implemented and checked, would concern only `parseGenerated` of the **complete exact emitted source string** and independent target operation semantics for construction/getters. It must derive the initial-state relation and getter observations from a successful Stage3b `checkBridge`, not assume them. A Lean parser/decoder must inspect the accepted embedded data and selected statements; an external exporter may only provide exact source strings. Strict whole-file recognition makes changes in other template sections invalidate this version's certificate, but it does not give those sections operational semantics. The host JS/Python implementation of modeled target instructions, TS stripping/transpilation, exact exporter serialization, YAML parsing, and SHA-256/file comparison remain external trust boundaries.

The following remain unproved after the planned first slice: actual `step` correspondence, target Pratt evaluator and sanitizer semantics, safe intermediate arithmetic agreement, eager type/error order, profile-wide required versus lazy runtime field reads, old-state guard and sequential target-phase effect simulation, first-transition/terminal checks, rollback/rejection projection, history, savepoint, reset overrides, reentrancy, arbitrary host objects and full runtime language semantics. The plan describes the necessary later step obligations and deliberately does not claim they are discharged by the first theorem or the finite probes. No solver result or legacy experiment is treated as a kernel proof.

## Design and plan self-review

The design names exact pinned files/functions, actual emitted syntax patterns, two alternative engineering routes, accepted constructor/getter subset, rejected inputs, trust boundary and later step obligations. The plan has four tasks with file map, stable interfaces, RED/GREEN/hostile probes, serial baseline/global constraints and CI/audit integration. New target names are consistent: `kadmosGeneratedSyntaxTest`, `kadmosGeneratedSemanticsTest`, `kadmosGeneratedCertificateTest`, `kadmosGeneratedAudit`, `kadmosGeneratedAuditRejection`. Proposed `TargetProgram`/`TargetStore`, `parseGenerated`, `targetConstruct`, getters, `checkGenerated` and `targetRel` are named consistently between design and plan. No product implementation was begun. The main review risk is whether this narrow first constructor/getter theorem is sufficiently valuable for T-396; parent Grok must judge it before product work. A second risk is that target-machine semantics could accidentally become a copied reference initializer. Task 2 tests and reviewer focus require independent statement execution and forbid calling the reference operations.

Pending parent gates: full design to physical Grok, independent verdict, future native implementation only after ACCEPT, future hosted Linux and integration. Current docs are a concrete reviewable proposal, not proof completion.
