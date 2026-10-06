# T-395 Kadmos IR Bridge Implementation Plan

> **For agentic workers:** Execute these four tasks in order with the physical Codex owner, one completed task and review gate at a time. Use `superpowers:executing-plans`; do not dispatch subagents. Independent physical Grok preflight must return ACCEPT before Task 1. Parent owns later review and integration.

**Goal:** Bind real pinned `parseWorldSpec` results to the existing Harmonia Kadmos `World` through a Lean-checked restricted source syntax and complete projection certificate.

**Architecture:** A provenance exporter produces tracked parsed-result JSON and Lean raw/candidate data from two actual Kadmos YAML fixtures. Init-only Lean code parses the retained expression strings, resolves ordered names and checks every candidate World field. Kernel theorems and concrete outcomes apply to the certified World; external parser/export/runtime assumptions remain labeled.

**Tech Stack:** Lean 4.16.0/Init, existing Lake targets, Python 3 standard library for artifact/hash/inventory checks, pinned Kadmos TypeScript `parseWorldSpec` and installed `tsc` for local provenance, GitHub Linux CI using tracked artifacts.

**Spec:** `docs/superpowers/specs/2026-10-06-kadmos-ir-bridge-design.md`

## Global constraints

- Source Kadmos commit: `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`; Harmonia starting main: `b81df540439846b9df3cedc9ee0ca68380677b7b`.
- Keep `lean-toolchain` at `leanprover/lean4:v4.16.0`; product imports Init and the existing certified application/Foundation modules only.
- No new YAML/WorldSpec product fields, mathlib, Veil, package dependency, toolchain/Core/Distributed/legacy behavior edit, `sorry`, `admit`, `sorryAx`, custom axiom or `native_decide`.
- Preserve all original Lake targets, audits, manifests, rejection isolation and inventories. Add modules to exact application inventory; retain whitelist `[propext, Quot.sound, Classical.choice]`.
- One Lake process at a time. Compile Kadmos only to private tmp; do not change Kadmos files, lockfile, installed versions or package-manager state.
- Use no subagents; do not edit internal or Kadmos, push, open PR, or merge. Parent handles physical review and integration.

## Files and interfaces

| File | Responsibility |
| --- | --- |
| `Harmonia/Applications/Kadmos/Bridge/Syntax.lean` | Restricted source tokens/AST, total parser and independent evaluator. |
| `Harmonia/Applications/Kadmos/Bridge/Certificate.lean` | Raw parsed declarations, ordered binding, `lowerExpr`, complete `checkBridge`, soundness statements. |
| `Harmonia/Applications/Kadmos/Bridge/Fixtures.lean` | Tracked generated raw records/candidate Worlds and closed certificate witnesses. |
| `HarmoniaTests/KadmosBridgeSyntax.lean`, `KadmosBridgeCertificate.lean`, `KadmosBridgeFixtures.lean`, `KadmosBridgeAxiomAudit.lean`, `KadmosBridgeAuditRejection.lean` | Focused probes, source-bound examples, audit and isolated traps. |
| `conformance/kadmos-ir-bridge/{balance.world.yaml,order_phase.world.yaml,profiles.json,parsed.json,provenance.json}` | Source fixtures, adapter profile, pinned parsed output and hashes. |
| `tools/export_kadmos_ir_bridge.mjs` | Pure exporter CLI: pinned parsed JSON → Lean data and provenance metadata; local `--kadmos` mode calls actual parser. |
| `scripts/check_kadmos_bridge_artifacts.py`, `scripts/check_kadmos_bridge_audit.py`, `scripts/test_kadmos_bridge_audit.py` | Hash/byte reproducibility and exact new module/root inventory; leave prior checkers untouched. |
| `lakefile.lean`, `Harmonia/Applications/Kadmos.lean`, `HarmoniaTests/AuditPolicy.lean`, `.github/workflows/foundations.yml` | Additive imports/targets/manifest/serial CI steps. |

The `parsed.json` file is a deterministic map keyed by fixture ID; values are actual returned `WorldSpec` objects, not hand-authored Lean expressions. `provenance.json` records YAML/profile/parsed hashes and pinned commit. Do not include generated logs or private-tmp files in Git.

## Review focus

1. A context key named `state`, `event` or `request` must fail before binding; Task 2 probes each.
2. Swapping context or field order while retaining names must fail exact candidate/certificate comparison; Tasks 2 and 3 probe both.
3. A syntactically valid but unsupported expression, especially `!=`, unary minus or arbitrary strings, must fail with an explicit bridge error; Task 1 probes each.
4. A final-safe cancellation through an unsafe intermediate must fail certification/execution and never be described as generated JS equivalence; Tasks 1 and 3 probe `(S+1)-1`.
5. A changed YAML, parsed JSON or profile with unchanged recorded hashes must fail the artifact check in hermetic CI; Task 4 probes each.

---

### Task 1: Restricted source syntax and evaluator

**Files:** Create `Harmonia/Applications/Kadmos/Bridge/Syntax.lean`, `HarmoniaTests/KadmosBridgeSyntax.lean`. Add a temporary `kadmosBridgeSyntaxTest` root in `lakefile.lean`, retained in the final targets.

**Interfaces:** `inductive SourceExpr` with `int`, `bool`, `context String`, `field String`, `stateEq String`, `add/sub/eqInt/lt/le/gt/ge/and/or/implies`, `not`; `parseSourceExpr (s : String) : Except BridgeError SourceExpr`; `sourceEval (phase : String) (context fields : String → Int) (e : SourceExpr) : Except EvalError Value`; `sourceSafe (phase ... ) (e : SourceExpr) : Prop` denotes safety of every reached literal/read/arithmetic result. `BridgeError` distinguishes lexical, syntax, unsupported, unbound, duplicate, reserved, type, bounds and projection failures with declaration/effect indices.

- [ ] Write closed RED probes for `event.amount > 0`, `state == 'B' => y == x`, `(1 + 2) * 3` unsupported, unary `-1`, `!=`, `null`, arbitrary string, `event.a.b`, and trailing token. Pin `a => b => c` as `a => (b => c)`; prove `sourceSafe` fails for `false && (S+1 < 0)` and `true || (S+1 < 0)` although the left boolean fixes the truth value.
- [ ] Run `lake build kadmosBridgeSyntaxTest`; expect missing module/target failure. Implement a total character tokenizer and precedence-climbing parser with exact source precedence and full token consumption. Recognize only the spec grammar. Avoid using Kadmos `identifiers()` as a parser or silently normalizing source strings.
- [ ] Define `sourceEval` directly by recursion on `SourceExpr`, with name lookups and mathematical Int arithmetic; left and right subexpressions are evaluated before boolean combining or operand sort checks. `sourceSafe` is inductive over the same visits but is not defined by `lowerExpr` or Lean `eval`. Prove the basic eager/precedence lemmas by cases and `simp`; the cross-IR theorem belongs to Task 2.
- [ ] Run `lake build kadmosBridgeSyntaxTest` and `lake env lean HarmoniaTests/KadmosBridgeSyntax.lean`, serially. Expect explicit parser errors and source value/error pins. Commit only these files and the additive test root.

### Task 2: Complete checked projection and kernel transfer

**Files:** Create `Harmonia/Applications/Kadmos/Bridge/Certificate.lean`, `HarmoniaTests/KadmosBridgeCertificate.lean`; add their root/import to `lakefile.lean` and `Harmonia/Applications/Kadmos.lean`.

**Interfaces:**

```lean
structure RawWorld where
  version name : String
  states : List RawState
  context : List (String × RawVariable)
  invariants : List (String × String)
  transitions : List RawTransition
  fields : List String  -- ordered external adapter profile, not YAML
def lowerExpr (raw : RawWorld) (e : SourceExpr) : Except BridgeError (Expr raw.states.length raw.context.length raw.fields.length)
def projectWorld (raw : RawWorld) : Except BridgeError
  (World raw.states.length raw.context.length raw.fields.length raw.transitions.length)
def checkBridge (raw : RawWorld)
  (candidate : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
  Except BridgeError (World raw.states.length raw.context.length raw.fields.length raw.transitions.length)
```

The `Raw*` records hold source order/strings/flags/exact `Option` fields; `checkBridge` validates profile and all raw declarations, calls `projectWorld`, compares every field extensionally over finite indices (including ordered effect lists and invariant strings), then checks `initialize candidate = .ok initial` and returns the candidate. The proposed World is never accepted on hash alone. Implement decidable equality through finite `List.ofFn` field observations; do not assert function equality by `rfl`.

- [ ] Write RED probes for duplicate/empty/unbound/reserved names; missing bounds and string variable; event-dependent invariant; wrong field order; changed action name, phase target, guard, directive, effect order and repeated effect; unknown property; exact null/string directive. Each probe must reject the whole certificate, not merely fail a later runtime request.
- [ ] Run `lake build kadmosBridgeCertificateTest`; expect missing API failure. Implement list-index lookup to `Fin`, exact effect assignment parsing, static sort checks, all declaration validation, `projectWorld` and `checkBridge`. Resolve `event.x` and `request.x` through the identical profile index; no inferred field list or YAML modification.
- [ ] Prove `lowerExpr_sound`: for `lowerExpr raw e = .ok x`, corresponding ordered environments, and `sourceSafe ... e`, `sourceEval ... e = eval ... x` (including matching `Except` errors where the restricted evaluator checks sorts). Prove by induction on `e`; use `simp` on evaluator/bind, `omega` for safe add/sub, and explicit source/target phase environment hypotheses. Prove `checkBridge_exact`: `checkBridge raw candidate = .ok w` implies `w = candidate`, `projectWorld raw = .ok candidate`, and an initial state exists with `initialize candidate = .ok initial`; destructure checker branches and use `funext` for finite functions. These are nonvacuous statements about the actual checked projection, not a second transition relation.
- [ ] Run the certificate target and fresh `lake env lean HarmoniaTests/KadmosBridgeCertificate.lean` serially. Verify no `sorry`/native proof path; commit Task 2 files.

### Task 3: Actual parser artifacts and source-bound outcomes

**Files:** Create the five `conformance/kadmos-ir-bridge/` files, `tools/export_kadmos_ir_bridge.mjs`, `Harmonia/Applications/Kadmos/Bridge/Fixtures.lean`, `HarmoniaTests/KadmosBridgeFixtures.lean`; import fixtures in the bridge test/audit, not in Core or Distributed.

**Interfaces:** Exporter accepts `--kadmos /absolute/pinned/checkout --out /private/tmp/...` for physical regeneration, or `--from-parsed conformance/.../parsed.json --out ...` for hermetic artifact derivation. Output is deterministic raw Lean declarations and proposed Worlds with closed witnesses:

```lean
theorem balance_certificate : checkBridge balanceRaw balanceCandidate = .ok balanceCandidate
theorem order_certificate : checkBridge orderRaw orderCandidate = .ok orderCandidate
theorem balance_30 : interpret balanceCandidate balanceInitial (balanceRequest 30) =
  ⟨balanceState 70, ⟨.accepted, none⟩⟩
theorem balance_130 : interpret balanceCandidate balanceInitial (balanceRequest 130) =
  ⟨balanceInitial, ⟨.rejected (.bounds 0), none⟩⟩
```

Use exact names/types established in Task 2; `balanceInitial`, `balanceState`, `balanceRequest` are local fixture definitions and must refer to `balanceCandidate`, never T-393 `balanceWorld`. `balance_trace` is the 30/20/130 `Foundation.Execution` over `system balanceCandidate`; `order_step` is the whole `Result` B/(2,2) and reversed-effects rejection is the whole original state.

- [ ] Write the two YAML sources exactly as spec: balance is the recorded `/private/tmp/t395-balance.world.yaml` content; order has A/B, x/y, `state == 'B' => y == x`, and `x = x + 1; y = x`. Write `profiles.json` with ordered fields; inspect actual parser output in private tmp before committing `parsed.json`. Reject a mistaken fixture if `parseWorldSpec` fails; never hand-edit parsed JSON to make it pass.

  The order fixture body is:

  ```yaml
  version: "kadmos.world.v0"
  name: "OrderPhaseWorld"
  states:
    - id: A
      initial: true
    - id: B
  context:
    x:
      type: integer
      min: 0
      max: 9007199254740991
      default: 1
    y:
      type: integer
      min: 0
      max: 9007199254740991
      default: 0
  invariants:
    - id: phase_order
      predicate: "state == 'B' => y == x"
  transitions:
    - id: STEP
      from: A
      to: B
      guard: true
      directive: null
      effects:
        - "x = x + 1"
        - "y = x"
  ```
- [ ] Run RED `lake build kadmosBridgeFixturesTest`; expect missing fixtures. Compile the pinned checkout's needed TS sources to private tmp with its installed `tsc`, invoke `parseWorldSpec`, serialize deterministic JSON, and record physical command/commit/hash provenance. Export Lean raw/candidate records; implement the closed certificate witnesses with `decide`/`simp` only for finite concrete checks, and full Result proofs with `funext`, `Fin.ext`, `omega` as needed. No `native_decide`.
- [ ] Prove source-bound balance 30 accepted 70; 130 bounds rejection at original 100; 30/20/130 trace ending 50. Prove order STEP B/(2,2) and reversed-effects invariant rejection A/(1,0); include a name-swap mutation that fails `checkBridge`. Pin input null/string/fractional/unsafe and `(S+1)-1` failure; the bridge only claims formal requests with the declared safe profile.
- [ ] Run `lake build kadmosBridgeFixturesTest` and fresh Lean fixture file serially, plus exporter repeat/byte comparison. Commit fixture sources, parser output, hashes, exporter and Lean artifacts only. Source commit must be exactly pinned; no Kadmos tree modification.

### Task 4: Artifact, audit and Linux isolation

**Files:** Create `scripts/check_kadmos_bridge_artifacts.py`, `scripts/check_kadmos_bridge_audit.py`, `scripts/test_kadmos_bridge_audit.py`, `HarmoniaTests/KadmosBridgeAxiomAudit.lean`, `HarmoniaTests/KadmosBridgeAuditRejection.lean`; add exact roots to `lakefile.lean`, exact source manifest to `HarmoniaTests/AuditPolicy.lean`, and additive steps to `.github/workflows/foundations.yml`.

- [ ] Write RED policy tests that mutate each YAML/parsed/profile byte or hash, and add unused normal/unsafe/namespace-escaped axiom sources or a trap import in new certified roots. Tests must also show old Foundation/Distributed/Kadmos source and target inventories remain accepted. Run `python3 scripts/check_kadmos_bridge_audit.py --self-test`; expect failures of new assertions.
- [ ] Implement artifact checker with SHA-256 of exact bytes, pinned commit/version fields, deterministic parsed-JSON/Lean-export byte comparison from tracked inputs, and no sibling-repo assumption in CI. Implement new inventory by extending the old checker through composition: exact disk-to-manifest coverage for `Bridge` product/probes/audit modules, complete certified import closure, product Init/Application/Foundation dependency boundary, forbidden proof tokens, trap-free certified roots, and isolated rejection roots. Do not weaken or rewrite old scripts/manifests.
- [ ] Add `kadmosBridgeSyntaxTest`, `kadmosBridgeCertificateTest`, `kadmosBridgeFixturesTest`, `kadmosBridgeAudit`, `kadmosBridgeAuditRejection` roots and serial Linux steps. Audit every certified new module and generated fixture; retain the same three-axiom whitelist. Pin mutation tests for byte drift, unregistered module, unused axiom and certified-root trap.
- [ ] Run, one Lake process at a time: `lake build`; `lake build foundationsTest foundationsAudit foundationsAuditRejection`; `lake build distributedTest distributedAudit distributedAuditRejection`; `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection`; `lake build kadmosBridgeSyntaxTest kadmosBridgeCertificateTest kadmosBridgeFixturesTest kadmosBridgeAudit kadmosBridgeAuditRejection`; fresh `lake env lean` on all four audit roots and all rejection roots. Run old/new Python `--self-test` and inventories, artifact checker, `git diff --check`, and protected-tree diff. Record actual counts/axioms per separate audit environment and Linux status; do not assert hosted CI if it was not run. Commit only Task 4 files and the updated verification receipt.

## Execution and review handoff

After preflight ACCEPT, execute each task with RED/GREEN evidence and a focused commit. Review actual file/API names against this plan before coding; if Lean 4.16 makes a named proof method impossible, use an equivalent kernel proof and record the ruling, without weakening the theorem or changing source behavior. Three consecutive **completed-task** failures or a genuine domain conflict stop execution for parent decision. After all tasks, parent obtains independent physical Grok review and owns publication/integration. No claim that Stage3b proves generated TS/Python or the host's physical behavior.
