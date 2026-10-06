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
- Preserve all original Lake targets, audits, rejection isolation and inventories. Extend the existing literal `kadmosWorldSourceModules` manifest by the three Bridge product modules; retain whitelist `[propext, Quot.sound, Classical.choice]`. The old Kadmos 426/752 count is a baseline, not a post-change target.
- One Lake process at a time. Compile Kadmos only to private tmp; do not change Kadmos files, lockfile, installed versions or package-manager state.
- Use no subagents; do not edit internal or Kadmos, push, open PR, or merge. Parent handles physical review and integration.

## Files and interfaces

| File | Responsibility |
| --- | --- |
| `Harmonia/Applications/Kadmos/Bridge/Syntax.lean` | Restricted source tokens/AST, total parser and independent evaluator. |
| `Harmonia/Applications/Kadmos/Bridge/Certificate.lean` | Raw parsed declarations, ordered binding, `lowerExpr`, complete `checkBridge`, soundness statements. |
| `Harmonia/Applications/Kadmos/Bridge/Fixtures.lean` | Tracked generated raw records/candidate Worlds and closed certificate witnesses. |
| `HarmoniaTests/KadmosBridgeSyntax.lean`, `KadmosBridgeCertificate.lean`, `KadmosBridgeFixtures.lean`, `KadmosBridgeAxiomAudit.lean`, `KadmosBridgeAuditRejection.lean`, `KadmosBridgeRejection/Unused.lean`, `KadmosBridgeRejection/Unsafe.lean` | Focused probes, source-bound examples, audit and isolated normal/unsafe traps. |
| `conformance/kadmos-ir-bridge/{balance.world.yaml,order_phase.world.yaml,profiles.json,parsed.json,provenance.json,evaluate-vectors.json}` | Source fixtures, adapter profile, pinned parsed output/hashes and finite source-evaluator comparison vectors. |
| `tools/export_kadmos_ir_bridge.mjs` | Pure exporter CLI: pinned parsed JSON → Lean data and provenance metadata; local `--kadmos` mode calls actual parser. |
| `scripts/check_kadmos_bridge_artifacts.py`, `scripts/check_kadmos_bridge_audit.py`, `scripts/test_kadmos_bridge_audit.py` | Hash/byte reproducibility and exact new module/root inventory; leave prior checkers untouched. |
| `lakefile.lean`, `Harmonia/Applications/Kadmos.lean`, `HarmoniaTests/KadmosWorldAxiomAudit.lean`, `HarmoniaTests/AuditPolicy.lean`, `.github/workflows/foundations.yml` | Additive imports/targets, old-audit import, old and new literal manifests/selectors, serial CI steps. |

The `parsed.json` file is a deterministic map keyed by fixture ID; values are actual returned `WorldSpec` objects, not hand-authored Lean expressions. `provenance.json` records exact YAML/profile/parsed/vector hashes, pinned commit, exporter/checker versions and private-tmp parser command. `evaluate-vectors.json` retains expression/environment/observed Kadmos-evaluate result or error for supported/divergence examples. Unknown keys and wrong JSON types fail before any record is dropped or coerced. Do not include generated logs or private-tmp files in Git.

Use exact JSON top-level shapes: `profiles.json` is `{ "balance": ["amount"], "order_phase": [] }`; `parsed.json` is `{ "balance": <actual WorldSpec>, "order_phase": <actual WorldSpec> }`; `evaluate-vectors.json` is an array of `{ "id": string, "expression": string|boolean, "environment": object, "outcome": {"value": boolean|number}|{"error": string} }`. `provenance.json` has `kadmosCommit`, `exporterVersion`, `checkerVersion`, `yamlSha256` (object keyed by fixture), `profilesSha256`, `parsedSha256`, `evaluateVectorsSha256`, `fixturesLeanSha256` and `parserCommand`. Canonical JSON uses UTF-8, source enumeration order, `JSON.stringify` compact form and one final newline; hash those exact bytes. These are artifact formats, not additions to WorldSpec.

## Review focus

1. A context key named `state`, `event` or `request` must fail before binding; Task 2 probes each.
2. Swapping context or field order against the original raw record must fail candidate/certificate comparison; Task 2 uses a synthetic two-field raw profile, and Task 3 pins context order in the real order fixture. A consistently regenerated source can certify separately.
3. A syntactically valid but unsupported expression, especially `!=`, unary minus or arbitrary strings, must fail with an explicit bridge error; Task 1 probes each.
4. An individually unsafe literal `9007199254740992` fails static certification; a final-safe `(S+1)-1` using safe literal tokens can certify but its unsafe execution rejects. Tasks 1–3 pin both and make no generated JS equivalence claim.
5. A changed YAML, parsed JSON or profile with unchanged recorded hashes must fail the artifact check in hermetic CI; Task 4 probes each.

---

### Task 1: Restricted source syntax and evaluator

**Files:** Create `Harmonia/Applications/Kadmos/Bridge/Syntax.lean`, `HarmoniaTests/KadmosBridgeSyntax.lean`. Add `kadmosBridgeSyntaxTest` to `lakefile.lean`; add Syntax import to `Harmonia/Applications/Kadmos.lean` and `HarmoniaTests/KadmosWorldAxiomAudit.lean`, and its entry to `HarmoniaTests/AuditPolicy.lean`'s old literal `kadmosWorldSourceModules`. Extend that manifest incrementally as each later Bridge product file appears, so the old inventory remains green after every completed task.

**Interfaces:** Use these exact constructor and environment names; the repeated binary constructors each take `(l r : SourceExpr)`:

```lean
inductive FieldOrigin where | event | request
inductive SourceExpr where
  | int (n : Int) | bool (b : Bool)
  | context (id : String) | field (origin : FieldOrigin) (id : String)
  | stateEq (phaseId : String)
  | add (l r : SourceExpr) | sub (l r : SourceExpr)
  | eqInt (l r : SourceExpr) | lt (l r : SourceExpr) | le (l r : SourceExpr)
  | gt (l r : SourceExpr) | ge (l r : SourceExpr)
  | and (l r : SourceExpr) | or (l r : SourceExpr)
  | implies (l r : SourceExpr) | not (e : SourceExpr)
structure SourceEnv where
  phase : String
  context : String → Int
  fields : String → Int
inductive BridgeError where
  | lexical (offset : Nat) | syntax (offset : Nat)
  | unsupported (token : String) | unbound (id : String)
  | duplicate (id : String) | reserved (id : String)
  | wrongSort (role : String) | invalidBounds (id : String)
  | unsafeLiteral (value : Int) | invalidProfile (id : String)
  | unknownProperty (path : String) | malformedEffect (index : Nat)
  | malformedWorld (reason : SpecError) | projection
```

Public function and judgment types:

```text
parseSourceExpr : String → Except BridgeError SourceExpr
sourceEval : SourceEnv → SourceExpr → Except EvalError Value
sourceSafe : SourceEnv → SourceExpr → Prop
```

The parser accepts only spec-listed tokens/precedence and consumes all input; `sourceEval` may construct only `.expectedInt`/`.expectedBool`, never `.overflow`; `sourceSafe` is an inductive judgment whose constructors require `safeInt` at each int literal/context/field read, premises for **both** subtrees of every binary operator, and for add/sub a safe mathematical result whenever both subtree values are Int. `sourceSafe` does not refer to `lowerExpr` or Lean `eval` and cannot be replaced by a final-value test. Declaration errors use the offending ID and effect parse errors use declaration-order indices.

- [ ] Write RED probes as concrete closed propositions: `parseSourceExpr "event.amount > 0" = .ok (.gt (.field .event "amount") (.int 0))`; `parseSourceExpr "a => b => c" = .ok (.implies (.context "a") (.implies (.context "b") (.context "c")))`; `parseSourceExpr "(1+2)*3" = .error (.unsupported "*")`. Pin `state == 'B' => y == x`, unary `-1`, `!=`, `null`, arbitrary string, `event.a.b`, and trailing token with their exact errors. For expression trees with `S` and `1` safe literals, prove `¬ sourceSafe ρ (.and (.bool false) (.lt (.add (.int S) (.int 1)) (.int 0)))` and the analogous `or true` case; mathematical `sourceEval` returns `.ok (.bool false/true)`.
- [ ] Run `lake build kadmosBridgeSyntaxTest`; expect missing module/target failure. Implement a total tokenizer over `String.toList` with a decreasing remaining-character list. Implement precedence climbing as `parse minPrec fuel tokens`; start `fuel = tokens.length + 1`, consume a token on each recursive descent, and return a syntax error at zero fuel. Enforce `=>` right associativity, source precedence, exact consumed-token exhaustion, and source effect token spellings. Avoid Kadmos `identifiers()` as a parser.
- [ ] Define `sourceEval` by structural recursion, evaluating each child left then right before operand type checks/boolean combination; use unbounded Int. Implement the inductive safe judgment on the same eager visits. Prove by `cases`/`simp` the closed source values and absence of an overflow constructor, plus `sourceSafe` failure for `(S+1)-1`. The cross-IR theorem belongs to Task 2.
- [ ] Run `lake build kadmosBridgeSyntaxTest`, `lake env lean HarmoniaTests/KadmosBridgeSyntax.lean`, `python3 scripts/check_kadmos_world_audit.py`, and `lake build kadmosWorldAudit` serially; expect all closed probes and the incrementally extended old inventory green. Commit Task 1 files/imports/manifest entry.

### Task 2: Complete checked projection and kernel transfer

**Files:** Create `Harmonia/Applications/Kadmos/Bridge/Certificate.lean`, `HarmoniaTests/KadmosBridgeCertificate.lean`; add their root/import to `lakefile.lean`, `Harmonia/Applications/Kadmos.lean` and `HarmoniaTests/KadmosWorldAxiomAudit.lean`; add the Certificate entry to `HarmoniaTests/AuditPolicy.lean`'s old manifest.

**Interfaces:** Use these complete raw shapes (record field names may use Lean's `«type»` escape):

```lean
structure RawState where
  id : String
  initial : Bool
  terminal : Bool
  description : Option String
structure RawVariable where
  «type» : String
  min : Option Int
  max : Option Int
  default : Option Int
  unit : Option String
  description : Option String
structure RawInvariant where
  id : String
  predicate : String
  description : Option String
inductive RawGuard where | bool (b : Bool) | expr (s : String)
structure RawTransition where
  id : String
  «from» : String
  to : String
  guard : RawGuard
  effects : List String
  directive : Option String
structure RawWorld where
  version : String
  name : String
  description : Option String
  states : List RawState
  context : List (String × RawVariable)
  invariants : List RawInvariant
  transitions : List RawTransition
  fields : List String
  extras : List String  -- unknown parsed JSON property paths; must be []
def NamesWF (raw : RawWorld) (fieldNames : List String) : Prop :=
  (List.ofFn (fun j : Fin raw.states.length => raw.states[j].id)).Nodup ∧
  (raw.context.map Prod.fst).Nodup ∧ fieldNames.Nodup
def lowerExpr (raw : RawWorld) (fieldNames : List String) (e : SourceExpr) :
  Except BridgeError (Expr raw.states.length raw.context.length fieldNames.length)
def lowerGuard (raw : RawWorld) (g : RawGuard) :
  Except BridgeError (Expr raw.states.length raw.context.length raw.fields.length)
def lowerEffect (raw : RawWorld) (s : String) :
  Except BridgeError (Effect raw.states.length raw.context.length raw.fields.length)
def lowerInvariant (raw : RawWorld) (s : String) :
  Except BridgeError (Expr raw.states.length raw.context.length 0)
def projectWorld (raw : RawWorld) : Except BridgeError
  (World raw.states.length raw.context.length raw.fields.length raw.transitions.length)
def checkBridge (raw : RawWorld)
  (candidate : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
  Except BridgeError (World raw.states.length raw.context.length raw.fields.length raw.transitions.length)
```

`lowerExpr raw raw.fields` is used for guards/effects. `lowerInvariant` calls `lowerExpr raw []`; any `field` node is rejected and its result has exactly `Expr p v 0`, matching `World.invariants`. `inferSort : SourceExpr → Except BridgeError Sort` assigns Int to literals/context/fields/arithmetic and Bool to booleans/state equality/comparisons/logical operators. Guards and invariants must sort Bool; effect RHS Int. `lowerEffect` accepts exactly `<identifier> = <complete rhs>` with the source regex identifier spelling and whitespace around `=`, preserving order/repeated targets; compound assignments reject. Unknown JSON paths become `extras` and reject even if a malicious exporter omits a field in the proposed World; strict JSON schema/type checks at export/artifact time are a separate external gate. Descriptions/units are retained but inert. Optional bounds are preserved as options until validation, where missing min/max reject; missing default becomes zero only within bounds.

`projectWorld` checks `NamesWF raw raw.fields` before any name lookup; it rejects duplicate IDs rather than relying on `lowerExpr` to detect them. Prove `projectWorld_names_wf : projectWorld raw = .ok w → NamesWF raw raw.fields` by splitting that validation branch, and `checkBridge_names_wf : checkBridge raw candidate = .ok w → NamesWF raw raw.fields` by first obtaining projection success. The general lowering theorem has an explicit `NamesWF raw fieldNames` premise; for invariants `fieldNames = []`, obtain it from the certified `raw.fields` condition because `[].Nodup`. `checkBridge` also validates version/name, profile and all raw declarations, compares every candidate field with a computable equality, then requires `initialize candidate = .ok initial`. Define `exprEq : Expr p v f → Expr p v f → Bool` recursively; define `effectEq`, `transitionEq` and `worldEq` from exact constructors and `List.ofFn` observations of each `Fin` table. Prove `exprEq = true ↔ equality` by constructor induction, then `worldEq = true ↔ w₁ = w₂`: for the reverse direction use congruence; for the forward direction take `congrArg (fun xs => xs[j.val]?)` of an `ofFn` list equality and simplify to obtain each indexed component, then `funext` and `Fin.ext` for functions. Compare invariant IDs **and lowered Expr**, not raw whitespace. Do not edit `World.lean` to derive equality or claim function equality by `rfl`.

- [ ] Write RED closed probes: nonempty `extras` returns `.error .unknownProperty`; reserved `state`/`event`/`request`; duplicate and unbound ID; absent bound; `«type» := "string"`; event-dependent invariant; `state == 'B'` as Int effect RHS; reversed candidate effects; changed target/name/directive; `request.amount` alias; malformed `x += 1`/`x = 1 trailing`; null versus string directive. For duplicate phases `states := [A,A]`, show first-match `lowerExpr raw [] (.stateEq "A")` can succeed while `sourceEval` at index 1 says true and `eval (.stateIs 0)` says false; `NamesWF raw []` is false and `projectWorld`/`checkBridge` reject that raw record. Repeat duplicate context/field ID rejection. Use a synthetic raw profile `fields := ["amount", "fee"]` and a candidate with those two `fieldIds` swapped; expect `.error .projection` even though both names exist. A consistently reversed raw/candidate pair may certify and is tested for interpretation in Task 3.
- [ ] Run `lake build kadmosBridgeCertificateTest`; expect missing API failure. Implement `lookupName` by declaration-order `List.ofFn`/`Fin`, complete effect assignment parsing, `inferSort`, all raw validation, `projectWorld`, `worldEq` and `checkBridge`. Add only the new Certificate product import/manifest entry in this task. Do not add `KadmosBridge*` probes to the old manifest or change old Python checkers. The old application audit count rises as new Bridge modules arrive.
- [ ] Prove `names_injective`: for `(List.ofFn names).Nodup` and `names i = names j`, conclude `i = j` using `List.getElem?_inj` and `Fin.ext` (the pinned Init-only probe elaborates this method). Then prove `lowerExpr_sound` by induction on `e`, for arbitrary `fieldNames`, **`NamesWF raw fieldNames`**, `lowerExpr raw fieldNames e = .ok x`, `sourceSafe ρ e`, `ρ.phase = raw.states[q].id`, `∀ j : Fin raw.context.length, ρ.context (raw.context[j].1) = c j`, and `∀ j : Fin fieldNames.length, ρ.fields (fieldNames[j]) = i j`: `sourceEval ρ e = eval q c i x`. These relations bind exactly the indexed tables, not just the first matching string. `sourceSafe` supplies every checkedInt fact; follow Lean's left/right child and type-check order. Instantiate guard at source phase/pre-context, effect at target phase/candidate context, and invariant at published phase/context with `fieldNames = []`/`Fin.elim0` and the derived `NamesWF raw []`. `>`/`>=` use `.not (.le l r)` / `.not (.lt l r)` without swapping operands. Prove `projectWorld_names_wf`, `checkBridge_names_wf`, and `checkBridge_exact`: `.ok w` implies `w = candidate ∧ projectWorld raw = .ok candidate ∧ ∃ initial, initialize candidate = .ok initial`. No second transition relation.
- [ ] Run `lake build kadmosBridgeCertificateTest`, fresh `lake env lean HarmoniaTests/KadmosBridgeCertificate.lean`, old `python3 scripts/check_kadmos_world_audit.py` and `lake build kadmosWorldAudit` serially. Expect additive old inventory and larger application audit counts, with unchanged whitelist. Commit Task 2 files/manifest/import changes.

### Task 3: Actual parser artifacts and source-bound outcomes

**Files:** Create the six `conformance/kadmos-ir-bridge/` files, `tools/export_kadmos_ir_bridge.mjs`, `Harmonia/Applications/Kadmos/Bridge/Fixtures.lean`, `HarmoniaTests/KadmosBridgeFixtures.lean`; add Fixtures import to `Harmonia/Applications/Kadmos.lean` and `HarmoniaTests/KadmosWorldAxiomAudit.lean` and its old-manifest entry. The Bridge audit root arrives in Task 4. Never import fixtures into Core or Distributed.

**Interfaces:** Exporter accepts `--kadmos /Users/yong/projects/substratum/kadmos --out /private/tmp/t395-bridge-out` for physical regeneration, or `--from-parsed conformance/kadmos-ir-bridge/parsed.json --out /private/tmp/t395-bridge-out` for hermetic derivation. The physical checkout path is illustrative and is verified by commit before use; Linux needs only the second mode. Both modes read `profiles.json`; both perform the same strict JSON schema/type/unknown-key validation and same escaping before any Lean text is emitted. A third read-only `--check` mode compares generated bytes with tracked `Fixtures.lean`/`parsed.json`/provenance hashes and returns nonzero on drift. These are exporter modes, not a runtime request adapter. Output contains deterministic raw Lean declarations and proposed Worlds with closed witnesses:

```lean
theorem balance_certificate : checkBridge balanceRaw balanceCandidate = .ok balanceCandidate
theorem order_certificate : checkBridge orderRaw orderCandidate = .ok orderCandidate
theorem balance_30 : interpret balanceCandidate balanceInitial (balanceRequest 30) =
  ⟨balanceState 70, ⟨.accepted, none⟩⟩
theorem balance_130 : interpret balanceCandidate balanceInitial (balanceRequest 130) =
  ⟨balanceInitial, ⟨.rejected (.bounds 0), none⟩⟩
```

Place these names in `Harmonia.Applications.Kadmos.BridgeFixtures` to avoid T-393 name collision. `balanceRequest (n : Int) : Request 1` is `⟨"DEBIT", fun _ => .int n, none⟩`; `balanceState (n : Int) : State 1 1` is Ready/constant n; `balanceInitial` is the certified initialization witness at 100. `orderInitial : State 2 2` is A/(1,0); `orderRequest : Request 0` has action `STEP`, payload `Fin.elim0`, directive none. `balance_trace` is the 30/20/130 `Foundation.Execution` over `system balanceCandidate`; `order_step` is the whole `Result` B/(2,2). A separate consistently reversed raw/candidate pair can pass `checkBridge`, but its whole interpreted result is rejected with original A/(1,0). A reversed **candidate alone** fails `checkBridge orderRaw`.

- [ ] Write the two YAML sources exactly as spec: balance is the recorded `/private/tmp/t395-balance.world.yaml` content; order has A/B, x/y, `state == 'B' => y == x`, and `x = x + 1; y = x`. Write `profiles.json` with ordered fields; inspect actual parser output in private tmp before committing `parsed.json`. Reject a mistaken fixture if `parseWorldSpec` fails; never hand-edit parsed JSON to make it pass.

  The balance fixture body is:

  ```yaml
  version: "kadmos.world.v0"
  name: "BalanceWorld"
  states:
    - id: Ready
      initial: true
  context:
    balance:
      type: integer
      min: 0
      max: 9007199254740991
      default: 100
  invariants:
    - id: nonnegative
      predicate: "balance >= 0"
  transitions:
    - id: DEBIT
      from: Ready
      to: Ready
      guard: "event.amount > 0"
      directive: null
      effects:
        - "balance = balance - event.amount"
  ```

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
- [ ] Run RED `lake build kadmosBridgeFixturesTest`; expect missing fixtures. Compile pinned Kadmos TS source to private tmp using its installed `tsc`, invoke its `parseWorldSpec` and `evaluate`, and serialize deterministic JSON. The parent already observed a private-tmp fresh compile returning the same balance JSON as installed dist; rerun from pinned source for the tracked artifacts. Record command, commit, YAML hashes, parsed JSON hashes and finite evaluate vectors (normal balance/order, right-associative implication, eager booleans and unsafe cancellation). Compare each Kadmos evaluate result with `sourceEval` or record the safe-domain divergence explicitly; this is finite external evidence.
- [ ] Implement a `leanString(s)` encoder that escapes `"`, `\\`, newline, tab and carriage return; emits printable Unicode as UTF-8; rejects other control code points and unpaired surrogates. Never interpolate raw source text as Lean code. Before export, validate each JSON object against the exact `Raw*` allowed-key/type schema, collect `extras` paths and fail on any nonempty list; reject fractional/unsafe/negative zero numeric encodings rather than coerce to `Int`. Add exporter RED/GREEN cases for `id: "\"; axiom forged : False"`, backslash, newline, non-ASCII, unknown key, wrong-type guard/directive/bound, and duplicate profile key. Check that emitted strings reparse as data and no axiom declaration is introduced. Export raw/candidate records; prove closed certificate witnesses with `decide`/`simp` for finite checker computations, and full Result equalities with `funext`/`Fin.ext`/`omega`, never `native_decide`.
- [ ] Prove `balance_30`, `balance_130`, and the 30/20/130 trace using the actual lowered guard `.not (.le (.request 0) (.int 0))`, not handwritten T-393 `balanceWorld` or its `.lt (.int 0) (.request 0)` lemma. Prove order STEP B/(2,2), original-raw/reversed-candidate certificate rejection, consistently reversed-world invariant rejection A/(1,0), and name-swap/phase-target drift rejection. For `Fin 2 → Int` context equality, split `j=0` versus `j=1` and use `Fin.ext`/`omega`; a private-tmp Lean 4.16 probe elaborated this method. Pin formal `Request` payload tags `.missing`, `.null`, `.bool`, `.string`, `.invalidNumber`, unsafe `.int`; do not call these host-object checks. Pin static rejection of literal `9007199254740992`, plus mathematical `.ok`/`¬sourceSafe`/Lean `.overflow` divergences for safe-token `S+1` in both eager booleans and `(S+1)-1`. The latter expression may certify structurally but rejects on execution.
- [ ] Run `lake build kadmosBridgeFixturesTest` and fresh Lean fixture file serially, plus exporter `--check`/byte comparison and vector tests. Commit fixture sources, actual parser output, hashes/vectors, exporter and Lean artifacts only. Source commit must be exactly pinned; no Kadmos tree modification.

### Task 4: Artifact, audit and Linux isolation

**Files:** Create `scripts/check_kadmos_bridge_artifacts.py`, `scripts/check_kadmos_bridge_audit.py`, `scripts/test_kadmos_bridge_audit.py`, `HarmoniaTests/KadmosBridgeAxiomAudit.lean`, `HarmoniaTests/KadmosBridgeAuditRejection.lean`, `HarmoniaTests/KadmosBridgeRejection/Unused.lean`, `HarmoniaTests/KadmosBridgeRejection/Unsafe.lean`; add exact roots to `lakefile.lean`, a separate Bridge source manifest/selector to `HarmoniaTests/AuditPolicy.lean`, and additive steps to `.github/workflows/foundations.yml`.

- [ ] Write RED policy tests in `scripts/test_kadmos_bridge_audit.py`: mutate one byte in each YAML, parsed JSON, profile, evaluate-vectors JSON, generated Lean file or recorded digest and expect artifact rejection; insert unused normal/unsafe/namespace-escaped axioms in a new Bridge product/probe source or indirectly imported module, and expect new audit/inventory rejection; add trap import to each certified Bridge root and expect rejection; keep isolated rejection roots accepted. Run `python3 scripts/check_kadmos_bridge_audit.py --self-test`; old checker need not know `KadmosBridge*` tests, so these tests explicitly own their coverage.
- [ ] Implement `check_kadmos_bridge_artifacts.py`: strict JSON parse (duplicate keys rejected), exact allowed-key/type tables matching `Raw*` including optional/null fields, profile key validation, exact byte SHA-256/version/pinned commit checks, deterministic regeneration of `Fixtures.lean` from tracked parsed JSON, and comparison of stored evaluate-vector bytes. Reject before losing unknown keys or wrong numeric types. Linux mode uses tracked parser output and no sibling repo; physical `--kadmos` regeneration remains the separately recorded source check. Unit tests pin Lean-string injection, malformed Unicode/control, fractional/unsafe JSON numbers, unknown key and changed hash.
- [ ] Extend `HarmoniaTests/AuditPolicy.lean` with literal `kadmosBridgeSourceModules : Array Name` consisting of exactly `Bridge/Syntax`, `Bridge/Certificate`, `Bridge/Fixtures`, the three `KadmosBridge*` certified probe modules and `KadmosBridgeAxiomAudit`. Define `kadmosBridgeDeclaration env n := bridgeNamespace.isPrefixOf n || bridgeNamespace.isPrefixOf (sourceModule env n) || kadmosBridgeSourceModules.contains (sourceModule env n)` with `bridgeNamespace = Harmonia.Applications.Kadmos.Bridge`; this covers escaped names from Bridge sources and does not select the whole old Application prefix. `KadmosBridgeAxiomAudit.lean` imports all these certified sources and invokes `auditSelected` with the existing whitelist. Create unused normal/unsafe and indirect custom-axiom rejection fixtures under `KadmosBridgeRejection/`; they are isolated and absent from the certified manifest.
- [ ] Implement `check_kadmos_bridge_audit.py` by first calling the unchanged old `check_kadmos_world_audit.check`, then require exact disk/manifest equality for all `Harmonia/Applications/Kadmos/Bridge/**/*.lean` and `HarmoniaTests/KadmosBridge*.lean` certified sources (excluding named rejection fixtures); exact import coverage of new audit and certified test roots; no unregistered or imported trap; forbidden proof tokens in every certified new source; source/namespace-escaped unused axiom detection and indirect dependency checks. Its own target-root inventory includes the three test targets plus `kadmosBridgeAudit` and isolated `kadmosBridgeAuditRejection`; old checker continues to own all old roots. Mutations must prove an unregistered nested Bridge source, escaped unused axiom, and indirect custom axiom cannot pass.
- [ ] Add `kadmosBridgeAudit` and `kadmosBridgeAuditRejection` Lake roots after the three prior task test roots, then append serial artifact/inventory/test/audit/rejection steps to `.github/workflows/foundations.yml`. Run one Lake process at a time: `lake build`; `lake build foundationsTest foundationsAudit foundationsAuditRejection`; `lake build distributedTest distributedAudit distributedAuditRejection`; `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection`; `lake build kadmosBridgeSyntaxTest kadmosBridgeCertificateTest kadmosBridgeFixturesTest kadmosBridgeAudit kadmosBridgeAuditRejection`; fresh `lake env lean` on Foundation, Distributed, KadmosWorld and KadmosBridge audit roots and all rejection roots. Run old/new Python `--self-test` and inventories, artifact checker, `git diff --check`, and protected-tree diff. Record actual counts/axioms per separate environment; Foundation52 and Distributed336/594 should remain separate, while old Kadmos counts grow. Do not claim hosted Linux CI unless run. Commit Task 4 files and the updated receipt.

## Execution and review handoff

After preflight ACCEPT, execute each task with RED/GREEN evidence and a focused commit. Review actual file/API names against this plan before coding; if Lean 4.16 makes a named proof method impossible, use an equivalent kernel proof and record the ruling, without weakening the theorem or changing source behavior. Three consecutive **completed-task** failures or a genuine domain conflict stop execution for parent decision. After all tasks, parent obtains independent physical Grok review and owns publication/integration. No claim that Stage3b proves generated TS/Python or the host's physical behavior.
