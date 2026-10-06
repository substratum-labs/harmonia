# T-396 Generated Implementation Correspondence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans task by task. Native physical CLI execution is selected; no virtual subagents. Actual physical Grok R1 completed exit 0 in 873.2 s and returned REVISE. This is the R1 design correction for parent-owned R2; product/test/CI work starts only after R2 ACCEPT.

**Goal:** Kernel-check a dynamic DEBIT step correspondence for the actual pinned TS and Python balance checkers, plus constructor/getter correspondence for balance and order.

**Architecture:** Deterministically export actual Kadmos outputs. Lean checks full emitted source strings, parses the constructor/getters and selected balance `step` call graph (including reached helper bodies) into a small target-language AST, and executes that AST with independent operational semantics. A dependent certificate binds the actual emitted JSON normal form to Stage3b's checked `World`; universal `b,n` lemmas establish target/model observations. Actual Node/CPython primitive semantics and source-string serialization remain explicit external boundaries.

**Tech Stack:** Lean 4.16.0/Init/Lake, pinned Kadmos TypeScript compiler, Node and Python physical probes, existing Python inventory policy, serial hosted Linux CI.

**Spec:** `docs/superpowers/specs/2026-10-06-generated-implementation-correspondence-design.md`

## Global Constraints

- Keep `lean-toolchain` exactly `leanprover/lean4:v4.16.0`; use Init only, no new dependencies, no `native_decide`, `sorry`, `admit`, `sorryAx` or certified custom axioms.
- Preserve Core, Distributed, legacy, World, Interpreter and Bridge semantics. Do not edit Kadmos or another repository.
- Use clean read-only Kadmos `fda8c6e42825b35afe5484a4af9d84d9d206ba9a` for local provenance; hosted Linux consumes tracked outputs without a sibling checkout.
- Every Lake process runs serially. No generated binary, `.lake/`, cache, credential or machine log is staged.
- T-396 is incomplete without universal dynamic generated `step` correspondence in **both** languages for the specified balance domain: one call from `Ready`, `0≤b≤S`, safe `n`, empty history, no undo, not busy, typed canonical request. Arbitrary history/multicall induction is deferred. Constructor/getter proof and physical traces alone cannot complete it.
- Target operations execute a parsed AST with mutable capture cells, explicit control exits, object heap metadata and module initialization; no reference `interpret`/`eval`/`sourceEval` call, no `targetResult = modelResult` premise, and no atomic helper macro named `evaluateWorld`, `sanitizeWorldPayload`, `checkBounds` or `checkInvariants`.
- Old Kadmos inventory scans all Applications. Register new modules there; isolate new Generated audit/rejection roots. Keep Foundation 52 and Distributed 336/594 separate; no fixed old application/Bridge counts.

## Review Focus

1. Shared TS `index` and Python `position` closure cells must change in recursive `parse`; copied captures make all positive DEBITs fail the trailing-token check (Task 2–3).
2. `return` inside bounds/invariant/effect loops must exit the function; `switch` `break` in evaluator must exit only the switch; the fourth tracked expression in order's constructor catches this (Task 2–3).
3. Default arguments and fresh `new Set()` at call time, Python definition-time defaults, TS `undefined` and omitted arguments, module globals/class fields, Python `_freeze`/`reset`/getter aliases must execute (Task 2–3).
4. Canonical descriptor/prototype/frozen/set identity, Python `.pyInt→.pyFloat→.pyInt` tag flow, lazy `&&/||/??/?:`, exact emitted JSON omissions and guard booleans must be preserved (Tasks 1–3).
5. One-call logical rejection frame and success undo/history shape, busy false after `finally`, fresh getter copy heap reference, exact dependent Bridge dimensions and all-`b,n` symbolic proof must be checked (Tasks 3–5).

---

## File map and binding interfaces

- `tools/export_kadmos_generated.mjs`; `conformance/kadmos-generated/{balance,order_phase}/{world_checker.ts,ports.d.ts,world_checker.py,ports.py}`; `conformance/kadmos-generated/provenance.json`; `scripts/check_kadmos_generated_artifacts.py`, `scripts/test_kadmos_generated_artifacts.py`: exact source bytes and Lean literal round trip.
- `Harmonia/Applications/Kadmos/Generated/TargetSyntax.lean`: neutral ordered `JSONValue`, TS/Python lexical tokens, `SourceParses`, `TargetExpr`/`TargetOp`/`TargetFunction`/`TargetProgram`, parser and desugaring proof.
- `Harmonia/Applications/Kadmos/Generated/TargetMachine.lean`: object/cell heap, descriptors, closures, frames, module globals, `ControlResult`, request allocation and primitive contracts.
- `Harmonia/Applications/Kadmos/Generated/TargetSemantics.lean`: expression and statement execution, call/default/closure semantics, constructor/getters/step and helper-path lemmas.
- `Harmonia/Applications/Kadmos/Generated/ArtifactCertificate.lean`: emitted-world normal form, dependent Bridge certificate, generic constructor/getter theorem.
- `Harmonia/Applications/Kadmos/Generated/Fixtures.lean`: complete emitted string literals `balanceTsSource`, `balancePySource`, `orderTsSource`, `orderPySource : String` and closed certificates.
- `Harmonia/Applications/Kadmos/Generated/BalanceStep.lean`: names `generatedBalanceState`, `generatedBalanceRequest`, one-call `balancePreRel`, model/target three-way lemmas and universal theorem.
- `HarmoniaTests/KadmosGeneratedSyntax.lean`, `KadmosGeneratedMachine.lean`, `KadmosGeneratedConstructor.lean`, `KadmosGeneratedStep.lean`, `KadmosGeneratedAxiomAudit.lean`, `KadmosGeneratedAuditRejection.lean`, `KadmosGeneratedRejection/{Unused,Unsafe}.lean`: certified probes and isolated adversarial roots.
- `scripts/check_kadmos_generated_audit.py`, `scripts/test_kadmos_generated_audit.py`, `lakefile.lean`, `HarmoniaTests/AuditPolicy.lean`, `.github/workflows/foundations.yml`, verification receipt: exact source/target/CI inventory. `Harmonia/Applications/Kadmos.lean` changes only if real import closure requires it.

```lean
def parseGenerated (lang : TargetLang) (source : String) : Except ParseError TargetProgram
inductive SourceParses : TargetLang → String → TargetProgram → Prop
inductive SurfaceStmt
  | jsFind (array : TargetExpr) (predicate : String) (result : String)
  | jsSome (array : TargetExpr) (predicate : String) (result : String)
  | jsMap (array : TargetExpr) (mapper : String) (result : String)
  | pythonNext (values : TargetExpr) (predicate : String)
      (fallback : TargetExpr) (result : String)
  | switchStmt (scrutinee : TargetExpr)
      (arms : List (TargetValue × List TargetOp))
inductive SurfaceExec : TargetLang → SurfaceStmt → TargetMachine →
    TargetMachine → ControlResult → Prop
def desugar (s : SurfaceStmt) : List TargetOp
inductive TargetExec : List TargetOp → TargetMachine →
    TargetMachine → ControlResult → Prop
theorem desugar_preserves {lang s before after exit}
    (h : SurfaceExec lang s before after exit) :
    TargetExec (desugar s) before after exit
theorem parseGenerated_sound {lang source program}
    (h : parseGenerated lang source = .ok program) : SourceParses lang source program
theorem SourceParses.unique {lang source p q}
    (hp : SourceParses lang source p) (hq : SourceParses lang source q) : p = q
def evalExpr (p : TargetProgram) (m : TargetMachine) (e : TargetExpr) :
    Except TargetError (TargetMachine × TargetValue)
def execOps (p : TargetProgram) (m : TargetMachine) (ops : List TargetOp) :
    Except TargetError (TargetMachine × ControlResult)
def installRequest (m : TargetMachine) (r : TargetRequest) : TargetMachine × TargetValue
def targetConstruct (p : TargetProgram) : Except TargetError TargetMachine
def targetGetState (p : TargetProgram) (m : TargetMachine) :
    Except TargetError (TargetMachine × TargetValue)
def targetGetContext (p : TargetProgram) (m : TargetMachine) :
    Except TargetError (TargetMachine × TargetValue)
def targetStep (p : TargetProgram) (m : TargetMachine) (r : TargetRequest) :
    Except TargetError TargetResult
def emittedWorldData (raw : Bridge.RawWorld) : Except CertError JSONValue
def checkGenerated (lang : TargetLang) (source : String) (raw : Bridge.RawWorld)
    (w : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
    Except CertError TargetProgram
```

The spec's schemas are binding: `TargetValue` uses heap references; `TargetMachine` includes global/cell/object heaps, stack, checker and fuel; `TargetRequest` is an allocation recipe; getters return the updated heap; `ControlResult` has normal/returned/targeted break/continue/raised; `TargetFunction` carries lexical qualified name and `ParamSpec` defaults. Do not reintroduce the deleted value-snapshot capture or list-only object interfaces. `SourceParses` is independent of `parseGenerated` and unique for a source after deterministic lexical-ID normalization; desugaring has its own control/effect preservation lemma.

## Task 1: Exact source and emitted-world provenance

**Files:** exporter, tracked artifacts, provenance, Python artifact checker/tests, verification receipt.

**Inputs/outputs:** consume actual pinned `parseWorldSpec`, `compileWorldSpec`, `compileWorldSpecPython`; produce complete source bytes and neutral ordered JSON literals. Exporter never emits a decoded `TargetProgram` or certificate.

- [ ] **RED:** Mutate each generated file, recompute manifest digest, then prove byte comparison still rejects; test TS embedded `states:[{"id":"B"}]` omission, Python JSON double quoting, `directive:null`, order `guard:true`, context object key order, absence of `fields`/`extras`/`terminal:false`, numeric `-0` and duplicate keys. Run `python3 scripts/check_kadmos_generated_artifacts.py --self-test`; initially fails.
- [ ] **GREEN:** Compile read-only pinned Kadmos source in private tmp, invoke both actual compilers on Stage3b parser results and compare full bytes. Implement Lean-literal escaping round trip; neutral `JSONValue` parser consumes actual TS literal and Python **normal string** argument to `json.loads`, separately from raw regex literal decoding. `emittedWorldData raw` is only the two fixture normal forms; reject unsupported presence patterns instead of reconstructing arbitrary WorldSpec from RawWorld.
- [ ] Run physical and hermetic check modes, then emit/execute unchanged balance boundary vectors `(0,0),(0,1),(100,-1),(100,30),(100,130),(S,S),(S,-S)` and order STEP. Record exit codes and source hashes without treating vectors as proof. Commit Task 1 paths only.

## Task 2: Source parser, cells/control and constructor/getter task

**Files:** `TargetSyntax.lean`, `TargetMachine.lean`, `TargetSemantics.lean`, `Fixtures.lean`, `HarmoniaTests/KadmosGeneratedSyntax.lean`, `KadmosGeneratedMachine.lean`, `KadmosGeneratedConstructor.lean`; add test roots `kadmosGeneratedSyntaxTest`, `kadmosGeneratedMachineTest`, `kadmosGeneratedConstructorTest`.

**Interfaces:** exact declarations above. Parser consumes TS annotations/generics/import aliases/class fields and Python imports/nonlocal/f-strings/raw regex, separates lexical syntax from runtime effects, and creates deterministic lexical qualified names. `SourceParses` has independent token-span/statement-order/call-target constructors; `SurfaceExec` independently specifies sugar behavior; prove soundness and uniqueness plus `desugar_preserves` meaning preservation for `.find/.some/.map`, `next`/generator/list comprehensions and switch desugaring.

- [ ] **RED syntax:** Closed `by decide +kernel` probes: `(parseGenerated .ts balanceTsSource).toOption.isSome = true`, Python likewise, order likewise; mutate `index++`, `nonlocal position`, `switch break`, `#context` field initializer, `_DEFAULTS` default mapping, TS value import alias, Python raw `_TOKEN`, and getter call target; each changed source must reject. Add source relation uniqueness/alpha-normalization probe. Run `lake build kadmosGeneratedSyntaxTest`; expect failure before implementation.
- [ ] **GREEN syntax:** Implement lexers and syntax-directed parser; `SourceParses` independent of parser code; track all selected helper bodies and module/class init. `regexMatch` result has full/span/groups; `_EFFECT` yields `(balance, balance - event.amount)`, own descriptor exposes value/get/set. Implement explicit lazy logical/coalesce/conditional syntax. Parse TS and Python calls with arity/default definitions (JS default on omitted or undefined with new Set each call; Python default at definition). No opaque selected call, ideal helper macro or generic unchecked callback.
- [ ] **RED/GREEN machine:** Use private-tmp Lean declaration sketches if needed, then formalize mutable cell captures. Add a recursive parser-scope probe where inner updates shared TS `index`/Python `position` and outer trailing check observes final length, while separate invocations receive fresh local/param cells. Add `ControlResult` probes: bounds-loop `return key` exits function, effect loop return exits step, evaluator switch break stays in Pratt while; `tryCatchFinally` evaluates return value then clears busy. Require changed cell/switch/finally semantics to make a test fail; restore.
- [ ] **Constructor/getters:** Execute module globals, TS class fields before ctor, Python `_freeze`/`next`/`_DEFAULTS`/`reset`, and order's **fourth** expression `state == 'B' => y == x` through the parsed evaluator with quote `slice`/`replace`, string equality, eager implication and actual `booleanWorld`/`_boolean` helpers. Prove token paths for all four expressions, TS `match/join/replace` and Python `_TOKEN` separately. Getters return `(updatedMachine, value)` and a fresh context ref that does not alias checker context. Closed Ready/100 and A/(1,0) witnesses pass; commit Task 2 only after source/AST/call coverage review.

## Task 3: Independent balance step execution

**Files:** extend `TargetMachine.lean`, `TargetSemantics.lean`, `HarmoniaTests/KadmosGeneratedMachine.lean`; add `kadmosGeneratedSemanticsTest` root.

**Inputs/outputs:** execute actual parsed `step`, evaluator, sanitizer, bounds, invariants, TS `deepFreezeWorld`, Python `_freeze`, and reached property wrappers using `TargetMachine`; output `TargetResult` with heap and observation. No reference model call.

- [ ] **RED:** Pin the actual parsed TS closure/control path with a closed test (repeat for `.python`, `0` and `130`; the universal theorem still comes in Task 4):

```lean
private def closedTsDebit30Allowed : Bool :=
  match parseGenerated .ts balanceTsSource with
  | .error _ => false
  | .ok p =>
    match targetConstruct p with
    | .error _ => false
    | .ok m =>
      match targetStep p m (canonicalBalanceRequest .ts 30) with
      | .error _ => false
      | .ok r => r.observation.allowed
example : closedTsDebit30Allowed = true := by decide +kernel
```

  Parse/execute selected helpers for canonical DEBIT with `b,n` boundary vectors. Mutate `>`→`>=`, `-`→`+`, `&&`/`??` branch, sanitizer descriptor/prototype check, Python int→float sanitizer conversion, bound comparison, invariant call, acceptance freeze/push, rollback clone, `finally busy=false`; expect parser rejection or diagnosed execution change. Include exact call probes for `parse()`/`parse(8)`, `sanitizeWorldPayload(raw)` with fresh `seen`, TS `checkInvariants(state,values)` and `(state,values,payload)`, Python `_invariant` with two/three arguments, and regex group shape.
- [ ] **GREEN primitives:** Define exact contracts for property/index/descriptor/prototype/frozen/set identity, restricted regexp/token match, string/number operations, `structuredClone` and `copy.deepcopy` on the canonical finite tree, and tagged Python numeric conversions. Model module globals and builtins through qualified alias bindings; `_freeze` and generated helpers execute parsed statements. `forDo` propagates function return; switch break is targeted; `tryCatchFinally` propagates saved return/exception after finalizer.
- [ ] **GREEN symbolic path:** Prove sanitizer allocates a copied TS `.jsNumber n` or Python `.pyFloat n`; recursive evaluator reads shared position cell and yields guard `n>0`, effect `b-n`, invariant `b-n≥0`; bounds returns first failed `balance` before invariant; rejected paths logically frame state/context/history/undo and end busy false; TS rejection still executes cloned/frozen trace construction before projection; accepted TS stores pre-call undo and frozen one-record history, Python stores one record with `.pyFloat n` and no undo. `omega` proves `0≤b≤S ∧ safeInt n ∧ n>0 → safeInt (b-n)`. Run `lake build kadmosGeneratedMachineTest kadmosGeneratedSemanticsTest`; mutation-disable the core cell/control rule to establish RED, then restore. Commit only if no reached helper/primitive is unsupported.

## Task 4: Dependent certificate and universal one-call theorem

**Files:** `ArtifactCertificate.lean`, `BalanceStep.lean`, `HarmoniaTests/KadmosGeneratedStep.lean`; update `Fixtures.lean` and constructor tests; add `kadmosGeneratedStepTest` root.

**Inputs/outputs:** `checkGenerated` has exactly the raw-dependent World dimensions above and checks Bridge projection plus fixture-normal-form emitted JSON, source relation and selected call graph; `BalanceStep` proves symbolic three-way target/model correspondence.

- [ ] **RED certificate:** Closed actual-source facts:

```lean
example : (checkGenerated .ts balanceTsSource balanceRaw balanceCandidate).toOption.isSome = true := by decide +kernel
example : (checkGenerated .python balancePySource balanceRaw balanceCandidate).toOption.isSome = true := by decide +kernel
example : (checkGenerated .ts
  (balanceTsSource.replace "balance - event.amount" "balance + event.amount")
  balanceRaw balanceCandidate).toOption.isSome = false := by decide +kernel
```

  Add a closed negative check against old `Balance.balanceWorld` (different guard/invariant AST), plus guard/bounds/sanitizer/publish/module-init/JSON-presence mutations with recomputed hashes; set BridgeFixture-style heartbeats for large closed decisions. Run `lake build kadmosGeneratedStepTest`; observe RED before checker.
- [ ] **GREEN certificate:** Implement `emittedWorldData` for the exact two fixture profiles and `checkGenerated` with dependent `checkBridge raw w`; the order profile has `step=none`, balance has `step=some`. Prove parser soundness/desugaring obligations, not an assumed decoder premise. Mutated helper bodies or control order fail certification independent of digest.
- [ ] **GREEN symbolic theorem:** Define `generatedBalanceState/Request` to avoid old Balance names, `balancePreRel lang b m` with empty history/undo and adequate **fixed one-call** fuel, plus `balancePreRel_exists` for every bounded b. Prove the three `interpret balanceCandidate` cases directly from `Interpreter.lean` (never `balanceWorld`); prove all three target cases through parsed AST. Establish normalized allow/current state/structural context/directive, code, busy false and logical frame or accepted history shape as specified in design for both actual languages. `decide +kernel` only closes source/certificate facts; universal b/n proof uses symbolic reductions/induction/omega.
- [ ] Run `lake build kadmosGeneratedConstructorTest kadmosGeneratedStepTest`; intentionally weaken a source validator and confirm a hostile mutation or theorem turns RED, then restore. Review every premise for result equality, copied capture, arbitrary-history leakage, missing helper, circularity or vacuity. Commit Task 4 only if both languages have actual-source certificates and universal theorem.

## Task 5: Audit isolation, policy, Linux and acceptance receipt

**Files:** Generated audit/rejection Lean roots, `scripts/check_kadmos_generated_audit.py`, `scripts/test_kadmos_generated_audit.py`, `HarmoniaTests/AuditPolicy.lean`, `lakefile.lean`, `.github/workflows/foundations.yml`, verification receipt; old Applications manifest/umbrella only for genuine closure.

**Targets:** `kadmosGeneratedSyntaxTest`, `kadmosGeneratedMachineTest`, `kadmosGeneratedConstructorTest`, `kadmosGeneratedSemanticsTest`, `kadmosGeneratedStepTest`, `kadmosGeneratedAudit`, `kadmosGeneratedAuditRejection`. Audit exact Generated product/probe/audit modules by namespace **or source module**, with isolated rejection roots. Old Kadmos inventory scans all Applications; Bridge closure expands only if actual imports require it.

- [ ] **RED/GREEN policy:** Test nested unregistered source/probe/trap, missing import/root, escaped unused axiom, custom-axiom indirect import, trap in certified closure, and blanket Applications selector; then register exact manifest/roots and make new/old inventory checks pass. Do not weaken Foundation/Distributed policies or assert fixed old totals.
- [ ] Add serial hosted Linux steps after Bridge for hermetic artifacts, inventory self-test/check, five tests, certified/fresh axiom audit and isolated rejection. No sibling Kadmos checkout required in CI; local pinned-source regeneration remains mandatory.
- [ ] Serial local acceptance: `lake build`, all 14 existing dedicated targets and seven new targets, new/old inventories, artifact self-test and physical/hermetic bytes check, boundary/mutation probes, fresh audits where closure changed. Record exact commands, exit codes, axiom sets/counts, symbolic theorem statement, host primitive/serializer assumptions, and excluded arbitrary history/host objects. Keep binaries/logs unstaged.
- [ ] Self-review actual selected call graph, object/cell/control coverage, `SourceParses` uniqueness, constructor/getter allocation, and three-way proof premises. Parent owns independent physical R2/final review, hosted Linux observation, publication and integration. No push/PR/merge by this owner.

## Handoff and stop condition

R1's route-2 verdict is REVISE, not permission to implement. The corrected plan requires real source-statement execution, not an idealized macro, and only one call from empty history/undo. If any selected helper or primitive remains unsupported, report the exact source construct and architecture options to the parent; constructor-only or finite-vector work cannot complete T-396. Parent sends the corrected full design for physical R2 and independently judges its verdict before product work.
