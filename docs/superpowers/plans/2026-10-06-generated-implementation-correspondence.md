# T-396 Generated Implementation Correspondence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans task by task. Native physical CLI execution is selected; no virtual subagents. Product/test/CI work starts only after the parent's actual physical Grok preflight ACCEPT. This plan corrects the parent-reviewed `e253b77` constructor-only scope; that review was not a Grok REVISE.

**Goal:** Kernel-check a dynamic DEBIT step correspondence for the actual pinned TS and Python balance checkers, plus constructor/getter correspondence for balance and order.

**Architecture:** Deterministically export actual Kadmos outputs. Lean checks full emitted source strings, parses the constructor/getters and selected balance `step` call graph (including reached helper bodies) into a small target-language AST, and executes that AST with independent operational semantics. A dependent certificate binds it to Stage3b's checked `World`; universal `b,n` lemmas establish target/model observations. Actual Node/CPython primitive semantics and source-string serialization remain explicit external boundaries.

**Tech Stack:** Lean 4.16.0/Init/Lake, pinned Kadmos TypeScript compiler, Node and Python physical probes, existing Python inventory policy, serial hosted Linux CI.

**Spec:** `docs/superpowers/specs/2026-10-06-generated-implementation-correspondence-design.md`

## Global Constraints

- Keep `lean-toolchain` exactly `leanprover/lean4:v4.16.0`; use Init only, no new dependencies, no `native_decide`, `sorry`, `admit`, `sorryAx` or certified custom axioms.
- Preserve Core, Distributed, legacy, World, Interpreter and Bridge semantics. Do not edit Kadmos or another repository.
- Use clean read-only Kadmos `fda8c6e42825b35afe5484a4af9d84d9d206ba9a` for local provenance; hosted Linux consumes tracked outputs without a sibling checkout.
- Every Lake process runs serially. No generated binary, `.lake/`, cache, credential or machine log is staged.
- T-396 is incomplete without universal dynamic generated `step` correspondence in **both** languages for the specified balance domain. Constructor/getter proof and physical traces alone cannot complete it.
- Target operations execute a parsed AST; no reference `interpret`/`eval`/`sourceEval` call, no `targetResult = modelResult` premise, and no atomic helper macro named `evaluateWorld`, `sanitizeWorldPayload`, `checkBounds` or `checkInvariants`.
- Old Kadmos inventory scans all Applications. Register new modules there; isolate new Generated audit/rejection roots. Keep Foundation 52 and Distributed 336/594 separate; no fixed old application/Bridge counts.

## Review Focus

1. `n=0` and `n<0` take guard failure without effect evaluation; `n=b=S` succeeds with zero and `n>b` rejects bounds without publication (Tasks 3–4).
2. TS ordinary descriptors and Python exact dict sanitizer paths preserve `amount:n`; a changed copy/lookup source rejects certification (Tasks 2–3).
3. A modified emitted evaluator/operator, bound comparison, invariant call, return or publish order fails exact parsing or an operational theorem (Tasks 2–4).
4. Wrong `World` dimensions cannot enter `checkBridge`; the dependent `World raw.states.length ...` signature elaborates without an assumed cast (Tasks 2–4).
5. Source bytes, Python double JSON quoting and TS literal escaping preserve exact world data/order; recomputed hashes cannot rescue mutated source (Tasks 1–2).

---

## File map and interfaces

- `tools/export_kadmos_generated.mjs`; `conformance/kadmos-generated/{balance,order_phase}/{world_checker.ts,ports.d.ts,world_checker.py,ports.py}`; `conformance/kadmos-generated/provenance.json`; `scripts/check_kadmos_generated_artifacts.py`, `scripts/test_kadmos_generated_artifacts.py`: exact emitted-source provenance and literal round trip.
- `Harmonia/Applications/Kadmos/Generated/TargetSyntax.lean`: `TargetLang`, `TargetValue`, `TargetExpr`, `TargetOp`, `TargetFunction`, `TargetProgram`, `TargetRequest`, `ParseError`, `SourceParses`, `parseGenerated`, `parseGenerated_sound`.
- `Harmonia/Applications/Kadmos/Generated/TargetSemantics.lean`: `TargetStore`, `TargetFrame`, `TargetObservation`, `TargetResult`, `TargetError`, primitive evaluator, function-call execution, `targetConstruct`, getters, `targetStep`.
- `Harmonia/Applications/Kadmos/Generated/ArtifactCertificate.lean`: dependent `checkGenerated`, `CertError` and generic constructor theorem. `Harmonia/Applications/Kadmos/Generated/BalanceStep.lean`: fixture-specific `balanceState`, `balanceRequest`, `balancePreRel`, source/target projections and universal step theorem; imports `Fixtures.lean` after the certificate.
- `Harmonia/Applications/Kadmos/Generated/Fixtures.lean`: `balanceTsSource`, `balancePySource`, `orderTsSource`, `orderPySource : String` containing complete exact emitted source; checked balance/order certificate facts.
- `HarmoniaTests/KadmosGeneratedSyntax.lean`, `KadmosGeneratedSemantics.lean`, `KadmosGeneratedConstructor.lean`, `KadmosGeneratedStep.lean`, `KadmosGeneratedAxiomAudit.lean`, `KadmosGeneratedAuditRejection.lean`, `KadmosGeneratedRejection/{Unused,Unsafe}.lean`: closed, universal, audit and hostile probes.
- `scripts/check_kadmos_generated_audit.py`, `scripts/test_kadmos_generated_audit.py`, `lakefile.lean`, `HarmoniaTests/AuditPolicy.lean`, `.github/workflows/foundations.yml`, `docs/verification/2026-10-06-generated-implementation-correspondence.md`: exact source/root/CI evidence integration. Update `Harmonia/Applications/Kadmos.lean` only if the real import closure needs it.

The following Lean declarations are shared interfaces, not explanatory shorthand. The design defines every AST constructor and record field. The dependent checker signature is exact; do not substitute `World p v f a` without checked equalities.

```lean
def parseGenerated (lang : TargetLang) (source : String) : Except ParseError TargetProgram
theorem parseGenerated_sound {lang : TargetLang} {source : String}
    {program : TargetProgram} (h : parseGenerated lang source = .ok program) :
    SourceParses lang source program
def targetConstruct (p : TargetProgram) : Except TargetError TargetStore
def targetGetState (p : TargetProgram) (s : TargetStore) : Except TargetError TargetValue
def targetGetContext (p : TargetProgram) (s : TargetStore) : Except TargetError TargetValue
def targetStep (p : TargetProgram) (s : TargetStore) (r : TargetRequest) :
    Except TargetError TargetResult
def targetStoredNumber (lang : TargetLang) (n : Int) : TargetValue
def canonicalBalanceRequest (lang : TargetLang) (n : Int) : TargetRequest
def checkGenerated (lang : TargetLang) (source : String) (raw : Bridge.RawWorld)
    (w : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
    Except CertError TargetProgram
```

## Task 1: Exact artifact provenance and physical vectors

**Files:** exporter, eight tracked target files, provenance, artifact checker/tests and verification receipt paths above.

**Consumes:** actual `parseWorldSpec`, `compileWorldSpec`, `compileWorldSpecPython` from pinned Kadmos, Stage3b balance/order YAML and `parsed.json`. **Produces:** complete exact TS/Python source UTF-8 files and Lean `String` literal round trip; `check_artifacts(root: Path, kadmos: Path | None) -> dict[str,str]`.

- [ ] **RED:** Add Python tests that alter each generated target file, mutate embedded defaults with recomputed digest, inject duplicate/unknown world keys, insert `-0`, corrupt TS/Python string escaping and change a ports file. Run `python3 scripts/check_kadmos_generated_artifacts.py --self-test`; expect failure before checker exists.
- [ ] **GREEN:** Compile pinned Kadmos with installed `tsc -p ... --outDir /private/tmp/t396-...`; invoke actual compiler functions on parser-returned specs; track exact outputs and identities. Hermetic path compares tracked source/string literals and manifests; local `--kadmos --check` additionally regenerates and compares every output byte. Never export decoded `TargetProgram` or a presumed successful certificate.
- [ ] Run both check modes and self-tests, then execute emitted balance boundary pairs `(0,0),(0,1),(100,-1),(100,30),(100,130),(S,S),(S,-S)` and order STEP with Node/Python. Record exit statuses and normalized outputs. These are finite provenance, not universal proof.
- [ ] Review `git diff --check`, staged paths and clean Kadmos; commit Task 1 only.

## Task 2: Source-directed parser and constructor/getter fragment

**Files:** `TargetSyntax.lean`, `TargetSemantics.lean`, `Fixtures.lean`, `HarmoniaTests/KadmosGeneratedSyntax.lean`, `KadmosGeneratedConstructor.lean`; add `kadmosGeneratedSyntaxTest` and `kadmosGeneratedConstructorTest` roots.

**Consumes:** Task 1 full source literals. **Produces:** exact schema and interfaces above; parser AST for both complete balance/order files; independent constructor/getter execution. Parser success requires unique bindings and a complete byte-consumption proof by its total `Except` result. Recognize unused sections exactly, but parse every selected statement and helper body into primitive AST nodes. AST function calls resolve only to parsed functions, with checked arity/order and lexical capture lists. Reached `.find`/`.some`/`.map` and Python `next` generator syntax desugars to `forEach`/condition/break nodes under an AST equivalence lemma; no callback is opaque.

- [ ] **RED:** Add closed checks such as:

```lean
example : (parseGenerated .ts balanceTsSource).toOption.isSome = true := by decide +kernel
example : (parseGenerated .python balancePySource).toOption.isSome = true := by decide +kernel
example : (parseGenerated .ts
  (balanceTsSource.replace "const boundError = this.checkBounds(candidate);"
    "const boundError = undefined;")).toOption.isSome = false := by decide +kernel
```

  Run `lake build kadmosGeneratedSyntaxTest`; expect missing parser/failing probes. Include changed `getContext`, `_DEFAULTS`, `evaluateWorld` call target, `_bounds` order and an opaque-body byte mutation.
- [ ] **GREEN parser:** Implement Lean lexical/string/JSON decoders for the actual literals and a restricted TS/Python statement parser. Define `SourceParses` as an independent restricted token/span grammar and prove `parseGenerated_sound`; the parser must produce `ifThenElse`/call/assignment/loop/return/throw nodes for selected `step` and reached sanitizer/evaluator/bounds/invariant helpers, Python `_freeze`/`reset` construction calls and TS `deepFreezeWorld` acceptance call. A recognizer that returns a single idealized helper node fails review. Check expression operator and helper call targets/arity in the AST; compare exact world data to the Stage3b raw record later in `checkGenerated`.
- [ ] **RED/GREEN constructor:** Add exact Ready/100 and A/(x=1,y=0) construction/getter tests for both languages and a getter-copy mutation. Implement independent constructor/check execution. For the order invariant and balance initial invariant, execute parsed helper AST; no `initialize` call inside target semantics. Run `lake build kadmosGeneratedSyntaxTest kadmosGeneratedConstructorTest`; temporarily swap parsed initializer/getter nodes to see a regression fail, then restore.
- [ ] Commit Task 2 only after checking no target primitive is a user-defined helper.

## Task 3: Independent execution of the reached balance step call graph

**Files:** extend `TargetSyntax.lean`, `TargetSemantics.lean`, create `HarmoniaTests/KadmosGeneratedSemantics.lean`; add `kadmosGeneratedSemanticsTest` root.

**Consumes:** parsed `TargetProgram`, canonical `TargetRequest`, `TargetStore`. **Produces:** `targetStep` through the actual parsed step body and reached helper bodies; lemmas about canonical request sanitization, transition lookup, three evaluator expressions and bounds/invariants. `TargetStore` and `TargetObservation` have exactly the fields in the design; `targetStep` returns both poststore and observation, without reading `interpret`.

- [ ] **RED:** Add source-execution tests for `amount=0,-1,30,130,S`, current balances `0,100,S`; add a test of `event.amount > 0`, `balance - event.amount`, `balance >= 0` through the *parsed evaluator function*, not a separate expression evaluator. Include changed `>`/`>=`, subtraction/addition, sanitizer copy, bound order, invariant call and publish-before-check mutations with recomputed manifest. Run `lake build kadmosGeneratedSemanticsTest`; expect missing operations/failure.
- [ ] **GREEN primitives:** Define small-step/evaluator rules for local/field access, ordered maps, own-data descriptors, copies, strict comparison, JS safe-integer arithmetic, Python float conversion on exact safe integers, exceptions, early return, `forEach`, `tryCatchFinally`, checked function call/return. Define restricted regex/token matching for the actual three expressions and anchored effect assignment; prove the parsed tokenizer/Pratt paths yield the expected tokens/evaluation for dynamic `n,b`. Do not make tokenization or helper correctness an axiom.
- [ ] **GREEN path:** Derive canonical sanitizer success and copied `amount:n`; TS `deepFreezeWorld` success on its finite record and Python `copy.deepcopy` finite-tree copy; first transition/directive; guard classification; effect candidate `b-n` only when `n>0`; safe-integer check; bounds and invariant order; rejection rollback/observation; success publication/observation. Prove `0≤b≤S ∧ safeInt n ∧ n>0 → safeInt (b-n)` with `omega`. Run the target and closed source-execution tests; temporarily change parsed effect or bound AST and verify RED before restore.
- [ ] Commit Task 3 after source/AST review confirms all reached calls resolve to parsed bodies. If a reached helper remains opaque, stop and report the concrete missing construct; do not proceed to a correspondence claim.

## Task 4: Dependent certificate and universal model simulation

**Files:** `ArtifactCertificate.lean`, `BalanceStep.lean`, `HarmoniaTests/KadmosGeneratedStep.lean`; update `Fixtures.lean` and constructor tests. Add `kadmosGeneratedStepTest` root.

**Consumes:** Task 2–3 parser/execution, `Bridge.checkBridge` at raw-dependent dimensions and existing `balance_certificate`. **Produces:** `checkGenerated`, two actual-source certificates, constructor/getter theorem, universal step theorem in the design. `balancePreRel lang b store` constrains only incoming checker shape/state/context/busy/history; it must not mention result, n or model poststate.

- [ ] **RED certificate:** Add:

```lean
example : (checkGenerated .ts balanceTsSource balanceRaw balanceCandidate).toOption.isSome = true := by decide +kernel
example : (checkGenerated .python balancePySource balanceRaw balanceCandidate).toOption.isSome = true := by decide +kernel
example : (checkGenerated .ts
  (balanceTsSource.replace "balance - event.amount" "balance + event.amount")
  balanceRaw balanceCandidate).toOption.isSome = false := by decide +kernel
```

  Include a changed guard, bound, sanitizer, publish and embedded world literal, each with recomputed external digest. Run `lake build kadmosGeneratedStepTest`; observe RED before implementation.
- [ ] **GREEN certificate:** Implement the exact dependent signature in the shared interface. Require `checkBridge raw w = .ok w`, exact ordered embedded data, parsed call graph and supported balance profile; map parser/Bridge/data errors to `CertError`. Prove parser success exposes the specific AST structure used by the step lemmas; never add a premise saying a helper gives the expected result.
- [ ] **RED/GREEN universal proof:** In `BalanceStep.lean`, define `balanceState (b : Int) : State 1 1 := ⟨0, fun _ => b⟩` and `balanceRequest (n : Int) : Request 1 := ⟨"DEBIT", fun _ => .int n, none⟩`; first prove reference `interpret`'s three cases for arbitrary `b,n` using these definitions, the actual `balanceCandidate`, `hb` and `hn`. Then prove target cases from Task 3 small-step execution. Combine with a prestate-only `balancePreRel` (`Ready`, one `balance` value, empty history, absent undo, not busy) and normalized observation mapping. Add `exists_balancePreRel` for every `0≤b≤S` and closed witnesses at `b=0,100,S`; invoke the theorem for both actual TS and Python certificate facts. A proof by `rfl` on closed 30/130 examples does not meet this task.
- [ ] Run `lake build kadmosGeneratedConstructorTest kadmosGeneratedStepTest`. Mutation-disable the source statement validator briefly: the negative probe or a theorem must fail, then restore. Check `targetStep`, helper execution and relation definitions for reference-operation calls or expected-poststate premises; commit Task 4 only after clean review.

## Task 5: Audit isolation, policy, Linux and acceptance evidence

**Files:** new Generated audit/rejection Lean roots, `scripts/check_kadmos_generated_audit.py`, `scripts/test_kadmos_generated_audit.py`, `HarmoniaTests/AuditPolicy.lean`, `lakefile.lean`, `.github/workflows/foundations.yml`, verification receipt; old application manifest/umbrella import only as real closure requires.

**Interfaces:** exact targets `kadmosGeneratedSyntaxTest`, `kadmosGeneratedConstructorTest`, `kadmosGeneratedSemanticsTest`, `kadmosGeneratedStepTest`, `kadmosGeneratedAudit`, `kadmosGeneratedAuditRejection`. The new audit selects exact Generated product/probe/audit source modules by namespace **or source module**. Its rejection target is isolated from certified roots and from old traps.

- [ ] **RED:** Add inventory mutation tests for nested unregistered source/probe/rejection file, missing root/import, escaped unused axiom, indirect custom-axiom import, trap in certified closure and blanket old Applications selector. Run `python3 scripts/check_kadmos_generated_audit.py --self-test` and observe initial rejection failures.
- [ ] **GREEN:** Register exact manifests/root closures and isolated traps. Compose with unchanged old Kadmos/Bridge audits. Run all old/new inventories; do not alter Foundation/Distributed policies or fix old counts. Add serial Linux steps for artifact self-test/check, inventory self-test/check, four tests, certified audit, fresh `lake env lean HarmoniaTests/KadmosGeneratedAxiomAudit.lean` and isolated rejection target.
- [ ] **Full serial acceptance:** `lake build`, all 14 pre-existing dedicated targets and six new targets serially; old/new inventory suites; actual pinned-source `--kadmos --check` and hermetic artifact check; physical boundary examples and hostile mutations; fresh audits for changed closures. Record commands, exit codes, actual theorem/declaration/axiom counts, model assumptions, host primitive boundary and exactly what the universal theorem proves. No solver/finite trace is a kernel proof.
- [ ] Review three-way `b,n` coverage, exact source-string fixture checks, no vacuous relation, no helper macro, complete reached call graph and clean Kadmos/Git state. Commit focused local implementation/evidence. Parent handles independent physical review, hosted Linux observation, Grok verdict, publication and integration; no push/PR/merge by this owner.

## Self-review and handoff

Five independently reviewable tasks cover actual artifact provenance, syntax-directed source recognition, independent execution of reached helper bodies, dependent Bridge certification with universal dynamic step simulation, and isolated audit/CI. `checkGenerated` uses raw-dependent dimensions everywhere. The theorem has only source certificate, `0≤b≤S`, `safeInt n` and a prestate relation; none assumes an observation or target/model equality. Both languages are required, and constructors/getters are an initial task. The major feasibility risk is parsing the generated evaluator/sanitizer control flow honestly. If Task 3 cannot give semantics to a branch exercised by the canonical balance call, implementation must stop and return a concrete architecture decision to the parent; a constructor-only result does not complete T-396. Parent sends this corrected design to physical Grok before work starts.
