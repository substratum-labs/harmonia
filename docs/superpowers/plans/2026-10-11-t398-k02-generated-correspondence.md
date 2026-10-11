# T-398 K-02 Generated BALANCE/DEBIT Correspondence Implementation Plan

> **For physical Codex implementers:** Use `superpowers:executing-plans` task by task, with RED/GREEN and independent review gates. Yong's 2026-10-11 resumption authorizes planning; **no task below starts until the parent obtains an actual physical current-source Grok preflight ACCEPT.** Prior three REVISE verdicts belong to the historical pinned-output attempt and are retained, not reused as this task's new review count. No virtual subagents or direct merge by this owner.

**Goal:** Kernel-check one canonical BALANCE/DEBIT step of actual K-02 emitted TypeScript and Python against the source-bound Harmonia reference World for every bounded starting balance and safe signed amount.

**Architecture:** Export actual admitted K-02 fixtures, check exact source bytes, parse the reached generated source fragment into an independent restricted TS/Python AST, execute that AST with explicit heap/control/numeric semantics, then prove constructor totality and a universal one-call commuting theorem. Unexecuted source is exactly recognized but receives no behavior theorem. The accepted T-395 Bridge certificate supplies the reference World only after explicit equality of the two pinned fixture records is checked.

**Tech Stack:** Lean 4.16.0/Init/Lake, pinned Kadmos TypeScript compiler `1ac9422a12ab743a9bbb8b8ad508d37c582637df` (`kadmos.compiler.k02.v1`), Node/TypeScript, Python, Python inventory scripts, hosted Linux CI.

**Spec:** `docs/superpowers/specs/2026-10-11-t398-k02-generated-correspondence-design.md` (supersedes the 2026-10-06 historical T-396 design).

## Global Constraints

- Source branch retains its historical name `feat/t396-generated-correspondence` but ledger task ID is **T-398**; Castor T-396 and T-401 FLP are separate and untouched.
- Keep `lean-toolchain` exactly `leanprover/lean4:v4.16.0`; Init-only new application modules, no mathlib/Veil/new dependency, `native_decide`, `sorry`, `admit`, `sorryAx` or custom certified axiom.
- Keep accepted Core/Distributed/legacy/World/Interpreter/Bridge, Quorum and CAP semantics unchanged. Do not edit Kadmos, generated seams in Kadmos, another agent's work or internal primary checkout.
- All Lake processes are serial. No `.lake/`, generated binaries, caches, credentials or machine logs are staged.
- The only certified runtime domain is **one call** from actual successful `targetConstruct(canonicalBalanceSeed lang b)`, `0≤b≤S`, `safeInt n`, canonical own-data/exact-dict DEBIT request with absent directive, empty history/undo and busy false. Both languages required. Order default construction/getters get closed facts; order STEP is finite evidence only.
- The target executor cannot call `interpret`, Lean `eval`, Bridge `sourceEval`, or a helper macro with an assumed ideal result. Every reached generated helper statement/call must be parsed and executed; only explicit basic host primitive contracts and external byte/serialization checks remain trusted.

## Review Focus

1. K-02 TS uses `JSON.parse` for *world and defaults*, `#constructorSeed` and constructor→reset; Python uses `__constructor_seed`, `_busy`, `__undo`, read-only properties and constructor→reset. Old source syntax must fail the current certificate (Tasks 1–2).
2. Python `_TOKEN.match(expression,offset)` and `match.end()` must advance at the current offset for guard/effect/balance/order invariant strings; shared `position` cell and targeted switch break must remain correct (Tasks 2–3).
3. Explicit seeded constructor must succeed for **every** `b∈[0,S]`, derive an enumerable one-key context, mutable empty history, no undo and busy false; wrong seed, null/default branch or stale private field must fail (Tasks 2–4).
4. For `n≤0`, `0<n≤b`, `n>b`, target violation/code/state/context/directive and logical frame or accepted savepoint/history must match actual `balanceCandidate`, including Python `.pyInt→.pyFloat→.pyInt` and safe intermediates (Tasks 3–4).
5. Hostile source mutations with a recomputed digest, unused/escaped axioms, nested unregistered sources, stale Bridge pin conflation and Linux-only drift must reject or be explicitly diagnosed (Tasks 1, 4–5).

---

## File map and binding interfaces

- `tools/export_kadmos_generated_k02.mjs`, `conformance/kadmos-generated-k02/{balance,order_phase}/{world_checker.ts,ports.d.ts,world_checker.py,ports.py,admitted.json}`, `conformance/kadmos-generated-k02/provenance.json`, `scripts/check_kadmos_generated_k02_artifacts.py`, `scripts/test_kadmos_generated_k02_artifacts.py`: exact K-02 bytes, old/new parser-result fixture equality, source literal round trip.
- `Harmonia/Applications/Kadmos/Generated/TargetSyntax.lean`: ordered JSON, two restricted lexical grammars, `TargetExpr/Stmt/Function/Program`, independently inductive `SourceParses`, parser soundness/uniqueness and desugaring lemma.
- `Harmonia/Applications/Kadmos/Generated/TargetMachine.lean`: tagged values, data descriptors, shared cell/object heap, lexical closures, module/class/instance fields, `ControlResult`, TS/Python truthiness and **closed primitive contracts**.
- `Harmonia/Applications/Kadmos/Generated/TargetSemantics.lean`: module/constructor/getter/reached-helper/step execution and state/request/observation relation. No reference interpreter import here.
- `Harmonia/Applications/Kadmos/Generated/ArtifactCertificate.lean`: dependent Bridge certificate and exact K-02 embedded-world/default comparison.
- `Harmonia/Applications/Kadmos/Generated/Fixtures.lean`: complete emitted source literals and closed certificate facts only.
- `Harmonia/Applications/Kadmos/Generated/BalanceStep.lean`: symbolic actual-`balanceCandidate` model cases, constructor totality, universal one-call target correspondence.
- `HarmoniaTests/KadmosGeneratedK02Syntax.lean`, `KadmosGeneratedK02Machine.lean`, `KadmosGeneratedK02Constructor.lean`, `KadmosGeneratedK02Step.lean`, `KadmosGeneratedK02AxiomAudit.lean`, `KadmosGeneratedK02AuditRejection.lean`, `KadmosGeneratedK02Rejection/{Unused,Unsafe}.lean`, `scripts/check_kadmos_generated_k02_audit.py`, `scripts/test_kadmos_generated_k02_audit.py`, `lakefile.lean`, `HarmoniaTests/AuditPolicy.lean`, `.github/workflows/foundations.yml`: isolated verification roots and source/axiom policy. Old Application inventory grows only for actual imports; old Bridge root grows only for real closure.

```lean
def parseGenerated (lang : TargetLang) (source : String) : Except ParseError TargetProgram
inductive SourceParses : TargetLang → String → TargetProgram → Prop
theorem parseGenerated_sound {lang source program}
    (h : parseGenerated lang source = .ok program) : SourceParses lang source program
theorem SourceParses.unique {lang source p q}
    (hp : SourceParses lang source p) (hq : SourceParses lang source q) : p = q

def checkGenerated (lang : TargetLang) (source : String) (raw : Bridge.RawWorld)
    (candidate : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
    Except CertError TargetProgram
structure Normalized where
  allowed : Bool
  currentState : String
  context : List (String × Int)
  directive : Option String
def sourceProjection (r : Result 1 1) : Normalized
def targetProjection (lang : TargetLang) (out : TargetOutcome) :
    Except TargetError Normalized
def logicalChecker (m : TargetMachine) : Except TargetError CheckerData
def logicalBalance (m : TargetMachine) : Except TargetError Int
def canonicalBalanceSeed (lang : TargetLang) (b : Int) : TargetSeed
def canonicalDebitRequest (lang : TargetLang) (n : Int) : TargetRequest
def targetConstruct (program : TargetProgram) (seed : TargetSeed) :
    Except TargetError TargetMachine
def targetStep (program : TargetProgram) (m : TargetMachine) (req : TargetRequest) :
    Except TargetError TargetOutcome
```

`TargetSeed` is an allocation recipe for ordinary TS `{balance:b}` or exact Python `{'balance':b}`; `TargetRequest` similarly allocates ordinary own-data/exact-dict action and payload, with no directive property. `TargetOutcome` carries machine plus observation. `TargetMachine` includes `checker.busy` shared by TS `#busy` and Python `_busy`, private `constructorSeed` and undo, globals, cell/closure/object heaps, descriptors, history/frozen flags and fuel. The spec gives the required operation/call inventory; the implementer cannot replace the source parsing obligation with ideal `guard`, `sanitize`, `bounds`, `constructor` or `step` operations.

## Task 1 — Exact K-02 provenance and old-Bridge compatibility

**Deliverable:** reproducible emitted files and a strict source identity gate, with no semantic theorem claimed.

- [ ] **RED:** Tests mutate a generated `world_checker.ts/.py` byte, rehash manifest, change TS `JSON.parse` default or world JSON, change Python `_WORLD` field order/guard type, and mismatch old T-395 `parsed.json`; each fails `check_kadmos_generated_k02_artifacts.py`. Run its `--self-test` and see failures before checker implementation.
- [ ] **GREEN:** Compile pinned read-only Kadmos into private tmp using its installed `tsc`, invoke actual parse/admit and both compilers on unchanged Stage3b YAML, track full output bytes plus SHA-256, Kadmos commit/contract, YAML bytes, admitted ordered JSON. Hermetic Linux checks tracked bytes; local `--kadmos --check` recompiles pinned source and compares exact bytes. Lean fixture generation serializes **complete source strings**, not ASTs/certificate success.
- [ ] Prove/record only external fixture equality: for balance/order, new K-02 admitted object equals the corresponding tracked T-395 parser record in ordered canonical JSON; old provenance remains old-pinned. Run Node/Python physical boundary vectors, order STEP, constructor/reset/rollback probe and effect `-→+` scratch mutation. Record that these finite results are not a kernel theorem. Commit Task 1 only after byte/manifest tests pass.

## Task 2 — K-02 syntax, module initialization and constructor

**Deliverable:** accepted actual source strings parse to a low-level AST; seeded constructors execute source code and give nonvacuous initial states.

- [ ] **RED:** Closed `by decide +kernel` probes for `(parseGenerated .ts balanceTsSource).toOption.isSome=true`, Python likewise, order likewise; mutations of TS `JSON.parse`, `contextDefaults`, `#constructorSeed`, `reset(initialContext)`, Python `__constructor_seed`, `_busy` dispatch and `__state` backing reject. The old fda8c6e emitted files reject under K-02 certificate. Run `lake build kadmosGeneratedK02SyntaxTest` and see RED.
- [ ] **GREEN parser:** Consume entire TS/Python output including TS types/import erasure, JSON-quoted world/default literals, Python normal versus raw strings, qualified lexical functions and method receiver binding. `SourceParses` is independent of the parser, names are canonical, and desugaring of `.find/.some/.map`, Python `next` and switch has a control/effect preservation proof. Check all reached constructor/reset/evaluator/invariant helpers; fixed text may guard unexecuted methods only, not provide helper semantics.
- [ ] **RED/GREEN machine:** Build cell/heap/control semantics. TS `#busy` and Python `_busy` dispatch to the **same** `checker.busy` slot. Python `_TOKEN.match(expression,offset)` uses `regexMatchAt` and `.end()` uses `matchEnd`, with matched start=current offset and strictly increasing stop; prove token loops terminate on all four exact expression strings. Mutating either operation must make a closed constructor/guard probe fail. Include shared recursive position cells, loop returns, targeted switch breaks, default arity, prototype/descriptor/frozen and Python int/float tags.
- [ ] **Constructor:** `targetConstruct program (canonicalBalanceSeed lang b)` follows parsed K-02 class/init→reset code for each supported b; prove totality and typed context/history/undo/busy/seed metadata symbolically. Closed `b=0,100,S` witnesses; default balance100 and order A/(1,0) getter witnesses. Getter returns updated heap and fresh copied context. `lake build kadmosGeneratedK02SyntaxTest kadmosGeneratedK02MachineTest kadmosGeneratedK02ConstructorTest`; commit only if every reached constructor operation is modeled.

## Task 3 — Independent selected-step execution

**Deliverable:** actual parsed BALANCE step produces target results for dynamic b,n under restricted source-language semantics.

- [ ] **RED:** A closed parsed-source test constructs balance100 then steps amount30 and expects allowed/Ready/70/null, while amount0 expects `GUARD_FAILED`/frame and amount130 `INVALID_BOUNDS`/frame. Alter shared `position`, Python `_busy`, regex offset/end, effect minus, bounds order, sanitizer descriptor or finally; parser rejects or result changes. No test-only handwritten evaluator.
- [ ] **GREEN:** Execute selected generated call graph: own data descriptor checks; sanitizer/deep-copy/freeze; first transition/directive; four-expression tokenizer/Pratt paths and explicit basic regex/string/numeric operations; old-state guard; target-state sequential candidate effect; safe-integer type check; bounds then invariant; rejection logical rollback; acceptance snapshot/history; finally busy=false. Python `_busy` must be the exact bit read by reentrancy guard and written by finalizer; `matchEnd` returns tagged `.pyInt` stop. All generated helpers are parsed bodies, not primitive macros.
- [ ] Prove target path lemmas symbolically for `n≤0`, `0<n≤b`, `n>b`, `0≤b≤S`, `safeInt n`; safe intermediate `b-n` on positive branch, negative candidate bounds failure, Python `.pyInt→.pyFloat→.pyInt`, JS exact Number domain, rejected logical frame and accepted undo/history shape. Run `lake build kadmosGeneratedK02MachineTest kadmosGeneratedK02StepTest`; temporarily disable one source check and verify hostile probe turns RED, then restore. Stop and report an explicit architecture decision if any reached operation remains opaque.

## Task 4 — Kernel certificate and correspondence

**Deliverable:** exact source-bound noncircular theorem for both languages and adversarial certificates.

- [ ] **RED certificates:** `checkGenerated .ts balanceTsSource balanceRaw balanceCandidate` and Python counterpart must become `.ok`; a source mutation `"balance - event.amount"→"balance + event.amount"` must fail even with recomputed external digest. Include guard `>` mutation, `#busy/_busy` dispatch, `regexMatchAt` offset/end, TS world/default JSON, constructor seed and bounds/invariant order. Run `lake build kadmosGeneratedK02StepTest` before implementation and observe RED.
- [ ] **GREEN:** `checkGenerated` uses exact raw-dependent dimensions and `checkBridge raw candidate=.ok candidate`; checks K-02 embedded JSON/defaults and whole-source grammar against fixture-normalized raw. Prove parser soundness/uniqueness and sugar meaning, no external decoded-AST premise. `targetConstruct` totality is a theorem conclusion, not a prestate assumption.
- [ ] Prove actual `BridgeFixtures.balanceCandidate` model cases directly from `Interpreter.lean`, then combine with target path lemmas to prove `k02_balance_one_call` for all b/n and both actual source strings. Separate accepted code, logical context, directive, busy=false, rejected frame and accepted savepoint/history facts; carry `logicalChecker m = .ok before` in the conclusion so two projection errors cannot witness a frame theorem. Use `decide +kernel` only on closed source/certificate facts and symbolic Lean proof on b/n. Do not substitute handwritten `balanceWorld`. Commit after reading theorem statement and axiom dependencies.

## Task 5 — Audits, physical validation and review handoff

**Deliverable:** exact source inventory, isolated certified axiom audit, Mac/Linux verification receipt and reviewed draft PR; no automatic merge.

- [ ] **RED/GREEN audit policy:** tests insert unused/escaped custom axioms, nested unregistered Generated modules, indirect imports and rejection-root leakage. Add exact new product/test/audit manifest and separate rejection roots; old Application audit discovers new sources because it scans all Applications, old Bridge audit grows only for real closure. No blanket entire Application namespace selector.
- [ ] Add serial Linux CI steps for K-02 artifact/manifest check, new source/root inventory, dedicated syntax/machine/constructor/step targets, certified/fresh axiom audit and isolated rejection. Keep old Foundation/Distributed/World/Bridge/Quorum/CAP gates and toolchain unchanged.
- [ ] Fresh serial `lake build`, all existing dedicated targets plus new ones, inventory self-tests/checks, fresh affected axiom audit, strict generated TS typecheck, Python import/runtime, physical Mac boundary and hostile mutations, hosted Linux exact-head result. Record commands/exits, axioms, fixture hashes, source/host/serializer assumptions and unproved paths. Parent coordinates independent physical final review and any later reviewed integration; owner does not merge here.

## Preflight and feasibility stop

The current invocation delivers this reviewable plan only. The existing-source route is possible in principle but expensive: each target is about 18–19 KB with nested evaluator, sanitizer, K-02 reset/savepoint and two host languages. The parent must obtain independent **current-source** preflight ACCEPT before Task 1 code. If preflight or Task 2 finds that all reached constructs cannot be parsed/executed without an ideal helper macro, report exact source syntax and alternatives; do not narrow the claim silently, start a certified alternate backend, or call the finite vectors a proof. The reset counter does not erase historical R1/R2/R3 evidence.
