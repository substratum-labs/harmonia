# T-398: K-02 generated BALANCE/DEBIT correspondence design

Status: **current-source design for parent-owned independent physical preflight; no T-398 product, theorem, test or CI implementation exists.** This document supersedes, without rewriting history, `2026-10-06-generated-implementation-correspondence-design.md` and its plan/receipt. Those files describe historical Harmonia T-396, which is now **T-398** in the project ledger. Castor T-396 is unrelated. Yong explicitly resumed T-398 on 2026-10-11 after the old three-REVISE pause; the review counter is reset only for this redesigned K-02 task. Parent owns Grok and integration. Implementation requires an actual current-source preflight ACCEPT.

## Purpose and exact sources

Two independent goals remain: prove properties of Harmonia's reference model, and prove behavioral correspondence of actual generated target code to that model. T-394/T-395 achieved a restricted World model and source-bound projection; neither proved the emitted programs. T-398's first code theorem must use **actual generated TypeScript and Python** from read-only Kadmos main `1ac9422a12ab743a9bbb8b8ad508d37c582637df`, contract `kadmos.compiler.k02.v1`, manifest `0.1.2`. No replacement compiler/backend, Kadmos edit, handwritten target-result replica, hash-only certificate, finite differential test as proof, or assumption that a generated helper is correct.

Harmonia work starts from `origin/main@bac00db43cdfff8ba44779fa537a1560958a6154` plus the four documentation commits rebased from historical source PR [#5](https://github.com/substratum-labs/harmonia/pull/5); source worktree `/Users/yong/.codex/worktrees/5b89/harmonia`, branch `feat/t396-generated-correspondence` is retained as a historical branch name for T-398. T-401 FLP, quorum, CAP, generic Core, Distributed, legacy and accepted World/Interpreter/Bridge semantics remain untouched. `lean-toolchain` stays `leanprover/lean4:v4.16.0`. Coordination lock is the separate T-398 row/ledger in a clean worktree from internal `origin/main@c254da370fd5fabc56aef2034af8933970ac82dd`; dirty internal primary and other agents' work are outside ownership.

Read-only physical compilation used the installed Kadmos `node_modules/.bin/tsc -p tsconfig.json --outDir /private/tmp/t398-k02/kadmos-js`, then imported actual compiled `parseWorldSpec`, `compileWorldSpec`, `compileWorldSpecPython` on the **unchanged** tracked Stage3b balance/order YAML. Node 26 type stripping ran emitted TS and Python 3 ran emitted Python. Exact source and port fingerprints, seven balance boundary vectors, order step, rollback and hostile mutation are in the companion receipt. These are provenance and finite observations, not a proof.

### Stage3b compatibility, with its limit

`parseWorldSpec` now delegates to `admitWorldSpec`, and both compiler entrypoints re-admit `WorldSpecInput`. For these **two** YAML fixtures, the resulting K-02 admitted JSON is value- and ordered-serialization-equal to the old tracked T-395 `parsed.json` entries. Transition order/guard types/directive null and object-key order match. K-02 admission also accepts explicitly empty context/invariants/transitions and canonicalizes omitted directives to null; the first theorem **does not** cover those broader admitted models. It must not infer that K-02 generally requires a nonempty invariant or directive set from the balance fixture. This permits the accepted `checkBridge balanceRaw balanceCandidate` certificate to supply the **reference World** for this fixture. T-395's exporter, artifact checker and provenance remain pinned to `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`; they do not certify K-02 admission, YAML parsing, emitted serialization, or cross-version compiler semantics. A new exact K-02 fixture/manifest/byte check must bind the K-02 parser return, re-admission return, complete emitted files and Lean source literals; the exact equality of the two admitted fixture records is externally checked evidence. Kernel `checkGenerated` then checks the embedded K-02 world data against the same restricted raw projection. It must reject a changed guard, directive presence, context order or constructor default even if external hashes are updated. No theorem reconstructs arbitrary omitted-versus-explicit-false WorldSpec metadata from `RawWorld`.

## Current emitted code and supported one-call domain

K-02 TS emits a contract header, a `WorldData` type, `world = JSON.parse(<quoted JSON>)`, `contextDefaults = JSON.parse(<quoted defaults>)`, aliases `contextDefinitions`, `stateDefinitions`, `invariantDefinitions`, `transitionDefinitions`, the evaluator/sanitizer, and a class. Class fields initialize `#state`, copied `#context`, empty `#history`, `#constructorSeed=null`, `#undo=null`, `#busy=false`. `constructor(initialContext=null)` calls parsed `reset(initialContext)`, then saves a copy of the resolved context as `#constructorSeed`. K-02 `reset` checks shape/descriptors and defaults, rechecks bounds/invariants, clears history/undo and ends `#busy=false`; its source path for canonical `{balance:b}` must be executed, not assumed. `step` uses descriptor checks/sanitizer, first transition+directive, old-state guard, ordered target-state effects, effect type/safe-integer check, bounds then invariant, then publication/accepted-history/savepoint. Refusal rolls back logical checker data; `finally` clears busy. Public rollback/reset semantics are recognized but their later calls are **outside** the first theorem.

K-02 Python emits `json.loads(<normal quoted JSON>)` followed by `_freeze`, `_INITIAL`, `_DEFAULTS`, regex/precedence and numeric globals. `WorldChecker.__init__(initial_context=None)` creates `__constructor_seed=None`, `__state`, `__context={}`, `__history=[]`, **plain** `_busy=False`, `__undo=None`, calls parsed `reset(initial_context)` and saves a copied seed. `state/context/history` are read-only properties (context/history copy); `getState/getContext` route through parsed getters. `reset` reads `__constructor_seed` only for omitted/None context, otherwise validates exact dict seed and overlays defaults. Its canonical `{'balance':b}` branch must be executed. `step` snapshots previous undo, sanitizes canonical exact dicts, evaluates guard/effect, performs bounds/invariant order, publishes or restores, and ends `_busy=False`. Python `_busy` and TS `#busy` resolve to **the same logical checker busy slot** in the formal machine; neither falls through to an unconstrained instance attribute. Python double-underscore names resolve to distinct backing slots, while method `self` and TS `this` are implicit bound receivers, not explicit `ParamSpec` arguments.

The theorem covers one call from each language's **actual successful constructor with explicit balance seed** `b`, for every mathematical integer `0 ≤ b ≤ S`, `S = 9007199254740991`. The canonical request has exactly own data `transitionId="DEBIT"`, `eventPayload={amount:n}`, absent `proposedDirective`, with `safeInt n` (`-S ≤ n ≤ S`). TS request/payload are ordinary, non-proxy, accessor-free objects sharing the canonical `Object.prototype`; Python uses exact dicts with string keys. No extra fields, hostile host objects, fractional/nonfinite/negative-zero values or callbacks. The constructor-produced prestate has `Ready`, typed one-key balance context, empty mutable history, no undo/savepoint and busy false. Because K-02 accepts an explicit seed, prove constructor totality for **all** such b; do not merely posit a possibly uninhabited `balancePreRel` or mutate a store by hand. Default no-arg constructor/getter witnesses for balance 100 and order A/(1,0) remain separate checks.

For all supported b,n, prove from **`BridgeFixtures.balanceCandidate`** (never handwritten `Balance.balanceWorld`): `n≤0` gives guard rejection and logical frame; `0<n≤b` accepts `b-n`; `n>b` gives bounds rejection and logical frame. In every case target normalized allow/current phase/ordered context/directive matches `interpret`; target code refines to `GUARD_FAILED`, no violation, or `INVALID_BOUNDS` respectively. `Ready` and busy=false hold after return. `n>0` makes `b-n∈[-S,S]`, so the effect's target-safe intermediate agrees with Lean; the negative candidate for n>b remains within safe range before final bounds rejects. Python input `.pyInt n` becomes sanitizer `.pyFloat n`, numeric evaluator uses floats exact on this domain even for negative guard n, effect stores `.pyInt (b-n)`. TS remains `.jsNumber`. Error messages and shortest trace are projected **after their actual construction**. Rejection proves equal logical state/context/history/undo/seed, not reference equality of cloned heap objects or frozen flags. Acceptance has one logical record; TS saves the pre-call snapshot in `#undo` and freezes accepted history record, Python `__undo` stores the pre-call tuple and accepted history retains sanitizer float tagging. Reset/rollback after this call and arbitrary prior history are deferred to a later theorem.

## Route and trust boundary

| Route | Judgment |
| --- | --- |
| Formalize full TS/JS and Python plus entire existing compiler | Strongest but too broad for this bounded slice: runtime objects, exceptions, regexes, callbacks, numeric representations and template emission would dominate the theorem. |
| **Checked per-artifact restricted source translation validation** | Selected, conditional on preflight and a complete reached-operation inventory. A Lean parser consumes each complete emitted file, derives low-level syntax for module/class/constructor/getters and the **selected step plus every reached helper body**, and exactly recognizes unexecuted suffixes without granting those suffixes a semantic theorem. Independent restricted source-language small-step semantics executes the parsed statements. No whole-helper macro is allowed. |
| Certified restricted backend | Could simplify proof only by changing Kadmos's generator/integration path. This is a material separate architecture decision; T-398 does not implement or silently substitute it. |

A fixed-text recognizer for a helper followed by a handwritten ideal `evaluate`, `sanitize`, `bounds` or `step` operation is insufficient. The checked AST must expose statement order, lexical calls/defaults, mutable captures, conditions, loops, exceptions/finalizers, heap reads/writes, and the four actual expression token paths. `SourceParses lang source program` is an inductive syntax relation independent of `parseGenerated`; prove parser soundness and canonical uniqueness, and prove each sugar desugaring preserves source control/effects. The verified claim is about **restricted formal source-language semantics of the parsed emitted text**. The external boundaries are: pinned Kadmos parser/admission and emitted file/literal serialization checked by exact bytes; Node/CPython implementation of explicitly specified basic primitive contracts on canonical values; and the future portability of those probes across supported hosts. Neither a digest nor an assumed decoder/certificate premise nor differential agreement establishes source-code correctness.

This route is technically **high risk**. Each target is about 18–19 KB and contains nested Pratt parsing, sanitization, cloned rejection traces, savepoints and constructor/reset. A honest two-language proof may exceed a bounded stage. Preflight must review a call-graph/operation coverage matrix and the smallest target AST. Implementation has a fail-closed milestone: if a reached construct cannot be parsed and given independent source semantics, stop without claiming T-398 complete and ask the parent for the concrete choice of a larger formalization versus a separately authorized backend. Constructor-only facts or finite tests remain partial evidence.

## Exact certificate and operational interfaces

New Init-only modules live in `Harmonia/Applications/Kadmos/Generated/`. Define an ordered `JSONValue` (object as ordered key/value list), tagged `TargetValue` (JS number, Python int/float, bool/string/null/undefined, object/closure/builtin/match references), `ObjRef`/`CellRef`/`ClosureRef`, and a heap with own data/accessor descriptors, enumerable/writable/configurable/frozen flags, array/list/set/mappingproxy kinds, prototype reference, match spans/groups and distinct Python backing attributes. `TargetMachine` contains global cells, lexical frame stack, shared cell heap, object heap, intrinsics, checker slots (`state`, `context`, `history`, `undo`, `busy`, `constructorSeed`), fuel and any Python instance attributes. In Python `_busy` must map to `checker.busy`; `__state/__context/__history/__undo/__constructor_seed` map to the corresponding slots. TS `#busy/#constructorSeed` map likewise. A getter returns **updated machine plus value** because copied context may allocate a new reference. `logicalChecker` dereferences data and deliberately forgets clone identities only after helpers finish.

`TargetExpr` has literals, local/cell/field/property/index lookup, call/lambda with captured **cell locations**, postincrement, primitive operation and lazy `&&/||/??/conditional`. `TargetOp` has declaration/assignment, expression statement, if/for/while/switch, return/throw/rethrow, targeted break/continue, try/catch/finally. `ControlResult` distinguishes normal, returned value, targeted break/continue and raised exception; a return inside bounds/effect loop exits its function, switch break leaves the Pratt while running, finally clears the same busy bit. JS default parameter expressions evaluate at each omitted/**undefined** argument call (fresh seen Set); Python defaults are bound at definition time. Method receiver is implicit. Qualified lexical names disambiguate `step.rollback`/`reset.rollback` and nested sanitizer copy versus imported `copy.deepcopy`. `sourceTruthy` handles actual JS/Python false cases, objects/functions and empty Python containers; lazy and/or return operand values, `??` is nullish-only; generated `booleanWorld`/`_boolean` remains a parsed strict-Bool helper.

Closed source operations must include JS `JSON.parse` for **both** world/default literals; Python `json.loads` normal string then `_freeze`; actual TS/Python regex token/effect matching, Python `_TOKEN.match(expression, offset)` anchored at the **current offset**, `match.end()` returning tagged Python stop, and full/group numbering; `isspace`/`isdigit`/token index, decimal token conversion, len/join/negative quote slice, own-descriptor/prototype and `Object.entries`/`.items()` pair destructuring, exact-tag finite/is_integer/abs, object copy/deep copy/freeze/set identity, and nullable seed checks. Define arity, return tag, mutation and error for each reached **host primitive**, rather than declaring any generated helper primitive. Python `matchAt(pattern,string,pos)` consumes at pos or fails; successful result stores `(full,start=pos,stop>pos,groups)` and `matchEnd` yields `.pyInt stop`. For each of the four exact fixture expression strings, prove the tokenizer's offset strictly advances to string length; wrong zero-offset matcher or missing `.end()` fails a closed test and certificate. K-02's TS `JSON.parse` is a new reached operation; the decoded data is checked against the fixture-normalized Bridge raw fields with exact omission/presence and key order. Full source byte recognition rejects mutations to guard/effect/constructor/reset/busy and helper bodies even if a manifest digest is recomputed.

The minimum **data and execution schema** is fixed for preflight. `TargetLang = ts | python`; `NumberTag = jsNumber | pyInt | pyFloat`. `TargetValue` is a tagged scalar (`undefined/null/bool/string/number`), `ObjRef`, `ClosureRef`, builtin or `MatchValue{full,start,stop,groups}`. `Descriptor` records value versus get/set and enumerable/writable/configurable flags. `HeapObject` records language kind (`jsOrdinary/jsArray/jsSet/pythonDict/pythonList/pythonTuple/pythonSet/mappingProxy/regexPattern`), `Option ObjRef` prototype, ordered own descriptors/items/set members and frozen flag. `CellHeap` maps fresh `CellRef` to values, so recursive Pratt `parse` closures share the outer index/position cell while each call allocates fresh parameters/locals. `TargetFrame` has qualified function name, remaining statements, local/captured cell addresses and control result (`normal/returned/broke target/continued target/raised`). `TargetMachine` has globals, frames, cells, object heap, shared `Object.prototype` intrinsic, checker and fuel. Checker slots are `state : String`, `context/history : ObjRef`, `undo : Option ObjRef`, `constructorSeed : Option ObjRef`, `busy : Bool`, plus Python instance attributes that are not mapped backing slots. TS `#busy` and Python `_busy` dispatch **to this one slot**; Python `__constructor_seed` dispatches to `constructorSeed`. No copied capture values or second busy bit.

`TargetSeed` and `TargetRequest` have the exact fields in the interface block below are **allocation recipes**. `canonicalBalanceSeed` allocates an own enumerable data descriptor with `balance` tagged `.jsNumber b` or `.pyInt b`; `canonicalDebitRequest` allocates action/payload in order with absent directive, payload amount tagged `.jsNumber n` or `.pyInt n`. `TargetObservation` retains allowed, previous/current state, context ref, directive and violation code/trace; `TargetOutcome` carries postmachine and observation. `targetProjection lang` checks the target numeric tag, dereferences the returned context and retains only allowed/current state/ordered integer context/directive, while separate lemmas prove target violation code and full logical checker frame/savepoint shape. `sourceProjection` maps the Lean Result into the same mathematical carrier; a malformed target projection returns an error rather than silently coercing a value. Getter signatures return `(updatedMachine, TargetValue)` so a copied reference lives in the returned heap.

`TargetProgram` contains neutral ordered `worldData` **and `contextDefaultsData`**, module initialization, TS class fields, constructor, reset, getters, selected step and a qualified function map. `TargetExpr` supports literal/local/field/property/index/call/closure, lazy and/or/??/conditional, postincrement and closed primitive operations; `TargetStmt` supports declaration/assignment, expression statement, if/for/while/switch, targeted break/continue, return/throw/rethrow and try/catch/finally. Every selected user function (`evaluateWorld`/`evaluate_world`, sanitizer, `_safe_integer`, bounds, invariants, `_freeze`, nested parser/copy/rollback) is represented by these statements and executed by a generic interpreter, **not** by a primitive named after the function. A `SurfaceExec` relation for recognized `.find/.some/.map`, Python `next` and switch proves desugaring meaning preservation. A caller method's `self`/`this` is the current checker receiver and not an explicit parameter; default expressions follow JS call-time omitted/undefined or Python definition-time behavior. Store projections compare logical contents after clone/freeze completes, never physical heap identity.

The **closed primitive contract inventory** required before proof includes these source forms and their result/update rules; an unknown reached call fails certification:

| Source form exercised by the profile | Required rule |
| --- | --- |
| TS `JSON.parse(worldString)` and `JSON.parse(defaultString)`; Python `json.loads(normalString)` then `_freeze` | Strict ordered JSON decode with actual omission/key order, numeric tags and fresh heap objects; `_freeze` is parsed user code, not a primitive. Both TS decoded globals and Python frozen globals are compared with fixture-normalized `RawWorld`, and constructor defaults with variable defaults. |
| JS/Python tokenizer and effect regex | TS expression `.match`/join/whitespace replace and anchored effect `.exec`; Python `_TOKEN.match(expression,offset)` is `regexMatchAt(pattern,string,pos)` at **pos**, `.end()` is `matchEnd(match)=.pyInt stop`, `.group()`/`.group(0)` is full, `.group(k>0)` is groups[k-1]. Match `stop>pos`; token loops advance to exact length for guard/effect/both invariants. Regex literals and normal JSON strings have distinct unescapers. |
| Primitive expression work | JS/Python truthiness for `if/while/!` and lazy and/or, nullish-only `??`; strict parsed `booleanWorld`/`_boolean`; finite/safe integer/float tags, decimal token parse, comparison, subtraction, is_integer/abs, string length/join/replace/slice/isspace/isdigit/index and exact match groups. On supported n,b, Python sanitizer `.pyInt n→.pyFloat n`; guard and arithmetic remain exact, effect publication `.pyInt(b-n)`. |
| Canonical seed/request and heap | Own descriptor/prototype/isProxy/type checks; TS `Object.prototype` and prototypeOf share a ref, `Object.create(null)` retains own reads; Python exact dict, `id` identity/set handling; own enumeration and `for [key,definition]` pair destructuring; fresh copy/deepcopy, freeze/isFrozen, array/list append and savepoint snapshots. Wrong arity/tag, missing property, malformed binder or frozen mutation is an explicit error. |
| K-02 control | TS class-field initialization; constructor→reset→seed copy, Python `__init__→reset→seed` and property copies; `#busy`/`_busy` map to one slot; `try/finally` clears it after return/raise; rejection clones context/history but preserves logical prior undo, acceptance sets prior snapshot; nested function returns exit the correct function and switch break leaves Pratt while active. |

The parent preflight should reject a plan that simply matches the helper text then returns an ideal `guardCheck`/`effectCheck`/`sanitize`/`boundsCheck` outcome. A parser/operation matrix generated from **the actual complete K-02 emitted files** must list each reached call with its AST node and primitive rule or parsed callee body; no generic "host runtime handles it" entry for a user helper. The prior R3's two final holes are explicit here: Python `_busy` aliases the checker busy cell, and anchored match-at-offset plus `.end()` is a source operation with a progress theorem.

Binding and theorem interfaces (names and dependent dimensions are fixed; implementer may split modules without changing their meaning):

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
-- checkGenerated invokes checkBridge raw candidate; no arbitrary-dimension cast.
structure Normalized where
  allowed : Bool
  currentState : String
  context : List (String × Int)
  directive : Option String
def sourceProjection (r : Result 1 1) : Normalized
def targetProjection (lang : TargetLang) (out : TargetOutcome) :
  Except TargetError Normalized
inductive RequestShape | ordinaryRecord | exactDict
structure TargetSeed where
  lang : TargetLang
  shape : RequestShape
  balance : Int
  extraFields : List (String × TargetValue)
  proxy : Bool
  accessor : Bool
structure TargetRequest where
  lang : TargetLang
  shape : RequestShape
  action : String
  amount : Int
  proposedDirectivePresent : Bool
  proposedDirective : Option String
  extraFields : List (String × TargetValue)
  proxy : Bool
  accessor : Bool
structure TargetObservation where
  allowed : Bool
  previousState : String
  currentState : String
  context : ObjRef
  directiveAllowed : Option String
  violationCode : Option String
  trace : Option ObjRef
structure TargetOutcome where
  machine : TargetMachine
  observation : TargetObservation
structure LogicalRecord where
  step : Nat
  state : String
  action : String
  payload : List (String × Int)
  proposedDirectivePresent : Bool
  proposedDirective : Option String
structure LogicalSnapshot where
  state : String
  context : List (String × Int)
  history : List LogicalRecord
structure CheckerData where
  state : String
  context : List (String × Int)
  history : List LogicalRecord
  undo : Option LogicalSnapshot
  constructorSeed : List (String × Int)
def logicalChecker (m : TargetMachine) : Except TargetError CheckerData
def logicalBalance (m : TargetMachine) : Except TargetError Int
def canonicalBalanceSeed (lang : TargetLang) (b : Int) : TargetSeed
def canonicalDebitRequest (lang : TargetLang) (n : Int) : TargetRequest
def targetConstruct (program : TargetProgram) (seed : TargetSeed) :
  Except TargetError TargetMachine
def targetGetContext (program : TargetProgram) (m : TargetMachine) :
  Except TargetError (TargetMachine × TargetValue)
def targetStep (program : TargetProgram) (m : TargetMachine) (req : TargetRequest) :
  Except TargetError TargetOutcome

theorem k02_balance_one_call (lang : TargetLang) (source : String)
  (program : TargetProgram)
  (hc : checkGenerated lang source BridgeFixtures.balanceRaw
    BridgeFixtures.balanceCandidate = .ok program)
  (b n : Int) (hb : 0 ≤ b ∧ b ≤ S) (hn : safeInt n) :
  ∃ m out before, targetConstruct program (canonicalBalanceSeed lang b) = .ok m ∧
    logicalChecker m = .ok before ∧
    targetStep program m (canonicalDebitRequest lang n) = .ok out ∧
    targetProjection lang out = .ok (sourceProjection
      (interpret BridgeFixtures.balanceCandidate
        (generatedBalanceState b) (generatedBalanceRequest n))) ∧
    out.machine.checker.state = "Ready" ∧ out.machine.checker.busy = false ∧
    (n ≤ 0 → out.observation.violationCode = some "GUARD_FAILED" ∧
      logicalChecker out.machine = .ok before) ∧
    (0 < n ∧ n ≤ b → out.observation.allowed = true ∧
      logicalBalance out.machine = .ok (b - n) ∧
      acceptedHistoryShape lang b n m out.machine) ∧
    (n > b → out.observation.violationCode = some "INVALID_BOUNDS" ∧
      logicalChecker out.machine = .ok before)
```

`generatedBalanceState/Request` are new names, distinct from old `Balance.lean`. `CheckerData` is the logical record of phase, ordered integer context, accepted-history records, optional pre-call savepoint and constructor seed. `logicalChecker` dereferences state/context/history/undo/seed into `Except TargetError CheckerData`, and `logicalBalance` requires exactly one balance value with the correct language numeric tag; both reject malformed references instead of supplying an ideal output. The theorem carries a successful pre-call `before` witness, so rejection frame equality cannot hold merely because both projections error. `acceptedHistoryShape` is a **conclusion-only** predicate defined as exactly one logical accepted record (step 1, Ready, DEBIT, sanitized amount, absent directive), plus the pre-call Ready/b/empty-history savepoint in TS `#undo` and Python `__undo`, and no change to constructor seed. It does not demand cloned heap identity. The displayed theorem states the three result cases explicitly, not via an assumed target result. The source/model three cases are proved symbolically from `Interpreter.lean` and `balanceCandidate`, and target cases from execution of the parsed AST. `targetConstruct`'s existence is in the **conclusion**, preventing vacuity. Constructor witness for every b derives context descriptors, unfrozen/mutable empty history, canonical globals, seed b and busy false from parsed K-02 code. Order default constructor/getter result is a separate closed kernel fact; order STEP remains finite evidence, not a theorem here. No `native_decide`, `sorry`, `admit`, `sorryAx`, custom axiom or helper-correctness assumption in certified roots.

## Acceptance and implementation boundary

A later accepted implementation must track exact K-02 emitted TS/Python source and port files for both fixtures, a strict byte/provenance checker, Lean source literal round trip, four closed certificates, nonvacuity witnesses, universal one-call theorem in both languages, malformed-host-input rejection outside the supported request profile, negative **source** mutations (at minimum effect `-`→`+`, guard `>`→`>=`, `_busy` mapping/finalizer, regex offset/end, constructor seed/default, bounds/invariant order) that fail certification or yield a kernel-diagnosed mismatch, and isolated generated-source audit/unused-axiom traps. Old Kadmos Application inventory scans all Applications; register exact new modules. Bridge audit grows only for real import closure, never blanket old namespace. Foundation 52 and Distributed 336/594 remain separate observations, not fixed old Application totals. Run serial `lake build`, dedicated Foundation/Distributed/World/Bridge/Quorum/CAP plus new targets and inventory/self-tests, fresh affected axiom audits, actual TS strict typecheck, Python import/execution, macOS local probes and hosted Linux exact-head CI. Record model/host assumptions and exact source IDs. No product/test/CI code begins in this invocation; no merge before reviewed integration.
