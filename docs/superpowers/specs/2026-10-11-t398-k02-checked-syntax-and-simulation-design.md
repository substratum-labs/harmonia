# T-398 K-02 checked syntax and compositional simulation design

Status: **proof strategy for parent-owned independent preflight; implementation is incomplete**. Parent selected option 1 on Harmonia `8a95c49822fe1b0cd5cb0e39b08c58e538a76f31` and coordinator `44a5fb5392c17ca7340233bd97a42bbce46347af`. This refines the accepted [K-02 correspondence design](2026-10-11-t398-k02-generated-correspondence-design.md) and its existing proof gates. It does not change Kadmos, the generated program, the first-call domain, or the target runtime. The historical feasibility stop is superseded as a task status, not erased as evidence.

## Exact claim and nonclaims

The candidate is the complete emitted BALANCE checker source for each language from read-only Kadmos `1ac9422a12ab743a9bbb8b8ad508d37c582637df` (`kadmos.compiler.k02.v1`), tracked in `conformance/kadmos-generated-k02`. `checkGenerated` must tie the **same returned low-level `TargetProgram`** to the exact source bytes, the independently checked syntax derivation, K-02 emitted world/default data, and dependent `checkBridge balanceRaw balanceCandidate`. Byte identity and SHA-256 are admission evidence, never an execution theorem. The existing T-395 `fda8c6e` pin remains separate. No result is assumed equal to the reference `interpret`.

The first theorem must conclude, for both TS and Python, successful actual-source `targetConstruct program (canonicalBalanceSeed lang b)` and `targetStep program machine (canonicalDebitRequest lang n)` for every `0 ≤ b ≤ S = 9007199254740991` and `-S ≤ n ≤ S`. The constructor-derived prestate has Ready/b, canonical own enumerable data, mutable empty history, no savepoint, and busy false. The three branches are guard refusal for `n ≤ 0`, acceptance with `b-n` for `0<n≤b`, and bounds refusal for `n>b`. In all branches the normalized allowed/current state/context/directive equals `interpret balanceCandidate`; separate conclusions establish violation code, logical frame or one-record history/savepoint, and final busy false. This is **one call from empty history**, not arbitrary history or a proof of the full TS/Python languages, runtime implementations, serializer, compiler template generator, rollback after the step, or order step. A physical `#eval`, one closed TS DEBIT30 theorem, and source digests do not imply this statement.

## Independently checked source syntax

Keep the existing `TargetExpr`, `TargetStmt`, `TargetFunction`, `TargetProgram` and raw TS/Python decoders. Add a **second checked path**; do not define `SourceParses` in terms of `parseGenerated`, parser success, source equality, or a constructor that accepts parser correctness as a premise. Proposed Lean interfaces (names may acquire a module prefix; the domains and conclusions are binding):

```lean
structure SourceSpan where
  start : Nat
  stop : Nat
inductive Lexes : TargetLang → String → List SourceToken → Prop
inductive ExprDerives : TargetLang → String → SourceSpan → TargetExpr → Prop
inductive StmtDerives : TargetLang → String → SourceSpan → TargetStmt → Prop
inductive ProgramDerives : TargetLang → String → List SourceToken → TargetProgram → Prop
inductive SourceParses : TargetLang → String → TargetProgram → Prop where
  | ofDerivation : Lexes lang source tokens →
      ProgramDerives lang source tokens program → SourceParses lang source program
def validateSource (lang : TargetLang) (source : String)
    (program : TargetProgram) : Bool
theorem validateSource_sound {lang source program} :
    validateSource lang source program = true → SourceParses lang source program
theorem SourceParses.unique {lang source p q} :
    SourceParses lang source p → SourceParses lang source q → p = q
def decodeGenerated (lang : TargetLang) (source : String) :
    Except ParseError TargetProgram
def parseGenerated (lang : TargetLang) (source : String) :
    Except ParseError TargetProgram := do
  let program ← decodeGenerated lang source
  if validateSource lang source program then pure program
  else throw (.unsupportedSyntax 0)
theorem parseGenerated_sound {lang source program} :
    parseGenerated lang source = .ok program → SourceParses lang source program
```

`Lexes` is an inductive character/interval relation: each token owns `[start,stop)`, `token.text` is that exact source substring, intervals are ordered/disjoint, and whitespace/comments fill the gaps. It is **not** the equation `tokenizeSource = .ok tokens`. `ProgramDerives` partitions the whole source into ordered module declarations, class fields, functions/methods and unexecuted declarations wherever they occur. Every `TargetProgram.functions` entry, including an unexecuted method, gets a **determinate** source-derived AST mapping; otherwise `SourceParses.unique` could fail through an unconstrained field. Only the reached call graph needs an execution-preservation theorem in this first slice. `ExprDerives`/`StmtDerives` consume their complete source spans and map each reached source construct to its low-level node. Examples: the actual `balance - event.amount` span derives `binary sub (local balance) (property (local event) amount)`; the Python `_TOKEN.match(expression, offset)` span derives a call with **two** arguments, then `.end()` is a subsequent call; `index++` derives `postIncrement` on the captured cell; `switch break` derives `breakTarget "switch"`; Python `nonlocal position` derives `nonlocalNames ["position"]`. The validator checks those maps rather than recognizing the function body as an ideal helper operation.

TS erasures (`import type`, type annotations/generics, `as`, `readonly`, `private`, `!`) and Python annotations/future import are separate derivation rules with owned spans and no runtime node; **value** imports such as `node:util` and Python `copy`/`json` retain runtime host bindings. Qualifiers and lexical paths distinguish `step.rollback`, `reset.rollback`, and sanitizer's nested `copy` from `copy.deepcopy`. Parameter defaults, `this`/`self` receiver binding, Python indentation, normal versus raw strings and regex literals, f-strings, comprehensions, generators, and callback bodies have explicit grammar rules. Python `PythonLine` currently drops absolute offsets; the validator must scan the original full string into located lines before checking bodies. Existing parser chunks are permitted as a decoder optimization, but the validator must prove each chunk's ownership and contiguous source coverage. No `opaque AST` node or unowned remainder can cover a reached body.

Proof order: `validateSource_sound` by induction on validator clauses into the grammar; lexer soundness from source slicing; determinism of token kinds, precedence, source partition and canonical lexical names; then `SourceParses.unique`. For `.find/.some/.map`, Python `next` and switch/control lowering, state a **surface evaluation rule** over the recognized source form and prove its result/heap/control equals the low-level AST execution rule on the supported domain. If a construct is represented directly, prove the direct rule instead of inventing a desugaring. In particular callback return exits the callback, function return exits bounds/effect, switch break exits the switch, and `finally` executes after saved return/exception. Exact-source pinning narrows which accepted grammar trees receive correspondence, but cannot replace these derivations.

`TargetCertificate.checkGenerated` must call this checked `parseGenerated`; its existing type retains `World raw.states.length raw.context.length raw.fields.length raw.transitions.length`. Closed kernel facts for each actual complete checker must establish validator success and parser success. Changed source with rehashed manifest must fail the pinned certificate. A hostile mutation accepted by the restricted grammar may be parsed, but its changed AST must execute differently or fail exact-source admission; it cannot inherit the original theorem by digest repair.

The tracked source fixes concrete validation and simulation checkpoints:

| Actual K-02 source span | Required syntax/execution evidence |
| --- | --- |
| TS `world_checker.ts:26–43`: `tokens[index++]`, recursive `parse`, `switch`/operator loop | Located `postIncrement` on the outer captured cell, fresh recursive frames, targeted switch exit and token progress; the returned cursor must reach each fixed expression end. |
| TS `world_checker.ts:82,90–96,190–192`: optional `nodeTypes?.isProxy`, own descriptors, sanitizer callback | Value import and optional-property AST, `Object.prototype`/descriptor primitive contracts on canonical ordinary objects, generic parsed sanitizer body; absent directive descriptor is undefined. |
| TS `world_checker.ts:112–113,141–178,180–235`: class fields, constructor→reset, snapshot/rollback, step/finally | Module/class/receiver/field binding, shared busy bit, source-ordered reset and step branches, cloned logical frame and finalizer. |
| Python `world_checker.py:12–32,55–78`: `_freeze`, `_TOKEN.match(expression, offset)`, `nonlocal position` | Python comprehension/generator/freeze user body, anchored match-at-offset/end host operations, shared position cell and lexical call resolution. |
| Python `world_checker.py:192–202,258–294,297–398`: `__init__→reset`, private backing fields, step/finally | Definition-time defaults, exact-dict seed/request, `_busy` alias, constructor-derived context/seed, sanitizer float tag, bounds before invariant, savepoint/history and finalizer. |

These locations are evidence anchors, not a permission to recognize a span and assign it a handwritten effect. The declarative grammar must derive its constituent statements and the execution relation must enter the parsed callees.

## Generic execution relation and canonical representation

The current executable `evalExpr`/`execStmt`, `targetConstructWithFuel`, `targetStepWithFuel`, machine/heap types and closed host primitives remain the implementation being proved about. The relation interface is:

```lean
inductive TargetFocus
  | eval (expr : TargetExpr) | exec (stmt : TargetStmt)
  | value (value : TargetValue) | exit (control : ControlResult)
inductive ResumeFrame
  | expr (parent : TargetExpr) (child : Nat)
      (evaluated : List TargetValue) (remaining : List TargetExpr)
  | stmt (parent : TargetStmt) (remaining : List TargetStmt)
  | call (caller : TargetFrame) (remainingArgs : List TargetExpr)
      (evaluatedArgs : List TargetValue)
  | loop (body : TargetStmt) (remainingItems : List TargetValue)
      (binders : List String)
  | switch (cases : TargetStmt)
  | protect (handler cleanup : TargetStmt)
      (catchType binder : Option String)
  | finally (saved : ControlResult)
structure TargetConfig where
  machine : TargetMachine
  frame : TargetFrame
  focus : TargetFocus
  continuation : List ResumeFrame
  fuelRemaining : Nat
inductive SmallStep (program : TargetProgram) :
    TargetConfig → TargetConfig → Prop
inductive Runs (program : TargetProgram) : TargetConfig → TargetConfig → Prop where
  | refl (config : TargetConfig) : Runs program config config
  | tail {first middle last : TargetConfig} :
      Runs program first middle → SmallStep program middle last →
      Runs program first last
def Triple (program : TargetProgram) (pre : TargetConfig → Prop)
    (code : TargetFocus) (post : TargetConfig → Prop) : Prop :=
  ∀ start, pre start → ∃ finish,
    Runs program { start with focus := code } finish ∧ post finish
def HeapWF (lang : TargetLang) (machine : TargetMachine) : Prop
def CanonicalGlobals (lang : TargetLang) (program : TargetProgram)
    (machine : TargetMachine) : Prop
def BalanceRep (lang : TargetLang) (b : Int) (machine : TargetMachine) : Prop
def StepRep (lang : TargetLang) (b n : Int) (phase : BalancePhase)
    (machine : TargetMachine) : Prop
```

`BalancePhase` is the closed path index `constructed | admitted | sanitized | selected | guarded | candidate | bounded | published | finalized`. `Runs` is defined here because Lean 4.16/Init has `Relation.TransGen` but no `Relation.ReflTransGen`; the private schema probe elaborates this closure. The `expr` continuation's child index and evaluated/pending lists are well-formed only when they are an actual ordered decomposition of `parent`; the `stmt` continuation similarly owns the remaining source-ordered sequence. The relation rules prove/preserve that zipper invariant. `call` pushes a fresh method/closure frame with cells captured by address; `loop` and `switch` consume only their targeted break/continue; `protect/finally` save and restore the prior return/exception unless cleanup itself exits. `ControlResult` retains `.normal/.returned/.broke/.continued/.raised`; no rule discards a nonlocal exit. Rules evaluate child expressions in source order, resolve local/global/receiver cells and actual call targets, allocate fresh frames/cells, and perform heap reads/writes. Only `BuiltinId` basic host operations use their explicit canonical-data contracts; a generated user function call pushes its **parsed body**. Derive evaluator soundness for the reached AST constructors: a successful `evalExpr`/`execStmt` run with fuel `k` has a `Runs` trace with the same result and logical machine. Do not define `SmallStep` by one call to `evalExpr`, `execStmt`, `targetConstruct`, or `targetStep`.

Define `HeapWF lang machine`: unique live object/cell/closure addresses below fresh counters; descriptors refer to live values; frame local/capture/global names point to live cells; a captured cell is the **same address** as the outer binding; Python generator and mapping-proxy refs remain live; checker refs and canonical `Object.prototype` are live. `CanonicalGlobals lang program machine` identifies the module's actually executed world/default bindings and ordered enumerable definitions. `BalanceRep lang b machine` extends these with Ready, exact one-key own enumerable data descriptor tagged `.jsNumber b` or `.pyInt b`, correct prototype/exact-dict kind, an unfrozen empty TS array or mutable empty Python list for history, `undo = none`, `busy = false`, and copied constructor seed. It is a relational predicate on live heap structure, **not** an exact heap-ID equation or a fabricated prestore. Derive it from successful parsed module/class/constructor/reset execution for every supported b. `StepRep lang b n phase machine` tracks original context/history/savepoint, copied payload and sanitizer tag, candidate object, shared Pratt `index`/`position` cell address and cursor, active lexical frames, and logical snapshots at guard/effect/bounds/publish/finally phases. Each phase lemma explicitly preserves `HeapWF` and the required unaffected cells/objects; fresh clone identities and frozen metadata may differ on rejection while logical data frame holds.

Prove a structural path budget for formal fuel 100: a rank on the fixed reached AST plus bounds for the one context key, one transition, one invariant and fixed guard/effect/invariant token strings. The length/depth bound is independent of numeric b,n because the source parses fixed expressions and primitive numeric contracts are atomic on safe tagged integers. Show each constructor and three step branch derivation fits `<100`; if the bound fails, prove a larger uniform bound and use that entrypoint fuel consistently, rather than extrapolating from finite vectors. The small-step relation and fuel theorem must link back to the existing executable entrypoints.

## Compositional proof units and trust

1. **Module and constructor/reset:** Execute parsed TS `JSON.parse` world/defaults, class field initializers and `constructor→reset→constructorSeed`; execute Python `json.loads→_freeze`, `_INITIAL/_DEFAULTS`, `__init__→reset→__constructor_seed`. Establish `CanonicalGlobals`, `HeapWF`, `BalanceRep` for every b and closed default/order getter witnesses. No constant ideal constructor.
2. **Sanitizer and evaluator:** From `BalanceRep` and allocated canonical request, execute descriptor/prototype/isProxy or exact-dict admission, sanitizer recursion, copy/set/seen and error-free payload. Python amount is `.pyInt n→.pyFloat n`; TS stays `.jsNumber n`. Execute actual tokenizer, shared recursive cursor cells, precedence parser and `booleanWorld`/`_boolean` on the fixed guard/effect/invariant strings. Token progress and exact arithmetic are symbolic in b,n. Prove these functions from `SmallStep`/generic evaluator rules, not as primitive helper contracts.
3. **Step decision and frame:** Execute transition lookup, absent-directive comparison, old-state guard, sequential effect candidate, type and safe-integer checks, bounds before invariant, then actual reject/accept closure. Derive guard/bounds codes, unchanged logical checker on rejection, accepted one-record history and pre-call savepoint on both targets, and `finally` busy false. Retain actual violation/trace object construction before projecting messages/traces away. `logicalChecker` currently returns raw `history : List TargetValue` and `undo : Option ObjRef`; strengthen it or add a **separate checked logical decoder** for history records/savepoint/seed so equality is about contents, not pointer equality.
4. **Composition:** For each `lang ∈ {ts,python}`, use closed checked-source certificate, the constructor theorem, one-call branch lemmas and existing symbolic `generated_balance_guard_reject/accept/bounds_reject` for `balanceCandidate`. Conclude the universal commuting theorem with constructor and step `.ok` in the conclusion. The target semantics module does not import the source interpreter; the final bridge theorem alone combines both sides.

The implementation's current `TargetRequest` is `⟨lang, shape, transitionId, amount⟩`, `TargetOutcome` is `⟨machine, verdict : TargetValue⟩`, `logicalChecker lang machine` returns a shallow `CheckerData` with raw history values/undo address, and the reference projection is named `balanceSourceProjection`. Do not use the older accepted spec's aspirational `TargetObservation` or broader request fields as if they existed. The proposed **first-call content interface** is:

```lean
structure BalanceRecord where
  step : Nat
  state : String
  action : String
  amount : TargetValue       -- .jsNumber n in TS, sanitized .pyFloat n in Python
  proposedDirectivePresent : Bool
structure BalanceSaved where
  state : String
  balance : Int
  history : List BalanceRecord
structure BalanceView where
  state : String
  balance : Int
  history : List BalanceRecord
  undo : Option BalanceSaved
  constructorSeed : Int
  busy : Bool
def balanceView (lang : TargetLang) (machine : TargetMachine) :
    Except TargetError BalanceView
def targetViolationCode (out : TargetOutcome) :
    Except TargetError (Option String)
def expectedRecord : TargetLang → Int → BalanceRecord
  | .ts, n => ⟨1, "Ready", "DEBIT", .number .jsNumber n, false⟩
  | .python, n => ⟨1, "Ready", "DEBIT", .number .pyFloat n, false⟩
```

Python's record contains sanitized `.pyFloat n`, while the input recipe begins `.pyInt n`. `balanceView` must check one-key descriptor contents, exact record keys/payload shape, record fields and savepoint contents after dereferencing, and reject malformed heaps. It may omit physical clone identity/frozen bits from its result **only after** `HeapWF` and source execution have checked those operations. A body theorem derives this view; it cannot assume it for an arbitrary machine. The final theorem shape is:

```lean
theorem k02_balance_one_call (lang : TargetLang) (source : String)
    (program : TargetProgram)
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ S) (hn : -S ≤ n ∧ n ≤ S) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed lang b) = .ok machine ∧
      BalanceRep lang b machine ∧ balanceView lang machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest lang n) = .ok out ∧
      balanceView lang out.machine = .ok after ∧
      targetProjection lang out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      (n ≤ 0 → targetViolationCode out = .ok (some "GUARD_FAILED") ∧
        after = before) ∧
      (0 < n ∧ n ≤ b → targetViolationCode out = .ok none ∧
        after.balance = b - n ∧ after.history = [expectedRecord lang n] ∧
        after.undo = some ⟨"Ready", b, []⟩ ∧
        after.constructorSeed = b) ∧
      (n > b → targetViolationCode out = .ok (some "INVALID_BOUNDS") ∧
        after = before)
```

In the actual Lean theorem qualify `balanceRaw`, `balanceCandidate`, `interpret` and `S` according to their modules. The theorem has no target-result, parser-correctness or heap-representation premise beyond the exact checked certificate; constructor and step success are conclusions. If `after = before` proves too strong because the logical view includes a legitimately changed field, identify that field from executed source and prove the four-field frame plus history/undo/seed individually; do not hide it in a projection error.

The trusted boundary is the declared restricted source-language model of basic JS/Python primitives on canonical data, externally checked serialization/byte provenance, and Node/CPython as implementations of those specified operations. `JSON.parse`/`json.loads`, exact regex matching, copying, descriptors, `MappingProxyType`, numeric tagged conversion and object identity have explicit contracts. **No assumption says Kadmos's evaluator, sanitizer, bounds, invariant, constructor or step helper is correct.** A full-language or runtime-implementation theorem remains deferred.

## Smallest feasible probe and next review

Private `/private/tmp/t398-option1-tiny.lean` (not staged) compiles with `lake env lean`: an independent `TinySurface` rule and `tinyValidate_sound` establish a token-to-AST mapping for the actual `balance - event.amount` expression; closed kernel checks confirm the existing TS/Python expression decoder returns that AST. A second closed kernel fact writes a mutable `CellRef` through a captured address and reads the changed value through the original address. The probe uses neither `native_decide` nor admitted axioms. It establishes **only** the shape of one syntax and heap lemma; it does not certify a whole file, a helper, a constructor or a dynamic step. Parent preflights this strategy before expensive proof implementation; current PR #5 remains draft and unmergeable.
