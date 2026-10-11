# T-398 K-02 checked syntax and compositional simulation design

Status: **proof-strategy R2 REVISE on `4087d8324baaa8e5384fc7bf7e0e8dcff984cecb`; corrected for parent-owned R3 preflight, not yet accepted.** Parent selected option 1 on Harmonia `8a95c49822fe1b0cd5cb0e39b08c58e538a76f31` and coordinator `44a5fb5392c17ca7340233bd97a42bbce46347af`. The independent reviewer retained that route but found an actual shared target-executor catch/finally bug and an inaccurate fuel-match inventory. This revision includes the narrow executor fix and test-first kernel regressions, then corrects the written rank/host-budget interface; full grammar and correspondence implementation remain open. It refines the accepted [K-02 correspondence design](2026-10-11-t398-k02-generated-correspondence-design.md) without changing Kadmos, emitted artifacts or the first-call domain.

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
def validateExprSpan (lang : TargetLang) (source : String)
    (span : SourceSpan) (expr : TargetExpr) : Bool
theorem validateExprSpan_sound {lang source span expr} :
    validateExprSpan lang source span expr = true →
    ExprDerives lang source span expr
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

TS erasures (`import type`, type annotations/generics, `as`, `readonly`, `private`, `!`) and Python annotations/future import are separate derivation rules with owned spans and no runtime node; **value** imports such as `node:util` and Python `copy`/`json` retain runtime host bindings. Qualifiers and lexical paths distinguish `step.rollback`, `reset.rollback`, and sanitizer's nested `copy` from `copy.deepcopy`. Parameter defaults, `this`/`self` receiver binding, Python indentation, normal versus raw strings and regex literals, **TS backtick template literals with ordered `${expression}` holes**, Python f-strings, comprehensions, generators, and callback bodies have explicit grammar rules. The TS template rule owns the opening/closing backticks, literal segments, `${`/`}` delimiters, nested expression spans and escaping; it maps to the existing `TargetExpr.formatted/formatPart` AST and preserves left-to-right interpolation, separately from the Python f-string rule. It must cover the reached `` `INVALID_BOUNDS: ${invalid}` `` and `` `Context bound failed on '${boundError}'` `` forms. Python `PythonLine` currently drops absolute offsets; the validator must scan the original full string into located lines before checking bodies. Existing parser chunks are permitted as a decoder optimization, but the validator must prove each chunk's ownership and contiguous source coverage. No `opaque AST` node or unowned remainder can cover a reached body.

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
  | finally (savedOutcomeControl : ControlResult)
structure TargetConfig where
  machine : TargetMachine
  frame : TargetFrame
  focus : TargetFocus
  continuation : List ResumeFrame
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

`BalancePhase` is the closed path index `constructed | admitted | sanitized | selected | guarded | candidate | bounded | published | finalized`. `Runs` is **unfueled**; it counts no global steps against the executable entrypoint's depth parameter. `TargetMachine` currently has a `fuel : Nat` field, but the existing evaluator does not read or write it; `SmallStep` must not repurpose that field as a trace budget. A separate `traceLength : Runs p a b → Nat` may count relation steps for diagnostics only and never appears in `targetConstructWithFuel`/`targetStepWithFuel` adequacy. Lean 4.16/Init has `Relation.TransGen` but no `Relation.ReflTransGen`, so the closure above is explicit. The `expr` continuation's child index and evaluated/pending lists are well-formed only when they are an actual ordered decomposition of `parent`; the `stmt` continuation similarly owns the remaining source-ordered sequence. The relation rules prove/preserve that zipper invariant. `call` pushes a fresh method/closure frame with cells captured by address; `loop` and `switch` consume only their targeted break/continue. The R2 review found that the old `execStmt` catch arm used `return` before the cleanup join, making its prior intended rule false. A test-first one-line `return`→`pure` correction lets the caught `StmtOutcome` bind to `handled` and reach the **existing** cleanup. `handled.frame.control` is cleared before cleanup, so `ResumeFrame.finally` saves `handled.control`; normal cleanup restores that saved outcome and exiting cleanup overrides it. Six new TS/Python kernel facts cover caught return, caught rethrow/busy clearing and exiting cleanup; a seventh covers Python normal return (the TS normal-return test already existed). The fix is to the shared formal target executor, not Kadmos or the emitted source. `ControlResult` retains `.normal/.returned/.broke/.continued/.raised`; no rule discards a nonlocal exit. Rules evaluate child expressions in source order, resolve local/global/receiver cells and actual call targets, allocate fresh frames/cells, and perform heap reads/writes. Only `BuiltinId` basic host operations use their explicit canonical-data contracts; a generated user function call pushes its **parsed body**. Do not define `SmallStep` by one call to `evalExpr`, `execStmt`, `targetConstruct`, or `targetStep`.

Define `HeapWF lang machine`: unique live object/cell/closure addresses below fresh counters; descriptors refer to live values; frame local/capture/global names point to live cells; a captured cell is the **same address** as the outer binding; Python generator and mapping-proxy refs remain live; checker refs and canonical `Object.prototype` are live. `CanonicalGlobals lang program machine` identifies the module's actually executed world/default bindings and ordered enumerable definitions. `BalanceRep lang b machine` extends these with Ready, exact one-key own enumerable data descriptor tagged `.jsNumber b` or `.pyInt b`, correct prototype/exact-dict kind, an unfrozen empty TS array or mutable empty Python list for history, `undo = none`, `busy = false`, and copied constructor seed. It is a relational predicate on live heap structure, **not** an exact heap-ID equation or a fabricated prestore. Derive it from successful parsed module/class/constructor/reset execution for every supported b. `StepRep lang b n phase machine` tracks original context/history/savepoint, copied payload and sanitizer tag, candidate object, shared Pratt `index`/`position` cell address and cursor, active lexical frames, and logical snapshots at guard/effect/bounds/publish/finally phases. Each phase lemma explicitly preserves `HeapWF` and the required unaffected cells/objects; fresh clone identities and frozen metadata may differ on rejection while logical data frame holds.

The executable's `fuel` is **mutual-recursion depth**, not trace length. `evalExpr (fuel+1)` and `execStmt (fuel+1)` pass the same predecessor to each child **and to each sibling**; `fuel=0` fails before visiting a node. Define rank as edges from the current fuel-matching entry to the deepest nested fuel-matching entry: leaf rank `0`, a parent with predecessor-fuel child entries `1 + max` of child ranks, and a sequence's first/rest siblings `1 + max` rather than a sum. The `rest` of a `TargetStmt.sequence` is itself a nested cons cell and contributes another edge; the same holds for parameter/default, argument/array/object, switch-case, formatted-part and iteration-tail cons spines. A leaf executes at fuel `1`, giving strict `rank < k`.

The **exact entrypoint-fuel match inventory**, read from `TargetSemantics.lean`, is 15 functions: `evalExpr`, `execStmt`, `bindCallParams`, `evalDefaults`, `evalArgValues`, `evalObjectFields`, `evalArrayElems`, `evalSwitchCases`, `execForItems`, `evalDictCompItems`, `evalListCompItems`, `evalArrayMethodItems`, `evalFormattedParts`, `resumeGenerator`, and `consumeGenerator`. Each matches `fuel`; only its recursive calls at the predecessor add an edge. `evalCompFilter`, `evalArrayMethod`, `evalOneDefault`, `callClosure`, `resumeNext` and `consumeIterable` pass the same fuel without their own match, so they contribute **zero** extra edges, although calls through them into a listed function still enter that function. `hostCall` has no entrypoint-fuel parameter. Its `cloneValue` uses its own fixed `2048` recursion budget, and JSON `jsonToValue`/`jsonArrayValues`/`jsonObjectFields` use `source.toList.length * 4 + 1`; these four separately fuel-matching host functions are **not** charged to entrypoint `k`. The supported canonical snapshots and pinned JSON literals need separate host-budget termination/adequacy lemmas; an assumption that clone/JSON always succeeds is insufficient. Other basic host operations remain explicit supported-domain primitive contracts.

`targetConstructWithFuel k` calls module initialization, TS class fields, and constructor/`__init__` call with the **same** `k`; prove three separate rank `< k` obligations and compose their resulting heaps. `targetStepWithFuel k` allocates the canonical request and calls step at the same `k`; prove the step-call rank separately. On each reached branch, bound one context key, one transition, one invariant, fixed token strings and all recursive cons tails. The rank is uniform in b,n, with no subtraction path for `n≤0`. Prove these ranks `<100` or choose a single larger **proved** constant for both entrypoints and every adequacy theorem. Never infer entrypoint success from `traceLength <100` or finite `#eval` samples.

Two directions link the relation to the existing executable interpreter. **Soundness:** by induction on the executable depth argument for reached AST constructors, `evalExpr k`/`execStmt k = .ok outcome` yields an unfueled `Runs` derivation with the same machine, value and outcome control. **Reached-path adequacy/completeness:** by induction on the source-derived relation derivation and rank, a deterministic terminating `Runs` path that obeys `HeapWF`, the supported primitive contracts and `rank < k` yields the corresponding `evalExpr k`/`execStmt k = .ok outcome`; the relation must choose the same branch, exception/finally outcome and heap updates, not merely some favorable execution. Lift adequacy through module/class initialization and the actual constructor/step call wrappers to conclude `targetConstructWithFuel k = .ok machine` and `targetStepWithFuel k = .ok out`. The universal theorem's executable `.ok` conclusions depend on this **reverse** direction; one-way evaluator soundness alone is insufficient.

Use ranked **semantic derivations**, not an equation to the executable functions, as the precise bridge carrier:

```lean
inductive DepthDerivesExpr (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetExpr → ExprOutcome → Nat → Prop
inductive DepthDerivesStmt (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetStmt → StmtOutcome → Nat → Prop
theorem expr_path_runs :
    DepthDerivesExpr program machine frame expr outcome rank →
    ExprRuns program machine frame expr outcome
theorem stmt_path_runs :
    DepthDerivesStmt program machine frame stmt outcome rank →
    StmtRuns program machine frame stmt outcome
theorem evalExpr_sound (h : evalExpr k program machine frame expr = .ok outcome) :
    ∃ rank, DepthDerivesExpr program machine frame expr outcome rank ∧ rank < k
theorem execStmt_sound (h : execStmt k program machine frame stmt = .ok outcome) :
    ∃ rank, DepthDerivesStmt program machine frame stmt outcome rank ∧ rank < k
theorem evalExpr_adequate
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (hr : rank < k) :
    evalExpr k program machine frame expr = .ok outcome
theorem execStmt_adequate
    (h : DepthDerivesStmt program machine frame stmt outcome rank)
    (hr : rank < k) :
    execStmt k program machine frame stmt = .ok outcome
```

`ExprRuns`/`StmtRuns` are projections of an unfueled `Runs` trace from `.eval expr`/`.exec stmt` to a terminal configuration whose machine, value or `StmtOutcome.control` equals the indexed outcome. `DepthDerivesExpr`/`Stmt` have one constructor per reached generic syntax/control rule, leaf rank `0` and parent rank `1+max` over child derivations; they cannot contain `evalExpr`/`execStmt` success as premises. The actual-source constructor/helper lemmas produce these derivations. Determinism and adequacy then yield the executable `.ok` facts. The type block omits routine implicit binders and qualifiers but fixes the proof direction, indexed outcomes and strict depth comparison.

## Compositional proof units and trust

1. **Module and constructor/reset:** Execute parsed TS `JSON.parse` world/defaults, class field initializers and `constructor→reset→constructorSeed`; execute Python `json.loads→_freeze`, `_INITIAL/_DEFAULTS`, `__init__→reset→__constructor_seed`. Establish `CanonicalGlobals`, `HeapWF`, `BalanceRep` for every b and closed default/order getter witnesses. No constant ideal constructor.
2. **Sanitizer and evaluator:** From `BalanceRep` and allocated canonical request, execute descriptor/prototype/isProxy or exact-dict admission, sanitizer recursion, copy/set/seen and error-free payload. Python amount is `.pyInt n→.pyFloat n`; TS stays `.jsNumber n`. Execute actual tokenizer, shared recursive cursor cells, precedence parser and `booleanWorld`/`_boolean` on the fixed guard/effect/invariant strings. The guard evaluator runs for every safe signed n. The effect evaluator, its `b-n` arithmetic and safe-intermediate facts run **only after** guard success, under `n>0`; the invariant evaluator runs only after bounds success. On `n≤0`, prove source guard-return/rollback/finally directly, including `b=S,n=-S`, for which `b-n=2S` is outside the target safe range but is never evaluated. On `0<n≤b`, `0≤b-n≤S`; on `n>b` with `n≤S` and `b≥0`, `-S≤b-n<0`. Prove those two conditional subtraction facts separately. Token progress and reached exact arithmetic are symbolic in b,n. Prove these functions from `SmallStep`/generic evaluator rules, not as primitive helper contracts.
3. **Step decision and frame:** Execute transition lookup, absent-directive comparison, old-state guard, sequential effect candidate only for `n>0`, type and safe-integer checks, bounds before invariant, then actual reject/accept closure. Derive guard/bounds codes, decoded-content equality on rejection, accepted one-record history and pre-call savepoint on both targets, and `finally` busy false. Retain actual violation/trace object construction before projecting messages/traces away. `logicalChecker` currently returns raw `history : List TargetValue` and `undo : Option ObjRef`; use the **separate checked `balanceView` content decoder** for history records/savepoint/seed. Prove `HeapWF` for both postheaps before comparing the decoded views. Rejection may allocate fresh context/history clones and different frozen metadata; `after = before` is a claim about dereferenced Ready/b, empty history, no undo, seed b and busy false, never raw `ObjRef` or `List TargetValue` equality. `finally` preserves the saved `StmtOutcome.control` even when the frame's control field was cleared before cleanup.
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

Python's record contains sanitized `.pyFloat n`, while the input recipe begins `.pyInt n`. `balanceView` must check one-key descriptor contents, exact record keys/payload shape, record fields and savepoint contents after dereferencing, and reject malformed heaps. It may omit physical clone identity/frozen bits from its result **only after** `HeapWF` and source execution have checked those operations. Pre/post view-equality lemmas derive `HeapWF lang machine` and `HeapWF lang out.machine` from actual execution, rather than assuming a favorable output heap. A body theorem derives this view; it cannot assume it for an arbitrary machine. The final theorem shape is:

```lean
theorem k02_balance_one_call (lang : TargetLang) (source : String)
    (program : TargetProgram)
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ S) (hn : -S ≤ n ∧ n ≤ S) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed lang b) = .ok machine ∧
      HeapWF lang machine ∧
      BalanceRep lang b machine ∧ balanceView lang machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest lang n) = .ok out ∧
      HeapWF lang out.machine ∧
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

In the actual Lean theorem qualify `balanceRaw`, `balanceCandidate`, `interpret` and `S` according to their modules. The theorem has no target-result, parser-correctness or heap-representation premise beyond the exact checked certificate; constructor, step success and both heap well-formedness facts are conclusions. `after = before` on both rejection paths compares only dereferenced logical data. The actual K-02 rollback/`finally` code makes Ready/b, empty history, no undo, constructor seed b and busy false equal even when physical context/history object identities and frozen flags differ. Do not use raw history values or undo references to prove this equality.

The trusted boundary is the declared restricted source-language model of basic JS/Python primitives on canonical data, externally checked serialization/byte provenance, and Node/CPython as implementations of those specified operations. `JSON.parse`/`json.loads`, exact regex matching, copying, descriptors, `MappingProxyType`, numeric tagged conversion and object identity have explicit contracts. **No assumption says Kadmos's evaluator, sanitizer, bounds, invariant, constructor or step helper is correct.** A full-language or runtime-implementation theorem remains deferred.

## Smallest feasible probe and next review

Private `/private/tmp/t398-option1-tiny.lean` (not staged) compiles with `lake env lean`: an independent `TinySurface` rule and `tinyValidate_sound` establish a token-to-AST mapping for the actual `balance - event.amount` expression; closed kernel checks confirm the existing TS/Python expression decoder returns that AST. A second closed kernel fact writes a mutable `CellRef` through a captured address and reads the changed value through the original address. The probe uses neither `native_decide` nor admitted axioms. It establishes **only** the shape of one syntax and heap lemma; it does not certify a whole file, a helper, a constructor or a dynamic step. Parent preflights this strategy before expensive proof implementation; current PR #5 remains draft and unmergeable.
