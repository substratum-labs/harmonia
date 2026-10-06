# T-396 Stage3c: generated implementation correspondence design

Status: R1 Grok REVISE design correction for parent-owned physical R2 preflight; no product, test or CI implementation has begun. Parent's review of `e253b774475dde8b7a6d4f814e6bbb57edfe66b5` required a dynamic generated `step` theorem. That review was **not** a Grok REVISE/strike. Owner: physical Codex thread `01a11179-2107-7842-8ea3-adaac2c2993a`, native worktree `/Users/yong/.codex/worktrees/5b89/harmonia`, branch `feat/t396-generated-correspondence`, Harmonia base `bcf44916b5cedf351a78e715470c351ddc84a2ad`. Parent owns Grok, publication and integration. Actual physical Grok R1 completed exit 0 in 873.2 s with structured success and `REVISE`; route 2 remains viable. Product execution waits for parent-owned R2 ACCEPT.

## Goal and acceptance boundary

The two user goals are proving Harmonia model properties and proving actual emitted program behavior corresponds to that model. Stage3b proves that an actual parsed Kadmos WorldSpec projects to a certified Lean `World`; it explicitly leaves emitted TypeScript/Python unproved. T-396 acceptance requires (1) default construction and getters for both emitted balance/order checkers and (2) a **universal dynamic balance DEBIT step correspondence theorem for each emitted TS and Python checker**. Constructor/getter proof alone is insufficient. The theorem is about a restricted **source-language operational semantics of the recognized emitted code**, with the host Node/CPython implementation of primitive operations separately stated as an external boundary. No test-only equality or copied reference interpreter substitutes for it.

For the step theorem, let `S = 9007199254740991`, `0 ≤ b ≤ S`, `-S ≤ n ≤ S`. The current target state is `Ready` with one integer context entry `balance=b`, a valid ordinary own-data request has `transitionId="DEBIT"`, `eventPayload={amount:n}`, and no `proposedDirective` property. TS permits only a canonical ordinary non-proxy object with the required own data descriptors and a canonical ordinary payload object; Python permits only exact built-in `dict` objects with string keys, each containing only the named entries. There are no extras, accessors, callbacks, shared/cyclic objects, non-finite/fractional numbers, bool-as-number, signed negative zero or inherited properties. Current target store is well-formed, `busy=false`, `history=[]`, `undo=none`, and one typed bounded balance; its phase/context relation to the source state is a **prestate** condition, not a demanded outcome. `n ≤ 0` yields `GUARD_FAILED` and preserves `b`; `0 < n ≤ b` accepts with `b-n`; `n > b` yields `INVALID_BOUNDS` and preserves `b`. In every case current state is `Ready`, directive is null, and normalized allow/state/context/directive equals `interpret BridgeFixtures.balanceCandidate (generatedBalanceState b) (generatedBalanceRequest n)`. The theorem quantifies over every such `b,n` and related prestore, not only the finite probes. Prove the three model cases as Lean lemmas rather than assume them as premises. For `n>0`, `b-n ∈ [-S,S]` automatically, including the rejected negative candidate; for `n≤0` the effect is not evaluated. This avoids the real unsafe-intermediate divergence without pretending arbitrary expressions are safe.

The first theorem does not cover other transition IDs/directives, arbitrary requests, reset overrides, savepoint/rollback API calls, reentrancy, error messages/history content or generic worlds. Order `STEP` remains finite physical step evidence; order construction/getters are planned kernel obligations, not yet proved. Rejected `step` preserves logical checker data (`Ready`, balance `b`, empty history, absent undo) and ends with `busy=false`; rollback may allocate fresh context/history objects, so physical heap identity and frozen metadata are **not** framed. On success TS stores the pre-call snapshot in `#undo` and pushes a frozen logical record; Python retains `undo=none` and pushes a record whose sanitized amount is tagged `.pyFloat`. The observation projection drops messages and counterexample traces with explicit justification that they cannot affect this one call's allow/state/context/directive.

## Pinned source and observed emitted behavior

Harmonia base and toolchain: `bcf44916b5cedf351a78e715470c351ddc84a2ad`, `leanprover/lean4:v4.16.0`. Read-only Kadmos: `/Users/yong/projects/substratum/kadmos` at `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`. Actual `parseWorldSpec` and `compileWorldSpec` in `src/world_compiler.ts`, `compileWorldSpecPython` in `src/python_compiler.ts`, compiled using the pinned checkout's installed `tsc` into `/private/tmp/t396-probe/kadmos-js`. The two Stage3b tracked YAML/profile/parser records and `Harmonia.Applications.Kadmos.BridgeFixtures.balance_certificate` bind the source side. The actual emitted `worldCheckerTs`/`worldCheckerPy` and ports were generated and executed from private tmp; their exact fingerprints, traces and new boundary probes are in the verification record. These observations do not certify helper semantics.

Actual balance path, in execution order:

| Stage | TS source construct | Python source construct | Required formal behavior |
| --- | --- | --- | --- |
| request shape/copy | own descriptors, proxy/array/accessor checks, `sanitizeWorldPayload`, `Object.getOwnPropertyNames`, `Object.defineProperty` | `type(request) is dict`, `dict.items`, `sanitize_world_payload`, `type(raw) is dict` | Canonical shape takes the success branches; copying retains exactly `amount:n`. No sanitizer is a primitive or assumed correct. |
| transition/directive | `.find((item) => item.id === action && item.from === state)`, null-normalized directive comparison | `next((item for ...), None)`, directive comparison | First/only `DEBIT` from Ready, directive null. |
| guard | `evaluateWorld("event.amount > 0", env(oldState,oldContext))` | `evaluate_world(...)` | Eager token/Pratt path reads copied amount, checks numeric `n > 0`, maps false to guard rejection. |
| candidate/effect | clone current context; anchored effect regex; `evaluateWorld("balance - event.amount", env(transition.to,candidate))`; integer/safe check; candidate assignment | `dict(original_context)`; `_EFFECT.fullmatch`; `evaluate_world`; `_safe_integer`; `int(value)`; candidate assignment | Target phase is Ready; old candidate balance read, exact subtraction for `n>0`, one ordered effect. Wrong type/error branches cannot fire in domain. |
| postchecks/publication | `checkBounds(candidate)`, `checkInvariants(transition.to,candidate,payload)`, rollback/reject or assign `#state/#context/#history` and return verdict | `_bounds`, `_invariant`, rollback/reject or assign `state/context/history` and return verdict | Bounds checks safe integer then min=0/max=S; negative candidate rejects before invariant; nonnegative candidate satisfies `balance >= 0`, then publishes. |

`evaluateWorld`/`evaluate_world` are generated user-defined Pratt evaluator bodies, not language primitives. TS uses JS `Number`; Python `_number` converts to float, with `_safe_integer` and `int` at effect publication. Their source bodies eagerly evaluate binary operands; numeric result checks differ from Lean outside this domain. Sanitizer, bounds and invariant helpers are likewise user-defined. The body of every helper **reached by the canonical balance path**, plus its call site and return/error routing, must be parsed/validated and receive independent formal execution semantics. The fourth tracked expression, order initial invariant `state == 'B' => y == x`, runs through the same evaluator during constructor certification and requires its own token/quote `slice`/`replace`, string equality, eager implication and generated `booleanWorld`/`_boolean` helper path proof. Type declarations alone impose no runtime constraints. Terminal selection and wrong action/directive branches may be present in the recognized code but are not taken in the theorem domain; their syntax/control-flow order is still checked, with no behavioral theorem for those branches.

## Options and ruling: how emitted text earns semantics

1. **Whole existing compiler plus JS/Python semantics:** strongest eventual assurance, too large for this stage (regex, descriptors/proxies, Python object model, exceptions, history, exact number behavior, emission). It would conflate project scope with a language verification effort.
2. **Per-artifact checked restricted target-language translation validation (chosen):** a Lean parser consumes the **complete source string**, decodes embedded data, validates the fixed nonselected suffix/prefix, and constructs syntax trees for constructor/getters and the selected `step` plus reached helper bodies. The parser is syntax directed: each recognized `let`/assignment/condition/loop/call/return/try-catch and expression operator creates its corresponding target AST node; calls have checked targets and argument order. An independently stated `SourceParses lang source program` grammar relation records the exact token spans, call targets, statement order and AST node for each selected construct; prove `parseGenerated_sound : parseGenerated lang source = .ok program → SourceParses lang source program`. An independently specified `SurfaceExec` gives the recognized source forms their control/effect behavior; prove `desugar_preserves` into the target AST execution relation for `.find/.some/.map`, Python `next`/generators and switch. A separate small-step/evaluation relation executes the resulting nodes, including reached helper bodies. This soundness theorem is about the restricted source grammar and parsed AST, not Node/CPython execution. The theorem proceeds by source-program execution and a simulation with Bridge `interpret`. A mere fixed-text match of a helper followed by an idealized `guardCheck` or `boundsCheck` macro is forbidden. Exact untouched text can guard *unexecuted* sections only; those sections receive no semantics theorem. Cost: substantial parser/semantics work even for one action and an explicit primitive host boundary.
3. **Certified restricted backend:** would produce a target with easier proof, but it is an alternative compiler and a material integration change. Do not silently replace Kadmos's existing output. Parent must explicitly choose it if route 2 cannot produce a genuine step theorem after preflight.

The R1-corrected route attempts a bounded **program-slice** formalization rather than a whole-language parser. Feasibility is conditional on representing every reached construct in the parser and operational semantics; failure at that gate is a concrete blocker, not permission to claim the constructor slice as T-396 completion. Source text is segmented only at exact grammar delimiters; lexing/quoting and embedded JSON are checked in Lean. All executable constructs on the selected balance call graph are parsed to a low-level AST and covered by the independent `SourceParses` relation; unsupported statement forms, unmatched calls, changed operators/order, duplicate definitions, altered helper bodies or unconsumed bytes fail certification. This includes `step`, `evaluateWorld`/`evaluate_world` including their tokenizer/precedence/parser loop paths for the four tracked expressions (three balance expressions and the order constructor invariant), sanitizer's canonical branch, bounds, invariants, Python `_freeze` and `reset` on default construction, TS `deepFreezeWorld` on accepted history record **and on cloned rejection trace records**, and getter/constructor methods. Standard `structuredClone`/`copy.deepcopy` on the canonical finite record are basic copy primitives with explicit finite-tree rules; they are not assumed to preserve arbitrary host objects. A lexer/regex primitive may be used only with an **explicitly defined restricted matching relation** for these concrete patterns; no axiom that the helper evaluator/sanitizer/bounds checker behaves ideally. Exact fixed helper source text may help recognition, but formal execution must be by the resulting statement/expression trees. Tokenization of all four fixed expressions is proved from parsed tokenizer operations, not supplied by the exporter. The supported source-language semantics use an explicit mutable object/cell heap, checked own-data lookup, integer/float exact-domain arithmetic, booleans, exceptions/early returns, and store updates. Only basic host primitive implementation of those specified operations is outside the kernel theorem.

## Exact emitted-data, syntax and machine interfaces

The emitted world is an **ordered JSON object**, not `Bridge.RawWorld`. Define a neutral `JSONValue` with `.null`, `.bool`, `.integer`, `.string`, `.array`, `.object (List (String × JSONValue))`. For the two pinned fixture profiles only, `emittedWorldData (raw : Bridge.RawWorld) : Except CertError JSONValue` emits exactly root keys `version,name,states,context,invariants,transitions` in source order. Context is an ordered object (`balance` definition keys `type,min,max,default`; order definitions likewise); `states`/invariants/transitions are ordered arrays. Transition keys are exactly `id,from,to,guard,directive,effects` for the pinned emitted records; invariant keys are `id,predicate`. Omit absent descriptions, unit/default/bounds and **false** initial/terminal keys according to the pinned fixture normal form; preserve `initial:true` on the initial state, `directive:null`, string guard in balance, JSON boolean `true` guard in order. There is no `fields`, `extras`, flattened context, or synthesized `terminal:false`. `RawState` cannot distinguish omitted from explicit false, so `emittedWorldData` is a *fixture-profile normal form* checked against the exact two source artifacts, not a general WorldSpec reconstruction theorem. Parse actual TS `const world = <JSON> as const` and Python `_freeze(json.loads(<normal Python string literal>))` to neutral JSON; the Python JSON string unescaper differs from raw `_TOKEN`/`_EFFECT` regex literal parsing. Match actual omission and key order before converting numbers to `.jsNumber` or `.pyInt` heap values. A changed presence bit or guard JSON type fails certification even if a hash is recomputed.

The following schemas replace the prior value-snapshot closures and list-only objects. Names in backticks are stable interfaces; implementation may split files by responsibility but may not change their meaning. `ObjRef`, `CellRef` and `ClosureRef` are distinct `Nat` wrappers; lexical frame stack positions are managed by `TargetMachine.frames`. `TargetValue` is `.undefined | .null | .bool Bool | .num NumberTag Int | .string String | .ref ObjRef | .closure ClosureRef | .builtin BuiltinId | .match MatchValue`; `NumberTag = jsNumber | pyInt | pyFloat`. `MatchValue` has `full`, `start`, `end`, `groups : List String`; TS `effect.match` exposes groups 1/2, Python `_EFFECT.fullmatch` exposes `.group(1/2)`, and token regex matching returns token spans/arrays. `Descriptor = {value : TargetValue, get : Option ClosureRef, set : Option ClosureRef, enumerable : Bool, writable : Bool, configurable : Bool}`. `HeapObject = {kind : jsOrdinary | jsArray | jsSet | pythonDict | pythonList | pythonTuple | pythonSet | mappingProxy | regexPattern, prototype : objectPrototype | nullPrototype | other, own : List (String × Descriptor), items : List TargetValue, members : List TargetValue, frozen : Bool}`. `ObjectHeap` contains `nextRef` and a finite map of objects; `CellHeap` contains `nextCell` and a finite map `CellRef → TargetValue`. `isFrozen`, `freeze`, property descriptors, prototype checks, set identity and `deepFreezeWorld` recursion read/update these records; none is assumed always true/false. `structuredClone` and `copy.deepcopy` are **basic library primitives with explicit finite-tree contracts** for the canonical one-record/no-cycle domain, allocating new references. Prove that these contracts suffice for reached calls, and leave arbitrary host objects outside scope.

`ParamSpec = {name : String, defaultExpr : Option TargetExpr}`; `TargetFunction = {qualifiedName : String, params : List ParamSpec, captures : List String, body : List TargetOp}`. Qualified lexical paths distinguish `WorldChecker.step.rollback` from `WorldChecker.reset.rollback` and `sanitize_world_payload.copy` from imported Python `copy.deepcopy`. A closure stores `(qualifiedName, List (String × CellRef))`: it captures **cell addresses**. `letLocal` allocates a fresh cell for each activation; `assignLocal` writes that cell; nested recursive `parse` calls get fresh parameter/local cells while sharing captured TS `index` or Python `position` cells, token arrays, `seen` set reference and budget cells where the source captures/mutates them. Globals and module aliases are separate cells/values in `TargetMachine`; host bindings resolve only to a fixed `BuiltinId` allowlist. No `callStack : List String` or copied `List (String × TargetValue)` can implement this.

`TargetExpr` constructors are `literal`, `local`, `checkerField`, `property`, `optionalProperty`, `index`, `call`, `lambda`, `primitive (PrimOp, List TargetExpr)`, `postIncrement CellRef`, and **lazy** `andThen`, `orElse`, `nullCoalesce`, `conditional`. `postIncrement name` reads the current cell, writes value+1, and returns the **old** value for `tokens[index++]`; the latter four lazy forms evaluate only the selected operand/branch and return the source-language value, not an eagerly computed Bool. `PrimOp` is restricted to basic JS/Python operations, with individually specified input/output/error rules: strict/typed equality and `ne`, `lt/le/gt/ge`, `add/sub/mul/div/unaryNeg`, `typeofName`, `isFinite/isInteger/isSafeInteger/abs`, string `join/replaceWhitespace/startsWith/slice`, `regexTest/regexMatch`, `arrayIndex/arrayPush/length`, `getProperty/getOrDefault/hasOwn/ownDescriptor/ownKeys/defineOwn`, `objectCopy/emptyObject/toStringTag/prototypeOf/isArray/isProxy`, `freeze/isFrozen`, `newSet/setHas/setAdd/setSize`, `entries`, `toFloat/toInt`, `deepCopy`, `newError`, and `isinstanceSequence`. `regexMatch` returns the stated `MatchValue` or token-array reference, **never merely Bool**; the pinned effect yields `some ("balance", "balance - event.amount")`. `ownDescriptor` yields a descriptor value with visible `value/get/set` fields. `exprDo` evaluates calls such as `rollback()`, `seen.add`, `history.push` for their effects. No user-defined helper is a `PrimOp`.

`TargetOp` is `letLocal`, `assignLocal`, `assignField`, `assignProperty`, `ifThenElse`, `forDo`, `whileDo`, `switchCases`, `tryCatchFinally`, `exprDo`, `returnValue`, `throwValue`, `rethrow`, `breakTarget`, `continueTarget`. A loop/switch has a fresh lexical `ControlId`. `ControlResult = normal | returned TargetValue | broke ControlId | continued ControlId | raised TargetValue`. `returnValue` inside `forDo`/`whileDo` propagates to the *enclosing function*; `breakTarget`/`continueTarget` are consumed only by their matching loop/switch. The emitted evaluator's `switch` `break` exits its switch, then the surrounding Pratt `while` continues; it must not become `breakLoop`. `tryCatchFinally` evaluates a return operand before the finalizer, runs the finalizer (including `busy=false`), then propagates the saved return/exception unless the finalizer itself exits. `.find`/`.some`/`.map`, Python `next`/generator/list comprehension, and for-of/two-name `for` desugar to these operations with **proved meaning preservation**; callback return becomes selected-result assignment plus targeted loop break, while ordinary function returns remain function returns.

`TargetFrame = {function : String, remaining : List TargetOp, locals : List (String × CellRef), captured : List (String × CellRef), control : ControlResult}`. `TargetMachine = {globals : List (String × CellRef), frames : List TargetFrame, cells : CellHeap, heap : ObjectHeap, checker : TargetStore, fuel : Nat}`. `TargetStore = {state : String, context : ObjRef, history : ObjRef, undo : Option ObjRef, busy : Bool}`; Python `undo` is an explicit ghost `none`. `TargetRequest = {lang : TargetLang, shape : ordinaryRecord | exactDict, action : String, amount : Int, proposedDirective : Option String, extraFields : List (String × TargetValue), proxy : Bool, accessor : Bool}` is an **allocation recipe**, not a post-sanitized payload. `installRequest : TargetMachine → TargetRequest → TargetMachine × TargetValue` allocates a fresh `jsOrdinary` TS object with `Object.prototype` and own data descriptors in `transitionId,eventPayload` order plus a fresh ordinary payload `amount`, or fresh `pythonDict` objects with those same keys. The canonical recipe sets action DEBIT, `proposedDirective=none` meaning the property is **absent** (explicit null is outside this recipe), no extras/proxy/accessors; TS `amount` starts `.jsNumber n`, Python starts `.pyInt n`. The executed Python sanitizer converts it to `.pyFloat n`; `_number` and subtraction use `.pyFloat`; `int(value)` stores `.pyInt (b-n)`. TS retains `.jsNumber`. `targetStoredNumber .ts n = .num .jsNumber n`, `.python n = .num .pyInt n`. Exactness lemmas cover Python conversion for **all** safe signed `n` (guard includes negative input) and `b-n` on the taken positive branch.

`TargetObservation = {allowed : Bool, previousState : String, currentState : String, context : ObjRef, directiveAllowed : Option String, violationCode : Option String, trace : Option ObjRef}`. `TargetResult = {machine : TargetMachine, observation : TargetObservation}`. `logicalChecker : TargetMachine → CheckerData` projects state and dereferenced ordered context/history/undo **logical values**, ignoring object identity/frozen bits only after the executed helpers finish; `logicalObservation` dereferences observation context and retains allow/current-state/context/directive. History records include the sanitized payload and proposed-directive presence bit. TS rejection computes `structuredClone` plus `deepFreezeWorld` for its returned trace before the projection discards that trace; Python rejection performs its `copy.deepcopy` record path. The theorem must establish these calls terminate without altering the logical frame, not skip them. `targetGetState`/`targetGetContext` return `Except TargetError (TargetMachine × TargetValue)` so a newly allocated getter copy lives in the returned heap. Prove the returned context reference differs from checker context on this domain and has equal logical entries.

`TargetProgram` contains `lang`, neutral `worldData : JSONValue`, `moduleInit : List TargetOp`, `classFields : List TargetOp`, `functions : List TargetFunction`, `constructor/getState/getContext : List TargetOp`, and `step : Option (List TargetOp)`. Parse and execute module globals and aliases before TS class fields/constructor or Python `__init__`: TS `world`, `contextDefinitions`, `stateDefinitions`, imported `nodeTypes.isProxy` (including `nodeTypes?.isProxy` optional lookup); TS fields `#state/#context/#history/#undo/#busy`; Python `_WORLD`, `_INITIAL`, `_DEFAULTS`, `_PRECEDENCE`, `_TOKEN`, `_NAME`, `_EFFECT`, `_MAX_INTEGER`, `_UNDEFINED`, imported `copy` and `re/types/json/math`; `_UNDEFINED = object()` allocates a distinct sentinel reference. Python `_freeze`, `next(state.get("initial"))`, default 100 mapping, `reset`, `_bounds`, `_invariant` and parsed getters/aliases are reached. `from __future__`, imports, Python `nonlocal`, f-strings/raw regex strings and TS `import type`, value aliases, generics, annotations, `as`/`as const`, `implements`, `private`, `readonly`, `!`, and `#fields` are consumed with specified erasure or binding rules; none is silently skipped. Python default expressions are evaluated when a function is **defined**; JS defaults are evaluated per call for omitted **or `undefined`** actual arguments. `sanitizeWorldPayload(raw,depth=0,seen=new Set())` therefore allocates a fresh set at each one-argument call. Calls with 0/1/2/3 actual arguments in the reached graph are accepted by these rules, not strict parameter-count equality.

The concrete core syntax and value declarations are:

```lean
structure ObjRef where id : Nat deriving DecidableEq
structure CellRef where id : Nat deriving DecidableEq
structure ClosureRef where id : Nat deriving DecidableEq
structure ControlId where id : Nat deriving DecidableEq
inductive NumberTag | jsNumber | pyInt | pyFloat deriving DecidableEq
inductive BuiltinId
  | nodeIsProxy | objectHasOwn | objectOwnDescriptor | objectOwnNames
  | objectPrototypeOf | objectCreate | objectDefineProperty | objectFreeze
  | objectIsFrozen | objectToStringTag | numberIsSafeInteger
  | numberIsFinite | arrayIsArray | structuredClone | setConstructor
  | pythonType | pythonDict | pythonList | pythonTuple | pythonSet
  | pythonIsinstance | pythonFloat | pythonInt | pythonMathIsfinite
  | pythonRegexCompile | pythonJsonLoads | pythonMappingProxy
  | pythonDeepcopy
inductive TargetValue
  | undefined | null | bool (value : Bool)
  | num (tag : NumberTag) (value : Int) | string (value : String)
  | ref (object : ObjRef) | closure (id : ClosureRef) | builtin (id : BuiltinId)
  | match (full : String) (start stop : Nat) (groups : List String)
inductive PrimOp
  | strictEq | typedEq | ne | lt | le | gt | ge
  | add | sub | mul | div | unaryNeg | typeofName
  | isFinite | isInteger | isSafeInteger | abs
  | stringJoin | replaceWhitespace | startsWith | slice
  | regexTest | regexMatch | arrayIndex | arrayPush | length
  | getProperty | getOrDefault | hasOwn | ownDescriptor | ownKeys
  | defineOwn | objectCopy | emptyObject | toStringTag | prototypeOf
  | isArray | isProxy | freeze | isFrozen | newSet | setHas | setAdd | setSize
  | entries | toFloat | toInt | deepCopy | newError | isinstanceSequence
inductive TargetExpr
  | literal (value : TargetValue) | local (name : String)
  | checkerField (name : String) | property (base : TargetExpr) (name : String)
  | optionalProperty (base : TargetExpr) (name : String)
  | index (base key : TargetExpr)
  | call (callee : TargetExpr) (args : List TargetExpr)
  | lambda (qualifiedName : String)
  | primitive (op : PrimOp) (args : List TargetExpr)
  | postIncrement (name : String)
  | andThen (left right : TargetExpr) | orElse (left right : TargetExpr)
  | nullCoalesce (left right : TargetExpr)
  | conditional (test yes no : TargetExpr)
inductive TargetOp
  | letLocal (name : String) (value : TargetExpr)
  | assignLocal (name : String) (value : TargetExpr)
  | assignField (name : String) (value : TargetExpr)
  | assignProperty (base key value : TargetExpr)
  | ifThenElse (test : TargetExpr) (yes no : List TargetOp)
  | forDo (id : ControlId) (binder : List String) (values : TargetExpr)
      (body : List TargetOp)
  | whileDo (id : ControlId) (test : TargetExpr) (body : List TargetOp)
  | switchCases (id : ControlId) (scrutinee : TargetExpr)
      (arms : List (TargetValue × List TargetOp))
  | tryCatchFinally (body : List TargetOp) (errorName : String)
      (handler finalizer : List TargetOp)
  | exprDo (value : TargetExpr) | returnValue (value : TargetExpr)
  | throwValue (value : TargetExpr) | rethrow
  | breakTarget (id : ControlId) | continueTarget (id : ControlId)
inductive ControlResult
  | normal | returned (value : TargetValue)
  | broke (id : ControlId) | continued (id : ControlId)
  | raised (value : TargetValue)
structure ParamSpec where
  name : String
  defaultExpr : Option TargetExpr
structure TargetFunction where
  qualifiedName : String
  params : List ParamSpec
  captures : List String
  body : List TargetOp
```

`BuiltinId` is a closed enumeration of reached standard library calls (`Object`/`Number`/`Array`/`Set`/`RegExp`, Node `nodeTypes.isProxy`, Python `dict`/`type`/`float`/`int`/`math`/`re`/`json`/`types`/`copy.deepcopy`); each member has a specified canonical-domain contract. `PrimOp` is the *closed* operation list in the preceding paragraph. `TargetValue.match` and heap arrays give the actual match/index/group shapes; no Boolean-only regex result is accepted. The parser allocates deterministic `ControlId`s and lexical names, then proves an inductive `SourceParses` relation for them. This block is the agreed signature target; Lean declaration order and mutual-inductive syntax are implementation details, not license to change the semantics.

The machine and public request/result records are:

```lean
inductive ObjectKind
  | jsOrdinary | jsArray | jsSet | pythonDict | pythonList | pythonTuple
  | pythonSet | mappingProxy | regexPattern
inductive PrototypeTag | objectPrototype | nullPrototype | other
structure Descriptor where
  value : TargetValue
  get : Option ClosureRef
  set : Option ClosureRef
  enumerable : Bool
  writable : Bool
  configurable : Bool
structure HeapObject where
  kind : ObjectKind
  prototype : PrototypeTag
  own : List (String × Descriptor)
  items : List TargetValue
  members : List TargetValue
  frozen : Bool
structure ObjectHeap where
  nextRef : Nat
  objects : List (ObjRef × HeapObject)
structure CellHeap where
  nextCell : Nat
  cells : List (CellRef × TargetValue)
structure TargetStore where
  state : String
  context : ObjRef
  history : ObjRef
  undo : Option ObjRef
  busy : Bool
structure TargetFrame where
  function : String
  remaining : List TargetOp
  locals : List (String × CellRef)
  captured : List (String × CellRef)
  control : ControlResult
structure TargetMachine where
  globals : List (String × CellRef)
  frames : List TargetFrame
  cells : CellHeap
  heap : ObjectHeap
  closures : List (ClosureRef × String × List (String × CellRef))
  checker : TargetStore
  fuel : Nat
inductive RequestShape | ordinaryRecord | exactDict
structure TargetRequest where
  lang : TargetLang
  shape : RequestShape
  action : String
  amount : Int
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
structure TargetResult where
  machine : TargetMachine
  observation : TargetObservation
inductive JSONValue
  | null | bool (value : Bool) | integer (value : Int) | string (value : String)
  | array (items : List JSONValue)
  | object (entries : List (String × JSONValue))
structure TargetProgram where
  lang : TargetLang
  worldData : JSONValue
  moduleInit : List TargetOp
  classFields : List TargetOp
  functions : List TargetFunction
  constructor : List TargetOp
  getState : List TargetOp
  getContext : List TargetOp
  step : Option (List TargetOp)
```

These are logical Lean records for the restricted source language; they do not claim a physical host heap is represented byte-for-byte. `logicalChecker` dereferences `context`, `history` and `undo` and observes ordered contents. Every reference used by a successful execution has a heap entry, enforced by the machine well-formedness invariant rather than assumed by the target result.

The parser/semantics boundary is:

```lean
def parseGenerated (lang : TargetLang) (source : String) : Except ParseError TargetProgram
inductive SourceParses : TargetLang → String → TargetProgram → Prop
-- constructors describe token spans, nesting, statement order, call targets and AST nodes;
-- no constructor refers to parseGenerated.
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
-- If temporary names differ, first deterministically canonicalize lexical IDs;
-- no unchecked alpha-equivalence premise is permitted.
def targetConstruct (p : TargetProgram) : Except TargetError TargetMachine
def targetGetState (p : TargetProgram) (m : TargetMachine) :
    Except TargetError (TargetMachine × TargetValue)
def targetGetContext (p : TargetProgram) (m : TargetMachine) :
    Except TargetError (TargetMachine × TargetValue)
def targetStep (p : TargetProgram) (m : TargetMachine) (r : TargetRequest) :
    Except TargetError TargetResult
def canonicalBalanceRequest (lang : TargetLang) (n : Int) : TargetRequest
def emittedWorldData (raw : Bridge.RawWorld) : Except CertError JSONValue
def checkGenerated (lang : TargetLang) (source : String) (raw : Bridge.RawWorld)
    (w : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
    Except CertError TargetProgram
```

`SurfaceExec` is defined independently of `desugar`, with one constructor family per recognized sugar: `jsFind` visits array elements left-to-right, returns the first whose parsed predicate is truthy or undefined; `jsSome` returns true at the first truthy predicate; `jsMap` evaluates mapper in order and returns an allocated array; `pythonNext` evaluates generator predicates in order and uses its fallback only on exhaustion; `switchStmt` selects the matching arm, consumes its own `broke ControlId`, and leaves the containing `whileDo` active. In every case callback bodies are parsed qualified `TargetFunction`s with captured **cell addresses**, so a function `return` cannot be confused with a loop break. The `TargetExec` constructors separately implement each `TargetOp` and preserve the same normal/return/break/continue/raise exits. These are independent definitions and a proof obligation, not a host-source-correctness premise.

The error constructors are:

```lean
inductive ParseError
  | badLexeme (offset : Nat) | badEscape (offset : Nat) | badNumber (offset : Nat)
  | unsupportedReachedSyntax (offset : Nat)
  | missingFunction (qualifiedName : String) | duplicateFunction (qualifiedName : String)
  | wrongCall (qualifiedName : String) | wrongDefault (qualifiedName : String)
  | badEmbeddedJSON | trailingSource (offset : Nat)
inductive CertError
  | parse (error : ParseError) | bridge (error : Bridge.BridgeError)
  | dataMismatch | unsupportedProfile | shapeMismatch
inductive TargetError
  | typeError | numberError | missingProperty (name : String)
  | uncaught (message : String) | fuelExhausted | unsupportedStep
```

The two execution entry points below also fix how heap changes propagate:

```lean
def evalExpr (p : TargetProgram) (m : TargetMachine) (e : TargetExpr) :
    Except TargetError (TargetMachine × TargetValue)
def execOps (p : TargetProgram) (m : TargetMachine) (ops : List TargetOp) :
    Except TargetError (TargetMachine × ControlResult)
```
`checkGenerated` invokes the **exact dependent** `checkBridge raw w` (no cast), compares parsed neutral world against `emittedWorldData raw`, checks full-file syntax, selected qualified call graph, constructor/defaults and balance `step=some body`. For order it checks constructor/getters and exact unexecuted `step` text with `step=none`. The external exporter provides complete source string literals only, never a decoded AST or success premise. `SourceParses` is independently inductive and deterministic; checked desugaring theorems must preserve control flow, lexical cells and call effects. Exact byte/hash comparison binds those Lean literals to actual compiler output but is not semantic preservation.

## Universal theorem and concrete one-call scope

Put fixture-specific names in `Generated/BalanceStep.lean` as `generatedBalanceState (b : Int) : State 1 1 := ⟨0, fun _ => b⟩` and `generatedBalanceRequest (n : Int) : Request 1 := ⟨"DEBIT", fun _ => .int n, none⟩`; avoid shadowing `Balance.lean` or `BridgeFixtures.Tests`. `balancePreRel lang b m` constrains **only** the incoming typed/bounded checker: `Ready`, one context key `balance` with `targetStoredNumber lang b`, `history=[]`, `undo=none`, `busy=false`, valid heap references/descriptors/prototypes, module initialization complete, and adequate fixed one-call fuel. It never mentions `n`, `targetStep`, the model poststate or expected observation. Construct a witness for every bounded `b`; a state with arbitrary history/undo is **outside this first theorem**. Empty history bounds trace/deep-copy work independently of `b,n`; arbitrary-history, fuel/tree-size and multicall induction are a later slice.

Define `sourceProjection lang` from `interpret`'s verdict/state/directive and `targetProjection` from dereferenced `TargetResult` observation (allow/current state/context/directive only). Compare context **structurally**; `previousState` may be left out of this four-field carrier but its actual computation is still executed. Prove model cases symbolically from `Interpreter.lean` on actual `BridgeFixtures.balanceCandidate`: `n≤0 → .guardFalse`, `0<n≤b → accepted` with `b-n`, `n>b → .bounds 0` with frame. Do not substitute `Balance.balanceWorld`, whose guard/invariant AST differs. Prove source-language target cases by executing the parsed operations/helpers. The target theorem is:

```lean
theorem generated_balance_step_correspondence
    (lang : TargetLang) (source : String) (program : TargetProgram)
    (hc : checkGenerated lang source BridgeFixtures.balanceRaw
      BridgeFixtures.balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ S) (hn : safeInt n)
    (m : TargetMachine) (hm : balancePreRel lang b m) :
    ∃ result, targetStep program m (canonicalBalanceRequest lang n) = .ok result ∧
      targetProjection result = sourceProjection lang
        (interpret BridgeFixtures.balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n)) ∧
      result.machine.checker.state = "Ready" ∧ result.machine.checker.busy = false ∧
      (n ≤ 0 → result.observation.violationCode = some "GUARD_FAILED" ∧
        logicalChecker result.machine = logicalChecker m) ∧
      (0 < n ∧ n ≤ b → result.observation.allowed = true ∧
        logicalContext result.machine = [("balance", targetStoredNumber lang (b-n))] ∧
        acceptedHistoryShape lang n m result.machine) ∧
      (n > b → result.observation.violationCode = some "INVALID_BOUNDS" ∧
        logicalChecker result.machine = logicalChecker m)
```

`acceptedHistoryShape` is defined by logical record fields: the sole record has `step=1`, `state="Ready"`, `action="DEBIT"`, `eventPayload={amount:n}` after sanitizer tagging, and **no** `proposedDirective` key. TS undo contains the pre-call Ready/b/empty-history snapshot and history holds this frozen record; Python undo is `none` and history holds this record with `.pyFloat n`; both end busy false. It does **not** require physical pre/post heap identity. `logicalChecker` on rejection compares state/context/history/undo logical data; heap clones are permitted. `balancePreRel_exists lang b hb` proves nonvacuity for every `b`. Closed certificates for both actual balance sources, `BridgeFixtures.balance_certificate`, constructor/getter witnesses, and `b,n=(100,30),(100,130),(100,0),(0,1),(S,S)` are separate kernel probes. `decide +kernel` is for closed parser/certificate facts; the universal theorem is symbolic (`omega`, induction on executed AST/control/cells), with bounded fuel independent of `b,n`. The theorem premises contain **no** target/model result equality, helper-correctness assumption or host runtime correctness claim.

The kernel claim is about this restricted TS/Python **source-language formal semantics** and exact serialized source literal. Node/CPython's implementation of the explicit basic primitive contracts, TS type erasure, Python normal-string/regex handling as modeled, and external byte-for-byte literal provenance remain trust boundaries. The host boundary cannot state that Kadmos helpers behave like an ideal target evaluator; their reached bodies are parsed and executed. No whole-JS/Python or arbitrary-host-object correctness follows.

## Verification, hostile cases and constraints

The first physical probe already ran both emitted languages: balance 100→70, 130 rejects/preserves 70, then 20→50; order A/(1,0)→B/(2,2). A private-tmp effect mutation from subtraction to addition made both balance checkers return 130 for DEBIT 30, diagnosing a mismatch. Additional boundary probes ran `b,n=(0,0),(0,1),(100,-1),(100,30),(100,130),(S,S),(S,-S)` in both emitted languages with the expected three-way results. None of these probes is the universal theorem. Implementation must mutate selected emitted source **with recomputed digest**: reverse subtraction, change `>` to `>=`, bypass sanitizer copy, change bound comparison/order, alter invariant call, publish before postcheck, or return stale context; each must fail `checkGenerated` or yield a kernel-diagnosed mismatch. A mutation confined to an unexecuted section must fail exact whole-file recognition but provides no proof of that section. Closed nonvacuity and wrong-source probes must fail under a temporary validator bypass and pass only after restoration.

Preserve `leanprover/lean4:v4.16.0`, Init-only new applications, unchanged Core/Distributed/legacy/World/Interpreter/Bridge semantics. No Veil, mathlib, new dependency, solver IO, `native_decide`, `sorry`, `admit`, `sorryAx` or unreported custom axiom. Serial Lake. Old Kadmos inventory scans **all** Applications: register new sources. New Generated audit selects its exact product/test/audit manifest by namespace **or source module**, including escaped/unused declarations, with isolated own rejection roots. Bridge audit grows only for real import closure; never broaden it to all Applications. Keep Foundation 52 and Distributed 336/594 separate; no fixed old application/Bridge count. Hosted Linux CI runs targets serially without a sibling Kadmos checkout; local pinned-source regeneration is mandatory. Never stage `.lake/`, generated binaries/caches, credentials or machine-specific logs. No pushes/PRs/merges or other-repository edits by this owner.

The key preflight risk is whether the selected statement/helper parser and operational semantics can be completed without smuggling an idealized macro for the existing runtime. Grok must inspect the call graph, exact AST/primitive boundary, dependent certificate type and universal proof obligations. If the parser cannot account for any helper branch taken by the canonical balance request, **no step-correctness claim is allowed**: parent must choose a larger formalization or explicitly authorize a certified restricted backend; constructor-only work can stand as a partial result but does not complete T-396. Actual R1 returned REVISE. Parent-owned physical R2 ACCEPT is the next gate; this corrected document has not received that verdict.
