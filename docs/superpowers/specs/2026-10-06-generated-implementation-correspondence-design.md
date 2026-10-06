# T-396 Stage3c: generated implementation correspondence design

Status: corrected investigation/design for parent-owned physical Grok preflight; no product, test or CI implementation has begun. Parent's review of `e253b774475dde8b7a6d4f814e6bbb57edfe66b5` required a dynamic generated `step` theorem. That review was **not** a Grok REVISE/strike. Owner: physical Codex thread `01a11179-2107-7842-8ea3-adaac2c2993a`, native worktree `/Users/yong/.codex/worktrees/5b89/harmonia`, branch `feat/t396-generated-correspondence`, Harmonia base `bcf44916b5cedf351a78e715470c351ddc84a2ad`. Parent owns Grok, publication and integration. Product execution waits for actual Grok preflight ACCEPT.

## Goal and acceptance boundary

The two user goals are proving Harmonia model properties and proving actual emitted program behavior corresponds to that model. Stage3b proves that an actual parsed Kadmos WorldSpec projects to a certified Lean `World`; it explicitly leaves emitted TypeScript/Python unproved. T-396 acceptance requires (1) default construction and getters for both emitted balance/order checkers and (2) a **universal dynamic balance DEBIT step correspondence theorem for each emitted TS and Python checker**. Constructor/getter proof alone is insufficient. The theorem is about a restricted **source-language operational semantics of the recognized emitted code**, with the host Node/CPython implementation of primitive operations separately stated as an external boundary. No test-only equality or copied reference interpreter substitutes for it.

For the step theorem, let `S = 9007199254740991`, `0 ≤ b ≤ S`, `-S ≤ n ≤ S`. The current target state is `Ready` with one integer context entry `balance=b`, a valid ordinary own-data request has `transitionId="DEBIT"`, `eventPayload={amount:n}`, and no `proposedDirective` property. TS permits only a canonical ordinary non-proxy object with the required own data descriptors and a canonical ordinary payload object; Python permits only exact built-in `dict` objects with string keys, each containing only the named entries. There are no extras, accessors, callbacks, shared/cyclic objects, non-finite/fractional numbers, bool-as-number, signed negative zero or inherited properties. Current target store is well-formed, not busy, with empty prior history and no savepoint; its phase/context relation to the source state is a **prestate** condition, not a demanded outcome. `n ≤ 0` yields `GUARD_FAILED` and preserves `b`; `0 < n ≤ b` accepts with `b-n`; `n > b` yields `INVALID_BOUNDS` and preserves `b`. In every case current state is `Ready`, directive is null, and normalized allow/state/context/directive equals `interpret balanceCandidate (balanceState b) (balanceRequest n)`. The theorem quantifies over every such `b,n` and related prestore, not only the finite probes. Prove the three model cases as Lean lemmas rather than assume them as premises. For `n>0`, `b-n ∈ [-S,S]` automatically, including the rejected negative candidate; for `n≤0` the effect is not evaluated. This avoids the real unsafe-intermediate divergence without pretending arbitrary expressions are safe.

The first theorem does not cover other transition IDs/directives, arbitrary requests, reset overrides, savepoint/rollback API calls, reentrancy, error messages/history content or generic worlds. Order `STEP` remains finite physical step evidence; order construction/getters are kernel checked. Rejected `step` preserves the complete modeled checker state including the initially empty history and absent undo (except transient busy, which resets); the observation projection drops messages and counterexample traces with explicit justification that they cannot affect this one call's allow/state/context/directive.

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

`evaluateWorld`/`evaluate_world` are generated user-defined Pratt evaluator bodies, not language primitives. TS uses JS `Number`; Python `_number` converts to float, with `_safe_integer` and `int` at effect publication. Their source bodies eagerly evaluate binary operands; numeric result checks differ from Lean outside this domain. Sanitizer, bounds and invariant helpers are likewise user-defined. The body of every helper **reached by the canonical balance path**, plus its call site and return/error routing, must be parsed/validated and receive independent formal execution semantics. Type declarations alone impose no runtime constraints. Terminal selection and wrong action/directive branches may be present in the recognized code but are not taken in the theorem domain; their syntax/control-flow order is still checked, with no behavioral theorem for those branches.

## Options and ruling: how emitted text earns semantics

1. **Whole existing compiler plus JS/Python semantics:** strongest eventual assurance, too large for this stage (regex, descriptors/proxies, Python object model, exceptions, history, exact number behavior, emission). It would conflate project scope with a language verification effort.
2. **Per-artifact checked restricted target-language translation validation (chosen):** a Lean parser consumes the **complete source string**, decodes embedded data, validates the fixed nonselected suffix/prefix, and constructs syntax trees for constructor/getters and the selected `step` plus reached helper bodies. The parser is syntax directed: each recognized `let`/assignment/condition/loop/call/return/try-catch and expression operator creates its corresponding target AST node; calls have checked targets and argument order. An independently stated `SourceParses lang source program` grammar relation records the exact token spans, call targets, statement order and AST node for each selected construct; prove `parseGenerated_sound : parseGenerated lang source = .ok program → SourceParses lang source program`. A separate small-step/evaluation relation executes these nodes, including reached helper bodies. This soundness theorem is about the restricted source grammar and parsed AST, not Node/CPython execution. The theorem proceeds by source-program execution and a simulation with Bridge `interpret`. A mere fixed-text match of a helper followed by an idealized `guardCheck` or `boundsCheck` macro is forbidden. Exact untouched text can guard *unexecuted* sections only; those sections receive no semantics theorem. Cost: substantial parser/semantics work even for one action and an explicit primitive host boundary.
3. **Certified restricted backend:** would produce a target with easier proof, but it is an alternative compiler and a material integration change. Do not silently replace Kadmos's existing output. Parent must explicitly choose it if route 2 cannot produce a genuine step theorem after preflight.

The proposed route attempts a bounded **program-slice** formalization rather than a whole-language parser. Feasibility is conditional on representing every reached construct in the parser and operational semantics; failure at that gate is a concrete blocker, not permission to claim the constructor slice as T-396 completion. Source text is segmented only at exact grammar delimiters; lexing/quoting and embedded JSON are checked in Lean. All executable constructs on the selected balance call graph are parsed to a low-level AST and covered by the independent `SourceParses` relation; unsupported statement forms, unmatched calls, changed operators/order, duplicate definitions, altered helper bodies or unconsumed bytes fail certification. This includes `step`, `evaluateWorld`/`evaluate_world` including their tokenizer/precedence/parser loop paths for the three concrete expressions, sanitizer's canonical branch, bounds, invariants, Python `_freeze` and `reset` on default construction, TS `deepFreezeWorld` on accepted history record, and getter/constructor methods. Standard `structuredClone`/`copy.deepcopy` on the canonical finite record are basic copy primitives with explicit finite-tree rules; they are not assumed to preserve arbitrary host objects. A lexer/regex primitive may be used only with an **explicitly defined restricted matching relation** for these concrete patterns; no axiom that the helper evaluator/sanitizer/bounds checker behaves ideally. Exact fixed helper source text may help recognition, but formal execution must be by the resulting statement/expression trees. Tokenization of the three fixed expressions is proved from parsed tokenizer operations, not supplied by the exporter. The supported source-language semantics use ordered immutable object maps, checked own-data lookup, integer/float exact-domain arithmetic, booleans, exceptions/early returns, and store updates. Only basic host primitive implementation of those specified operations is outside the kernel theorem.

## Exact interfaces and noncircular proof shape

All new types live in `Harmonia.Applications.Kadmos.Generated`. The following is the required **schema**, not an unresolved generic signature; constructors may be split into additional declarations without changing their fields/meaning. `NumberTag` is `.jsNumber | .pyInt | .pyFloat`. `TargetValue` includes `.undefined`, `.null`, `.bool Bool`, `.number (tag : NumberTag) (value : Int)`, `.string String`, and `.object (List (String × TargetValue))`, and `.array (List TargetValue)`; object lists preserve insertion order. This first numeric carrier covers exact integral values reached by the certified path; a Python float is tagged `.pyFloat` even when its exact value is integral. Primitive conversion from `.pyInt` to `.pyFloat`, arithmetic and `int` back to `.pyInt` are proved exact for the stated domain. Unsupported nonintegral/unsafe primitive outcomes fail the restricted interpreter rather than being silently identified with `Int`. `TargetExpr` includes literals, local/field reads, property/own-descriptor lookup, strict equality, numeric comparison/subtraction, boolean operations, object copy, safe-integer/type tests, regex token/assignment match with explicit restricted semantics, and calls to declared functions. `TargetOp` uses the statement constructors in the schema below, including loops, `tryCatchFinally`, return and throw; sequencing is `List TargetOp`. **No** `evaluateWorld`, `sanitizeWorldPayload`, `checkBounds`, `checkInvariants`, `interpret`, `sourceEval`, or `modelResult` constructor exists as an atomic primitive. Calls to these names resolve to parsed `TargetFunction.body` and evaluate it. `TargetFunction` has `name : String`, `params : List String`, `captures : List String`, `body : List TargetOp`. `TargetProgram` has `lang`, `worldData : TargetValue`, `functions : List TargetFunction`, `constructor`, `getState`, `getContext`, and `step : Option (List TargetOp)`; checked unique function names and lexical variables are part of parse success.

The minimal Lean data declarations are:

```lean
inductive TargetLang | ts | python deriving DecidableEq
inductive NumberTag | jsNumber | pyInt | pyFloat deriving DecidableEq
inductive TargetValue
  | undefined | null | bool (b : Bool)
  | number (tag : NumberTag) (value : Int)
  | string (value : String)
  | object (entries : List (String × TargetValue))
  | array (items : List TargetValue)
  | closure (functionName : String) (captures : List (String × TargetValue))
  deriving DecidableEq
inductive RequestShape | ordinaryRecord | exactDict deriving DecidableEq
inductive PrimOp
  | strictEq | less | greater | add | sub | boolNot | boolAnd | boolOr
  | typeofName | safeInteger | getProperty | hasOwn | ownDescriptor | ownKeys
  | objectCopy | putOwn | defineOwn | isArray | isProxy | prototypeOf
  | arrayLength | regexToken | regexEffect | toFloat | toInt
  deriving DecidableEq
inductive TargetExpr
  | literal (v : TargetValue) | local (name : String) | checkerField (name : String)
  | primitive (op : PrimOp) (args : List TargetExpr)
  | call (functionName : String) (args : List TargetExpr)
  | lambda (functionName : String)
inductive TargetOp
  | letLocal (name : String) (value : TargetExpr)
  | assignLocal (name : String) (value : TargetExpr)
  | assignField (name : String) (value : TargetExpr)
  | ifThenElse (test : TargetExpr) (yes no : List TargetOp)
  | forEach (name : String) (values : TargetExpr) (body : List TargetOp)
  | whileDo (test : TargetExpr) (body : List TargetOp)
  | breakLoop | continueLoop
  | tryCatchFinally (body : List TargetOp) (errorName : String)
      (handler finalizer : List TargetOp)
  | returnValue (value : TargetExpr) | throwValue (value : TargetExpr)
structure TargetFunction where
  name : String
  params : List String
  captures : List String
  body : List TargetOp
structure TargetProgram where
  lang : TargetLang
  worldData : TargetValue
  functions : List TargetFunction
  constructor : List TargetOp
  getState : List TargetOp
  getContext : List TargetOp
  step : Option (List TargetOp)
structure TargetRequest where
  lang : TargetLang
  shape : RequestShape
  ownData : List (String × TargetValue)
  proxy : Bool
  accessor : Bool
```

`PrimOp` has individually defined value/error/order semantics; it is **not** an escape hatch for a user helper. The actual templates may require more basic primitive cases (for example property access, object spread, or `isArray`) before source parsing succeeds; add only the concrete primitive case and rule, not a new macro for a whole helper. `regexToken` and `regexEffect` take the recognized pattern as an argument and use a proved restricted matching relation for the three fixture expressions/effect assignment. Parser output uses `TargetFunction` for the generated evaluator, sanitizer, bounds/invariant methods and the nested parser/closure bodies they call; `lambda` constructs a closure with exactly the checked capture names. Array `.find`/`.some`/`.map`, Python `next` generators and list comprehensions on the reached path are desugared to `forEach` plus `ifThenElse`/`breakLoop` with an AST equivalence lemma for the recognized source form. No selected call remains an opaque callback. A `whileDo`/recursive call must have fuel or a well-founded measure, with a theorem that the balance path has sufficient fuel for all `b,n` in the domain.

`TargetStore` has `state : String`, `context : List (String × TargetValue)`, `history : List TargetValue`, `undo : Option TargetValue`, `busy : Bool`; `TargetFrame` holds ordered locals, a call stack and checker store. `TargetRequest` is `lang`, `shape : ordinaryRecord | exactDict`, `ownData : List (String × TargetValue)`, `proxy : Bool`, `accessor : Bool`; its canonical constructor puts action and payload in that order, with payload containing only amount. `TargetObservation` and `TargetResult` have these exact fields:

```lean
structure TargetStore where
  state : String
  context : List (String × TargetValue)
  history : List TargetValue
  undo : Option TargetValue
  busy : Bool
structure TargetFrame where
  locals : List (String × TargetValue)
  callStack : List String
  checker : TargetStore
structure TargetObservation where
  allowed : Bool
  previousState : String
  currentState : String
  context : List (String × TargetValue)
  directiveAllowed : Option String
  violationCode : Option String
structure TargetResult where
  postStore : TargetStore
  observation : TargetObservation
```

A checker `TargetStore` includes all fields that rejection can restore. Any omitted generated field that can affect the selected path is a parser/semantics gap to repair before claiming the theorem. `targetStep` executes the parsed `step` operations with this request, not a separately scripted balance algorithm. `normalize` discards only code/message/history fields as stated; for this theorem it retains allow/state/context/directive, with `violationCode` separately proved to be the expected target code. All host values in the theorem are exact safe integers, so the target primitive numeric interpretation is exact; Python float conversion has a separate exactness lemma for `[-S,S]` and `b-n` on the taken branch.

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

The error interfaces are exact:

```lean
inductive ParseError
  | badToken (offset : Nat) | badEscape (offset : Nat) | badNumber (offset : Nat)
  | missingFunction (name : String) | duplicateFunction (name : String)
  | unsupportedConstruct (offset : Nat) | wrongCall (name : String)
  | trailingSource (offset : Nat) | badEmbeddedData
inductive CertError
  | parse (error : ParseError) | bridge (error : Bridge.BridgeError)
  | dataMismatch | unsupportedProfile | shapeMismatch
inductive TargetError
  | typeError | numberError | missingProperty (name : String)
  | uncaught (message : String) | fuelExhausted | unsupportedStep
```

`checkGenerated` maps `checkBridge raw w` errors and checks exact ordered embedded world data and initial/defaults; on the balance profile it also checks the supported selected step call graph. On the order profile it checks whole-file shape and construction/getters while leaving its step section unexecuted by any theorem. It cannot accept a candidate of arbitrary dimensions. No checked dimension cast is needed. For the order fixture the same dependent checker certifies construction/getters with `step = none`; `targetStep` returns `.error .unsupportedStep` there, so it grants no order-step theorem. For balance, certificate success requires `step = some body` with the parsed selected call graph. The exporter provides complete source string literals only; no predecoded AST, purported target result or certificate premise.

Put the fixture-specific theorem and `balanceState (b : Int) : State 1 1 := ⟨0, fun _ => b⟩`, `balanceRequest (n : Int) : Request 1 := ⟨"DEBIT", fun _ => .int n, none⟩` in `Generated/BalanceStep.lean`, importing `Generated/Fixtures.lean`; this avoids a certificate/fixture import cycle. Write `targetRel` against **prestate** phase/context entries, numeric type/safe bounds, inactive `busy`, and `history=[]`, `undo=none`; do not require a result or poststate. Define `sourceProjection lang` from `interpret`'s result, using `targetStoredNumber lang` for context: verdict accepted → allowed; state.phase/context → ordered target keys/values; observation.directive → target directive. Define `targetProjection` from `TargetResult` observation, checking that it agrees with the poststore. In the theorem below, `balancePreRel` and the fixture-specific projections are defined in `BalanceStep.lean`; generic parser/certificate declarations do not import fixtures. Prove, for each language, a generic cert-success constructor/getter theorem and this fixture-specific universal theorem (exact dependent dimensions are `World 1 1 1 1` for `balanceRaw`):

```lean
theorem balance_step_correspondence
    (lang : TargetLang) (source : String) (program : TargetProgram)
    (hc : checkGenerated lang source BridgeFixtures.balanceRaw
      BridgeFixtures.balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ S) (hn : safeInt n)
    (store : TargetStore) (hr : balancePreRel lang b store) :
    ∃ result, targetStep program store (canonicalBalanceRequest lang n) = .ok result ∧
      targetProjection result =
        sourceProjection lang (interpret BridgeFixtures.balanceCandidate
          (balanceState b) (balanceRequest n)) ∧
      (n ≤ 0 → result.observation.violationCode = some "GUARD_FAILED" ∧
          result.postStore.context = store.context) ∧
      (0 < n ∧ n ≤ b → result.observation.allowed = true ∧
          result.postStore.context = [("balance", targetStoredNumber lang (b-n))]) ∧
      (n > b → result.observation.violationCode = some "INVALID_BOUNDS" ∧
          result.postStore.context = store.context)
```

The theorem is nonvacuous only with closed `by decide +kernel` certificates for **both actual emitted source strings**, `balance_certificate`, explicit witnesses `b=100,n=30/130/0` and boundary witnesses `b=0,n=1`, `b=S,n=S`. `balancePreRel` must be constructible for every bounded `b` (prove `exists_balancePreRel lang b`) and must not mention `program`, `n`, `targetStep`, `interpret` result or expected observation. Prove model cases `n≤0`, `0<n≤b`, `n>b` from existing `interpret` code via reductions/`omega`; prove target cases by executing parsed AST and helper bodies. No result equality is assumed in `hc`, `hr` or host primitive assumptions. Rejection restores complete checker store; acceptable transient busy changes are internal to a call and `finally` clears them before the returned poststore.

`checkGenerated` binds the emitted string to the Bridge projection and AST. Kernel theorem is **conditional on that exact Lean source literal and the restricted target-language semantics**. A tracked exporter must regenerate the actual pinned TS/Python bytes, compare them byte-for-byte with tracked files, and prove a deterministic literal round trip before Lean compilation. This external serialization/file comparison remains a trust boundary; SHA-256 is drift evidence, not semantic preservation. The host boundary is only that Node/CPython implements the chosen primitive language operations on canonical plain values (including TS exact safe integer arithmetic and Python exact float conversion in the proved range). There is no assumption saying the generated helper implements the formal evaluator: its recognized body is executed within the formal source-language semantics. Full-language semantics, hostile objects and other expressions remain outside scope and must be stated at completion.

## Verification, hostile cases and constraints

The first physical probe already ran both emitted languages: balance 100→70, 130 rejects/preserves 70, then 20→50; order A/(1,0)→B/(2,2). A private-tmp effect mutation from subtraction to addition made both balance checkers return 130 for DEBIT 30, diagnosing a mismatch. Additional boundary probes ran `b,n=(0,0),(0,1),(100,-1),(100,30),(100,130),(S,S),(S,-S)` in both emitted languages with the expected three-way results. None of these probes is the universal theorem. Implementation must mutate selected emitted source **with recomputed digest**: reverse subtraction, change `>` to `>=`, bypass sanitizer copy, change bound comparison/order, alter invariant call, publish before postcheck, or return stale context; each must fail `checkGenerated` or yield a kernel-diagnosed mismatch. A mutation confined to an unexecuted section must fail exact whole-file recognition but provides no proof of that section. Closed nonvacuity and wrong-source probes must fail under a temporary validator bypass and pass only after restoration.

Preserve `leanprover/lean4:v4.16.0`, Init-only new applications, unchanged Core/Distributed/legacy/World/Interpreter/Bridge semantics. No Veil, mathlib, new dependency, solver IO, `native_decide`, `sorry`, `admit`, `sorryAx` or unreported custom axiom. Serial Lake. Old Kadmos inventory scans **all** Applications: register new sources. New Generated audit selects its exact product/test/audit manifest by namespace **or source module**, including escaped/unused declarations, with isolated own rejection roots. Bridge audit grows only for real import closure; never broaden it to all Applications. Keep Foundation 52 and Distributed 336/594 separate; no fixed old application/Bridge count. Hosted Linux CI runs targets serially without a sibling Kadmos checkout; local pinned-source regeneration is mandatory. Never stage `.lake/`, generated binaries/caches, credentials or machine-specific logs. No pushes/PRs/merges or other-repository edits by this owner.

The key preflight risk is whether the selected statement/helper parser and operational semantics can be completed without smuggling an idealized macro for the existing runtime. Grok must inspect the call graph, exact AST/primitive boundary, dependent certificate type and universal proof obligations. If the parser cannot account for any helper branch taken by the canonical balance request, **no step-correctness claim is allowed**: parent must choose a larger formalization or explicitly authorize a certified restricted backend; constructor-only work can stand as a partial result but does not complete T-396. Parent's actual focused Grok ACCEPT is the next gate; this document has not received that verdict.
