# T-393: certified Kadmos World IR subset

Status: revised design for coordinator repreflight, not implementation evidence. Owner: actual Codex; independent reviewer: actual Grok, dispatched by
parent. User-approved scope and managed planning authorization replace routine skill approval stops. No subagents.

## Intent and choice

Give Harmonia a small Lean reference semantics for a supported subset of the existing Kadmos `kadmos.world.v0` WorldSpec, with kernel proofs
about the actual interpreter. Keep the accepted foundation-first layering. Choose finite indexed declarations and a small expression AST; a
string parser would add an unnecessary trust boundary, while hand-coded balance transitions would fail to certify the interpreter. A universal
DSL would exceed this slice. No new Kadmos YAML language or fields are introduced. Lean `Harmonia.Applications.Kadmos` depends only on Init and
the existing Foundation modules. Core, Distributed, legacy experiments and their behavior remain unchanged. Keep `leanprover/lean4:v4.16.0`;
standard library only. No mathlib, Veil, dependencies, `sorry`, `admit`, custom axioms or `native_decide` in certified application modules.

## Exact minimum representation

All dimensions below are Nat parameters: p phases, v context variables, f request fields, a actions. Fin indices prevent undeclared phase,
variable and action references. Finite lists are enumerated with `List.ofFn`; functions here are finite tables, not user-supplied semantic hooks.
Zero variables/fields/actions are allowed; zero phases cannot initialize. No histories, savepoints or other hidden protected metadata.
```lean
structure State (p v : Nat) where
  phase : Fin p
  context : Fin v → Int
inductive RawPrimitive where
  | missing | null | int (n : Int) | bool (b : Bool) | string (s : String)
  | invalidNumber -- fractional, NaN or infinite host number; never decoded
inductive Value where | int (n : Int) | bool (b : Bool)
inductive Expr (p v f : Nat) where
  | int (n : Int) | bool (b : Bool)
  | context (x : Fin v) | request (x : Fin f) | stateIs (q : Fin p)
  | add (l r : Expr p v f) | sub (l r : Expr p v f)
  | eqInt (l r : Expr p v f) | lt (l r : Expr p v f) | le (l r : Expr p v f)
  | not (e : Expr p v f) | and (l r : Expr p v f)
  | or (l r : Expr p v f) | implies (l r : Expr p v f)
structure VarDef where
  min : Int
  max : Int
  defaultValue : Option Int
structure Effect (p v f : Nat) where
  target : Fin v
  rhs : Expr p v f
structure Transition (p v f : Nat) where
  source : Fin p
  target : Fin p
  guard : Expr p v f
  effects : List (Effect p v f)
  directive : Option String
structure World (p v f a : Nat) where
  phaseIds : Fin p → String
  initialFlags : Fin p → Bool
  terminalFlags : Fin p → Bool
  contextIds : Fin v → String
  variables : Fin v → VarDef
  fieldIds : Fin f → String
  actionIds : Fin a → String
  transitions : Fin a → Transition p v f
  invariants : List (String × Expr p v 0)
structure Request (f : Nat) where
  actionId : String
  payload : Fin f → RawPrimitive
  proposedDirective : Option String
```
Fin references are typed; expression sorts are dynamic, not a static GADT. Expression types are checked strictly at evaluation, as in Kadmos: guards/invariants must produce Bool; assignment RHS must produce Int. There
are no implicit conversions. `stateIs` is the supported spelling of phase equality, not arbitrary string operations. Integer equality plus lt/le,
reversed operands and not cover comparisons. All declared request fields are required safe integers for every action in this first contract. This
uniform Lean application contract is deliberately narrower than Kadmos payloads; it is not an existing WorldSpec input-schema field.
Event/request reads map to the same field table. Unknown/extra raw object properties and JS/Python object mechanics are outside the model.
Arbitrary primitive strings/booleans remain distinct rejection data.

## Total evaluator and initialization

Let S = 9007199254740991 and `safeInt n := -S ≤ n ∧ n ≤ S`. `EvalError = expectedInt | expectedBool | overflow`. `SpecError = phaseIds |
contextIds | fieldIds | actionIds | invariantIds | initialCount | terminalSource | invalidBounds | invalidDefault | initialInvariant`.
`RejectReason = malformedSpec SpecError | unknownAction | wrongPhase | unauthorizedDirective | inputType Nat | inputRange Nat | guardFalse |
guardError EvalError | effectError EvalError | bounds Nat | invariant Nat`. Errors carrying Nat identify declaration-order indices. Names are
nonempty and unique within each respective table/list; action IDs are globally distinct. Public signatures (implicit dimension parameters
inferred from World/State):
```lean
decode (raw : Fin f → RawPrimitive) : Except RejectReason (Fin f → Int)
eval (phase : Fin p) (ctx : Fin v → Int) (input : Fin f → Int)
  (e : Expr p v f) : Except EvalError Value
runEffects (phase : Fin p) (input : Fin f → Int)
  (effects : List (Effect p v f)) (ctx : Fin v → Int) : Except EvalError (Fin v → Int)
checkState (w : World p v f a) (s : State p v) : Bool
initialize (w : World p v f a) : Except SpecError (State p v)
```
`decode` traverses fields in index order; only `.int n` with safeInt n succeeds. Out-of-range ints and invalidNumber yield inputRange; other tags yield inputType. `eval` checks integer literals, context/request reads and every
add/sub intermediate against [-S,S]; Int arithmetic is exact, then checked. Arithmetic and comparison operands must be Int; logical operands must
be Bool. Binary boolean operators evaluate both operands left-to-right even when the left value determines the answer. No short-circuiting: false
&& overflowing expression still fails; so do true || overflow, false implies overflow and not overflow. Both implication operands run before computing !left || right. First error wins. Unary not is strict. No floats, multiplication/division, recursion or host helpers.
`initialize` checks unique/nonempty IDs, exactly one initial phase, no transition from terminal phases, and explicit context bounds `0 ≤ min ≤
max ≤ S` (aligning the current parser's nonnegative bounds). Missing defaults mean 0; defaults must be safe and in bounds. Bounds are mandatory
in this certified subset. Then it builds the initial state and requires checkState=true; invariant evaluation errors fail initialization.
`checkState` requires all safe bounded context values and every state-only invariant evaluating to `.ok (.bool true)` with input `Fin.elim0`. No
request predicate can be encoded in invariants because their field dimension is 0. Empty/malformed worlds return SpecError, never an initialized
certified system witness. Invariant false and evaluation errors both identify the same invariant index on a step; overflowing initialization invariants yield initialInvariant.

## Step equations and publication

```lean
inductive Verdict where | accepted | rejected (reason : RejectReason)
structure Observation where
  verdict : Verdict
  directive : Option String
structure Result (p v : Nat) where
  state : State p v
  observation : Observation
interpret (w : World p v f a) (s : State p v) (r : Request f) : Result p v
system (w : World p v f a) : Harmonia.Foundation.TransitionSystem
  (State p v) (Request f) Observation
```
Interpretation order: initialize/validate spec; resolve action ID to Fin a; require source=s.phase; match proposedDirective exactly; decode; eval
guard on PRE-state; require true; runEffects on private context using TARGET phase; check final bounds; check state-only invariants on
target+candidate; publish candidate and declared directive. Each failed stage returns `⟨s, ⟨.rejected reason, none⟩⟩`. Success returns
`⟨⟨transition.target, candidate⟩, ⟨.accepted, transition.directive⟩⟩`. Revalidating static initialization per call is the simple reference
contract; no cache. Pin unknownAction before wrongPhase, wrongPhase before unauthorizedDirective, and inputType/inputRange before guardFalse.
Prove `initialize w = .error e → interpret w s r = ⟨s, ⟨.rejected (.malformedSpec e), none⟩⟩`. Malformed initialization becomes malformedSpec before request processing; every rejection has original state and directive none.
`runEffects q i [] c = .ok c`. For `(x := e)::es`, eval q c i e; require a safe Int n; update `c' y = if y=x then n else c
y`; recursively run es on c'. Bounds/invariants are checked only after all assignments, but integer safety is checked at each read and arithmetic
operation. Thus temporary context may violate declared bounds without escaping its private candidate. Even boolean RHS phase predicates evaluate
at target phase before failing the integer-assignment type requirement; no conditional operator is added to emulate a source construct Kadmos
does not support. Successful numeric effects cannot distinguish the phase argument behaviorally. The actual interpret pipeline must call
`runTransitionEffects t i s := runEffects t.target i t.effects s.context`; prove this target-phase equation by unfolding the used helper.
`system.init s := initialize w = .ok s`. `system.step s r o t := interpret w s r = ⟨t,o⟩`. There is no second hand-written
transition relation. Every rejected request is an observable labeled self-step; accepted output is a token authorizing only the declared
directive. No physical effects occur. Protected metadata is precisely phase+context.

## Source alignment and boundaries

Read sources in `/Users/yong/projects/substratum/kadmos` during planning:

| Source | Align here | Deliberate boundary |
| --- | --- | --- |
| `src/types/world.ts` | finite states, integer context, guards, ordered effects, directives | no parser/adapter or imported YAML compatibility theorem |
| `src/world_checker.ts` createWorldChecker/step | pre-guard, target-phase candidate effects, strict types, bounds/invariants before publish, directive match | omit history/reset API/savepoints/security object handling |
| `src/world_expression.ts` evaluate | strict Int/Bool operators; eager binary boolean operands | every numeric intermediate safe; source only tests finite operands and assignment results |
| `src/world_compiler.ts` parseWorldSpec and generated checker | unique action IDs, one initial phase, defaults, nonnegative bounds, terminal-source exclusion | no TS/Python/C correspondence or compiler certification |
| `conformance/fixtures/order_settlement.world.yaml` | phase guards, conservation predicates, ordered assignments, directive tokens | not claimed as a fully imported/certified fixture |
| `tests/test_harness_world_compiler.test.ts` | existing parser rejection and generated-checker tests | read-only context, no new Kadmos tests or behavior claim |

Safe intermediate arithmetic strengthens current JS behavior. A future correspondence must restrict to executions with safe intermediates and
prove representation/decoding alignment; it cannot assert the existing compiler already enforces this restriction. Unsupported: string
context/equality, optional request fields, null expressions, nested payloads, YAML/string parsing, savepoints/history/rollback, directive IO,
codegen, TS/Python correspondence, distributed composition, TLC/SMT and a universal DSL.

## Kernel obligations and acceptance

Prove decode success implies each raw field is an int with safe range; all other tags and out-of-range ints reject. Prove actual interpret
rejection preserves entire State and produces no directive; acceptance satisfies checkState and returns exactly the selected transition
directive. Prove initialize success implies checkState, and use Foundation.invariant for initialized reachability safety with an explicit
successful initialization witness. No assertion that all actions inherently preserve invariants: a bad effect must reach postchecks and reject.

Prove runEffects cons/append sequencing and a concrete order-sensitive application probe: from (x=1,y=0), `x=x+1; y=x` gives (2,2); reversal
gives (2,1). Probe zero effects, repeated assignments, pre-guard and target-phase evaluation, eager boolean errors, wrong phase/unknown
action/directive mismatch, invalid defaults, empty/duplicate initials, bounds and invariant-only failures, and intermediate overflow `(S+1)-1`
even though its mathematical final result is safe. From100/bounds[0,S], subtract150 then add150 must accept100 despite private -50;
subtract150 alone rejects bounds0 preserving100. Reversing both constant writes also accepts100: (100+150)-150=100.
The review's reversed-final-minus50 claim is declined; order sensitivity belongs to the x/y probe, not commuting constants.

Balance: Ready, balance default100, bounds[0,S], invariant balance>=0; debit self-loop, amount required safe int, guard amount>0, effect
balance=balance-amount, directive none. Prove positive arbitrary safe amounts accept when their resulting balance is legal; 30 yields70; 130
passes guard but rejects at bounds with original100. Repeat debits remain enabled until a negative candidate rejects. Trace 30,20,130 ends50
including rejection. String/bool/null/missing/invalidNumber/out-of-range inputs reject explicitly. Safety covers arbitrary finite executions, not
only these examples. General debit theorems equate the whole Result, including verdict/directive: n=b>0 accepts zero; debit1 from0
rejects bounds0. Exhibit Reachable(system balanceWorld)(balanceState100). Pin malformedSpec reasons for duplicate initials, invalid
bounds (min>max, min<0, max>S), empty/duplicate action IDs and terminal source; absent default0 succeeds at min0. `World 0 0 0 0`
initialization is initialCount (there is no State0 to pass to interpret). Pin literal/context S+1 overflow, decode error at field1,
unused required fields and Fin0 decode success. `World 1 0 0 0` initializes and any request yields unknownAction.

Add kadmosWorldTest, kadmosWorldAudit and isolated kadmosWorldAuditRejection targets. Reuse AuditPolicy's engine, selecting by namespace AND
certified source-module inventory, including unused source axioms and namespace escapes. New inventory policy tests must fail before policy
implementation. Inventory equals all application sources/probes on disk, requires audit import coverage, rejects unknown/missing modules and
adversarial imports into certified roots. Explicit trap-free targets: foundationsTest, foundationsAudit, distributedTest, distributedAudit,
kadmosWorldTest and kadmosWorldAudit. foundationsAuditRejection, distributedAuditRejection and kadmosWorldAuditRejection may import
their isolated traps and shared AuditPolicy; isolation forbids certified-to-trap edges, not rejection-to-shared-tooling edges.
Synthetic tests distinguish contamination of a certified root from legal isolated rejection roots. Preserve all existing audit/adversarial targets and Distributed inventory coverage. Linux CI runs
new targets and inventory serially. Record actual theorem/declaration count and observed standard axiom union after execution; no new proof
counts or hosted Linux/revised-preflight success exist at this stage. Preserve Foundation52 and Distributed336/594 in their separate
certified import environments. Combined application environments may select imported Foundation/probe declarations; report count scope,
not a fixed combined count. Grok's first package review returned REVISE; coordinator rulings are recorded in the receipt.
