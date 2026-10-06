# T-393 Kadmos World IR Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Native execution only; no subagents. Parent dispatches actual Grok preflight before execution and owns review/integration.

**Goal:** Certify a small supported subset of existing Kadmos WorldSpec through its pure Lean interpreter, including accepted balance updates and state-preserving rejection.

**Architecture:** Fin-indexed declaration tables and a strict expression evaluator live in Harmonia.Applications.Kadmos. Candidate effects precede bounds/invariant checks; Foundation Step is interpreter-result equality. No separate balance transition relation.

**Tech Stack:** Lean 4.16.0 / Init, existing Foundation APIs; Python standard-library inventory tests; existing Linux GitHub workflow.

**Spec:** [2026-10-05-kadmos-world-ir-design.md](../specs/2026-10-05-kadmos-world-ir-design.md).

## Global constraints

- Keep `leanprover/lean4:v4.16.0`; standard library only.
- No mathlib, Veil, dependencies, `sorry`, `admit`, custom axioms or `native_decide` in certified application modules.
- Core, Distributed, legacy experiments and their behavior remain unchanged.
- Protected metadata is precisely phase+context. No physical effects occur.
- All declared request fields are required safe integers for every action in this first contract.
- Native supplied worktree; branch `feat/t393-kadmos-world-ir`; no nested worktree, Kadmos/internal edits, push or merge by this worker.
- One Lake process at a time. Preserve existing audit/adversarial targets and Distributed inventory checks.
- This plan is unexecuted. Document commits in the planning call do not authorize early product implementation; coordinator preflight starts execution.

## Review focus

Five failure classes to pin in their owning task, beyond the happy balance trace:

1. Empty/duplicate initial flags and invalid default/bounds must fail initialization (Task 1).
2. Eager boolean RHS overflow must fail even when the left operand decides the truth value (Task 1).
3. A later assignment failure must discard earlier private writes (Task 2).
4. An invariant-only failure with valid bounds must reject the original state (Task 3).
5. An unused axiom in a namespace-escaped new source must be caught, with rejection roots excluded (Task 4).

## Files and interfaces

Create `Harmonia/Applications/Kadmos/World.lean` (IR/errors/decoder/evaluator/initialization),
`Interpreter.lean` (effects/result/interpret/properties), `System.lean` (Foundation instance),
`Balance.lean` (fixture/general debit theorems), and umbrella `Harmonia/Applications/Kadmos.lean`.
All application declarations use `Harmonia.Applications.Kadmos`; no root `Harmonia.lean` edit.
Create `HarmoniaTests/KadmosWorld{IR,Interpreter,Balance,AxiomAudit,AuditRejection}.lean`;
trap sources `HarmoniaTests/KadmosWorldRejection/{Unused,Unsafe}.lean` are uncertified.
Modify `lakefile.lean`, `HarmoniaTests/AuditPolicy.lean`, `.github/workflows/foundations.yml`;
create `scripts/check_kadmos_world_audit.py`, `scripts/test_kadmos_world_audit.py`.
Extend the T-393 receipt after execution; optional concise README application section only.

Every signature/type below refers to the exact fields/constructors in the spec. Do not
replace finite declaration tables with arbitrary evaluator callbacks. New property proofs
must analyze interpret/eval/runEffects, not postulate duplicate semantic rules.

### Task 1: validated IR, strict decoding and expressions

**Files:** World.lean; KadmosWorldIR.lean; lakefile.lean (initial kadmosWorldTest root).
**Consumes:** Init only. **Produces:** spec IR/error types and public decode/eval/checkState/initialize;
`safeInt : Int → Prop`, `S : Int := 9007199254740991`, `checkBounds : World p v f a → State p v → Option Nat`,
`checkInvariants : World p v f a → State p v → Option Nat`, and `Good w s := checkState w s = true`.
`checkState w s := (checkBounds w s).isNone && (checkInvariants w s).isNone`.
`checkedInt : Int → Except EvalError Int` and `requireInt/requireBool` enforce strict Value tags.

- [ ] Add closed regression statements before implementation:

```lean
-- In namespace Harmonia.Applications.Kadmos.Tests.IR, after importing World.
example : decode (fun _ : Fin 1 => .string "30") = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .bool true) = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .null) = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .missing) = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .invalidNumber) = .error (.inputRange 0) := by rfl
example : decode (fun _ : Fin 1 => .int (S+1)) = .error (.inputRange 0) := by rfl
example : eval (0 : Fin 1) (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
  (.sub (.add (.int S) (.int 1)) (.int 1)) = .error .overflow := by rfl
example : eval (0 : Fin 1) (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
  (.and (.bool false) (.eqInt (.add (.int S) (.int 1)) (.int 0))) =
  .error .overflow := by rfl
```

- [ ] RED: `lake build kadmosWorldTest` (unknown target first); add target root KadmosWorldIR,
  rerun and record missing World import/API failure. Keep these tests until GREEN.
- [ ] Implement spec structures and enums. Decode recursively over `List.ofFn id`, building
  a finite function by updates; first error uses index.val. Return an Int function, not
  undecoded raw tags. Prove `decode_field`: decode raw=.ok input implies for every j,
  raw j=.int (input j) and safeInt (input j); derive strict-tag/range rejection lemmas.
- [ ] Implement eval by structural recursion. Every binary node evaluates both children
  before strict operand checks/computation; checkedInt applies at every numeric leaf and
  add/sub result. Bool stateIs compares phases. Prove checkedInt success implies safeInt.
- [ ] Implement checkBounds in variable order, checkInvariants in list order with Fin.elim0;
  spec validation checks IDs/initial count/terminal source/bounds before initial Good.
  Use Option defaults via `getD 0`. No arbitrary input in persistent predicates.
- [ ] Add an inline `World 1 1 0 0` initializer factory `initWorld (flags : Bool)
  (lo hi : Int) (d : Option Int)` with IDs Ready/balance, empty action/field tables via
  Fin.elim0 and no invariants. Pin initialize(initWorld true 0 S (some 100)) success,
  false flag => initialCount, min>max => invalidBounds, default -1 => invalidDefault,
  absent default with min1 => invalidDefault. World 0 0 0 0 rejects initialCount.
  A World 2 0 0 0 with both flags true rejects initialCount; duplicate phase IDs reject
  phaseIds. State-only invariant `.bool false` rejects initialInvariant.
- [ ] Prove `initialize_good : initialize w = .ok s → Good w s` by unfolding validators;
  do not create a successful default state on an error branch.
- [ ] GREEN: `lake build kadmosWorldTest`; `lake build foundationsTest foundationsAudit foundationsAuditRejection`.
- [ ] Commit explicit files: `feat: define validated Kadmos World subset and strict evaluation`.

### Task 2: actual interpreter, private sequential effects and outcome proofs

**Files:** Interpreter.lean; KadmosWorldInterpreter.lean; lakefile.lean test roots.
**Consumes:** Task 1 functions/Good/errors. **Produces:** Verdict/Observation/Result, runEffects,
`runEffect (q : Fin p) (i : Fin f → Int) (e : Effect p v f) (c : Fin v → Int) : Except EvalError (Fin v → Int)`,
`setContext (c : Fin v → Int) (x : Fin v) (n : Int) : Fin v → Int`, interpret and theorems below.
`lookupAction (w : World p v f a) (id : String) : Option (Fin a)` searches finite indices.

- [ ] Add probes before implementation for sequential order, empty effects and intermediate
  overflow; RED: `lake build kadmosWorldTest` fails at missing Interpreter APIs.

```lean
-- Namespace Harmonia.Applications.Kadmos.Tests.Interpreter.
def increment : Effect 1 2 0 := ⟨0, .add (.context 0) (.int 1)⟩
def copy : Effect 1 2 0 := ⟨1, .context 0⟩
def start : Fin 2 → Int := fun x => if x = 0 then 1 else 0
example : (runEffects (0 : Fin 1) Fin.elim0 [increment,copy] start).map
  (fun c => (c 0,c 1)) = .ok (2,2) := by rfl
example : (runEffects (0 : Fin 1) Fin.elim0 [copy,increment] start).map
  (fun c => (c 0,c 1)) = .ok (2,1) := by rfl
example : runEffects (0 : Fin 1) Fin.elim0 [] start = .ok start := by rfl
```

- [ ] Implement the private update and recursion equations directly:

```lean
def setContext (c : Fin v → Int) (x : Fin v) (n : Int) : Fin v → Int :=
  fun y => if y = x then n else c y
-- runEffect q i e c = do
--   let n ← requireInt (← eval q c i e.rhs)
--   return setContext c e.target n
-- runEffects q i (e::es) c = (runEffect q i e c).bind (runEffects q i es)
```

- [ ] Prove setContext self/other, runEffects_nil, runEffects_cons and
  `runEffects_append : runEffects q i (xs++ys) c =
  (runEffects q i xs c).bind (runEffects q i ys)` by induction. Retain concrete probes
  as application evidence; append alone does not show second assignment reads first.
  Add [increment,increment] => (3,0) to pin repeated assignment to the same variable.
- [ ] Implement interpret as a checked Except pipeline yielding `(candidate,directive)`;
  its single error handler returns original state/rejected/none. Follow spec stage order
  exactly. checkBounds/checkInvariants report first failing index; an initial SpecError
  is wrapped in malformedSpec. Effects eval uses transition.target, never s.phase.
- [ ] Prove `rejection_frame`: if (interpret w s r).observation.verdict=.rejected e,
  then (interpret w s r).state=s and its directive=none. Prove `accepted_good` under
  verdict=.accepted and `accepted_directive`: lookupAction w r.actionId=some k and
  accepted imply directive=(w.transitions k).directive. Unfold actual pipeline and split
  Except/Bool branches; use checkState's conjunction and Option.isNone facts.
- [ ] Probe a two-write action whose second expression overflows: no first write escapes;
  a distinct zero-effect action preserves context on acceptance. Probe strict boolean
  guard (`.int 1` => guardError expectedBool), false guard, and proposal mismatch.
  A declared some "SEND" directive with matching proposal must accept and emit only SEND;
  none/wrong proposal must reject with no authorization.
  Probe `eval` of stateIs at effect target explicitly; boolean assignment RHS then rejects
  expectedInt. Add target invariant and source guard with different phase IDs (Task 3
  supplies a complete accepted target-phase example).
- [ ] GREEN: `lake build kadmosWorldTest`; run existing foundation and distributed test/audit/rejection targets serially.
- [ ] Commit explicit files: `feat: interpret Kadmos candidates with proved rejection and publication`.

### Task 3: Foundation system and nonvacuous general balance model

**Files:** System.lean; Balance.lean; umbrella Kadmos.lean; KadmosWorldBalance.lean; test roots.
**Consumes:** interpret, Good, initialize_good, rejection_frame, accepted_good.
**Produces:** system exactly as spec, `reachable_good (hi : initialize w = .ok initial)
  : ∀ s, Foundation.Reachable (system w) s → Good w s`;
`balanceWorld : World 1 1 1 1`, `balanceState (n : Int) : State 1 1`,
`debit (n : Int) : Request 1`, and arbitrary-amount debit theorems.

- [ ] Add the following kernel probes first; RED: `lake build kadmosWorldTest` fails on missing fixture/system.

```lean
-- Namespace Harmonia.Applications.Kadmos.Tests.Balance.
example : initialize balanceWorld = .ok (balanceState 100) := by rfl
example : interpret balanceWorld (balanceState 100) (debit 30) =
  ⟨balanceState 70, ⟨.accepted, none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) (debit 130) =
  ⟨balanceState 100, ⟨.rejected (.bounds 0), none⟩⟩ := by rfl
```

- [ ] Define Ready/DEBIT/balance/amount singleton tables; bounds0..S/default100;
  invariant `(balance>=0)` encoded `.le (.int 0) (.context 0)`; transition Ready→Ready,
  guard `.lt (.int 0) (.request 0)`, effect `⟨0,.sub (.context 0) (.request 0)⟩`,
  directive none. balanceState n = ⟨0,fun _=>n⟩; debit n = ⟨"DEBIT",fun _=>.int n,none⟩.
- [ ] Define system without an inductive replacement Step. For preservation, case-split
  interpret verdict: rejection uses frame and predecessor Good; acceptance uses accepted_good.
  Invoke Foundation.invariant with initialize_good; keep successful initial witness hi
  in public reachable_good even though invariant induction alone could prove vacuous safety.
- [ ] Prove `debit_accept`: for `0 ≤ b`, `b ≤ S`, `0 < n`, `n ≤ b`, interpretation at
  balanceState b equals accepted balanceState(b-n). Prove `debit_insufficient`: same b
  bounds, `b < n`, `n ≤ S` yields bounds0 rejection of balanceState b. Use Int arithmetic
  (`omega` from Lean standard tactics if needed) to prove -S≤b-n≤S, unfold actual eval,
  then extensionality for context equality. No hardcoded-amount premise or new axiom.
- [ ] Prove initialized balance safety for arbitrary Reachable states, extracting the
  bound 0≤context0≤S from Good. Build Foundation.Execution for 30,20,130 from100 to50,
  with two accepted observations then rejected bounds0; use interpreter equalities as steps.
  Include another debit from0 proving request enabled by positive guard but rejected postcheck.
- [ ] Add complete inline variant worlds in probes: unknown action; wrong source on World2;
  zero/negative amount guardFalse; each raw invalid tag and range. A two-phase action
  with source guard stateIs0, target1, effect balance=70, and invariants
  `stateIs0 implies balance=100` and `stateIs1 implies balance=70` shows guard uses PRE
  and candidate checks use TARGET: initial phase0/balance100 and target1/balance70 pass,
  while checking the candidate at source0 fails. An invariant-only failure world uses bounds0..S,
  default100, invariant balance>=50, effect balance=40: reject invariant0, preserve100.
  Bad bounds/default/initial flags from Task1 remain distinct from runtime errors.
- [ ] GREEN: `lake build kadmosWorldTest`; existing test/audit/rejection targets serially.
- [ ] Commit explicit files: `feat: connect interpreted Kadmos balance safety to Foundation`.

### Task 4: source-complete audit, adversarial policy and Linux CI

**Files:** AuditPolicy.lean; KadmosWorldAxiomAudit.lean; KadmosWorldAuditRejection.lean;
KadmosWorldRejection/{Unused,Unsafe}.lean; both new Python scripts; lakefile; workflow; receipt.
**Consumes:** existing HarmoniaAudit.auditSelected/sourceModule, Python scrub/parse_imports/import_closure
from check_distributed_audit.py. **Produces:** `kadmosWorldSourceModules : Array Name`,
`kadmosWorldDeclaration : Lean.Environment → Lean.Name → Bool`, command `#audit_kadmos_world`;
Python `check(root: Path) -> dict`, CLI --root/--self-test, three final targets.

- [ ] RED policy first: a temporary repository test adding
  `Harmonia.Applications.Kadmos.Hidden` with namespace Escape and unused axiom must
  assert inventory rejection. Run it against the existing distributed checker to
  demonstrate the missing application policy, before writing the new checker:

```python
from test_distributed_audit import InventoryTests
from check_distributed_audit import check, AuditInventoryError
class KadmosPolicyRed(InventoryTests):
    def test_new_application_is_not_silently_excluded(self):
        self.write('Harmonia.Applications.Kadmos.Hidden', 'namespace Escape\naxiom unused : Nat\nend Escape\n')
        with self.assertRaises(AuditInventoryError):
            check(self.root)
```

- [ ] Run `python3 scripts/test_kadmos_world_audit.py`; record that this assertion fails
  because old distributed inventory does not certify applications. Replace test imports
  with the task-owned checker when it exists; do not alter distributed checker semantics.
- [ ] Add manifest of all certified new product/probe/audit modules. Select namespace
  Harmonia.Applications.Kadmos OR source prefix Harmonia.Applications.Kadmos OR exact
  manifest membership; reuse auditSelected with allObserved=true. Add an optional summary
  prefix parameter defaulting to existing DISTRIBUTED AUDIT PASS, so new output says
  KADMOS WORLD AUDIT PASS without changing old diagnostics/count policy.
- [ ] Certified audit imports umbrella and every IR/interpreter/balance probe; rejection
  root imports traps separately. Trap modules declare unused normal/unsafe source axioms
  under renamed namespaces. #guard_msgs checks #audit_module for both unused traps.
  Add a contaminated theorem under Harmonia.Applications.Kadmos.AuditTrap in the isolated
  harness so #audit_kadmos_world rejects it; add a clean escaped-namespace marker theorem
  in the certified IR probe and check it appears in the source-selected audit output.
  Retain indirect custom axiom, sorryAx contamination and missing declaration/module probes. Adversarial sorryAx is isolated, never certified.
- [ ] Implement inventory using existing lexical/import helpers without refactoring them:
  enumerate all Harmonia/Applications/**/*.lean and HarmoniaTests/KadmosWorld*.lean plus
  recursive KadmosWorld* directories; reject non-Kadmos application paths. Parse named
  kadmosWorldSourceModules array strictly; manifest equals non-adversarial disk inventory;
  closure of KadmosWorldAxiomAudit covers it. Exclude only AuditRejection and Rejection/**.
  Check new rejection contamination in Foundation, Distributed and Kadmos certified closures;
  scan certified source forbidden proof tokens; reject legacy/Distributed/test/audit
  imports from product closure. Missing project/external imports are errors.
  Parse the three certified audit targets' explicit roots from scrubbed lakefile source;
  reject malformed root arrays, unknown project roots and any rejection-root closure.
  Test accidental adversarial Lake roots separately from adversarial imports.
- [ ] Python temporary-tree tests: clean inventory, unknown top/nested product/probe,
  escaped namespace unimported source, imported unused axiom, missing imports, malformed/
  duplicate/extra manifest, multiline imports/comments, all three certified-root trap
  contaminations, certified sorry/native_decide, forbidden dependency. New checker invokes
  existing distributed check too; run its unchanged 16 tests separately.
- [ ] Lake targets: kadmosWorldTest roots three probes; kadmosWorldAudit roots AuditPolicy
  and KadmosWorldAxiomAudit only; kadmosWorldAuditRejection roots both traps and rejection
  harness only. CI append inventory self-test/check and all three targets as serial steps.
- [ ] GREEN: final matrix below; inspect actual output and fresh audit, update receipt with
  observed theorem/declaration counts, union of axioms and subset assumptions. No solver
  evidence or claimed Linux/reviewer success without coordinator observation.
- [ ] Commit explicit files: `test: audit Kadmos World sources and enforce certification in CI`.

## Final execution acceptance matrix (serial CLI)

| Command | Required evidence |
| --- | --- |
| `lake env lean --version` | version4.16.0; unchanged lean-toolchain |
| `lake build` | exit0; unchanged legacy executable build |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | exit0; original policy/probes intact |
| `lake build distributedTest distributedAudit distributedAuditRejection` | exit0; original policy/probes intact |
| `python3 scripts/check_distributed_audit.py --self-test` and checker without flag | exit0; unchanged coverage |
| `python3 scripts/check_kadmos_world_audit.py --self-test` and checker without flag | exit0; exact application inventory |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | exit0; actual interpreter probes and audit |
| `lake env lean HarmoniaTests/KadmosWorldAxiomAudit.lean` | fresh summary/count/observed union, no replay assumption |
| `lake env lean HarmoniaTests/KadmosWorldAuditRejection.lean` | expected rejection diagnostics matched |
| `git diff --check` and scoped diff of Core/Distributed/legacy/toolchain | no whitespace errors; no protected source edits |

Use explicit git add paths, never generated .lake or machine logs. Record RED/GREEN exit
codes per task and model assumptions in receipt. Parent owns durable registry, actual
Grok independent review and reviewed integration. Stop after this planning call's
three-document commit; no product changes before dispatched preflight.
