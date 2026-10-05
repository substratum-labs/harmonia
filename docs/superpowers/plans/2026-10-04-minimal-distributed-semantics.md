# Minimal Distributed Semantics Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Native physical Codex execution only; selected physical CLI workflow uses no subagents. Independent physical Grok preflight precedes code, and Grok reviews the resulting branch before coordinator integration. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Build an asynchronous, finite-membership crash/omission layer with restricted local protocol inputs, unique transmission occurrences and proved finite-execution safety infrastructure.

**Architecture:** `Harmonia.Distributed` instantiates the unchanged `Harmonia.Foundation` relational system. Typed members, permutation-based occurrence relations and fixed fault profiles constrain global rules; protocols receive only local data and explicit input. Focused proofs, nonvacuous fixtures and audited source inventories establish the boundary.

**Tech Stack:** Lean 4.16.0, Init/core List API, Lake, existing Lean audit tooling, Python 3 standard library for source inventory, Ubuntu CI.

**Spec:** [stage-two design](../specs/2026-10-04-minimal-distributed-semantics-design.md).

## Global Constraints

- Keep `lean-toolchain` pinned to `leanprover/lean4:v4.16.0`.
- Lean core only; no mathlib or new dependencies.
- Preserve stage-one `Harmonia.Foundation` semantic contracts and source modules.
- No Veil, Kadmos, consensus protocol, crypto, fairness/liveness, infinite execution, extraction, codegen or SMT.
- Preserve legacy experiments; claim no behavioral connection without a correspondence theorem.
- No `sorry`, `admit`, `sorryAx` or custom axioms in certified proofs.
- No message-count or execution-depth bound in the semantics.
- Parent coordinator owns internal ledger and physical Grok review; no subagents.

## Review Focus

- Empty membership: checked success, witnessed empty initialization and no fabricated member or enabled network fault from empty pool (Task 1/3/5).
- Zero/multiple emissions and self-send: exact supply arithmetic, all new IDs distinct, own endpoint valid (Task 2/5).
- A spent transmission versus a retry: no replay of one consumed tid, but repeat logical ID with new occurrence remains legal (Task 3/5).
- Wrong observation and nonempty initial pool: reject both despite otherwise legal process behavior (Task 3/5).
- Unimported sources and namespace escape: inventory rejects omissions, audit rejects unused axioms and renamed contaminated declarations (Task 6).

These supplement the explicit hostile requirements, all mapped below.

## Workspace, inputs and evidence

This plan was executed natively; see the committed receipt for task evidence. Read AGENTS.md, the spec, ARCHITECTURE.md,
Core/{TransitionSystem,Execution,Invariant,Refinement}.lean and all existing
HarmoniaTests audit sources before code. Existing linked worktree is
`/Users/yong/.codex/worktrees/991b/harmonia`, branch
`feat/t392-minimal-distributed-semantics`. Do not create a nested worktree.
Baseline receipt is [here](../../verification/2026-10-04-minimal-distributed-semantics.md).
Do not edit internal ledger or Kadmos. Parent coordinator supplies physical
Grok preflight findings; resolve material findings in spec/plan before code.
Run one Lake build process at a time. Record each RED/GREEN command, exit code
and diagnostic in the receipt; do not commit temporary mutant code or build
artifacts. Commit each independently verified task with explicitly named files.

The code blocks below are implementation blueprints, not already certified
Lean code. Type parameters are those declared in the spec. Within namespaces
use `universe u`, `{N : Type u} [DecidableEq N] (c : Config N)` and
`{D V L P C K : Type u}` consistently. `M` in signatures abbreviates `Member c`,
`T` abbreviates `Transmission M L P`, `S` abbreviates `State M D V L P`,
`A` abbreviates `Label M L P C K`, and `p : Protocol M D V L P C K`,
`f : FaultProfile`. These aliases describe signatures; avoid leaked aliases
with unresolved typeclass metavariables. Protocol/types need no DecidableEq
on D,V,L,P,C,K. Verify public binders with `#check` before each consuming task.

## File responsibilities

| File | Responsibility / imports |
| --- | --- |
| `Harmonia/Distributed/Membership.lean` | Config.checked, member lookup and membership theorems; Init.Data.List.Perm |
| `Harmonia/Distributed/Protocol.lean` | Status, Local, Outgoing, Envelope, Transmission, Stimulus, Input, Protocol, FaultProfile; Membership |
| `Harmonia/Distributed/Network.lean` | Take, allocation, Publish and occurrence lemmas; Protocol |
| `Harmonia/Distributed/Semantics.lean` | State, Label, update, six Step rules, system embedding; Network and Core.Invariant |
| `Harmonia/Distributed/Properties.lean` | WF, frame, durability, freshness, congruence, execution lifting, provenance; Semantics |
| `Harmonia/Examples/Distributed.lean` | two/three-node counting fixtures, states and witness traces; Properties |
| `Harmonia/Distributed.lean` | certified layer umbrella importing Properties only |
| `HarmoniaTests/DistributedMembership.lean` | checked-constructor and endpoint/actor type probes |
| `HarmoniaTests/DistributedNetwork.lean` | permutation, exact-one and allocation probes |
| `HarmoniaTests/DistributedSteps.lean` | enabled/disabled/precondition/frame tests |
| `HarmoniaTests/DistributedTraces.lean` | initialized histories, retries, duplication, recovery and observations |
| `HarmoniaTests/DistributedAxiomAudit.lean` | certified imports and #audit_distributed only |
| `HarmoniaTests/AuditPolicy.lean` | shared selection/audit engine; preserve foundation command |
| `HarmoniaTests/DistributedAuditRejection.lean` | isolated negative audit command probes |
| `HarmoniaTests/DistributedRejection/Unused.lean` | isolated source-origin fixture with unused axiom outside Distributed namespace |
| `scripts/check_distributed_audit.py` | source inventory, import-closure and forbidden-adversarial checks plus --self-test |
| `lakefile.lean` | three dedicated distributed lean_lib targets |
| `.github/workflows/foundations.yml` | retain foundation steps; add runtime version, inventory and distributed steps |
| `ARCHITECTURE.md`, `README.md`, receipt | state exactly implemented guarantees and observed checks |

Do not modify `Harmonia.lean`: its legacy umbrella remains as-is. Consumers
import `Harmonia.Distributed` or a focused module. New modules must never import
legacy Core.Network/SmallStep, Protocols, DSL, SMT or Gatekeeper. No adversarial
module enters any certified import closure.

### Task 1: Checked membership and restricted protocol boundary

**Files:** create Membership, Protocol, DistributedMembership; add distributedTest
roots incrementally in lakefile (only files that exist at this task).

**Interfaces:** consumes only core List. Produces all types and exact fields in
spec Membership/Local knowledge sections. Config.checked and Config.member?
require DecidableEq N; Member membership is by subtype. Fault profiles are
`reliable := ⟨false,false,false,false⟩`,
`crashRecovery := ⟨false,false,true,true⟩`,
`omission := ⟨true,true,true,true⟩` in drop/duplicate/crash/recover field order.

- [x] Add decisive failing probes first:

```lean
import Harmonia.Distributed.Protocol
open Harmonia.Distributed
example : Config.checked ([0, 0] : List Nat) = none := by rfl
example : (Config.checked ([0, 1] : List Nat)).isSome = true := by decide
example : (Config.checked ([] : List Nat)).isSome = true := by decide
-- Fixture configuration can bypass Option extraction only with an explicit
-- proof of Nodup. Keep checked-constructor tests independent of this value.
def pair : Config Nat := ⟨[0, 1], by decide⟩
example : pair.member? 2 = none := by decide
example (m : Member pair) : m.val ∈ pair.members := m.property
#check_fail (show Member pair from (2 : Nat))
#check_fail ({ recipient := (2 : Nat), logical := 7, payload := () } :
  Outgoing (Member pair) Nat Unit)
```

Also prove no member with val 2 (`by intro h; have := m.property; ...` using
finite-list simplification), and `∀ m : Member empty, False` by `m.property`.

- [x] Run `lake env lean HarmoniaTests/DistributedMembership.lean`; expect exit
1, missing imported module before implementation. Record it.
- [x] Implement Config exactly as spec and prove checked_rejects and
checked_preserves by `unfold Config.checked; split <;> simp_all` (adjust
Option constructor injection as needed). Implement protocol structures with
`react` exactly `M → D → V → Input M L P C K → D → V → List (Outgoing M L P) → Prop`.
Add a `#check` that applies react to actor,D,V,input,d,v,outs. A `#check_fail`
application supplying a function of global-state arguments must fail the type
expected by Protocol.react; keep this distinct from behavioral locality.
- [x] Build `lake build Harmonia`; then run the membership probe and
`lake build foundationsTest foundationsAudit foundationsAuditRejection`
serially. Require exit 0, no new certified warnings. Check Protocol source
contains no State/network/profile parameter; read the full structure rather
than relying solely on string matching.
- [x] Commit exact Task 1 paths with message `feat: define checked distributed membership and local protocol interface`.

### Task 2: Unordered occurrence consumption and fresh publication

**Files:** create Network and DistributedNetwork; add that probe to distributedTest.

**Interfaces:** consumes Outgoing, Envelope, Transmission. Produces:

```lean
def Take (pool : List T) (e : T) (rest : List T) : Prop := List.Perm pool (e :: rest)
def allocate (actor : M) : Nat → List (Outgoing M L P) → List T
  | _, [] => []
  | n, out :: tail =>
    ⟨n, ⟨actor, out.recipient, out.logical, out.payload⟩⟩ :: allocate actor (n+1) tail
def Publish (actor : M) (n : Nat) (outs : List (Outgoing M L P))
    (base result : List T) : Prop := List.Perm result (base ++ allocate actor n outs)
def freshCopy (e : T) (n : Nat) : T := ⟨n, e.envelope⟩
```

- [x] Add nonhead and multiplicity probes before Network exists:

```lean
example (x y : T) : Take [x,y] y [x] := by
  exact List.Perm.swap y x []
example (x : T) : Take [x,x] x [x] := List.Perm.refl _
example (x : T) : ¬ Take [x] x [x] := by
  intro h
  have bad := h.length_eq
  simp at bad
example (actor : M) : allocate actor 9 [] = [] := rfl
```

The scratch core probe confirms `List.Perm.swap y x []` has this direction.
The closed duplicate-config rejection uses rfl: by decide would unnecessarily
require Decidable equality for the proof-carrying Config result.
Add a two-output example with IDs `[9,10]`, repeated logical 7, one self-send
and one peer-send, all senders equal actor. No logical-ID uniqueness condition.

- [x] Run probe, record missing module exit 1. Implement the four definitions.
Prove these exact obligations with generic implicit binders:

```lean
Take.length : Take pool e rest → pool.length = rest.length + 1
Take.perm_left : List.Perm pool pool' → (Take pool e rest ↔ Take pool' e rest)
Take.middle : Take (prefix ++ e :: suffix) e (prefix ++ suffix)
Take.rest_unique : Take pool e r → Take pool e r' → List.Perm r r'
allocate_length : (allocate actor n outs).length = outs.length
allocate_ids : (allocate actor n outs).map (fun e => e.tid) =
  (List.range outs.length).map (fun i => n + i)
allocate_fresh : ((allocate actor n outs).map (fun e => e.tid)).Nodup ∧
  ∀ e, e ∈ allocate actor n outs → n ≤ e.tid ∧ e.tid < n + outs.length
allocate_sender : e ∈ allocate actor n outs → e.envelope.sender = actor
```

Use Perm.trans/symm for left transport; rest_unique uses
`(h.symm.trans h').cons_inv`. middle is core `List.perm_middle`.
For allocation use structural induction and Nat arithmetic; establish a helper
`List.range` bound if convenient, but no arithmetic library/dependency. Fresh
induction: head ID n cannot occur among tail IDs ≥ n+1; use `Nat.not_lt_of_ge`
and successor strictness. Take.length uses Perm.length_eq and simp.

- [x] Prove `Publish.perm_base` and `Publish.perm_result` by append/trans;
run Network probe, `lake build distributedTest` and foundation targets. For a
meaningful RED, temporarily change Take to `pool = e :: rest` and confirm the
nonhead generic probe fails, restore; temporarily make tail start n and confirm
the two-output ID probe fails, restore. Do not commit mutants.
- [x] Commit Task 2 paths and receipt with `feat: model unordered message occurrences and fresh allocation`.

### Task 3: Six global rules and Foundation embedding

**Files:** create Semantics, DistributedSteps; extend distributedTest roots.

**Interfaces:** consumes Take/Publish/allocate/protocol and Core.Invariant.
Produces State, Label, actorOf, setNode, Step, system, and rule-level lemmas.
`actorOf process/crash/recover = some actor`, `actorOf deliver = some recipient`,
`actorOf drop/duplicate = none`. Observation type equals Label.

- [x] Write a small protocol fixture in DistributedSteps with Nat durable and
volatile, Unit payload/timeout and typed-member local command, initial zeros,
reset-zero and recovery-identity. Its react relation is precisely:

```lean
match input with
| .scheduled (.local peer) =>
    d' = d+1 ∧ v' = v+1 ∧ outs = [⟨peer, 7, ()⟩]
| .scheduled (.timeout ()) => d' = d ∧ v' = v+1 ∧ outs = []
| .message _ => d' = d+1 ∧ v' = v+1 ∧ outs = []
```

Define concrete running and crashed states with empty pool. Write an actual
process witness and universal negations before Semantics exists. The negations
are `¬ Step c p f crashed (.process receiver (.timeout ()) []) t`, local analog,
`¬ Step ... crashed (.deliver e []) t`, crash-on-crashed and recover-on-running.
Give receive a pool actually containing e so it tests status, not absence.
Also negate each fault on an otherwise applicable state when its flag is false.

- [x] Run the probe, record missing module exit 1. Implement State/Label from
spec, `setNode` via member equality and prove setNode_other by simp.
Define Step constructors with resulting state record and Publish premise.
For example, under the declared parameters:

```lean
-- A constructor blueprint: d/v/rest/result are quantified witnesses.
| deliver (running : (s.nodes e.envelope.recipient).status = .running)
    (take : Take s.pending e rest)
    (reaction : p.react e.envelope.recipient
      (s.nodes e.envelope.recipient).durable
      (s.nodes e.envelope.recipient).volatile (.message e.envelope) d v outs)
    (publish : Publish e.envelope.recipient s.next outs rest result) :
    Step c p f s (.deliver e outs)
      ⟨setNode s.nodes e.envelope.recipient ⟨d,v,.running⟩,
       result, s.next + outs.length⟩
```

Implement the other five from the spec table, with distinct named guards for
flags and status. Process uses old pool; duplicate retains source and freshCopy;
crash/recover keep exact pending and next. Never add a global react guard or WF
premise to enable a rule; WF is proved independently.

```lean
def system : Harmonia.Foundation.TransitionSystem S A A where
  init s := s.pending = [] ∧ s.next = 0 ∧
    ∀ m, (s.nodes m).status = .running ∧
      p.initial m (s.nodes m).durable (s.nodes m).volatile
  step s a o t := Step c p f s a t ∧ o = a
```

- [x] Prove disabled-status and disabled-flag generic lemmas by cases on Step
and contradictory Bool/Status equality. Verify universal negative probes and
positive witnesses. Add `system.step` wrong-observation negation and `init`
nonempty-pool negation with actual concrete states. Add empty configuration
initial witness (`nodes := fun m => False.elim (by exact m.property)` after
simplifying membership in []) and no-step result from that initial state.
- [x] Run `lake build distributedTest` and foundation targets. Temporarily
remove running premise from process and show timeout-negative proof fails;
restore. Remove one profile guard and show its corresponding negation fails;
restore. Commit Task 3 paths/receipt as `feat: instantiate foundation with local network and fault steps`.

### Task 4: Structural proofs and representation boundary

**Files:** create Properties and layer umbrella; extend DistributedNetwork/Steps
with generic theorem probes. No stage-one source edit.

**Interfaces:** consumes Step/system and Foundation.Execution/invariant.
Produces these definitions and theorem signatures:

```lean
def WF (s : S) : Prop := (s.pending.map (fun e => e.tid)).Nodup ∧
  ∀ e, e ∈ s.pending → e.tid < s.next
def PoolEq (s t : S) : Prop := s.nodes = t.nodes ∧ s.next = t.next ∧
  List.Perm s.pending t.pending
-- `emitted` returns envelope list, using allocate actor s.next outs
-- for process/deliver; [] for every environment label.
def emitted (s : S) (a : A) : List (Envelope M L P)
```

`Step.frame : Step ... s a t → ∀ peer, actorOf a ≠ some peer →
t.nodes peer = s.nodes peer`.
`Step.permutation_lift : PoolEq s s' → Step ... s a t →
∃ t', Step ... s' a t' ∧ PoolEq t t'`.
`execution_permutation : PoolEq s s' → Foundation.Execution system s labels t →
∃ t', Foundation.Execution system s' labels t' ∧ PoolEq t t'`.
`wf_initial : Foundation.Initially system WF`;
`wf_preserved : Foundation.Preserved system WF`;
`reachable_wf : Foundation.Reachable system s → WF s`.
Durability statements bind the crash/recover actor and equate its post/pre D.
Consumption/freshness statements are those in the spec.

- [x] Add probes applying each named theorem to generic hypotheses before
Properties exists; require the missing import RED. Include a concrete malformed
pool with duplicate tids so `¬ WF bad` proves the predicate is substantive.
- [x] Implement PoolEq/WF, frame and durability by cases on all constructors
and setNode_other. For Step congruence rewrite nodes/supply equalities; transport
Take pre-pool, Publish base/result, and duplicate membership by Perm.mem_iff.
Crash/recover preserve the exact input pool representation, so choose the lifted
successor with s'.pending. The representation theorem supplies a related legal
successor; it does not require independently reordered output states to be legal.
Use the following accepted signature:

```lean
Step.permutation_lift : PoolEq s s' → Step c p f s a t →
  ∃ t', Step c p f s' a t' ∧ PoolEq t t'
```

For process/deliver/duplicate choose same post nodes/supply and a legal permuted
pool; for crash/recover choose s'.pending; for drop choose transported residual.
Derive symmetric existence via PoolEq.symm. This is formal step
congruence modulo PoolEq and still proves representation does not restrict
receive/drop. `execution_permutation` inducts on Execution, applies this step
lifting and then the tail induction. No semantic change to stage one.

- [x] Prove residual WF from Take using map Perm, nodup_cons and membership.
Prove Publish preservation with allocation freshness/disjointness and append
nodup (derive directly by induction if append lemma inconvenient). Establish
WF preservation for all constructors and apply Foundation.invariant exactly:

```lean
theorem reachable_wf (h : Harmonia.Foundation.Reachable (system c p f) s) : WF s :=
  Harmonia.Foundation.invariant (wf_initial c p f) (wf_preserved c p f) s h
```

Also prove next monotone for all steps, and fresh allocation IDs cannot match
any pending ID. Deliver exact-one consumption is about Take's rest before
publication: a receiver may emit replies, so post-pool length need not decrease
by one. Prove `t.pending.length + 1 = s.pending.length + outs.length`.
Duplicate freshness includes source retention, copied envelope equality and
fresh tid n absence; no duplicate permission assumption hidden in WF.

- [x] Implement provenance with an Execution-indexed relation:

```lean
inductive SentIn : {s t : S} → {labels : List (A × A)} →
    Harmonia.Foundation.Execution (system c p f) s labels t →
    Envelope M L P → Prop where
  | head (hs : (system c p f).step s a o m)
      (tail : Harmonia.Foundation.Execution (system c p f) m labels t)
      (h : envelope ∈ emitted s a) : SentIn (.cons hs tail) envelope
  | tail (hs : (system c p f).step s a o m)
      (path : Harmonia.Foundation.Execution (system c p f) m labels t)
      (h : SentIn path envelope) : SentIn (.cons hs path) envelope
```

First prove one-step origin: post pending envelope came from pre pending or
emitted. Deliver uses residual membership; duplication uses identical envelope.
Induct on path for `pending_origin : e ∈ t.pending →
(∃ old, old ∈ s.pending ∧ old.envelope = e.envelope) ∨ SentIn path e.envelope`.
Combine with init.pending = [] for provenance_history. Do not use uniqueness
or an unproved authentication axiom. Binder/constructor details may be changed
for Lean elaboration but proposition and empty-init consequence must stay exact.

- [x] Run theorem probes, `lake build distributedTest`, foundation targets.
Counterchecks: change freshCopy to tid = e.tid and see wf_preserved/freshness
fail; restore. Change crash to overwrite D and see durability fail; restore.
Create umbrella importing Properties only. Commit with `proof: establish distributed frames network invariants and provenance`.

### Task 5: Nonvacuous behavior traces and hostile regressions

**Files:** create Examples/Distributed and DistributedTraces; update Steps for
shared fixture imports and add trace root. Move the temporary Task 3 fixture
into the example module, removing duplication without changing tests.

**Interfaces:** example namespace `Harmonia.Distributed.Examples` exports
`pair`, `left`, `right`, `triple`, `first`, `second`, `third`, `counting`,
`initialState`, `sentState`, `crashedState`, `recoveredState`, `deliveredState`,
`e0`, `e1`. Pair typed values are `⟨0, by decide⟩` and `⟨1, by decide⟩`;
triple membership is `[0,1,2]`. `counting` uses Task 3 react exactly, instantiated
per configuration. InitialState has zero nodes, empty pending, next 0.
SentState increments left D/V to 1 and contains e0 = left→right, logical 7,
payload Unit, tid 0, next 1. Crash/recover states change right only. Delivered
state increments right D/V to 1, empty pending, next 1.

- [x] Write the witness statements before example module:

```lean
example : ∃ s, (system pair counting FaultProfile.crashRecovery).init s :=
  ⟨initialState, by simp [system, initialState, counting]⟩
example : Harmonia.Foundation.Execution
  (system pair counting FaultProfile.crashRecovery) initialState
  [(.process left (.local right) [⟨right,7,()⟩],
    .process left (.local right) [⟨right,7,()⟩]),
   (.crash right, .crash right), (.recover right, .recover right),
   (.deliver e0 [], .deliver e0 [])] deliveredState := send_crash_recover_deliver
```

Run missing-module RED. Prove the trace with `.cons ⟨Step.process ...,rfl⟩`
and subsequent constructors, finishing `.nil`; exhibit init separately and
derive reachable endpoint with Foundation.execution_reachable.

- [x] Prove the nonzero durable trace: send/deliver, crash right, recover right;
state equalities explicitly show right `(D,V)` changes `(1,1)`→`(1,0)`→`(1,1)`.
Prove pool/supply survive crash and recovery in the earlier inflight trace.
- [x] Prove duplicate trace under omission: send, duplicate e0 (e1.tid = 1,
e1.envelope = e0.envelope), deliver e1 first then e0, final right D = 2.
Prove a retry under reliable: two local sends logical 7 get tids 0 and 1, then
two deliveries, same visible count 2. No duplication gate needed for retry.
- [x] Prove a second send/nonhead drop and receive witness, full reordered-start
step lifting via PoolEq, and absence of Step.deliver e0 once its only instance
has been consumed. Prove timeout at left while right remains running. Prove
three-node frame equality for third during send/deliver/crash/recover of first
and second. Exercise setNode_other with actual distinct member proofs.
- [x] Retain all universal negative probes from Task 3, add disabled recover
with allowCrash true and allowRecover false, and disabled crash with recover
true. Add wrong observation, empty-init pool rejection, actor/endpoint lookup,
self-send, zero and multiple outputs tests. Witness two different allowed react
successors in a separate tiny protocol to ensure no determinism requirement
was introduced; no claim counting itself is nondeterministic.
- [x] Run `lake build distributedTest` and all baseline commands serially.
Inspect tests for negations proved only by missing messages; repair receive
precondition tests to contain an actual transmission. Every behavioral theorem
must state state/step/trace facts rather than True. Commit as
`test: certify distributed crash recovery duplicate and hostile behaviors`.

### Task 6: Comprehensive audit, rejection coverage, CI and receipt

**Files:** modify AuditPolicy/lakefile/CI/docs; create certified audit root,
isolated rejection modules and inventory script. Keep AxiomAudit and original
AuditRejection roots/imports unchanged.

**Interfaces:** preserve #audit_foundations, #audit_namespace,
#audit_declaration. Extract `auditSelected (select : Name → Bool) (label : String)
: CommandElabM Unit` using current collection and log format. Add
`distributedDeclaration (env : Environment) (n : Name) : Bool` selecting namespace
or source modules: all Harmonia.Distributed descendants, Harmonia.Examples.Distributed,
and DistributedMembership/Network/Steps/Traces plus DistributedAxiomAudit.
Add #audit_distributed and #audit_module for source-origin rejection fixtures.
Declare an explicit `distributedSourceModules : Array Name` manifest:

```lean
def distributedSourceModules : Array Name := #[
  `Harmonia.Distributed, `Harmonia.Distributed.Membership,
  `Harmonia.Distributed.Protocol, `Harmonia.Distributed.Network,
  `Harmonia.Distributed.Semantics, `Harmonia.Distributed.Properties,
  `Harmonia.Examples.Distributed, `HarmoniaTests.DistributedMembership,
  `HarmoniaTests.DistributedNetwork, `HarmoniaTests.DistributedSteps,
  `HarmoniaTests.DistributedTraces, `HarmoniaTests.DistributedAxiomAudit]
```

Source selection uses product module prefix or membership in this manifest;
namespace selection is an additional independent route. The inventory script
checks the manifest against disk and certified import closure. Adding a new
file requires adding its import and manifest entry, never a theorem-name entry.
The generic scan must inspect selected source axioms even if they are unused;
do that before empty-theorem check, then audit safe definitions and all theorem
dependencies. Do not filter any theorem's collected dependency set.

- [x] Add `DistributedAxiomAudit.lean` imports of all four certified probes
and AuditPolicy with `#audit_distributed`. Add targets:

```lean
lean_lib distributedTest where
  roots := #[`HarmoniaTests.DistributedMembership, `HarmoniaTests.DistributedNetwork,
    `HarmoniaTests.DistributedSteps, `HarmoniaTests.DistributedTraces]
lean_lib distributedAudit where
  roots := #[`HarmoniaTests.AuditPolicy, `HarmoniaTests.DistributedAxiomAudit]
lean_lib distributedAuditRejection where
  roots := #[`HarmoniaTests.DistributedAuditRejection]
```

Initial audit RED should be unknown command; once a deliberately nonchecking
stub exists, negative #guard_msgs probes must fail due to missing errors. Record
both, then implement shared scanner. Retain log `AUDIT PASS: N theorems; observed
axioms [...]; whitelist [...]`; use a distinguishing distributed label without
losing per-theorem results or the foundation summary. For the distributed
summary, union axioms from every checked selected declaration, including safe
definitions, and report checked declaration count as well as theorem count;
retain the original foundation summary contract.

- [x] Construct isolated source fixture `DistributedRejection/Unused.lean`
with `namespace RenamedTrap; axiom unused : Nat; theorem clean : 0 = 0 := rfl`.
In DistributedAuditRejection, #guard_msgs around
`#audit_module HarmoniaTests.DistributedRejection.Unused` must reject unused
axiom even though no theorem depends on it and namespace is outside Distributed.
Separate fixture namespaces test custom axiom indirect dependencies, sorryAx,
newly-added contaminated theorem discovered by #audit_namespace, unknown name
and empty namespace. For #audit_distributed automatic enumeration use an
isolated theorem under Harmonia.Distributed and expect the full command to
reject; put that test last to avoid contaminating earlier audit probes.
Use exact expected Lean diagnostics after inspecting RED output. These modules
contain intentional contaminants and are never certified imports.

- [x] Implement inventory script with standard pathlib/re/argparse/tempfile:
convert root module to relative `.lean`; parse `^\s*import\s+(.+)$` lines and
follow all repository-resident imports recursively. Discover certified source
inventory from `Harmonia/Distributed/**/*.lean`, `Harmonia/Distributed.lean`,
`Harmonia/Examples/Distributed.lean` and the four explicit probe modules.
Discover other `HarmoniaTests/Distributed*.lean`: only certified audit root and
explicit DistributedAuditRejection are known exceptions; any other discovered
file must be in the certified closure and added to the source selector, or
fail. Never exclude files based on substrings such as 'Rejection'; use exact
adversarial paths plus the fixed DistributedRejection directory. Assert all
certified inventory is in certified audit closure and its modules are selected
by audit policy. Parse the exact `distributedSourceModules` definition's `#[...]` block in
AuditPolicy with a bounded regex, extract backtick module names, and compare
its set exactly to discovered certified inventory including the audit root.
Fail for a malformed/missing manifest, missing/extra entries or absent imported
modules. Use module source indices for selection, not declaration-name guesses.
Never permit namespace-prefix selection to excuse an omitted source manifest.
Assert certified foundation closure and distributed closure contain no known
adversarial files. Reject forbidden legacy imports in new product closure.

Script `--self-test` operates on temporary synthetic source trees, tests omitted
module, namespace-independent module inclusion, unused-axiom module inclusion,
unknown new probe file, certified import of adversarial fixture, and missing
import file. Core external imports are skipped only when recognized as installed
Lean modules; missing Harmonia/HarmoniaTests imports fail. Exit nonzero for each
violating synthetic tree and zero for a fully covered clean one. Run actual
inventory separately. This tooling is a tested policy check, not a kernel theorem.

- [x] Extend Ubuntu CI, retaining all existing commands:

```yaml
      - name: Verify running Lean version
        run: lake env lean --version | grep -F 'version 4.16.0,'
      - name: Distributed source and import inventory
        run: python3 scripts/check_distributed_audit.py --self-test && python3 scripts/check_distributed_audit.py
      - name: Distributed formal regression probes
        run: lake build distributedTest
      - name: Distributed certified axiom audit
        run: lake build distributedAudit
      - name: Distributed adversarial audit rejection probes
        run: lake build distributedAuditRejection
```

Do not add distributed rejection to any certified root. AxiomAudit's four
imports stay unchanged. Re-run original foundationsAuditRejection to catch
shared-policy regressions; shared scanner must preserve unknown-name rejection.

- [x] Update ARCHITECTURE/README with actual implemented API and guarantees,
explicit atomicity/knowledge/fault/fairness boundaries and dedicated commands.
Update receipt with each model, assumption, observed theorem counts and axioms,
red/green failures, preflight decisions and any unresolved risks. No claim that
Hosted Linux CI or physical Grok final review ran until coordinator provides
that evidence.
- [x] Run the final matrix serially and inspect each exit/output:

```sh
lake env lean --version
lake build
lake build foundationsTest foundationsAudit foundationsAuditRejection
python3 scripts/check_distributed_audit.py --self-test
python3 scripts/check_distributed_audit.py
lake build distributedTest distributedAudit distributedAuditRejection
lake env lean HarmoniaTests/AxiomAudit.lean
lake env lean HarmoniaTests/DistributedAxiomAudit.lean
lake env lean HarmoniaTests/AuditRejection.lean
lake env lean HarmoniaTests/DistributedAuditRejection.lean
git diff --check
```

Fresh elaboration audit commands avoid relying only on cached output. Scan
certified product and probes for `sorry|admit|sorryAx|axiom`; exclude isolated
adversarial files explicitly, inspect comments separately. Confirm source/import
inventory and no legacy/toolchain/Core semantic diff. Run source-level shape
check of Protocol and review full react signature. Require zero failures,
report actual counts/axioms rather than anticipating them. Stage named source,
doc/script/CI files only; commit `test: audit distributed sources and enforce dedicated verification in CI`.

## Self-review and handoff

Coverage: membership/knowledge → Task 1; occurrence/multiplicity/fresh IDs →
Task 2; running guards/atomic publication/fault policy/init/observations →
Task 3; frames/durability/representation lifting/WF/provenance → Task 4;
all hostile behaviors/nonvacuous histories → Task 5; source coverage/unused
axioms/rejection separation/CI/observed evidence → Task 6.

Implementation stops after local verification for physical Grok review through
parent coordinator; coordinator owns reviewed integration, remote Linux CI,
push/PR/merge. Do not request redundant human design authorization. Return
worktree, branch, commit chain, receipt, commands/exit codes/counts, exact proved
scope and remaining review risks. The first design invocation stopped before Task 1; all six implementation tasks
are now locally verified. Final independent review remains coordinator-owned.

## Physical Grok preflight pins (2026-10-04)

Physical Grok ACCEPT was read from `/private/tmp/harmonia-stage-two-preflight-verdict.md`.
This text review is not a kernel proof. Coordinator reports the original review
terminated after 764.1s, exit 143, with no verdict; compact streaming retry
completed after 564.0s, exit 0, ACCEPT. Six pins govern implementation:

1. actorOf deliver is recipient, never sender; process/crash/recover actor,
   drop/duplicate none. Prove/probe this alongside frame.
2. Name PoolEq.symm, PoolEq.init_iff, PoolEq.wf_iff and execution_permutation
   (same labels and related endpoint); prove all, not just prose assertions.
3. Actual Core.Invariant imports Core.Execution, which imports TransitionSystem.
   Parent verification and local source reading resolve the omitted-Core concern.
   Use those imports and real Foundation.Execution.nil/cons, no invented module.
4. One file Harmonia.Examples.Distributed is imported by DistributedTraces.
   Its namespace Harmonia.Distributed.Examples does not determine source origin.
5. Universal wrong-outs negations for both process and deliver, with other
   premises legal. No spent-tid replay in reachable WF pools; malformed raw pools
   may contain duplicate tids and permit a second consumption. Distinguish them.
6. reliable has all four flags false; prove reliable_no_drop, reliable_no_duplicate,
   reliable_no_crash, reliable_no_recover and independent recovery gating.

Global next/tid are mathematical bookkeeping, not a central runtime service,
and are not passed to protocols. No native_decide in certified proofs. Envelope
origin identifies prior envelope publication, not the allocating step of every
tid, and does not authenticate payload claims. Exhibit distinct payloads under
one logical ID. Inventory parser tests multiline manifests, multiple imports,
trailing comments, unknown/unimported namespace-escape files, unused axioms and
adversarial contamination. Fixed-closure discipline and abstract atomic update/
publication assumptions remain explicit; no physical IO or fairness guarantee.

## Implemented policy rulings

The auxiliary source-axiom scan uses Lean declaration ranges: unsafe compiler
placeholders with no range are exempt, while ranged unsafe source axioms reject.
No theorem dependency is filtered. Physical metadata probe distinguished these
cases, and isolated normal/unsafe unused-axiom modules exercise the policy.
Inventory tests live in scripts/test_distributed_audit.py and are invoked by
--self-test; recursive discovery covers nested Distributed probe modules too.
The rejection target explicitly lists both fixture modules to satisfy Lake's
module ownership; neither is a certified import. Lean 4.16 type rejection uses
fail_if_success instead of unavailable #check_fail. No semantic obligation changed.
