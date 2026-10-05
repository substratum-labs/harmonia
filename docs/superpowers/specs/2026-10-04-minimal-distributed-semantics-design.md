# T-392 minimal distributed semantics design

Status: design/plan handoff, physical Grok preflight ACCEPT; implementation authorized.
Owner: physical Codex. Reviewer: physical Grok through parent coordinator.
Date: 2026-10-04. Baseline: `d0b2fa497f69eb702733d3ef87c989c7e31e40db`.

## Intent and authority

Instantiate the approved [minimal formal core](2026-10-04-minimal-formal-core-design.md)
with the smallest useful asynchronous crash/omission distributed model. The
result must expose membership, local knowledge, occurrence consumption and
crash/recovery assumptions as formal interfaces and kernel-checked obligations.
It must include nonvacuous examples of behavior that exactly-once or FIFO
assumptions would incorrectly exclude. This is architectural work, using
brainstorming and writing-plans. The user's preserved managed authorization
replaces repeated human design approval; physical Grok preflight precedes code.
This invocation writes only spec, plan and baseline receipt. No product or test
implementation, agents, ledger edits, push, PR or integration.

## Global constraints

- Keep `lean-toolchain` pinned to `leanprover/lean4:v4.16.0`.
- Lean core only; no mathlib or new dependencies.
- Preserve stage-one `Harmonia.Foundation` semantic contracts and source modules.
- No Veil, Kadmos, consensus protocol, crypto, fairness/liveness, infinite execution, extraction, codegen or SMT.
- Preserve legacy experiments; claim no behavioral connection without a correspondence theorem.
- No `sorry`, `admit`, `sorryAx` or custom axioms in certified proofs.
- No message-count or execution-depth bound in the semantics.
- Parent coordinator owns internal ledger and physical Grok review; no subagents.

## Alternatives and decisions

**Membership:** use a checked list of external node identities and a member
subtype. `Fin members.length` also makes actors finite, but forces users to
translate indices to identities and prove the translation injective. Raw
identities with global guards keep signatures shorter but repeat membership
obligations in every rule and allow accidental omissions. The subtype retains
external names, rejects duplicates, and excludes nonmembers from every endpoint
and actor position. Configuration order enumerates members; it gives no network
or scheduling order. Equality of node identities is decidable, with no global
`Fintype` requirement. The list itself witnesses finiteness.

**Network:** core `List` occurrences with `List.Perm`, rather than quotient
multisets or a head-pop list. Lean 4.16 core supplies permutation, nodup and
length lemmas. A pure quotient multiset would hide representation order but
adds quotient lifting and API burden without improving this small model.
Head-pop incorrectly restricts delivery. All network premises/conclusions are
permutation-based, with a full step congruence theorem. There is no administrative
reorder transition: reordering is representation equivalence.

**Publication:** outgoing transmissions are published atomically with a local
or receive transition. A separate send staging queue would add another
persistence/fault boundary and proof obligations. Labels explicitly carry the
ordered finite outgoing list; allocation records each send occurrence. The
abstract transition includes durable update, volatile update and publication,
without asserting physical storage/network IO atomicity. A later adapter may
refine this into several steps with an explicit persistence contract.

## Membership API

All new public declarations live in `Harmonia.Distributed` (fixtures may use a
nested Examples namespace). Initial implementation can use one universe for
all parameter types; Foundation remains universe-polymorphic.

```lean
structure Config (N : Type u) where
  members : List N
  distinct : members.Nodup

def Config.checked [DecidableEq N] (xs : List N) : Option (Config N) :=
  if h : xs.Nodup then some ⟨xs, h⟩ else none
abbrev Member (c : Config N) := { n : N // n ∈ c.members }
-- With [DecidableEq N], member equality is decidable.
def Config.member? [DecidableEq N] (c : Config N) (n : N) : Option (Member c) :=
  if h : n ∈ c.members then some ⟨n, h⟩ else none
```

Never deduplicate. Prove checked failure iff `¬ xs.Nodup`, success preserves
exact list order/content, and `Member.property` supplies membership. Empty
configuration succeeds. Its member type is empty, so no process, receive,
crash or recover label can be formed; initialized empty pool enables no drop
or duplicate either. A zero-step initialized execution exists even then.
Initial predicates may be inconsistent for a particular nonempty protocol;
there is no universal inhabitance assertion. Explicit two-node initial witness
is mandatory, independent of the empty case.

## Local knowledge and message types

Use parameters `D V L P C K : Type u`: durable data, volatile data, logical ID,
payload, local command and timeout token. Write `M := Member c` in explanations.
These are parameters, not a shared DSL or a consensus vocabulary.

```lean
inductive Status where | running | crashed
structure Local (D V : Type u) where
  durable : D
  volatile : V
  status : Status
structure Outgoing (M L P : Type u) where
  recipient : M
  logical : L
  payload : P
structure Envelope (M L P : Type u) where
  sender : M
  recipient : M
  logical : L
  payload : P
structure Transmission (M L P : Type u) where
  tid : Nat
  envelope : Envelope M L P
inductive Stimulus (C K : Type u) where
  | local : C → Stimulus C K
  | timeout : K → Stimulus C K
inductive Input (M L P C K : Type u) where
  | message : Envelope M L P → Input M L P C K
  | scheduled : Stimulus C K → Input M L P C K
structure Protocol (M D V L P C K : Type u) where
  initial : M → D → V → Prop
  react : M → D → V → Input M L P C K →
    D → V → List (Outgoing M L P) → Prop
  crashReset : D → V → V
  recover : D → V
```

`react` is nondeterministic and can be disabled. It gets actor, its own D/V,
and explicit input only. No global state, other local states, pending pool,
fault profile or scheduler oracle argument is available. Message evidence is
exactly the envelope's sender, recipient, logical ID and payload; timeout/local
inputs contain only their supplied values. Transmission ID is transport
bookkeeping and is not passed to the protocol. A protocol may encode explicit
peer claims in P, but those claims do not become a global-state read.

The typed signature enforces the argument boundary, not an epistemic theorem
about arbitrary Lean closures. Fixed protocol definitions must not capture a
changing global state or an external oracle. Static configuration knowledge
is permitted. Global proof predicates may inspect all nodes and messages.
Outgoings omit sender: the global publication rule stamps the acting member,
preventing false transport provenance. No Byzantine forge rule exists. Logical
IDs are application-defined, need not be globally unique, and may be reused
by retry sends; payload equality is not inferred merely from matching IDs.
Duplication, in contrast, preserves the complete envelope exactly.

## Global state, labels and observations

```lean
structure State (M D V L P : Type u) where
  nodes : M → Local D V
  pending : List (Transmission M L P)
  next : Nat
structure FaultProfile where
  allowDrop : Bool
  allowDuplicate : Bool
  allowCrash : Bool
  allowRecover : Bool
inductive Label (M L P C K : Type u) where
  | process : M → Stimulus C K → List (Outgoing M L P) → Label M L P C K
  | deliver : Transmission M L P → List (Outgoing M L P) → Label M L P C K
  | drop : Transmission M L P → Label M L P C K
  | duplicate : Transmission M L P → Label M L P C K
  | crash : M → Label M L P C K
  | recover : M → Label M L P C K
```

Profile is a fixed parameter of the model, never mutable state or a protocol
argument. `reliable` is all four flags false: fault-free, with no delivery
progress promise. `crashRecovery` permits crash and recover but neither drop
nor duplicate. `omission` permits all four. Any custom combination is explicit;
recover has an independent gate. Calling a profile reliable means drop and
duplicate are prohibited; it never implies eventual delivery or fair scheduling.

Observation is `Label` itself. The embedded system requires `o = a`, preserving
actor, stimulus, consumed/source transmission and outgoing sends in finite
history. Process sends are identified by pre-state next supply and outgoing
position, not separate scheduler actions. Crash, recover, drop and duplicate
are observable. A later observation map may hide fields; this stage makes no
trace equivalence claim under such a map.

## Occurrence and publication relations

For lists of transmissions define:

```lean
def Take (pool : List T) (e : T) (rest : List T) : Prop :=
  List.Perm pool (e :: rest)
```

Take removes exactly one occurrence, even if full transmission values repeat
in malformed states. Reachable well-formed states have unique `tid`, so an ID
identifies one transmission instance. No equality decision on P or L is needed.
`Take.length` proves `pool.length = rest.length + 1`. Prove `Take.perm_left`,
`Take.rest_unique` up to permutation, and `Take.middle` for any prefix/suffix.

`allocate actor n outs` structurally recurses on `outs`: empty yields `[]`;
head is transmission `tid := n`, envelope stamped with actor and head fields;
tail starts at `n + 1`. IDs are exactly the interval from n inclusive to
n + outs.length exclusive, without a fixed bound. Output order chooses IDs
only; it imposes no delivery order. Define `Publish actor n outs base result :=
List.Perm result (base ++ allocate actor n outs)`.

Local processing uses `base = s.pending`. Delivery uses a witness `rest`
satisfying `Take s.pending e rest` and publishes into rest. Both set next to
`s.next + outs.length`. Each emitted occurrence is explicit in the label's
outs and uniquely determined allocation. Output finiteness follows from List,
not a bounded semantics. Duplicate uses fresh `tid := s.next`, exact old envelope,
keeps the source, advances next by one, and permits any permutation of the
source pool plus the copy. Drop consumes one occurrence and does not advance
next. IDs never reset on crash, recovery, receive or drop.

## Transition equations

`setNode nodes actor value := fun peer => if peer = actor then value else nodes peer`.
Write `Step c protocol profile s label t` as an inductive relation with exactly
these six constructors; the following are their complete semantic premises:

| Constructor | Premises and resulting state |
| --- | --- |
| process actor stimulus outs | actor running; `react actor oldD oldV (.scheduled stimulus) d v outs`; t.nodes = setNode with `(d,v,running)`; Publish into old pool; t.next = old next + outs.length |
| deliver e outs | e.envelope.recipient running; Take old pool e rest; `react e.envelope.recipient oldD oldV (.message e.envelope) d v outs`; update recipient only to `(d,v,running)`; Publish into rest; t.next = old next + outs.length |
| drop e | allowDrop = true; Take old pool e rest; t.nodes = s.nodes; t.pending = rest; t.next = s.next |
| duplicate e | allowDuplicate = true; e ∈ s.pending; t.nodes = s.nodes; t.pending Perm `(freshCopy e s.next :: s.pending)`; t.next = s.next + 1 |
| crash actor | allowCrash = true; actor running; update actor to `(oldD, crashReset oldD oldV, crashed)`; pending and next equal old values |
| recover actor | allowRecover = true; actor crashed; update actor to `(oldD, recover oldD, running)`; pending and next equal old values |

For drop, a permuted rest can always be chosen by Take; requiring equality to
the witness does not constrain observable network order. `react` never changes
status. No receive, local action or timeout while crashed. Crash resets V via
the explicit function, which may preserve protocol-selected portions; “loss”
is illustrated by a reset-to-zero fixture, not mandated for every V. Recovery
rebuilds from D only. Neither function changes D. Inflight messages survive
crash and recovery unchanged and may deliver after recovery. Self-send is legal
when the endpoint is configured. Drop/duplicate may affect messages to crashed
recipients; neither invokes protocol code. Crash/recovery require both profile
permission and the correct process precondition. No rule forces a next step.

`system c p f : Foundation.TransitionSystem (State ...) (Label ...) (Label ...)`
has init: pending = [], next = 0, and each configured node is running and its
D/V satisfy p.initial. Step is `Step c p f s a t ∧ o = a`. Foundation's existing
finite Execution, Reachable and invariant are used unchanged.

## Required theorem surface

Use implicit model/type binders consistently. These are propositions to prove,
not axioms; final binder elaboration is checked before downstream work.

| Theorem | Exact obligation / proof method |
| --- | --- |
| Config.checked_rejects | checked xs = none ↔ ¬ xs.Nodup; split dependent if |
| Config.checked_preserves | checked xs = some c → c.members = xs |
| member_configured | ∀ m : Member c, m.val ∈ c.members; subtype evidence |
| setNode_other | peer ≠ actor → setNode nodes actor value peer = nodes peer |
| Take.length / middle / rest_unique | exact-one length decrease; arbitrary position selectable; residuals permutation-related via cons_inv |
| allocate_ids / allocate_sender | ID map is interval and every envelope sender is actor |
| allocate_fresh | all allocated IDs ≥ n and < n + outs.length, nodup; induction on outs |
| Step.permutation_lift | PoolEq s s' → Step c p f s a t → ∃ t', Step c p f s' a t' ∧ PoolEq t t' |
| Step.frame | Step ... s a t → ∀ peer, actorOf a ≠ some peer → t.nodes peer = s.nodes peer |
| crash_durable / recover_durable | corresponding step label preserves target D (and frame preserves others) |
| deliver_consumes | deliver step → ∃ rest, Take s.pending e rest ∧ Publish e.envelope.recipient s.next outs rest t.pending |
| duplicate_fresh | WF s → duplicate step → new tid absent from old pool, envelope identical, source retained, and next advances |
| wf_initial / wf_preserved | Initially system WF; Preserved system WF, covering every successor of all six constructors |
| reachable_wf | ∀ s, Foundation.Reachable system s → WF s, via Foundation.invariant |
| reliable_no_drop / reliable_no_duplicate | ∀ s e t, ¬ Step ... reliable s (.drop e) t, and duplicate analog |
| provenance_history | initialized finite execution → each final pending envelope equals an envelope stamped by some process/deliver publication in that history |

`PoolEq s t := s.nodes = t.nodes ∧ s.next = t.next ∧ List.Perm s.pending t.pending`.
Prove step lifting for arbitrary states, without WF premises; Take's witnesses
and Publish's permutation conclusions make this possible. Symmetry of PoolEq
gives lifting in both directions. Crash/recover preserve the exact input list
representation, so their lifted successor uses the reordered input pool. An iff
with independently reordered output lists would be false; the required congruence
is existence of a related successor. This is stronger than one nonhead example. Also lift to finite executions: PoolEq start
states and Execution from one imply an Execution with identical labels from
the other and PoolEq endpoints. The system's initial predicate and WF respect
PoolEq. This supplies the formal representation boundary without quotienting
State or modifying Foundation.

`WF s := (s.pending.map (fun e => e.tid)).Nodup ∧
  ∀ e, e ∈ s.pending → e.tid < s.next`.
Membership of actors/endpoints is by typing, not an extra partial predicate.
Allocate disjointness follows because old IDs < old next and new IDs ≥ old
next. Take preserves nodup and ID bounds for residuals; Publish transports
through permutation. Duplicate uses old next, absent by the strict bound;
crash/recover preserve pool and supply. Nondecreasing next and allocation
intervals establish no reuse along initialized executions, including after loss.

Provenance history is separate from WF: uniqueness alone would allow a forged
initial pool if initialization were omitted. Define `emitted c s label` to be
allocated envelopes for process/deliver labels, empty otherwise. Define an
inductive `SentIn path envelope` indexed by a Foundation Execution proof:
cons admits an envelope in the head step's emitted list or in the tail's
SentIn. Prove a stronger pending-origin lemma with an arbitrary initial pool:
final pending envelope either appears in start pending or SentIn path. Empty
initialized pools eliminate the first case. Duplicate does not create a new
origin; it copies an envelope already pending. No crypto authentication theorem
is claimed. Protocol safety still needs separate initial/preservation proofs;
network WF does not imply agreement, deduplication or application correctness.

## Behavioral fixtures and acceptance

Use external Nat nodes `[0,1]`, D/V = Nat, L = Nat, P = Unit, C = Member c,
K = Unit. Initial D = V = 0. Local command to peer increments actor D/V and
emits logical ID 7; timeout increments own V only and emits nothing; receipt
increments recipient D/V and emits nothing. crashReset returns 0; recover
returns D. Thus repeated deliveries visibly change D twice. This is a small
message-counting example, not a distributed protocol safety claim.

Prove actual initialized send(0→1), crash(1), recover(1), deliver(tid 0) execution:
recipient D/V/status goes `(0,0,running)` → `(0,0,crashed)` →
`(0,0,running)` → `(1,1,running)`; pool survives both faults and ends empty.
A second trace first delivers once, then crashes/rebuilds nonzero D:
`(1,1,running)` → `(1,0,crashed)` → `(1,1,running)`.
A duplication trace sends, duplicates tid 0 to tid 1, delivers both: same
logical envelope, different occurrences, final recipient D = 2. A retry trace
sends ID 7 again with fresh tid even without duplication permission.

Required positive/negative probes include duplicate `[0,0]` rejection, failed
lookup of external 2 and type rejection for raw nonmember actor/recipient;
empty and two-node initial witnesses; running peer yet timeout allowed;
no receive/local/timeout on crashed node; no crash of crashed node or recovery
of running node; independently disabled crash/recover/drop/duplicate flags;
nonhead delivery and drop plus reordered-pool congruence; no second consumption
of a spent tid unless another occurrence exists; unchanged other node, and
three-node fixture with node 2 untouched during actor 0 / recipient 1 steps;
volatile loss/rebuild at nonzero D; multiple emissions allocated distinctly,
zero emissions preserving supply, self-send; wrong observation rejection;
nonempty initial pool rejection. Negative step probes quantify over all possible
successors, not a selected bad successor. Type probes use #check_fail or
#guard_msgs and source-shape checks to protect the restricted Protocol signature.
No behavioral fixture is merely a proof of True.

## Audit and verification boundary

Add `distributedTest`, `distributedAudit`, `distributedAuditRejection`. Reuse
AuditPolicy through a generic selected-declaration scan, retaining the existing
foundation selection and command. Distributed selection covers namespace
`Harmonia.Distributed`, source modules under `Harmonia.Distributed`, the example
module and all certified distributed probes regardless of declaration namespace.
Audit every theorem transitively, plus all selected safe definitions and all
selected source axioms (even unused). Maintain whitelist propext, Quot.sound,
Classical.choice; report actual theorem count and observed axiom union.
Compiler-only unsafe specializations may retain the current exception, but
never exempt source axioms or filter any theorem's dependencies.

A source-import inventory check must establish that every new certified source
module is in the distributed audit import closure; loaded-environment scanning
cannot detect an unimported file. It must fail for an unlisted module or for an
adversarial fixture in a certified closure. Isolated rejection tests exercise
transitive custom axioms, sorryAx, automatic new-theorem coverage, renamed
namespace/source-module selection, unused source axiom, absent declarations,
empty selection, and the inventory policy. Preserve foundationsAuditRejection;
no adversarial root is imported by certified modules. Implement new tooling
only in the future execution stage.

Extend the existing Ubuntu workflow with actual Lean version verification,
source-inventory check and all three distributed targets, keeping all foundation
commands. Mac CLI checks provide physical local evidence; hosted Linux results
must be separately observed by coordinator. Future final receipt lists commands,
exit codes, theorem counts, actual axioms, models and assumptions. No solver or
finite-exploration claim substitutes for a kernel proof.

## Risks and preflight questions for Grok

Review subtype proof ergonomics, multi-output allocation/disjointness, universal
permutation lifting, and whether full labels sufficiently record publication.
Confirm the chosen atomicity is acceptable for this abstract stage and leaves
physical IO for later refinement. Review provenance history induction and the
audit inventory/unused-axiom policy together; both close gaps that WF or loaded
namespace enumeration alone cannot close. All listed theorem signatures are
intended obligations, not claims of implemented proof. Local core probes confirm
available building blocks; complete elaboration and proof complexity remain
implementation risks. See [receipt](../../verification/2026-10-04-minimal-distributed-semantics.md)
and [plan](../plans/2026-10-04-minimal-distributed-semantics.md).

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
