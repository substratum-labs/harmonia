# FLP impossibility proof status

Toolchain: `leanprover/lean4:v4.16.0`. The theorem modules import Lean `Init`
through `Harmonia.Core.Execution`; they do not import Mathlib.

## Model

`Config` contains process-local state, a buffer multiplicity for each
destination/message pair, and per-process decision status. A deterministic
`Protocol` reads only the target process state and delivered message. Each
event delivers one buffered copy or performs a silent tick. Sends add natural
counts; a proved invariant keeps reachable buffers nonnegative when the
initial buffer is nonnegative. The buffer is commutative, so disjoint process
events commute exactly even when both send to the same destination. An existing
decision register is write-once; `decisions_persist_step` proves persistence
for every protocol in this transition model.
The same invariant is proved for every state of an infinite run that starts
from a nonnegative buffer.

An `InfiniteRun` records an event and configuration at every natural time.
`NonFaulty` means that the process takes a step at arbitrarily late times.
`Admissible` allows at most one process to take only finitely many steps. For
each pending message kind at **every** nonfaulty process, including a process
named as the possible fault, sufficiently many later matching
deliveries must occur to account for every copy present at the earlier time.
The multiplicity model does not identify individual message instances.

## Kernel-checked results and premises

- `flp_lemma1_diamond`, `flp_lemma1_schedule`, and
  `flp_lemma1_schedules`: disjoint process events and two finite schedules
  commute, given local deterministic update rules.
- `flp_lemma2_initial_bivalent`: a finite chain of initial binary-input
  configurations, opposite endpoint outcomes, replay of steps by other
  processes, and a finite deciding trace when any selected process stays
  silent imply an initial bivalent configuration. The concrete replay
  obligation is discharged by `IndistinguishableExcept`.
- `initial_bivalent_from_binary_inputs` builds that chain from a finite
  exhaustive node list and an initial-configuration map that preserves every
  other process's view when one input changes. Weak binary validity supplies
  opposite endpoint outcomes.
- `initial_crash_deciding_of_reachable` converts one-crash deciding from all
  states reachable from each initial configuration into the initial-state
  premise used by Lemma 2. The converse is not established.
- `flp_lemma3_bivalence_step`: a bivalent reachable configuration and any
  enabled event admit a finite schedule delaying that event, then applying it
  while retaining bivalence. It assumes `CrashDecidingReachable` and
  `DecisionsPersist`, both explicit protocol obligations. The crash premise
  requires a deciding process distinct from the silent process.
- `no_uniform_decision_bound`: under agreement and the preceding finite
  obligations **and an initially bivalent configuration**, no single
  event-count bound forces every schedule to decide.
- `flp_impossibility`: takes the binary input map, finite exhaustive node
  list, one-input-flip indistinguishability, binary validity, agreement,
  reachable one-crash deciding for each input, and persistence. It derives an
  initial bivalent witness via Lemma 2, then applies Lemma 3 to refute a
  uniform finite decision bound for that witness.
- `bivalent_stage_not_acc`: the relation of positive bivalence-preserving
  stages is not accessible at a reachable bivalent state, so that stage
  relation is not well founded. This remains a proposition-level result;
  it does not exhibit an infinite path.
- `no_termination_of_fair_bivalent_run`: any supplied admissible infinite
  run that remains bivalent refutes guaranteed termination. This theorem does
  not construct the run.

## Remaining theorem boundary

The certified `flp_impossibility` is the connected **finite-bound** theorem.
`bivalent_stages_not_well_founded` is a separate proposition-level corollary.
Neither theorem constructs a fair infinite run or refutes
`GuaranteedTermination` directly.

`no_termination_of_fair_bivalent_run` assumes an `Admissible` infinite run
whose every state remains bivalent. A p. 379 stage queue, constructive
selector, and proof that its generated run is admissible remain open. The
finite-bound theorem does not imply this infinite-run statement without
an additional compactness or scheduling argument. The certified theorem
dependency whitelist remains `[propext, Quot.sound]`.

The historical 2PC/SMT/C modules are not connected to this FLP model.

## Observed checks (2026-10-11, macOS)

- `lake build`: passed.
- `lake build flpTest flpAudit flpAuditRejection`: passed; FLP audit checked
  107 theorems and 270 declarations with observed axioms
  `[Quot.sound, propext]`.
- `python3 scripts/test_flp_audit.py`: six hostile mutation tests passed,
  including insertion of `Classical.choice` into a certified source file.
- `python3 scripts/check_flp_audit.py`: `FLP CHECK PASS`.
