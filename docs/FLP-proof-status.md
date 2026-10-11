# T-401 FLP proof status

Toolchain: `leanprover/lean4:v4.16.0`. The theorem modules import Lean `Init`
through `Harmonia.Core.Execution`; they do not import Mathlib.

## Model

`Config` contains process-local state, a buffer multiplicity for each
destination/message pair, and per-process decision status. A deterministic
`Protocol` reads only the target process state and delivered message. Each
event delivers one buffered copy or performs a silent tick. Sends add natural
counts; a proved invariant keeps reachable buffers nonnegative when the
initial buffer is nonnegative. The buffer is commutative, so disjoint process
events commute exactly even when both send to the same destination.
The same invariant is proved for every state of an infinite run that starts
from a nonnegative buffer.

An `InfiniteRun` records an event and configuration at every natural time.
`Admissible` allows at most one process to stop taking steps. For each pending
message kind at a nonfaulty process, sufficiently many later matching
deliveries must occur to account for every copy present at the earlier time.
The multiplicity model does not identify individual message instances.

## Kernel-checked results and premises

- `flp_lemma1_diamond` and `flp_lemma1_schedule`: independent events and
  schedules commute, given local deterministic update rules.
- `flp_lemma2_initial_bivalent`: a finite chain of initial binary-input
  configurations, opposite endpoint outcomes, replay of steps by other
  processes, and a finite deciding trace when any selected process stays
  silent imply an initial bivalent configuration. The concrete replay
  obligation is discharged by `IndistinguishableExcept`.
- `initial_bivalent_from_binary_inputs` builds that chain from a finite
  exhaustive node list and an initial-configuration map that preserves every
  other process's view when one input changes. Weak binary validity supplies
  opposite endpoint outcomes.
- `flp_lemma3_bivalence_step`: a bivalent reachable configuration and any
  enabled event admit a finite schedule delaying that event, then applying it
  while retaining bivalence. It assumes `CrashDecidingReachable` and
  `DecisionsPersist`, both explicit protocol obligations. The crash premise
  requires a deciding process distinct from the silent process.
- `no_uniform_decision_bound`: under agreement and the preceding finite
  obligations, no single event-count bound forces every schedule to decide.
- `bivalent_stage_not_acc`: the relation of positive bivalence-preserving
  stages is not accessible at a reachable bivalent state, so that stage
  relation is not well founded. This remains a proposition-level result;
  it does not exhibit an infinite path.
- `no_termination_of_fair_bivalent_run`: any supplied admissible infinite
  run that remains bivalent refutes guaranteed termination. This theorem does
  not construct the run.

## Remaining theorem boundary

The finite choice-free FLP impossibility theorem `flp_impossibility` is proved
and certified: under agreement, validity (binary input chain), one-crash deciding,
and decision persistence, no uniform finite decision bound exists
(`no_uniform_decision_bound`), and the bivalent stage transition relation is not
well-founded (`bivalent_stages_not_well_founded`). This proves impossibility of
deterministic consensus without invoking `Classical.choice`.

For the classical infinite-run formulation (`no_termination_of_fair_bivalent_run`),
constructing an infinite sequence from existential step witnesses in an unconstrained
type theory requires dependent choice (`Classical.choice`). Keeping `flp_impossibility`
at the finite-bound level preserves the strict `[propext, Quot.sound]` axiom whitelist.

The historical 2PC/SMT/C modules are not connected to this FLP model.

## Observed checks (2026-10-11, macOS)

- `lake build`: passed.
- `lake build flpTest flpAudit flpAuditRejection`: passed with 0 warnings, 0 errors.
- `lake build flpAudit`: PASSED with 98 theorems, 256 declarations, observed axioms `[Quot.sound, propext]`, zero `sorry`, zero `Classical.choice`.
- `python3 scripts/test_flp_audit.py`: five hostile mutation self-tests passed.
- `python3 scripts/check_flp_audit.py`: `FLP CHECK PASS`.
- Final independent reviewer verdict pending.
