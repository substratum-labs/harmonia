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
- `flp_lemma3_bivalence_step`: a bivalent reachable configuration and any
  enabled event admit a finite schedule delaying that event, then applying it
  while retaining bivalence. It assumes `CrashDecidingReachable` and
  `DecisionsPersist`, both explicit protocol obligations.
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

The standard FLP conclusion requires constructing an infinite admissible
nondeciding run from Lemma 3's existential finite extensions. For the generic
protocol model, selecting successive extensions is a dependent-choice step;
Lean's generic choice principle would appear as `Classical.choice` in the
axiom audit, contrary to T-401's strict whitelist. A constructive selector
with a proved fair stage policy, or a changed audit policy, is needed before
the final impossibility claim can be certified. The audit deliberately names
`flp_impossibility` so it remains red while that declaration is absent.

Additional model obligations for a faithful universal theorem include a
finite or enumerable process/message domain, finite support of each send, and
a fair policy for selecting process and pending message occurrences. They
are not consequences of the current unconstrained `send` function.

The historical 2PC/SMT/C modules are not connected to this FLP model.

## Observed checks (2026-10-11, macOS)

- `lake build`: passed.
- `lake build flpTest flpAuditRejection`: passed, including the isolated
  `#guard_msgs` rejection fixture.
- `python3 scripts/test_flp_audit.py`: five self tests passed.
- `lake build flpAudit`: failed as intended at the explicit
  `flp_impossibility` declaration check. Its preceding source-wide axiom
  report counted 89 theorems and observed only `propext` and `Quot.sound`.
- Linux verification and the final independent reviewer verdict are pending.
