# T-400 CAP model and verification

The Lean development follows the write-then-read indistinguishability argument
in Gilbert and Lynch, *Brewer's Conjecture and the Feasibility of Consistent,
Available, Partition-Tolerant Web Services* (SIGACT News, 2002), Theorem 1:
https://www.comp.nus.edu.sg/~gilbert/pubs/BrewersConjecture-SigAct.pdf.

## Model and assumptions

- `Partition` carries two nonempty, disjoint node lists. The abstract protocol
  state aggregates all nodes within each component. The partitioned product
  transition system allows only a G1-local or G2-local transition, preserving
  the other component's state. It has no cross-component delivery transition.
  Local silent transitions can represent any finite internal processing or
  within-component communication. This is a permanent-cut model; it does not
  construct a packet-level network or prove a refinement from another network
  implementation.
- `Op` and `Resp` describe a one-register read/write API. A `complete` action
  packages one request and response as a visible event. Arbitrarily many silent
  steps can precede completion. Separate invocation and response timestamps,
  overlapping operations, fairness, and crash behavior are outside this model.
  The contradiction uses only a completed write before a read starts.
- `Available` requires a finite completing trace for either operation from
  every reachable local state on either side, with a correctly shaped
  response. The theorem extracts the particular write and read traces.
- `Linearizable` requires each finite completed history of the partitioned
  product system to obey the sequential register specification in observed
  completion order. This is stronger than standard interval-based
  linearizability for overlapping operations; its required nonoverlapping
  write-then-read and initial-read consequences are the ones used by the
  impossibility proof.
- `partition_replay` constructs the combined global execution from the two
  local traces. It proves the G2 read response remains possible after the G1
  write, because G1 steps preserve G2 state. The register specification then
  forces the same answer to equal both distinct values.

## Verification record

The certified source is `Harmonia/Theorems/CAP.lean`, with positive examples
in `HarmoniaTests/CAPTest.lean`. Deliberate axioms and `sorryAx` appear only in
`HarmoniaTests/CAPRejection.lean`, which is isolated from certified targets.
`#audit_cap` checks all declarations selected by source module or CAP
namespace, allowing only `propext` and `Quot.sound`; the static checker also
verifies manifest coverage, import isolation, and source-token restrictions.

The result is a kernel-checked theorem about this abstract product-state
model. The audit and finite exploration fixtures do not establish a
correspondence with any executable application or the legacy 2PC/SMT/C code.

## Observed results (2026-10-09)

On macOS with `leanprover/lean4:v4.16.0`, `lake build`, the dedicated
foundation and CAP targets, `python3 scripts/check_cap_audit.py --self-test`,
and `python3 scripts/check_cap_audit.py` all passed. A fresh Linux/amd64
Ubuntu 24.04 container installed the same Lean toolchain and Python 3,
copied the source without `.lake` or `.git`, and passed the same commands.
The five hostile static mutation tests passed on both platforms. The CAP
audit reported 63 theorems, 157 declarations, observed axioms `[propext]`,
and whitelist `[propext, Quot.sound]`. No build warnings or errors were
reported by the final verification runs.

The physical Grok read-only review returned **ACCEPT** for the theorem under
the documented product-state model. It confirmed the initial-read and
write-then-read contradiction and called out the same scope boundaries:
aggregate component state, no packet-network refinement, and atomic
completion events rather than overlapping operation intervals.
