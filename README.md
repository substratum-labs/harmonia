# Harmonia (Ἁρμονία)

Harmonia independently develops formal foundations for distributed algorithms
in Lean. Kadmos is an application, rather than the definition of the Core API.
The approved canonical design is
[the foundation-first design](docs/superpowers/specs/2026-10-04-minimal-formal-core-design.md).

Stage one provides kernel-checked generic relational transition systems,
finite labeled executions, reachability, invariant induction, and one-step
observation-preserving forward simulation lifted to executions. State, action
and observation types are parameters; steps may be nondeterministic or disabled.
The new API lives in `Harmonia.Foundation` and uses Lean 4.16.0's standard
library only. See [architecture](ARCHITECTURE.md) and the
[verification receipt](docs/verification/2026-10-04-foundations-stage-one.md)
for exact guarantees, assumptions and RED/GREEN evidence.

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake build
lake build foundationsTest
lake build foundationsAudit
```

`lean-toolchain` pins `leanprover/lean4:v4.16.0`. Foundation verification needs
no SMT solver. The audit enumerates every theorem from the imported new modules,
checks transitive dependencies and prints each theorem's axiom set. Isolated
adversarial fixtures verify rejection of custom axioms and `sorryAx`; they are
not imported into the certified foundation audit.

The legacy CLI remains available as `lake exe harmonia`; its SMT demonstrations
require Z3. `Event`, `Network`, `SmallStep`, handwritten 2PC, DSL datatype macros,
SMT queries, C exports and Rust experiments remain legacy prototypes. The Lean
2PC model, SMT behavior and C gatekeeper are not proved compiler-connected.
Timestamp comparison in the legacy Event model does not establish message
causality. No FLP/CAP theorem, distributed crash/recovery guarantee, verified
runtime or solver proof reconstruction is claimed by stage one.

Next stages are minimal distributed semantics, Kadmos application semantics,
and verification/codegen correspondence, followed by evidence-driven expansion.
Forward simulation transfers the stated safety properties; it does not prove
liveness or bisimulation.
