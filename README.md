# Harmonia (Ἁρμονία)

> Formalizing the Foundations of Distributed Systems in Lean 4.

Harmonia is an ambitious project to mechanize the foundational principles of distributed computing—bridging high-order meta-theorems (FLP, CAP, Quorum bounds), push-button SMT verification, and verified runtime gatekeepers.

## Directory Structure

```text
harmonia/
├── ARCHITECTURE.md          # Architectural specification and layer definitions
├── lakefile.lean            # Lake build configuration
├── lean-toolchain           # Lean 4 toolchain pin (v4.16.0)
├── Main.lean                # Executable CLI entrypoint
├── Harmonia.lean            # Top-level library root
└── Harmonia/
    ├── Core/                # Foundational Calculus
    │   ├── Event.lean       # Lamport logical clocks & causal happens-before (≺)
    │   ├── Network.lean     # Asynchronous message pools & omission failures
    │   └── SmallStep.lean   # Global interleaved semantics & inductive invariants
    ├── Protocols/           # Concrete Protocol Specifications
    │   └── TwoPhaseCommit.lean # Tracer vertical slice (2PC agreement)
    ├── Theorems/            # Mechanized Meta-Theorems (Quorum, CAP, FLP)
    ├── DSL/                 # Declarative eDSL Macros
    └── Gatekeeper/          # C-ABI export & runtime gatekeeper
```

## Quick Start

### Prerequisites
- [Elan](https://github.com/leanprover/elan) (Lean version manager)
- [Lean 4](https://lean-lang.org/) (`v4.16.0`)
- [Z3](https://github.com/Z3Prover/z3) (SMT solver for push-button verification)

```bash
# Build Harmonia
lake build

# Run CLI
lake exe harmonia
```

## Relationship to Substratum Ecosystem

Harmonia is the sister project to **Kadmos**:
- **Kadmos**: Regulates single-node state machine laws and invariants.
- **Harmonia**: Regulates multi-node consensus, causal ordering, and distributed fault tolerance.
