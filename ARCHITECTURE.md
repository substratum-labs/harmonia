# Harmonia Architecture & Design Spec

## 1. Vision & Core Philosophy

**Harmonia** (Greek: Ἁρμονία, goddess of concord and agreement; wife of **Kadmos**) is a foundational formal verification and synthesis framework for distributed systems implemented in **Lean 4**.

Where **Kadmos** legislates the non-negotiable laws and state invariants within a single-node boundary (The World vs The Fabric), **Harmonia** legislates the invariants of multi-node consensus, causal ordering, and fault tolerance across asynchronous and partially synchronous networks.

```text
       [ Kadmos ]                           [ Harmonia ]
Single-Node Deterministic Law      Multi-Node Consensus & Agreement
   Local State Transitions            Global Interleaved Network Semantics
  WorldChecker Gatekeepers          Consensus & Invariant Gatekeepers
```

---

## 2. Layered System Architecture

Harmonia is structured into four distinct layers:

### L1: Core Calculus (`Harmonia/Core/`)
- **Event Structures**: `Event.lean` defines Lamport causal order $(E, \prec)$ and logical epochs.
- **Network Semantics**: `Network.lean` models in-flight message pools as non-deterministic multisets with packet omission and delay.
- **Operational Semantics**: `SmallStep.lean` defines global interleaved state transitions $\langle \mathcal{N}, \mathcal{M} \rangle \to \langle \mathcal{N}', \mathcal{M}' \rangle$ and inductive reachability.

### L2: Meta-Theorems (`Harmonia/Theorems/`)
- **Quorum Intersection**: Mechanized proofs of $N \ge 2f + 1$ (Crash-Fault Tolerant) and $N \ge 3f + 1$ (Byzantine-Fault Tolerant) pigeonhole intersections.
- **CAP Impossibility**: Gilbert-Lynch impossibility theorem formalization under network partitions.
- **FLP Impossibility**: Bivalent configuration tree construction and undecidability in pure asynchronous models.

### L3: Protocol eDSL & SMT Automation (`Harmonia/DSL/`, `Harmonia/SMT/`)
- Declarative macro syntax: `declare_protocol <Name> where roles := [...] states := [...] messages := [...]`.
- SMT-LIB2 AST (`AST.lean`), Z3 pipeline (`Solver.lean`), and Verification Condition generator (`TwoPhaseCommitVC.lean`).
- Automated push-button inductive verification (`UNSAT`) and CEGIS counterexample synthesis (`SAT`).

### L4: Runtime Gatekeeper & Code Extraction (`Harmonia/Gatekeeper/`, `examples/rust_node/`)
- C-ABI shared library emission (`libharmonia_gatekeeper.dylib`).
- Zero-allocation pre-commit gatekeeper executing in **14.5 nanoseconds** in native Rust services.

---

## 3. Tracer Slice: Two-Phase Commit (2PC) Physical Evidence

1. **Lean 4 Base Theorem**: Initial state trivially satisfies Agreement (`init_satisfies_agreement` in `TwoPhaseCommit.lean`).
2. **SMT Verification (Phase 1)**: Z3 mathematically verified 8 valid operational transitions preserve inductive invariants in 15ms (`UNSAT`).
3. **CEGIS Falsification (Phase 2)**: Z3 synthesized a counterexample trace when injecting premature prepared timeout (`SAT`).
4. **eDSL Synthesis (Phase 3)**: Raft Leader Election declared in 5 lines of eDSL macro with automatic SMT datatype compilation (`RaftElection.lean`).
5. **Rust Physical Defense (Phase 4)**: Host Rust node (`examples/rust_node`) intercepts illegal unilateral timeouts in memory at 14ns latency with 0 allocations.

---

## 4. Canonical Specification & Whitepaper

The full whitepaper, theoretical trade-offs, and open mathematical questions for peer AI discussion are recorded in:
- `../substratum-internal/design/harmonia/harmonia_foundations_architecture_roadmap.md`
