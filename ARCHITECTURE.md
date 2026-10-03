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
- High-level declarative macro syntax (`distributed_protocol`).
- Restriction to EPR (Effectively Propositional Logic) fragment to guarantee decidability.
- Automated SMT-LIB2 lowering to Z3/CVC5 for push-button inductive invariant checking and counterexample trace synthesis.

### L4: Runtime Gatekeeper & Code Extraction (`Harmonia/Gatekeeper/`)
- C-ABI shared library emission (`libharmonia_gatekeeper.dylib`).
- Pluggable into production systems (Rust Tokio, Go, C++) as an unbypassable pre-commit gatekeeper.

---

## 3. Tracer Slice: Two-Phase Commit (2PC)

The repository bootstraps with an end-to-end vertical slice:
1. **Spec**: `Harmonia/Protocols/TwoPhaseCommit.lean`
2. **Safety Property**: `AgreementInvariant` (No node committed while another aborted).
3. **Target Validation**: SMT-based push-button proof of safety and automatic counterexample generation on unhandled participant failure.
