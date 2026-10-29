# Harmonia (Ἁρμονία)

**Harmonia** is a zero-dependency Lean 4 library for formalizing and verifying distributed systems and state machines.

Built entirely on Lean's standard library (`Init`), Harmonia compiles from scratch **in seconds** with **zero external dependencies** (no Mathlib, no external SMT solvers), **zero `sorry`**, and **choice-free proofs** (`[propext, Quot.sound]`).

Use Harmonia to:
- Model state machines and prove **inductive invariants** and **forward simulations**.
- Reason about **distributed protocols** under message loss, duplication, reordering, and node crash/recovery.
- Reuse mechanized **classical distributed systems theorems** (CFT/BFT Quorum Intersection, CAP, FLP, Lamport & Vector Clocks) and **verified protocols** (Fenced Quorum Lease, Two-Phase Commit, and BFT Quorum Commit).

---

## Quick Start

### 1. Add Harmonia to your `lakefile.lean`

Pin `leanprover/lean4:v4.35.0` in your `lean-toolchain`, then add to `lakefile.lean`:

```lean
require harmonia from git
  "https://github.com/substratum-labs/harmonia" @ "v0.3.0"
```

*(If using `lakefile.toml`:)*
```toml
[[require]]
name = "harmonia"
git = "https://github.com/substratum-labs/harmonia"
rev = "v0.3.0"
```

### 2. Import and use

```lean
import Harmonia

open Harmonia.Foundation

-- 1. Define a simple state machine (a counter bounded by 10)
def Counter : TransitionSystem Nat Unit Nat where
  init n := n = 0
  step n _ obs n' := n < 10 ∧ n' = n + 1 ∧ obs = n'

-- 2. Prove an inductive safety invariant over all reachable states
theorem counter_bounded (n : Nat) (h : Reachable Counter n) : n ≤ 10 := by
  refine invariant (I := fun s => s ≤ 10) ?_ ?_ n h
  · rintro s rfl; omega
  · rintro s _ _ s' _ ⟨hstep, rfl, _⟩; omega

-- 3. Or directly apply distributed systems theorems and verified protocols
#check @Harmonia.Quorum.cft_intersection_at_least
#check @Harmonia.VerifiedProtocols.QuorumLease.fenced_commit_safety
#check @Harmonia.VerifiedProtocols.TwoPhaseCommit.twoPC_atomic_agreement
#check @Harmonia.VerifiedProtocols.BFTQuorumCommit.bft_commit_safety
```

---

## What's Inside

`import Harmonia` exports four foundational layers (see [ARCHITECTURE.md](ARCHITECTURE.md) for the high-level design):

| Layer | Namespace | What It Provides |
| :--- | :--- | :--- |
| **1. State Machine Core** | `Harmonia.Foundation` | Relational transition systems (`TransitionSystem`), finite execution traces, inductive invariants (`invariant`), and safety-preserving `ForwardSimulation`. |
| **2. Distributed Model** | `Harmonia.Distributed` | Asynchronous message-passing cluster model with durable vs. volatile node state (`crashReset`, `recover`) and configurable fault profiles (`reliable`, `omission`, `crashRecovery`). |
| **3. Classical Theorems** | `Harmonia.Quorum`<br>`Harmonia.CAP`<br>`Harmonia.FLP`<br>`Harmonia.Causal` | Mechanized foundational results:<br>• **Quorum**: CFT ($N \ge 2f+1$) & BFT ($N \ge 3f+1$) quorum intersection<br>• **CAP**: Gilbert–Lynch consistency/availability impossibility<br>• **FLP**: Choice-free Fischer–Lynch–Paterson consensus impossibility<br>• **Causal**: Happened-before ($\prec$), Lamport clocks, and Vector Clock isomorphism |
| **4. Verified Protocols** | `Harmonia.VerifiedProtocols.QuorumLease`<br>`Harmonia.VerifiedProtocols.TwoPhaseCommit`<br>`Harmonia.VerifiedProtocols.BFTQuorumCommit` | End-to-end verified protocols over `Harmonia.Distributed`:<br>• **QuorumLease**: CFT single-epoch mutual exclusion, fenced commit agreement across crashes, and `ForwardSimulation` refinement.<br>• **TwoPhaseCommit**: Unanimous (`N`-of-`N`) atomic commit agreement, commit validity, prepared-no-abort-without-coordinator, and `ForwardSimulation` refinement.<br>• **BFTQuorumCommit**: Single-shot $N \ge 3f+1$ quorum certificate safety under up to $f$ equivocating Byzantine nodes and `ForwardSimulation` refinement. |

---

## Building & Verifying Locally

With [elan](https://github.com/leanprover/elan) installed:

```sh
# Build the certified library
lake build

# Run the test suite and transitive axiom audits
python3 scripts/check_verified_protocols_audit.py
python3 scripts/check_external_consumer.py
```

---

## Downstream Ecosystem

- **[Kadmos](https://github.com/substratum-labs/kadmos)** — Uses Harmonia (`require harmonia`) to verify its state-machine interpreter and compiler syntax bridge.
- **Using with Mathlib** — Harmonia keeps its core `Init`-only for speed, but downstream Mathlib projects can trivially bridge `Finset.toList` into Harmonia's duplicate-free `List` quorum APIs.

## License

Licensed under [Apache-2.0](LICENSE).
