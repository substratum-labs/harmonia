# Harmonia Architecture

Harmonia is structured as a layered formal verification stack in Lean 4. Each layer builds on the one below it so that abstract mathematical proofs (like quorum intersection) connect directly to operational distributed protocol executions and state-machine refinements.

```
┌───────────────────────────────────────────────────────────────────┐
│                   Downstream Applications                         │
│            (e.g., Kadmos, custom consensus protocols)             │
└─────────────────────────────────┬─────────────────────────────────┘
                                  │
┌─────────────────────────────────▼─────────────────────────────────┐
│        Layer 4: Verified Protocols (Harmonia.VerifiedProtocols)   │
│   QuorumLease (CFT), TwoPhaseCommit (N-of-N atomic commit),       │
│   BFTQuorumCommit (3f+1 BFT QC) + ForwardSimulation refinements   │
└──────────────────┬──────────────────────────────┬─────────────────┘
                   │                              │
┌──────────────────▼─────────────────┐ ┌──────────▼─────────────────┐
│  Layer 3: Classical Meta-Theorems  │ │ Layer 2: Distributed Model │
│        (Harmonia.Theorems)         │ │   (Harmonia.Distributed)   │
│  • Quorum (CFT / BFT intersection) │ │  • Durable / volatile RAM  │
│  • CAP & FLP Impossibility         │ │  • Unordered network pool  │
│  • Causal / Lamport / Vector Clock │ │  • Crash, recovery, drop   │
└──────────────────┬─────────────────┘ └──────────┬─────────────────┘
                   └──────────────┬───────────────┘
                                  │
┌─────────────────────────────────▼─────────────────────────────────┐
│          Layer 1: Transition System Core (Harmonia.Core)          │
│   TransitionSystem • Execution • Reachable • Invariant            │
│   ForwardSimulation (observation-preserving safety transfer)      │
└───────────────────────────────────────────────────────────────────┘
```

---

## 1. Core Design Principles

1. **Zero-Dependency Core (`Init`-only)**
   Harmonia relies solely on Lean 4's standard library (`Init`). Avoiding heavyweight dependencies like Mathlib or external SMT solvers keeps clean compilation times **in seconds** and prevents fragile version lock-in for downstream users.
2. **Constructive & Choice-Free Proofs**
   All theorems in the distributed model, classical theorem suite, and verified protocols avoid `Classical.choice` and `sorryAx`. Automated axiom audits verify that public theorems depend at most on Lean's standard propositional and quotient axioms (`[propext, Quot.sound]`).
3. **Mechanism vs. Application Separation**
   Harmonia provides reusable transition-system mechanics and distributed network semantics. Application-specific schemas, runtime code generators, and I/O wrappers belong in downstream repositories (such as [Kadmos](https://github.com/substratum-labs/kadmos)).

---

## 2. Architectural Layers

### Layer 1: Transition System Core (`Harmonia/Core/`)

Exported under `Harmonia.Foundation`, this layer defines the minimal vocabulary for state machines:
- **`TransitionSystem.lean`**: Universe-polymorphic relational state machines defined by an `init` predicate and a labeled `step : State → Action → Obs → State → Prop` relation, along with inductive `Reachable` states.
- **`Execution.lean`**: Proof-indexed finite execution traces connecting initial states to reachable endpoints while recording ordered external observations.
- **`Invariant.lean`**: Inductive invariant framework (`Initially`, `Preserved`, `invariant`) for proving safety properties across all reachable states.
- **`Refinement.lean`**: Observation-preserving **`ForwardSimulation`**. If a concrete system $C$ simulates an abstract specification $B$ through a coupling relation $R$, any safety invariant proved on $B$ transfers automatically to $C$ (`ForwardSimulation.transfer_invariant`).

### Layer 2: Distributed Execution Model (`Harmonia/Distributed/`)

Exported under `Harmonia.Distributed`, this layer embeds an asynchronous message-passing cluster into a `TransitionSystem`:
- **Node State Split (`Protocol.lean`)**: Every node separates **durable state** (survives crashes, e.g., disk/WAL) from **volatile state** (lost on crash and reconstructed from durable state upon recovery).
- **Locality Constraint**: A node's transition function sees only its own identity, its local durable/volatile state, and a single incoming message or timeout—never global cluster state.
- **Unordered Network (`Network.lean`)**: In-flight messages live in an unordered multiset of unique transmission occurrences, supporting arbitrary reordering, packet drop, and packet duplication.
- **Fault Profiles (`Semantics.lean`)**: A single parameterized step relation models local processing, message delivery, drop, duplication, node crash, and node recovery, gated by a configurable `FaultProfile` (`reliable`, `omission`, or `crashRecovery`).

### Layer 3: Classical Meta-Theorems (`Harmonia/Theorems/`)

Self-contained, mechanized proofs of foundational distributed systems results using finite duplicate-free lists (`List.Nodup`):
- **Quorum Intersection (`Quorum.lean`)**: Proves that any two CFT majorities ($N \ge 2f+1$, $N \le |Q| + f$) intersect in at least one node (`cft_intersection_at_least`), and any two BFT quorums ($N \ge 3f+1$, $N \le |Q| + f$, i.e., $|Q| \ge N - f$) intersect in at least $f+1$ nodes (`bft_intersection_at_least`) containing at least one honest node when at most $f$ nodes are faulty (`bft_honest_exists_at_least`).
- **Impossibility Results (`CAP.lean`, `FLP.lean`)**:
  - **Gilbert–Lynch CAP (`cap_impossibility`)**: Proves that no partitioned read/write register can simultaneously guarantee linearizability and unconditional availability, accompanied by constructive AP and CP witnesses.
  - **Fischer–Lynch–Paterson (`flp_impossibility`)**: Choice-free mechanization of the 1985 FLP theorem (Lemma 1 diamond commutativity, Lemma 2 initial bivalence, Lemma 3 bivalence preservation), refuting deterministic bounded-step consensus under a single unannounced crash.
- **Logical Time (`Causal.lean`, `Lamport.lean`, `VectorClock.lean`)**: Formalizes Lamport's happened-before relation ($\prec$), scalar clock monotonicity ($a \prec b \implies C(a) < C(b)$), and the Mattern/Fidge canonical Vector Clock isomorphism ($a \prec b \iff V(a) < V(b)$).

### Layer 4: Verified Protocols (`Harmonia/VerifiedProtocols/`)

Combines Layers 1, 2, and 3 into end-to-end verified protocol implementations across three canonical distributed coordination regimes:
- **Fenced Quorum Lease (`QuorumLease.lean`)**: Models a multi-node cluster electing epoch leaders and committing values with epoch fencing over `Harmonia.Distributed`:
  - **Durable Votes & Volatile Tallies**: Nodes persist at most one vote per epoch to durable storage; leaders collect vote grants in volatile memory (which is wiped on crash).
  - **Mutual Exclusion (`quorum_lease_mutual_exclusion`)**: Uses Layer 3's CFT quorum intersection to prove at most one leader can acquire a lease per epoch.
  - **Fenced Commit Safety (`fenced_commit_safety`)**: Proves that even under arbitrary crashes, recoveries, and message drops/duplications, all committed values in a given epoch agree.
  - **Refinement (`quorum_lease_refines_spec`)**: Uses Layer 1's `ForwardSimulation` to prove the multi-node distributed protocol refines a simple sequential write-once-per-epoch register.
- **Two-Phase Commit (`TwoPhaseCommit.lean`)**: Models coordinator-driven unanimous (`N`-of-`N`) atomic commit across crash/recovery and message loss/duplication:
  - **Unanimous Commit Certificate (`IsAllMembers`)**: The coordinator can decide `true` only after collecting duplicate-free `voteYes` responses covering the full cluster (`c.members.length ≤ (voters.map Subtype.val).length`, from which `all_members_of_unanimous` derives `∀ m : Member c, m ∈ voters`); any non-coordinator participant may unilaterally abort (`castVoteNo`), and the coordinator may abort before deciding (`coordAbort` or `recvVoteNo`).
  - **Atomic Agreement & Validity (`twoPC_atomic_agreement`, `twoPC_commit_validity`, `twoPC_prepared_no_abort_without_coord`)**: Proves that no two nodes ever record conflicting outcomes (`true` vs. `false`), any committed transaction has durable `voteYes` from all members, and a prepared (`voted = some true`) participant never records `outcome = some false` unless the coordinator durably decided `false`.
  - **Refinement (`twoPC_refines_spec`, `twoPC_safety_via_refinement`)**: Proves forward simulation to a write-once sequential transaction table (`sequentialTwoPCSpec`) and transports coordinator decision uniqueness through the simulation.
- **BFT Quorum Commit (`BFTQuorumCommit.lean`)**: Models single-shot Byzantine quorum certificate (`commitQC`) formation under $N \ge 3f+1$ with up to $f$ equivocating Byzantine nodes:
  - **Explicit Byzantine Equivocation (`byzantineEquivocate`)**: Nodes in `faulty` (`FaultyBounded c f faulty`, i.e., `|F| ≤ f`) can send conflicting `.vote view proposer val` messages for arbitrary proposers and values in the same view without durable vote locks, while honest nodes (`actor ∉ faulty`) persist at most one `(proposer, val)` pair per view (`castHonestVote`).
  - **QC Uniqueness & Commit Safety (`bft_qc_unique`, `bft_commit_safety`)**: Instantiates Layer 3's `Harmonia.Quorum.bft_honest_exists_at_least` to prove that any two duplicate-free BFT quorums satisfying $N \ge 3f+1$ and $N \le |Q| + f$ (i.e., $|Q| \ge N - f$) under $|F| \le f$ share at least one honest voter, forcing both proposer identity and committed value to agree (`leader₁ = leader₂ ∧ val₁ = val₂`).
  - **Refinement (`bft_commit_refines_spec`, `bft_safety_via_refinement`)**: Proves forward simulation to a sequential write-once per-view register (`sequentialBFTSpec`) and transfers cross-node commit agreement through refinement.

---

## 3. Repository Layout & Axiom Auditing

Harmonia strictly separates the **certified library** from **test and audit harnesses**:

```
Harmonia/                  # Certified library (compiled by `lake build`)
├── Core/                  # Layer 1: TransitionSystem, Execution, Invariant, Refinement
├── Distributed/           # Layer 2: Membership, Network, Protocol, Semantics, Properties
├── Theorems/              # Layer 3: Quorum, CAP, FLP, Causal, Lamport, VectorClock
├── VerifiedProtocols/     # Layer 4: QuorumLease, TwoPhaseCommit, BFTQuorumCommit
└── Examples/              # Reference witnesses for Core and Distributed models

HarmoniaTests/             # Regression probes, axiom audits, and negative fixtures
scripts/                   # Automated CI audit runners and external-consumer checks
```

Every theorem in `Harmonia/` is checked in CI by `HarmoniaTests/AuditPolicy.lean` and the Python audit runners in `scripts/`. These checks traverse the full Lean declaration DAG to ensure:
1. No `sorryAx`, custom axioms, or `unsafe` declarations appear anywhere in the transitive dependency closure.
2. Distributed, theorem, and protocol layers remain strictly choice-free (`[propext, Quot.sound]`).
3. Adversarial rejection fixtures (`*Rejection.lean`) are verified separately to confirm that the audit gates actively catch violations.

---

## 4. Model Scope & Boundaries

To read Harmonia's theorems accurately, keep two boundaries in mind:
- **Safety vs. Liveness**: The core models and `VerifiedProtocols` (`QuorumLease`, `TwoPhaseCommit`, `BFTQuorumCommit`) prove **safety** (invariants and simulation refinement over arbitrary finite executions under crash/recovery, message loss, and bounded Byzantine equivocation). They do not claim physical-time lease expiration, non-blocking 2PC termination under coordinator failure, multi-phase BFT view-change liveness, or network fairness.
- **Abstract Atomicity vs. Physical I/O**: In `Harmonia.Distributed`, a node's local state transition and durable write are modeled as an atomic step. Physical disk flush (`fsync`), cryptographic signature verification, and wire serialization are responsibilities of the concrete runtime layer.
