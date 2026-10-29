-- Generic transition systems, executions, invariants, and refinement.
import Harmonia.Core.TransitionSystem
import Harmonia.Core.Execution
import Harmonia.Core.Invariant
import Harmonia.Core.Refinement

-- Distributed semantics and certified distributed systems theorems.
import Harmonia.Distributed
import Harmonia.Theorems.Quorum
import Harmonia.Theorems.CAP
import Harmonia.Theorems.FLP
import Harmonia.Theorems.FLPBounds
import Harmonia.Theorems.Causal
import Harmonia.Theorems.Lamport
import Harmonia.Theorems.VectorClock

import Harmonia.VerifiedProtocols

namespace Harmonia

def version : String := "0.3.0"

def welcomeBanner : String :=
  s!"Harmonia {version} - Formal Foundations of Distributed Systems (Lean 4)"

end Harmonia
