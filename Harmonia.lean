import Harmonia.Core.Execution
/-
  Harmonia: Formalizing the Foundations of Distributed Systems
  Root module aggregating core semantics, protocols, and theorem mechanizations.
-/

import Harmonia.Core.Event
import Harmonia.Core.Network
import Harmonia.Core.SmallStep
import Harmonia.Protocols.TwoPhaseCommit
import Harmonia.Protocols.RaftElection
import Harmonia.SMT.AST
import Harmonia.SMT.Solver
import Harmonia.SMT.TwoPhaseCommitVC
import Harmonia.DSL.Syntax
import Harmonia.Gatekeeper.CExport

namespace Harmonia

def version : String := "0.1.0-alpha"

def welcomeBanner : String :=
  s!"Harmonia {version} - Formal Foundations of Distributed Systems (Lean 4)"

end Harmonia
