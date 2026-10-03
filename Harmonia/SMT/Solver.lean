/-
  Harmonia.SMT.Solver
  Interface to invoke Z3 / SMT solvers, stream SMT-LIB2 scripts, and parse results.
-/

import Harmonia.SMT.AST

namespace Harmonia.SMT

inductive SolverStatus where
  | sat
  | unsat
  | unknown
  | error (msg : String)
deriving DecidableEq, Repr

structure SolverResult where
  status    : SolverStatus
  model     : Option String
  rawOutput : String
  queryPath : String
deriving Repr

/-- Dispatch an SMT-LIB2 command sequence to local Z3 solver and collect verdicts. -/
def solveWithZ3 (cmds : List Command) (queryName : String := "query") : IO SolverResult := do
  let script := renderScript cmds
  let queryPath := s!".lake/{queryName}.smt2"
  IO.FS.writeFile queryPath script

  let proc ← IO.Process.output {
    cmd := "z3",
    args := #[queryPath]
  }

  let out := proc.stdout.trim
  let lines := out.splitOn "\n"
  let firstLine := lines.head?.getD "" |>.trim

  let status :=
    if firstLine == "unsat" then
      SolverStatus.unsat
    else if firstLine == "sat" then
      SolverStatus.sat
    else if firstLine == "unknown" then
      SolverStatus.unknown
    else
      SolverStatus.error s!"Solver exited with code {proc.exitCode}: {proc.stderr} {out}"

  let model :=
    if status == SolverStatus.sat then
      let modelLines := lines.tail? |>.getD []
      some (String.intercalate "\n" modelLines)
    else
      none

  return {
    status := status,
    model := model,
    rawOutput := out,
    queryPath := queryPath
  }

end Harmonia.SMT
