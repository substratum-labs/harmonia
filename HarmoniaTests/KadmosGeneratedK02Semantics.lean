import Harmonia.Applications.Kadmos.Generated.TargetSemantics

open Harmonia.Applications.Kadmos.Generated

private def tsProgram : TargetProgram :=
  ⟨.ts, .empty, .empty, [], .empty, .empty⟩
private def pyProgram : TargetProgram :=
  { tsProgram with lang := .python }
private def frame : TargetFrame :=
  ⟨"test", [], [], [], none, .normal⟩

example : (evalExpr 20 tsProgram TargetMachine.empty frame
    (.binary .sub (.integer 100) (.integer 30))).map ExprOutcome.result =
    .ok (.ok (.number .jsNumber 70)) := by rfl
example : (evalExpr 20 pyProgram TargetMachine.empty frame
    (.binary .sub (.integer 100) (.integer 30))).map ExprOutcome.result =
    .ok (.ok (.number .pyInt 70)) := by rfl
example : (evalExpr 20 tsProgram TargetMachine.empty frame
    (.andThen (.bool false) (.local "missing"))).map ExprOutcome.result =
    .ok (.ok (.bool false)) := by rfl
example : evalExpr 20 tsProgram TargetMachine.empty frame
    (.binary .add (.integer 9007199254740991) (.integer 1)) =
    .error .outsideNumericDomain := by rfl
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.property (.object (.objectEntry "balance" (.integer 100) .empty))
      "balance")).map ExprOutcome.result =
    .ok (.ok (.number .jsNumber 100)) := by rfl
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.index (.array (.sequence (.integer 30) .empty)) (.integer 0))).map
      ExprOutcome.result = .ok (.ok (.number .jsNumber 30)) := by rfl
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.index (.array (.sequence (.integer 10)
      (.sequence (.integer 30) .empty)))
      (.unary .neg (.integer 1)))).map ExprOutcome.result =
    .ok (.ok (.number .pyInt 30)) := by rfl
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.slice (.string "'abc'") (.integer 1)
      (.unary .neg (.integer 1)))).map ExprOutcome.result =
    .ok (.ok (.string "abc")) := by rfl
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.property (.array (.sequence (.integer 30) .empty)) "length")).map
      ExprOutcome.result = .ok (.ok (.number .jsNumber 1)) := by rfl
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.builtin .length (.sequence (.string "abc") .empty))).map
      ExprOutcome.result = .ok (.ok (.number .pyInt 3)) := by rfl
example : (execStmt 40 tsProgram TargetMachine.empty frame
    (.sequence (.letLocal "x" true (.integer 70))
      (.returnValue (.local "x")))).map StmtOutcome.control =
    .ok (.returned (.number .jsNumber 70)) := by rfl
example : (execStmt 60 pyProgram TargetMachine.empty frame
    (.sequence (.letLocal "position" true (.integer 0))
      (.sequence (.assign (.local "position")
        (.binary .add (.local "position") (.integer 1)))
        (.returnValue (.local "position"))))).map StmtOutcome.control =
    .ok (.returned (.number .pyInt 1)) := by rfl
private def indexMachine : TargetMachine :=
  let withCell := { TargetMachine.empty with cells := [(3, .number .jsNumber 0)] }
  let withPermission := { withCell with writableCells := [(3, true)] }
  { withPermission with nextCell := 4 }
private def indexFrame : TargetFrame :=
  { frame with locals := [("index", 3)] }
example : (evalExpr 20 tsProgram indexMachine indexFrame (.postIncrement "index")).map
    (fun out => (out.result, readCell out.machine 3)) =
    .ok (.ok (.number .jsNumber 0), .ok (.number .jsNumber 1)) := by rfl
private def capturedIndexFrame : TargetFrame :=
  { frame with captures := [("index", 3)] }
example : (evalExpr 20 tsProgram indexMachine capturedIndexFrame (.postIncrement "index")).map
    (fun out => readCell out.machine 3) = .ok (.ok (.number .jsNumber 1)) := by rfl
private def switchControl : TargetStmt :=
  .sequence (.letLocal "flag" true (.integer 0))
    (.sequence (.whileDo (.bool true)
      (.sequence (.switchOn (.string "+")
        (.switchCase "+" (.breakTarget "switch") .empty))
        (.sequence (.assign (.local "flag") (.integer 1))
          (.breakTarget "loop"))))
      (.returnValue (.local "flag")))
example : (execStmt 80 tsProgram TargetMachine.empty frame switchControl).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 1)) := by rfl
private def busyMachine : TargetMachine :=
  { TargetMachine.empty with checker :=
    { TargetMachine.empty.checker with busy := true } }
private def finallyControl : TargetStmt :=
  .tryCatchFinally (.returnValue (.integer 7)) none none .empty
    (.assign (.field "busy") (.bool false))
example : (execStmt 40 tsProgram busyMachine frame finallyControl).map
    (fun out => (out.control, out.machine.checker.busy)) =
    .ok (.returned (.number .jsNumber 7), false) := by rfl
private def boundFrame : TargetFrame :=
  { frame with receiver := some busyMachine.checkerRef }
private def actualBusyFinally : TargetStmt :=
  .tryCatchFinally (.returnValue (.integer 7)) none none .empty
    (.assign (.property (.local "this") "#busy") (.bool false))
example : (execStmt 40 tsProgram busyMachine boundFrame actualBusyFinally).map
    (fun out => (out.control, out.machine.checker.busy)) =
    .ok (.returned (.number .jsNumber 7), false) := by rfl
private def candidateWrite : TargetStmt :=
  .sequence (.letLocal "candidate" true
    (.object (.objectEntry "balance" (.integer 100) .empty)))
    (.sequence (.assign (.index (.local "candidate") (.string "balance"))
      (.integer 70))
      (.returnValue (.index (.local "candidate") (.string "balance"))))
example : (execStmt 80 tsProgram TargetMachine.empty frame candidateWrite).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 70)) := by rfl
private def loopReturn : TargetStmt :=
  .sequence (.forDo ["x"]
    (.array (.sequence (.integer 1) (.sequence (.integer 2) .empty)))
    (.ifThenElse (.binary .strictEq (.local "x") (.integer 2))
      (.returnValue (.local "x")) .empty))
    (.returnValue (.integer 0))
example : (execStmt 100 tsProgram TargetMachine.empty frame loopReturn).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 2)) := by rfl
private def pairLoop : TargetStmt :=
  .forDo ["key", "value"]
    (.array (.sequence (.tuple (.sequence (.string "balance")
      (.sequence (.integer 100) .empty))) .empty))
    (.returnValue (.local "value"))
example : (execStmt 100 tsProgram TargetMachine.empty frame pairLoop).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 100)) := by rfl
private def actualEntriesLoop : TargetStmt :=
  .forDo ["key", "definition"]
    (.builtin .objectEntries (.sequence
      (.object (.objectEntry "balance" (.integer 100) .empty)) .empty))
    (.returnValue (.local "key"))
example : (execStmt 100 tsProgram TargetMachine.empty frame actualEntriesLoop).map
    StmtOutcome.control = .ok (.returned (.string "balance")) := by rfl
private def pythonItemsLoop : TargetStmt :=
  .forDo ["name", "definition"]
    (.call (.property (.object (.objectEntry "balance" (.integer 100) .empty)) "items")
      .empty)
    (.returnValue (.local "name"))
example : (execStmt 100 pyProgram TargetMachine.empty frame pythonItemsLoop).map
    StmtOutcome.control = .ok (.returned (.string "balance")) := by rfl
