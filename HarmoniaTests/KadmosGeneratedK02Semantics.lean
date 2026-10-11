import Harmonia.Applications.Kadmos.Generated.TargetSemantics

open Harmonia.Applications.Kadmos.Generated

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b =>
      if h : a = b then isTrue (by cases h; rfl)
      else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b =>
      if h : a = b then isTrue (by cases h; rfl)
      else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def tsProgram : TargetProgram :=
  ⟨.ts, .empty, .empty, [], .empty, .empty⟩
private def pyProgram : TargetProgram :=
  { tsProgram with lang := .python }
private def frame : TargetFrame :=
  ⟨"test", [], [], [], none, .normal⟩

example : ((evalExpr 20 tsProgram TargetMachine.empty frame
    (.binary .sub (.integer 100) (.integer 30))).toOption.bind
      (fun out => out.result.toOption)) =
    some (.number .jsNumber 70) := by decide +kernel
example : (evalExpr 20 pyProgram TargetMachine.empty frame
    (.binary .sub (.integer 100) (.integer 30))).map ExprOutcome.result =
    .ok (.ok (.number .pyInt 70)) := by decide +kernel
example : (evalExpr 20 tsProgram TargetMachine.empty frame
    (.andThen (.bool false) (.local "missing"))).map ExprOutcome.result =
    .ok (.ok (.bool false)) := by decide +kernel
example : (match evalExpr 20 tsProgram TargetMachine.empty frame
    (.binary .add (.integer 9007199254740991) (.integer 1)) with
    | .error .outsideNumericDomain => true | _ => false) = true := by decide +kernel
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.property (.object (.objectEntry "balance" (.integer 100) .empty))
      "balance")).map ExprOutcome.result =
    .ok (.ok (.number .jsNumber 100)) := by decide +kernel
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.index (.array (.sequence (.integer 30) .empty)) (.integer 0))).map
      ExprOutcome.result = .ok (.ok (.number .jsNumber 30)) := by decide +kernel
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.index (.array (.sequence (.integer 10)
      (.sequence (.integer 30) .empty)))
      (.unary .neg (.integer 1)))).map ExprOutcome.result =
    .ok (.ok (.number .pyInt 30)) := by decide +kernel
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.slice (.string "'abc'") (.integer 1)
      (.unary .neg (.integer 1)))).map ExprOutcome.result =
    .ok (.ok (.string "abc")) := by decide +kernel
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.property (.array (.sequence (.integer 30) .empty)) "length")).map
      ExprOutcome.result = .ok (.ok (.number .jsNumber 1)) := by decide +kernel
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.builtin .length (.sequence (.string "abc") .empty))).map
      ExprOutcome.result = .ok (.ok (.number .pyInt 3)) := by decide +kernel
example : (execStmt 40 tsProgram TargetMachine.empty frame
    (.sequence (.letLocal "x" true (.integer 70))
      (.returnValue (.local "x")))).map StmtOutcome.control =
    .ok (.returned (.number .jsNumber 70)) := by decide +kernel
example : (execStmt 60 pyProgram TargetMachine.empty frame
    (.sequence (.letLocal "position" true (.integer 0))
      (.sequence (.assign (.local "position")
        (.binary .add (.local "position") (.integer 1)))
        (.returnValue (.local "position"))))).map StmtOutcome.control =
    .ok (.returned (.number .pyInt 1)) := by decide +kernel
private def indexMachine : TargetMachine :=
  let withCell := { TargetMachine.empty with cells := [(3, .number .jsNumber 0)] }
  let withPermission := { withCell with writableCells := [(3, true)] }
  { withPermission with nextCell := 4 }
private def indexFrame : TargetFrame :=
  { frame with locals := [("index", 3)] }
example : (evalExpr 20 tsProgram indexMachine indexFrame (.postIncrement "index")).map
    (fun out => (out.result, readCell out.machine 3)) =
    .ok (.ok (.number .jsNumber 0), .ok (.number .jsNumber 1)) := by decide +kernel
private def capturedIndexFrame : TargetFrame :=
  { frame with captures := [("index", 3)] }
example : (evalExpr 20 tsProgram indexMachine capturedIndexFrame (.postIncrement "index")).map
    (fun out => readCell out.machine 3) = .ok (.ok (.number .jsNumber 1)) := by decide +kernel
private def switchControl : TargetStmt :=
  .sequence (.letLocal "flag" true (.integer 0))
    (.sequence (.whileDo (.bool true)
      (.sequence (.switchOn (.string "+")
        (.switchCase "+" (.breakTarget "switch") .empty))
        (.sequence (.assign (.local "flag") (.integer 1))
          (.breakTarget "loop"))))
      (.returnValue (.local "flag")))
example : (execStmt 80 tsProgram TargetMachine.empty frame switchControl).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 1)) := by decide +kernel
private def busyMachine : TargetMachine :=
  { TargetMachine.empty with checker :=
    { TargetMachine.empty.checker with busy := true } }

private def caughtReturnWithExitingFinally : TargetStmt :=
  .tryCatchFinally (.throwValue (.string "boom")) (some "any") none
    (.returnValue (.integer 1)) (.returnValue (.integer 2))

theorem kadmos_generated_caught_return_finally_ts :
    (execStmt 20 tsProgram busyMachine frame caughtReturnWithExitingFinally).toOption.map
      StmtOutcome.control = some (.returned (.number .jsNumber 2)) := by
  decide +kernel

theorem kadmos_generated_caught_return_finally_python :
    (execStmt 20 pyProgram busyMachine frame caughtReturnWithExitingFinally).toOption.map
      StmtOutcome.control = some (.returned (.number .pyInt 2)) := by
  decide +kernel

private def caughtRethrowWithFinally : TargetStmt :=
  .tryCatchFinally (.throwValue (.string "boom")) (some "any") none
    .rethrow (.assign (.field "busy") (.bool false))

theorem kadmos_generated_caught_rethrow_finally_ts :
    (execStmt 20 tsProgram busyMachine frame caughtRethrowWithFinally).toOption.map
      (fun out => (out.control, out.machine.checker.busy)) =
        some (.raised (.string "boom"), false) := by
  decide +kernel

theorem kadmos_generated_caught_rethrow_finally_python :
    (execStmt 20 pyProgram busyMachine frame caughtRethrowWithFinally).toOption.map
      (fun out => (out.control, out.machine.checker.busy)) =
        some (.raised (.string "boom"), false) := by
  decide +kernel

private def caughtReturnWithNormalFinally : TargetStmt :=
  .tryCatchFinally (.throwValue (.string "boom")) (some "any") none
    (.returnValue (.integer 1)) (.assign (.field "busy") (.bool false))

theorem kadmos_generated_caught_return_normal_finally_ts :
    (execStmt 20 tsProgram busyMachine frame caughtReturnWithNormalFinally).toOption.map
      (fun out => (out.control, out.machine.checker.busy)) =
        some (.returned (.number .jsNumber 1), false) := by
  decide +kernel

theorem kadmos_generated_caught_return_normal_finally_python :
    (execStmt 20 pyProgram busyMachine frame caughtReturnWithNormalFinally).toOption.map
      (fun out => (out.control, out.machine.checker.busy)) =
        some (.returned (.number .pyInt 1), false) := by
  decide +kernel

private def finallyControl : TargetStmt :=
  .tryCatchFinally (.returnValue (.integer 7)) none none .empty
    (.assign (.field "busy") (.bool false))
example : (execStmt 40 tsProgram busyMachine frame finallyControl).map
    (fun out => (out.control, out.machine.checker.busy)) =
    .ok (.returned (.number .jsNumber 7), false) := by decide +kernel
theorem kadmos_generated_normal_return_finally_python :
    (execStmt 40 pyProgram busyMachine frame finallyControl).toOption.map
      (fun out => (out.control, out.machine.checker.busy)) =
      some (.returned (.number .pyInt 7), false) := by
  decide +kernel
private def boundFrame : TargetFrame :=
  { frame with receiver := some busyMachine.checkerRef }
private def actualBusyFinally : TargetStmt :=
  .tryCatchFinally (.returnValue (.integer 7)) none none .empty
    (.assign (.property (.local "this") "#busy") (.bool false))
example : (execStmt 40 tsProgram busyMachine boundFrame actualBusyFinally).map
    (fun out => (out.control, out.machine.checker.busy)) =
    .ok (.returned (.number .jsNumber 7), false) := by decide +kernel
private def candidateWrite : TargetStmt :=
  .sequence (.letLocal "candidate" true
    (.object (.objectEntry "balance" (.integer 100) .empty)))
    (.sequence (.assign (.index (.local "candidate") (.string "balance"))
      (.integer 70))
      (.returnValue (.index (.local "candidate") (.string "balance"))))
example : (execStmt 80 tsProgram TargetMachine.empty frame candidateWrite).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 70)) := by decide +kernel
private def loopReturn : TargetStmt :=
  .sequence (.forDo ["x"]
    (.array (.sequence (.integer 1) (.sequence (.integer 2) .empty)))
    (.ifThenElse (.binary .strictEq (.local "x") (.integer 2))
      (.returnValue (.local "x")) .empty))
    (.returnValue (.integer 0))
example : (execStmt 100 tsProgram TargetMachine.empty frame loopReturn).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 2)) := by decide +kernel
private def pairLoop : TargetStmt :=
  .forDo ["key", "value"]
    (.array (.sequence (.tuple (.sequence (.string "balance")
      (.sequence (.integer 100) .empty))) .empty))
    (.returnValue (.local "value"))
example : (execStmt 100 tsProgram TargetMachine.empty frame pairLoop).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 100)) := by decide +kernel
private def actualEntriesLoop : TargetStmt :=
  .forDo ["key", "definition"]
    (.builtin .objectEntries (.sequence
      (.object (.objectEntry "balance" (.integer 100) .empty)) .empty))
    (.returnValue (.local "key"))
example : (execStmt 100 tsProgram TargetMachine.empty frame actualEntriesLoop).map
    StmtOutcome.control = .ok (.returned (.string "balance")) := by decide +kernel
private def pythonItemsLoop : TargetStmt :=
  .forDo ["name", "definition"]
    (.call (.property (.object (.objectEntry "balance" (.integer 100) .empty)) "items")
      .empty)
    (.returnValue (.local "name"))
example : (execStmt 100 pyProgram TargetMachine.empty frame pythonItemsLoop).map
    StmtOutcome.control = .ok (.returned (.string "balance")) := by decide +kernel
private def callUserBody : TargetStmt :=
  .sequence (.defineFunction "inc" [⟨"x", none⟩]
    (.returnValue (.binary .add (.local "x") (.integer 1))))
    (.returnValue (.call (.local "inc")
      (.sequence (.integer 30) .empty)))
example : (execStmt 100 tsProgram TargetMachine.empty frame callUserBody).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 31)) := by decide +kernel
private def defaultTiming : TargetStmt :=
  .sequence (.letLocal "seed" true (.integer 5))
    (.sequence (.defineFunction "f" [⟨"x", some (.local "seed")⟩]
      (.returnValue (.local "x")))
      (.sequence (.assign (.local "seed") (.integer 9))
        (.returnValue (.call (.local "f") .empty))))
example : (execStmt 120 tsProgram TargetMachine.empty frame defaultTiming).map
    StmtOutcome.control = .ok (.returned (.number .jsNumber 9)) := by decide +kernel
example : (execStmt 120 pyProgram TargetMachine.empty frame defaultTiming).map
    StmtOutcome.control = .ok (.returned (.number .pyInt 5)) := by decide +kernel
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.builtin .float (.sequence (.integer 30) .empty))).toOption.bind
      (fun out => out.result.toOption) = some (.number .pyFloat 30) := by decide +kernel
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.builtin .float (.sequence (.string "0") .empty))).toOption.bind
      (fun out => out.result.toOption) = some (.number .pyFloat 0) := by decide +kernel
example : (evalExpr 40 tsProgram TargetMachine.empty frame
    (.builtin .number (.sequence (.string "0") .empty))).toOption.bind
      (fun out => out.result.toOption) = some (.number .jsNumber 0) := by decide +kernel
example : (evalExpr 40 tsProgram (initialHostMachine .ts) frame
    (.call (.local "Number") (.sequence (.string "0") .empty))).toOption.bind
      (fun out => out.result.toOption) = some (.number .jsNumber 0) := by decide +kernel
example : (evalExpr 40 pyProgram TargetMachine.empty frame
    (.call (.property (.builtin .float (.sequence (.integer 30) .empty)) "is_integer")
      .empty)).toOption.bind (fun out => out.result.toOption) =
      some (.bool true) := by decide +kernel
example : (evalExpr 80 tsProgram TargetMachine.empty frame
    (.property (.builtin .jsonParse
      (.sequence (.string "{\"balance\":100}") .empty)) "balance")).toOption.bind
      (fun out => out.result.toOption) = some (.number .jsNumber 100) := by decide +kernel
example : (evalExpr 80 tsProgram (initialHostMachine .ts) frame
    (.property (.call (.property (.local "JSON") "parse")
      (.sequence (.string "{\"balance\":100}") .empty)) "balance")).toOption.bind
      (fun out => out.result.toOption) = some (.number .jsNumber 100) := by decide +kernel
example : (evalExpr 20 tsProgram TargetMachine.empty frame
    (.typeCast (.string "Ready") "WorldState")).toOption.bind
      (fun out => out.result.toOption) = some (.string "Ready") := by decide +kernel
example : (execStmt 40 pyProgram TargetMachine.empty frame
    (.tryCatchFinally (.throwValue (.string "e")) (some "any") none
      .rethrow .empty)).toOption.map StmtOutcome.control =
      some (.raised (.string "e")) := by decide +kernel
private def classCall : TargetStmt :=
  .sequence (.fromImport "ports" "IWorldChecker" "IWorldChecker")
    (.sequence (.defineClass "WorldChecker" (.local "IWorldChecker")
      (.defineFunction "get_state" [] (.returnValue (.string "Ready"))))
      (.returnValue (.call (.property (.local "self") "get_state") .empty)))
example : (execStmt 100 pyProgram (initialHostMachine .python)
    { frame with receiver := some TargetMachine.empty.checkerRef } classCall).toOption.map
      StmtOutcome.control = some (.returned (.string "Ready")) := by decide +kernel
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    (.binary .isIdentity
      (.builtin .type (.sequence (.object (.objectEntry "balance" (.integer 100) .empty)) .empty))
      (.local "dict"))).toOption.bind (fun out => out.result.toOption) =
      some (.bool true) := by decide +kernel
private def typeTupleMembership : TargetExpr :=
  .binary .inObject
    (.builtin .type (.sequence (.integer 30) .empty))
    (.tuple (.sequence (.local "int") (.sequence (.local "float") .empty)))
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    typeTupleMembership).toOption.bind (fun out => out.result.toOption) =
      some (.bool true) := by decide +kernel
example : (evalExpr 120 pyProgram (initialHostMachine .python) frame
    (.index (.dictComprehension (.local "k") (.local "v") ["k", "v"]
      (.call (.property (.object (.objectEntry "balance" (.integer 100) .empty)) "items") .empty)
      .empty) (.string "balance"))).toOption.bind (fun out => out.result.toOption) =
      some (.number .pyInt 100) := by decide +kernel
example : (evalExpr 160 pyProgram (initialHostMachine .python) frame
    (.call (.local "next") (.sequence
      (.generator (.binary .div (.integer 10)
        (.binary .sub (.integer 2) (.local "x"))) ["x"]
        (.array (.sequence (.integer 1) (.sequence (.integer 2) .empty))) .empty)
      .empty))).toOption.bind (fun out => out.result.toOption) =
      some (.number .pyInt 10) := by decide +kernel
example : (evalExpr 160 pyProgram (initialHostMachine .python) frame
    (.call (.local "tuple") (.sequence
      (.generator (.local "x") ["x"]
        (.array (.sequence (.integer 1) (.sequence (.integer 2) .empty))) .empty)
      .empty))).toOption.bind (fun out =>
      out.result.toOption.bind (fun value => match value with
        | .object ref => (objectAt out.machine ref).toOption.map HeapObject.items
        | _ => none)) =
      some [.number .pyInt 1, .number .pyInt 2] := by decide +kernel
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    (.builtin .mappingProxy (.sequence
      (.object (.objectEntry "balance" (.integer 100) .empty)) .empty))).toOption.bind
      (fun out => out.result.toOption.bind (fun value => match value with
        | .object ref => (objectAt out.machine ref).toOption.map HeapObject.kind
        | _ => none)) = some .mappingProxy := by decide +kernel
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    (.call (.property (.object (.objectEntry "balance" (.integer 100) .empty)) "get")
      (.sequence (.string "missing") (.sequence (.integer 7) .empty)))).toOption.bind
      (fun out => out.result.toOption) = some (.number .pyInt 7) := by decide +kernel
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    (.builtin .regexCompile (.sequence (.string "[A-Za-z_]+") .empty))).toOption.bind
      (fun out => out.result.toOption.bind (fun value => match value with
        | .object ref => (objectAt out.machine ref).toOption.map HeapObject.kind
        | _ => none)) = some .regexPattern := by decide +kernel
example : (evalExpr 120 pyProgram (initialHostMachine .python) frame
    (.call (.property (.builtin .regexCompile
      (.sequence (.string pythonTokenPattern) .empty)) "match")
      (.sequence (.string "balance >= 0") (.sequence (.integer 0) .empty)))).toOption.bind
      (fun out => out.result.toOption.map (fun value => match value with
        | .regexMatch result => (result.full, result.stop)
        | _ => ("", 0))) = some ("balance", 7) := by decide +kernel
private def appendToken : TargetStmt :=
  .sequence (.letLocal "tokens" true (.array .empty))
    (.sequence (.doExpr (.call (.property (.local "tokens") "append")
      (.sequence (.string "balance") .empty)))
      (.returnValue (.index (.local "tokens") (.integer 0))))
example : (execStmt 80 pyProgram TargetMachine.empty frame appendToken).toOption.map
    StmtOutcome.control = some (.returned (.string "balance")) := by decide +kernel
private def nonlocalPosition : TargetStmt :=
  .sequence (.letLocal "position" true (.integer 0))
    (.sequence (.defineFunction "parse" []
      (.sequence (.nonlocalNames ["position"])
        (.augment (.local "position") .add (.integer 1))))
      (.sequence (.doExpr (.call (.local "parse") .empty))
        (.returnValue (.local "position"))))
example : (execStmt 120 pyProgram TargetMachine.empty frame nonlocalPosition).toOption.map
    StmtOutcome.control = some (.returned (.number .pyInt 1)) := by decide +kernel
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    (.call (.local "object") .empty)).toOption.bind
      (fun out => out.result.toOption.bind (fun value => match value with
        | .object ref => (objectAt out.machine ref).toOption.map HeapObject.kind
        | _ => none)) = some .pythonOrdinary := by decide +kernel
example : (evalExpr 80 pyProgram (initialHostMachine .python) frame
    (.index (.call (.local "dict") (.sequence
      (.object (.objectEntry "balance" (.integer 100) .empty)) .empty))
      (.string "balance"))).toOption.bind (fun out => out.result.toOption) =
      some (.number .pyInt 100) := by decide +kernel
private def copiedFrame : TargetStmt :=
  .sequence (.letLocal "original" true
    (.object (.objectEntry "balance" (.integer 100) .empty)))
    (.sequence (.letLocal "copied" true
      (.builtin .deepCopy (.sequence (.local "original") .empty)))
      (.sequence (.assign (.index (.local "copied") (.string "balance"))
        (.integer 70))
        (.returnValue (.index (.local "original") (.string "balance")))))
example : (execStmt 120 pyProgram TargetMachine.empty frame copiedFrame).toOption.map
    StmtOutcome.control = some (.returned (.number .pyInt 100)) := by decide +kernel
