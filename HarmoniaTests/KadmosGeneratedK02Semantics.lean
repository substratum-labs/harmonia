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
