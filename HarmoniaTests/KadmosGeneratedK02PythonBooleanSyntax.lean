import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

private def pythonBooleanCondition : TargetExpr :=
  .binary .isNotIdentity
    (.call (.local "type") (.sequence (.local "value") .empty))
    (.local "bool")

private def pythonBooleanError : TargetExpr :=
  .call (.local "ValueError")
    (.sequence (.string "INVALID_EXPRESSION: expected boolean operand") .empty)

private def pythonBooleanIf : TargetStmt :=
  .ifThenElse pythonBooleanCondition
    (.sequence (.throwValue pythonBooleanError) .empty) .empty

private def pythonBooleanBody : TargetStmt :=
  .sequence pythonBooleanIf
    (.sequence (.returnValue (.local "value")) .empty)

private def pythonBooleanFunction : TargetFunction :=
  ⟨"_boolean", [⟨"value", none⟩], pythonBooleanBody⟩

theorem kadmos_generated_python_boolean_condition_decodes :
    (parseTargetExpr .python ((⟨1634, 1657⟩ : SourceSpan).text balancePySource)).toOption =
      some pythonBooleanCondition := by
  decide +kernel

theorem kadmos_generated_python_boolean_condition_owned :
    validatePythonIsNotValues
      ((⟨1634, 1657⟩ : SourceSpan).text balancePySource)
      (.call (.local "type") (.sequence (.local "value") .empty))
      (.local "bool") = true := by
  decide +kernel

theorem kadmos_generated_python_boolean_condition_derives :
    ExprSyntax .python
      ((⟨1634, 1657⟩ : SourceSpan).text balancePySource)
      pythonBooleanCondition :=
  validatePythonIsNotValues_sound
    kadmos_generated_python_boolean_condition_owned

theorem kadmos_generated_python_boolean_error_owned :
    validateExprSpan .python balancePySource ⟨1673, 1731⟩
      pythonBooleanError = true := by
  decide +kernel

theorem kadmos_generated_python_boolean_error_derives :
    ExprSyntax .python
      ((⟨1673, 1731⟩ : SourceSpan).text balancePySource)
      pythonBooleanError := by
  cases validateExprSpan_sound kadmos_generated_python_boolean_error_owned with
  | ofSyntax _ hSyntax => exact hSyntax

theorem kadmos_generated_python_boolean_raise_derives :
    StmtSyntax .python .function
      ((⟨1667, 1731⟩ : SourceSpan).text balancePySource)
      (.throwValue pythonBooleanError) := by
  have hText : ((⟨1667, 1731⟩ : SourceSpan).text balancePySource) =
      "raise " ++ ((⟨1673, 1731⟩ : SourceSpan).text balancePySource) := by
    decide +kernel
  rw [hText]
  exact .pythonRaise kadmos_generated_python_boolean_error_derives

theorem kadmos_generated_python_boolean_if_derives :
    StmtSyntax .python .function
      ((⟨1631, 1731⟩ : SourceSpan).text balancePySource)
      pythonBooleanIf := by
  have hText : ((⟨1631, 1731⟩ : SourceSpan).text balancePySource) =
      "if " ++ ((⟨1634, 1657⟩ : SourceSpan).text balancePySource) ++
        ":\n        " ++ ((⟨1667, 1731⟩ : SourceSpan).text balancePySource) := by
    decide +kernel
  rw [hText]
  exact .pythonIfThen kadmos_generated_python_boolean_condition_derives
    (.pythonFinal kadmos_generated_python_boolean_raise_derives)

theorem kadmos_generated_python_boolean_return_derives :
    StmtSyntax .python .function
      ((⟨1736, 1748⟩ : SourceSpan).text balancePySource)
      (.returnValue (.local "value")) := by
  have hText : ((⟨1736, 1748⟩ : SourceSpan).text balancePySource) =
      "return value" := by decide +kernel
  rw [hText]
  have hLocal : ExprSyntax .python "value" (.local "value") :=
    ExprSyntax.local (name := "value")
      ⟨'v', ['a', 'l', 'u', 'e'], rfl, by decide, by decide⟩
  exact .pythonReturn hLocal

theorem kadmos_generated_python_boolean_body_derives :
    StmtSyntax .python .function
      ((⟨1631, 1748⟩ : SourceSpan).text balancePySource)
      pythonBooleanBody := by
  have hText : ((⟨1631, 1748⟩ : SourceSpan).text balancePySource) =
      ((⟨1631, 1731⟩ : SourceSpan).text balancePySource) ++ "\n    " ++
        ((⟨1736, 1748⟩ : SourceSpan).text balancePySource) := by
    decide +kernel
  rw [hText]
  exact .pythonSequence kadmos_generated_python_boolean_if_derives
    (.pythonFinal kadmos_generated_python_boolean_return_derives)

theorem kadmos_generated_python_boolean_function_derives :
    FunctionDerives .python balancePySource ⟨1593, 1748⟩
      pythonBooleanFunction := by
  have hBounds : (⟨1593, 1748⟩ : SourceSpan).start ≤
      (⟨1593, 1748⟩ : SourceSpan).stop ∧
      (⟨1593, 1748⟩ : SourceSpan).stop ≤ balancePySource.length := by
    decide +kernel
  have hText : ((⟨1593, 1748⟩ : SourceSpan).text balancePySource) =
      "def _boolean(value: Any) -> bool:\n    " ++
        ((⟨1631, 1748⟩ : SourceSpan).text balancePySource) := by
    decide +kernel
  apply FunctionDerives.ofSyntax hBounds
  rw [hText]
  exact FunctionSyntax.pythonAnyToBool
    (identifierTextCheck_sound (name := "_boolean") (by decide))
    (identifierTextCheck_sound (name := "value") (by decide))
    kadmos_generated_python_boolean_body_derives

private def findPythonBoolean : TargetStmt → Option TargetStmt
  | .sequence first rest =>
      (findPythonBoolean first).orElse fun _ => findPythonBoolean rest
  | .defineFunction "_boolean" params body =>
      some (.defineFunction "_boolean" params body)
  | _ => none

theorem kadmos_generated_python_boolean_raw_function_matches :
    (parseGenerated .python balancePySource).toOption.bind
      (fun program => findPythonBoolean program.moduleInit) =
      some (.defineFunction "_boolean" pythonBooleanFunction.params
        pythonBooleanFunction.body) := by
  decide +kernel
