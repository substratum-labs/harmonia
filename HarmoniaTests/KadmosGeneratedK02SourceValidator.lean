import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser
import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

private def effectSource : String := "balance - event.amount"
private def effectExpr : TargetExpr :=
  .binary .sub (.local "balance") (.property (.local "event") "amount")

theorem kadmos_generated_effect_span_ts :
    validateExprSpan .ts effectSource ⟨0, 22⟩ effectExpr = true := by
  decide +kernel

theorem kadmos_generated_effect_span_python :
    validateExprSpan .python effectSource ⟨0, 22⟩ effectExpr = true := by
  decide +kernel

theorem kadmos_generated_effect_mutation_rejected :
    validateExprSpan .ts effectSource ⟨0, 22⟩
      (.binary .add (.local "balance") (.property (.local "event") "amount")) = false := by
  decide +kernel

private def tsTemplate : String := "`INVALID_BOUNDS: ${invalid}`"
private def pyFormat : String := "f\"INVALID_BOUNDS: {invalid}\""
private def formatExpr : TargetExpr :=
  .formatted (.formatPart "INVALID_BOUNDS: " (.local "invalid") .empty)

theorem kadmos_generated_ts_template_owned :
    validateExprSpan .ts tsTemplate ⟨0, tsTemplate.length⟩ formatExpr = true := by
  decide +kernel

theorem kadmos_generated_python_fstring_owned :
    validateExprSpan .python pyFormat ⟨0, pyFormat.length⟩ formatExpr = true := by
  decide +kernel

theorem kadmos_generated_ts_template_hole_mutation_rejected :
    validateExprSpan .ts tsTemplate ⟨0, tsTemplate.length⟩
      (.formatted (.formatPart "INVALID_BOUNDS: " (.local "violated") .empty)) = false := by
  decide +kernel

theorem kadmos_generated_ts_template_source_mutation_rejected :
    validateExprText .ts "`INVALID_BOUNDS: ${violated}`" formatExpr = false := by
  decide +kernel

private def twoHoleTS : String :=
  "`Transition '${snapshotAction}' is not legal from state '${snapshotState}'`"
private def twoHoleTSExpr : TargetExpr :=
  .formatted (.formatPart "Transition '" (.local "snapshotAction")
    (.formatPart "' is not legal from state '" (.local "snapshotState")
      (.formatPart "'" .empty .empty)))

theorem kadmos_generated_ts_template_order_owned :
    validateExprSpan .ts twoHoleTS ⟨0, twoHoleTS.length⟩ twoHoleTSExpr = true := by
  decide +kernel

private def twoHolePy : String :=
  "f\"Transition '{action}' is not legal from state '{previous}'\""
private def twoHolePyExpr : TargetExpr :=
  .formatted (.formatPart "Transition '" (.local "action")
    (.formatPart "' is not legal from state '" (.local "previous")
      (.formatPart "'" .empty .empty)))

theorem kadmos_generated_python_fstring_order_owned :
    validateExprSpan .python twoHolePy ⟨0, twoHolePy.length⟩ twoHolePyExpr = true := by
  decide +kernel

theorem kadmos_generated_python_nonlocal_owned :
    validateStmtSpan .python .function "nonlocal position" ⟨0, 17⟩
      (.nonlocalNames ["position"]) = true := by
  decide +kernel

theorem kadmos_generated_python_nonlocal_mutation_rejected :
    validateStmtSpan .python .function "nonlocal position" ⟨0, 17⟩
      (.letLocal "position" true (.integer 0)) = false := by
  decide +kernel

theorem kadmos_generated_python_nonlocal_source_mutation_rejected :
    validateStmtText .python .function "global position"
      (.nonlocalNames ["position"]) = false := by
  decide +kernel

theorem kadmos_generated_ts_switch_break_owned :
    validateStmtSpan .ts .switch "break;" ⟨0, 6⟩
      (.breakTarget "switch") = true := by
  decide +kernel

theorem kadmos_generated_ts_switch_as_loop_rejected :
    validateStmtSpan .ts .switch "break;" ⟨0, 6⟩
      (.breakTarget "loop") = false := by
  decide +kernel

theorem kadmos_generated_ts_switch_source_mutation_rejected :
    validateStmtText .ts .switch "continue;" (.breakTarget "switch") = false := by
  decide +kernel

theorem kadmos_generated_ts_value_import_owned :
    validateStmtSpan .ts .module balanceTsSource ⟨74, 121⟩
      (.fromImport "node:util" "types" "nodeTypes") = true := by
  decide +kernel

theorem kadmos_generated_ts_value_import_alias_mutation_rejected :
    validateStmtSpan .ts .module balanceTsSource ⟨74, 121⟩
      (.fromImport "node:util" "types" "proxyTypes") = false := by
  decide +kernel

theorem kadmos_generated_ts_value_import_module_mutation_rejected :
    validateStmtSpan .ts .module balanceTsSource ⟨74, 121⟩
      (.fromImport "node:buffer" "types" "nodeTypes") = false := by
  decide +kernel

private def tsTypeNames : List String :=
  ["IWorldChecker", "WorldContext", "WorldState", "TransitionStepRequest",
   "StepVerdict", "StepRecord"]

theorem kadmos_generated_ts_type_import_owned :
    validateErasedTypeImport .ts balanceTsSource ⟨122, 244⟩
      tsTypeNames "./ports.js" = true := by
  decide +kernel

theorem kadmos_generated_ts_type_import_module_mutation_rejected :
    validateErasedTypeImport .ts balanceTsSource ⟨122, 244⟩
      tsTypeNames "./ports.py" = false := by
  decide +kernel

theorem kadmos_generated_ts_type_import_name_mutation_rejected :
    validateErasedTypeImport .ts balanceTsSource ⟨122, 244⟩
      ["IWorldChecker", "WorldContext", "WorldState", "TransitionStepRequest",
       "StepRecord", "StepVerdict"] "./ports.js" = false := by
  decide +kernel

theorem kadmos_generated_balance_ts_type_alias_owned :
    validateErasedWorldDataAlias .ts balanceTsSource ⟨245, 771⟩ = true := by
  decide +kernel

theorem kadmos_generated_order_ts_type_alias_owned :
    validateErasedWorldDataAlias .ts orderTsSource ⟨245, 771⟩ = true := by
  decide +kernel

theorem kadmos_generated_type_alias_source_mutation_rejected :
    validateErasedWorldDataAlias .ts
      (emittedWorldDataTypeAlias.replace "readonly context" "mutable context")
      ⟨0, (emittedWorldDataTypeAlias.replace
        "readonly context" "mutable context").length⟩ = false := by
  decide +kernel

theorem kadmos_generated_python_future_import_owned :
    validateStmtSpan .python .module balancePySource ⟨94, 128⟩
      (.fromImport "__future__" "annotations" "annotations") = true := by
  decide +kernel

theorem kadmos_generated_python_copy_import_owned :
    validateStmtSpan .python .module balancePySource ⟨129, 140⟩
      (.importModule "copy" "copy") = true := by
  decide +kernel

private def tsModuleConstCheck (source : String) (name : String)
    (statementSpan valueSpan : SourceSpan) : Option Bool :=
  (parseTargetExpr .ts (valueSpan.text source)).toOption.map
    (fun value => validateStmtSpan .ts .module source statementSpan
      (.letLocal name false value))

theorem kadmos_generated_ts_world_module_binding_owned :
    tsModuleConstCheck balanceTsSource "world" ⟨772, 1267⟩
      ⟨797, 1266⟩ = some true := by
  decide +kernel

theorem kadmos_generated_ts_defaults_module_binding_owned :
    tsModuleConstCheck balanceTsSource "contextDefaults" ⟨1268, 1367⟩
      ⟨1335, 1366⟩ = some true := by
  decide +kernel

theorem kadmos_generated_ts_context_definition_binding_owned :
    tsModuleConstCheck balanceTsSource "contextDefinitions" ⟨1368, 1512⟩
      ⟨1498, 1511⟩ = some true := by
  decide +kernel

theorem kadmos_generated_ts_state_definition_binding_owned :
    tsModuleConstCheck balanceTsSource "stateDefinitions" ⟨1513, 1616⟩
      ⟨1603, 1615⟩ = some true := by
  decide +kernel

theorem kadmos_generated_ts_invariant_definition_binding_owned :
    tsModuleConstCheck balanceTsSource "invariantDefinitions" ⟨1617, 1727⟩
      ⟨1710, 1726⟩ = some true := by
  decide +kernel

theorem kadmos_generated_ts_transition_definition_binding_owned :
    tsModuleConstCheck balanceTsSource "transitionDefinitions" ⟨1728, 1962⟩
      ⟨1944, 1961⟩ = some true := by
  decide +kernel

#check validateExprSpan_sound

theorem kadmos_generated_effect_span_derives :
    ExprDerives .ts effectSource ⟨0, 22⟩ effectExpr :=
  validateExprSpan_sound kadmos_generated_effect_span_ts

private def booleanWorldCondition : TargetExpr :=
  .binary .strictNe (.unary .typeof (.local "value")) (.string "boolean")

theorem kadmos_generated_boolean_world_condition_decodes :
    (parseTargetExpr .ts ((⟨2019, 2045⟩ : SourceSpan).text balanceTsSource)).toOption =
      some booleanWorldCondition := by
  decide +kernel

theorem kadmos_generated_boolean_world_condition_owned :
    validateTSStrictNeTypeofValue
      ((⟨2019, 2045⟩ : SourceSpan).text balanceTsSource)
      (.local "value") (.string "boolean") = true := by
  decide +kernel

theorem kadmos_generated_boolean_world_condition_derives :
    ExprSyntax .ts ((⟨2019, 2045⟩ : SourceSpan).text balanceTsSource)
      booleanWorldCondition :=
  validateTSStrictNeTypeofValue_sound
    kadmos_generated_boolean_world_condition_owned

private def booleanWorldThrowExpr : TargetExpr :=
  .newExpr (.call (.local "Error")
    (.sequence (.string "INVALID_EXPRESSION: expected boolean") .empty))

theorem kadmos_generated_boolean_world_throw_decodes :
    (parseTargetExpr .ts ((⟨2053, 2102⟩ : SourceSpan).text balanceTsSource)).toOption =
      some booleanWorldThrowExpr := by
  decide +kernel

theorem kadmos_generated_boolean_world_throw_owned :
    validateTSNewValue
      ((⟨2053, 2102⟩ : SourceSpan).text balanceTsSource)
      (.call (.local "Error")
        (.sequence (.string "INVALID_EXPRESSION: expected boolean") .empty)) = true := by
  decide +kernel

theorem kadmos_generated_boolean_world_throw_derives :
    ExprSyntax .ts ((⟨2053, 2102⟩ : SourceSpan).text balanceTsSource)
      booleanWorldThrowExpr :=
  validateTSNewValue_sound kadmos_generated_boolean_world_throw_owned

theorem kadmos_generated_boolean_world_condition_operator_mutation_rejected :
    validateTSStrictNeTypeofValue "typeof value == \"boolean\""
      (.local "value") (.string "boolean") = false := by
  decide +kernel

private def booleanWorldIf : TargetStmt :=
  .ifThenElse booleanWorldCondition (.throwValue booleanWorldThrowExpr) .empty

private def booleanWorldBody : TargetStmt :=
  .sequence booleanWorldIf
    (.sequence (.returnValue (.local "value")) .empty)

theorem kadmos_generated_boolean_world_throw_stmt_derives :
    StmtSyntax .ts .function
      ((⟨2047, 2103⟩ : SourceSpan).text balanceTsSource)
      (.throwValue booleanWorldThrowExpr) := by
  have hText : ((⟨2047, 2103⟩ : SourceSpan).text balanceTsSource) =
      "throw " ++ ((⟨2053, 2102⟩ : SourceSpan).text balanceTsSource) ++ ";" := by
    decide +kernel
  rw [hText]
  exact .tsThrow kadmos_generated_boolean_world_throw_derives

theorem kadmos_generated_boolean_world_if_stmt_derives :
    StmtSyntax .ts .function
      ((⟨2015, 2103⟩ : SourceSpan).text balanceTsSource) booleanWorldIf := by
  have hText : ((⟨2015, 2103⟩ : SourceSpan).text balanceTsSource) =
      "if (" ++ ((⟨2019, 2045⟩ : SourceSpan).text balanceTsSource) ++
        ") " ++ ((⟨2047, 2103⟩ : SourceSpan).text balanceTsSource) := by
    decide +kernel
  rw [hText]
  exact .tsIfThen kadmos_generated_boolean_world_condition_derives
    kadmos_generated_boolean_world_throw_stmt_derives

theorem kadmos_generated_boolean_world_return_stmt_derives :
    StmtSyntax .ts .function
      ((⟨2106, 2119⟩ : SourceSpan).text balanceTsSource)
      (.returnValue (.local "value")) := by
  have hText : ((⟨2106, 2119⟩ : SourceSpan).text balanceTsSource) =
      "return value;" := by decide +kernel
  rw [hText]
  have hLocal : ExprSyntax .ts "value" (.local "value") :=
    ExprSyntax.local (name := "value")
      (expressionIdentifierCheck_sound (by decide +kernel))
  exact .tsReturn hLocal

theorem kadmos_generated_boolean_world_body_derives :
    StmtSyntax .ts .function
      ((⟨2015, 2119⟩ : SourceSpan).text balanceTsSource)
      booleanWorldBody := by
  have hText : ((⟨2015, 2119⟩ : SourceSpan).text balanceTsSource) =
      ((⟨2015, 2103⟩ : SourceSpan).text balanceTsSource) ++ "\n  " ++
        ((⟨2106, 2119⟩ : SourceSpan).text balanceTsSource) := by
    decide +kernel
  rw [hText]
  exact .tsSequence kadmos_generated_boolean_world_if_stmt_derives
    (.tsFinal kadmos_generated_boolean_world_return_stmt_derives)

theorem kadmos_generated_boolean_world_raw_body_matches :
    (parseGenerated .ts balanceTsSource).toOption.bind
      (fun program =>
        (program.functions.find? (fun function =>
          function.qualifiedName == "booleanWorld")).map
          (fun function => function.body == booleanWorldBody)) = some true := by
  decide +kernel

private def booleanWorldFunction : TargetFunction :=
  ⟨"booleanWorld", [⟨"value", none⟩], booleanWorldBody⟩

theorem kadmos_generated_boolean_world_function_derives :
    FunctionDerives .ts balanceTsSource ⟨1964, 2121⟩
      booleanWorldFunction := by
  have hBounds : (⟨1964, 2121⟩ : SourceSpan).start ≤ 2121 ∧
      (⟨1964, 2121⟩ : SourceSpan).stop ≤ balanceTsSource.length := by
    decide +kernel
  have hText : ((⟨1964, 2121⟩ : SourceSpan).text balanceTsSource) =
      "function booleanWorld(value: unknown): boolean {\n  " ++
        ((⟨2015, 2119⟩ : SourceSpan).text balanceTsSource) ++ "\n}" := by
    decide +kernel
  apply FunctionDerives.ofSyntax hBounds
  rw [hText]
  exact FunctionSyntax.tsUnknownToBool
    (identifierTextCheck_sound (name := "booleanWorld") (by decide))
    (identifierTextCheck_sound (name := "value") (by decide))
    kadmos_generated_boolean_world_body_derives

theorem kadmos_generated_boolean_world_raw_function_matches :
    (parseGenerated .ts balanceTsSource).toOption.bind
      (fun program => program.functions.find? (fun function =>
        function.qualifiedName == "booleanWorld")) =
      some booleanWorldFunction := by
  decide +kernel

theorem kadmos_generated_python_line_offsets :
    validateLinesAt "x\n  y" 0 (locateSourceLines "x\n  y") = true := by
  decide +kernel

theorem kadmos_generated_python_line_offset_mutation_rejected :
    validateLinesAt "x\n  y" 0
      [⟨1, 2, "x", true⟩, ⟨2, 5, "  y", false⟩] = false := by
  decide +kernel

theorem kadmos_generated_ts_quoted_string_owned :
    validateExprSpan .ts "\"Ready\"" ⟨0, 7⟩ (.string "Ready") = true := by
  decide +kernel

theorem kadmos_generated_ts_escaped_quote_owned :
    validateExprSpan .ts "\"{\\\"id\\\":1}\"" ⟨0, 12⟩
      (.string "{\"id\":1}") = true := by
  decide +kernel

theorem kadmos_generated_python_raw_regex_owned :
    validateExprSpan .python "r\"\\s+\"" ⟨0, 6⟩
      (.string "\\s+") = true := by
  decide +kernel

theorem kadmos_generated_string_value_mutation_rejected :
    validateExprSpan .ts "\"Ready\"" ⟨0, 7⟩ (.string "Reject") = false := by
  decide +kernel

private def balanceWorldLiteralSpan : SourceSpan := ⟨808, 1265⟩

/-- The untrusted decoder proposes the literal value; the independent
    string grammar checks that value against 457 actual emitted characters. -/
theorem kadmos_generated_balance_world_literal_owned :
    (parseTargetExpr .ts (balanceWorldLiteralSpan.text balanceTsSource)).toOption.map
      (validateExprSpan .ts balanceTsSource balanceWorldLiteralSpan) = some true := by
  decide +kernel

/-- The actual TS module binding is a property call with a fully decoded JSON
    string argument; no WorldSpec or evaluator macro is substituted here. -/
theorem kadmos_generated_balance_ts_world_call_owned :
    (parseTargetExpr .ts ((⟨797, 1266⟩ : SourceSpan).text balanceTsSource)).toOption.map
      (validateExprSpan .ts balanceTsSource ⟨797, 1266⟩) = some true := by
  decide +kernel

/-- Python's actual module expression has two separately derived calls:
    user-defined `_freeze` around host `json.loads` of a normal JSON string. -/
theorem kadmos_generated_balance_python_world_calls_owned :
    (parseTargetExpr .python ((⟨489, 967⟩ : SourceSpan).text balancePySource)).toOption.map
      (validateExprSpan .python balancePySource ⟨489, 967⟩) = some true := by
  decide +kernel

private def changeTSJSONCall : TargetExpr → TargetExpr
  | .call (.property receiver _) args => .call (.property receiver "stringify") args
  | expr => expr

theorem kadmos_generated_ts_world_call_target_mutation_rejected :
    (parseTargetExpr .ts ((⟨797, 1266⟩ : SourceSpan).text balanceTsSource)).toOption.map
      (fun expr => validateExprSpan .ts balanceTsSource ⟨797, 1266⟩
        (changeTSJSONCall expr)) = some false := by
  decide +kernel

theorem kadmos_generated_ts_world_source_mutation_rejected :
    (parseTargetExpr .ts ((⟨797, 1266⟩ : SourceSpan).text balanceTsSource)).toOption.map
      (fun expr => validateExprText .ts
        (((⟨797, 1266⟩ : SourceSpan).text balanceTsSource).replace
          "JSON.parse(" "JSON.xarse(") expr) = some false := by
  decide +kernel

private def changePythonFreezeCall : TargetExpr → TargetExpr
  | .call _ args => .call (.local "idealFreeze") args
  | expr => expr

theorem kadmos_generated_python_world_call_target_mutation_rejected :
    (parseTargetExpr .python ((⟨489, 967⟩ : SourceSpan).text balancePySource)).toOption.map
      (fun expr => validateExprSpan .python balancePySource ⟨489, 967⟩
        (changePythonFreezeCall expr)) = some false := by
  decide +kernel

theorem kadmos_generated_python_world_module_binding_owned :
    (parseTargetExpr .python ((⟨489, 967⟩ : SourceSpan).text balancePySource)).toOption.map
      (fun value => validateStmtSpan .python .module balancePySource
        ⟨480, 967⟩ (.assign (.local "_WORLD") value)) = some true := by
  decide +kernel

theorem kadmos_generated_python_world_module_name_mutation_rejected :
    (parseTargetExpr .python ((⟨489, 967⟩ : SourceSpan).text balancePySource)).toOption.map
      (fun value => validateStmtSpan .python .module balancePySource
        ⟨480, 967⟩ (.assign (.local "_MODEL") value)) = some false := by
  decide +kernel
