import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

#check Lexes.unique
#check validateLexes_sound
#check validateExprSpan_sound
#check validateSourceItems_sound
#check PrefixDerives
#check FunctionDerives

theorem kadmos_generated_reserved_ts_literal_not_local :
    validateExprText .ts "true" (.local "true") = false := by
  decide +kernel

theorem kadmos_generated_reserved_ts_literal_not_grammatical :
    ¬ ExprSyntax .ts "true" (.local "true") := by
  have aux : ∀ source name, name ≠ "this" →
      name ∈ expressionReserved .ts →
      ¬ ExprSyntax .ts source (.local name) := by
    intro source name hNot hReserved h
    cases h with
    | tsThis => exact hNot rfl
    | «local» hName => exact hName.2 hReserved
  exact aux _ _ (by decide) (by decide)

theorem kadmos_generated_reserved_python_literal_not_local :
    validateExprText .python "None" (.local "None") = false := by
  decide +kernel

theorem kadmos_generated_reserved_python_literal_not_grammatical :
    ¬ ExprSyntax .python "None" (.local "None") := by
  have aux : ∀ source, ¬ ExprSyntax .python source (.local "None") := by
    intro source h
    cases h with
    | «local» hName => exact hName.2 (by decide)
  exact aux _

theorem kadmos_generated_call_requires_argument_sort :
    validateExprText .ts "f(x)" (.call (.local "f") (.local "x")) = false := by
  decide +kernel

theorem kadmos_generated_bare_call_argument_not_grammatical :
    ¬ ExprSyntax .ts "f(x)" (.call (.local "f") (.local "x")) := by
  have aux : ∀ source,
      ¬ ExprSyntax .ts source (.call (.local "f") (.local "x")) := by
    intro source h
    cases h with
    | call _ _ _ _ hArgs _ => cases hArgs
  exact aux _

theorem kadmos_generated_call_single_argument_owned :
    validateExprText .ts "f(x)"
      (.call (.local "f") (.sequence (.local "x") .empty)) = true := by
  decide +kernel

theorem kadmos_generated_argument_sort_sound :
    ArgumentSyntax .ts "x" (.sequence (.local "x") .empty) :=
  validateArgumentText_sound .ts "x" (.sequence (.local "x") .empty)
    (by decide +kernel)

theorem kadmos_generated_empty_argument_spine_rejected :
    validateArgumentText .ts "" (.sequence .empty .empty) = false := by
  decide +kernel

theorem kadmos_generated_empty_argument_spine_not_grammatical :
    ¬ ArgumentSyntax .ts "" (.sequence .empty .empty) := by
  intro h
  have hOnly := ArgumentSyntax.empty_only h rfl
  cases hOnly

theorem kadmos_generated_empty_callee_rejected :
    validateExprText .ts "(x)"
      (.call .empty (.sequence (.local "x") .empty)) = false := by
  decide +kernel

theorem kadmos_generated_empty_callee_not_grammatical :
    ¬ ExprSyntax .ts "(x)"
      (.call .empty (.sequence (.local "x") .empty)) :=
  ExprSyntax.no_empty_callee

theorem kadmos_generated_leading_comma_argument_rejected :
    validateArgumentText .ts ", x"
      (.sequence .empty (.sequence (.local "x") .empty)) = false := by
  decide +kernel

theorem kadmos_generated_leading_comma_argument_not_grammatical :
    ¬ ArgumentSyntax .ts ", x"
      (.sequence .empty (.sequence (.local "x") .empty)) :=
  ArgumentSyntax.no_empty_first

theorem kadmos_generated_empty_property_receiver_rejected :
    validateExprText .ts ".x" (.property .empty "x") = false := by
  decide +kernel

theorem kadmos_generated_empty_property_receiver_not_grammatical :
    ¬ ExprSyntax .ts ".x" (.property .empty "x") :=
  ExprSyntax.no_empty_property_receiver

theorem kadmos_generated_empty_optional_receiver_rejected :
    validateExprText .ts "?.x" (.optionalProperty .empty "x") = false := by
  decide +kernel

theorem kadmos_generated_empty_optional_receiver_not_grammatical :
    ¬ ExprSyntax .ts "?.x" (.optionalProperty .empty "x") :=
  ExprSyntax.no_empty_optional_receiver

theorem kadmos_generated_empty_index_receiver_rejected :
    validateExprText .ts "[x]" (.index .empty (.local "x")) = false := by
  decide +kernel

theorem kadmos_generated_empty_index_receiver_not_grammatical :
    ¬ ExprSyntax .ts "[x]" (.index .empty (.local "x")) :=
  ExprSyntax.no_empty_index_receiver

private def pyChainedWhitespaceCall : TargetExpr :=
  .call (.property (.call (.property (.local "match") "group") .empty)
    "isspace") .empty

theorem kadmos_generated_python_chained_call_source_owned :
    validateExprSpan .python balancePySource ⟨2837, 2860⟩
      pyChainedWhitespaceCall = true := by
  decide +kernel

theorem kadmos_generated_python_chained_call_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨2837, 2860⟩ : SourceSpan).text balancePySource)).toOption =
        some pyChainedWhitespaceCall := by
  decide +kernel

theorem kadmos_generated_python_chained_call_derives :
    ExprDerives .python balancePySource ⟨2837, 2860⟩
      pyChainedWhitespaceCall :=
  validateExprSpan_sound kadmos_generated_python_chained_call_source_owned

theorem kadmos_generated_python_chained_call_target_mutation_rejected :
    validateExprSpan .python balancePySource ⟨2837, 2860⟩
      (.call (.property (.call (.property (.local "match") "group") .empty)
        "idealIsspace") .empty) = false := by
  decide +kernel

private def pyFloatIntegerCall : TargetExpr :=
  .call (.property (.call (.local "float")
    (.sequence (.local "value") .empty)) "is_integer") .empty

theorem kadmos_generated_python_float_chained_call_source_owned :
    validateExprSpan .python balancePySource ⟨2276, 2301⟩
      pyFloatIntegerCall = true := by
  decide +kernel

theorem kadmos_generated_python_float_chained_call_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨2276, 2301⟩ : SourceSpan).text balancePySource)).toOption =
        some pyFloatIntegerCall := by
  decide +kernel

theorem kadmos_generated_sub_right_association_rejected :
    validateExprText .ts "a - b - c"
      (.binary .sub (.local "a")
        (.binary .sub (.local "b") (.local "c"))) = false := by
  decide +kernel

private def twoArgs : TargetExpr :=
  .sequence (.local "a") (.sequence (.local "b") .empty)

theorem kadmos_generated_two_argument_sort_owned :
    validateExprText .ts "f(a, b)" (.call (.local "f") twoArgs) = true := by
  decide +kernel

private def nestedArgs : TargetExpr :=
  .sequence (.call (.local "g") twoArgs)
    (.sequence (.local "c") .empty)

theorem kadmos_generated_nested_comma_is_not_outer_split :
    validateExprText .python "f(g(a, b), c)"
      (.call (.local "f") nestedArgs) = true := by
  decide +kernel

theorem kadmos_generated_two_argument_swap_rejected :
    validateExprText .ts "f(a, b)"
      (.call (.local "f")
        (.sequence (.local "b") (.sequence (.local "a") .empty))) = false := by
  decide +kernel

private def generatedPythonNestedCall : TargetExpr :=
  .call (.local "_div")
    (.sequence (.call (.local "_number")
      (.sequence (.local "left") .empty))
      (.sequence (.call (.local "_number")
        (.sequence (.local "right") .empty)) .empty))

theorem kadmos_generated_python_nested_call_source_owned :
    validateExprSpan .python balancePySource ⟨6105, 6140⟩
      generatedPythonNestedCall = true := by
  decide +kernel

theorem kadmos_generated_python_nested_call_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨6105, 6140⟩ : SourceSpan).text balancePySource)).toOption =
        some generatedPythonNestedCall := by
  decide +kernel

theorem kadmos_generated_python_nested_call_derives :
    ExprDerives .python balancePySource ⟨6105, 6140⟩
      generatedPythonNestedCall :=
  validateExprSpan_sound kadmos_generated_python_nested_call_source_owned

theorem kadmos_generated_python_nested_call_wrong_name_rejected :
    validateExprSpan .python balancePySource ⟨6105, 6140⟩
      (.call (.local "ideal_div")
        (.sequence (.call (.local "_number")
          (.sequence (.local "left") .empty))
          (.sequence (.call (.local "_number")
            (.sequence (.local "right") .empty)) .empty))) = false := by
  decide +kernel

private def generatedPythonCtorInvariantCall : TargetExpr :=
  .call (.property (.local "self") "_invariant")
    (.sequence (.local "_INITIAL")
      (.sequence (.local "candidate") .empty))

theorem kadmos_generated_python_ctor_invariant_call_owned :
    validateExprSpan .python balancePySource ⟨12175, 12211⟩
      generatedPythonCtorInvariantCall = true := by
  decide +kernel

theorem kadmos_generated_python_ctor_invariant_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨12175, 12211⟩ : SourceSpan).text balancePySource)).toOption =
        some generatedPythonCtorInvariantCall := by
  decide +kernel

theorem kadmos_generated_python_ctor_invariant_call_derives :
    ExprDerives .python balancePySource ⟨12175, 12211⟩
      generatedPythonCtorInvariantCall :=
  validateExprSpan_sound kadmos_generated_python_ctor_invariant_call_owned

theorem kadmos_generated_python_ctor_invariant_argument_swap_rejected :
    validateExprSpan .python balancePySource ⟨12175, 12211⟩
      (.call (.property (.local "self") "_invariant")
        (.sequence (.local "candidate")
          (.sequence (.local "_INITIAL") .empty))) = false := by
  decide +kernel

private def generatedTSCtorInvariantCall : TargetExpr :=
  .call (.property (.local "this") "checkInvariants")
    (.sequence (.string "Ready")
      (.sequence (.local "candidate") .empty))

theorem kadmos_generated_ts_ctor_invariant_call_owned :
    validateExprSpan .ts balanceTsSource ⟨11893, 11933⟩
      generatedTSCtorInvariantCall = true := by
  decide +kernel

theorem kadmos_generated_ts_ctor_invariant_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨11893, 11933⟩ : SourceSpan).text balanceTsSource)).toOption =
        some generatedTSCtorInvariantCall := by
  decide +kernel

theorem kadmos_generated_ts_ctor_invariant_call_derives :
    ExprDerives .ts balanceTsSource ⟨11893, 11933⟩
      generatedTSCtorInvariantCall :=
  validateExprSpan_sound kadmos_generated_ts_ctor_invariant_call_owned

theorem kadmos_generated_ts_ctor_invariant_target_mutation_rejected :
    validateExprSpan .ts balanceTsSource ⟨11893, 11933⟩
      (.call (.property (.local "this") "idealCheckInvariants")
        (.sequence (.string "Ready")
          (.sequence (.local "candidate") .empty))) = false := by
  decide +kernel

theorem kadmos_generated_ts_private_field_source_owned :
    validateExprSpan .ts balanceTsSource ⟨8234, 8247⟩
      (.property (.local "this") "#context") = true := by
  decide +kernel

theorem kadmos_generated_ts_private_field_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨8234, 8247⟩ : SourceSpan).text balanceTsSource)).toOption =
        some (.property (.local "this") "#context") := by
  decide +kernel

theorem kadmos_generated_ts_private_field_derives :
    ExprDerives .ts balanceTsSource ⟨8234, 8247⟩
      (.property (.local "this") "#context") :=
  validateExprSpan_sound kadmos_generated_ts_private_field_source_owned

theorem kadmos_generated_ts_private_field_mutation_rejected :
    validateExprSpan .ts balanceTsSource ⟨8234, 8247⟩
      (.property (.local "this") "#history") = false := by
  decide +kernel

private def tsPrototypeCallTarget : TargetExpr :=
  .property (.property (.property (.local "Object") "prototype")
    "toString") "call"

theorem kadmos_generated_ts_nested_property_source_owned :
    validateExprSpan .ts balanceTsSource ⟨6469, 6499⟩
      tsPrototypeCallTarget = true := by
  decide +kernel

theorem kadmos_generated_ts_nested_property_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨6469, 6499⟩ : SourceSpan).text balanceTsSource)).toOption =
        some tsPrototypeCallTarget := by
  decide +kernel

theorem kadmos_generated_ts_nested_property_derives :
    ExprDerives .ts balanceTsSource ⟨6469, 6499⟩
      tsPrototypeCallTarget :=
  validateExprSpan_sound kadmos_generated_ts_nested_property_source_owned

theorem kadmos_generated_ts_keyword_property_allowed :
    validateExprText .ts "obj.true"
      (.property (.local "obj") "true") = true := by
  decide +kernel

theorem kadmos_generated_python_keyword_property_rejected :
    validateExprText .python "obj.None"
      (.property (.local "obj") "None") = false := by
  decide +kernel

theorem kadmos_generated_ts_optional_property_source_owned :
    validateExprSpan .ts balanceTsSource ⟨6115, 6133⟩
      (.optionalProperty (.local "nodeTypes") "isProxy") = true := by
  decide +kernel

theorem kadmos_generated_ts_optional_property_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨6115, 6133⟩ : SourceSpan).text balanceTsSource)).toOption =
        some (.optionalProperty (.local "nodeTypes") "isProxy") := by
  decide +kernel

theorem kadmos_generated_ts_optional_property_derives :
    ExprDerives .ts balanceTsSource ⟨6115, 6133⟩
      (.optionalProperty (.local "nodeTypes") "isProxy") :=
  validateExprSpan_sound kadmos_generated_ts_optional_property_source_owned

theorem kadmos_generated_ts_optional_property_target_mutation_rejected :
    validateExprSpan .ts balanceTsSource ⟨6115, 6133⟩
      (.optionalProperty (.local "nodeTypes") "idealIsProxy") = false := by
  decide +kernel

theorem kadmos_generated_ts_optional_property_operator_mutation_rejected :
    validateExprText .ts "nodeTypes.isProxy"
      (.optionalProperty (.local "nodeTypes") "isProxy") = false := by
  decide +kernel

theorem kadmos_generated_ts_env_index_source_owned :
    validateExprSpan .ts balanceTsSource ⟨3608, 3618⟩
      (.index (.local "env") (.local "token")) = true := by
  decide +kernel

theorem kadmos_generated_ts_env_index_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨3608, 3618⟩ : SourceSpan).text balanceTsSource)).toOption =
        some (.index (.local "env") (.local "token")) := by
  decide +kernel

theorem kadmos_generated_ts_env_index_derives :
    ExprDerives .ts balanceTsSource ⟨3608, 3618⟩
      (.index (.local "env") (.local "token")) :=
  validateExprSpan_sound kadmos_generated_ts_env_index_source_owned

theorem kadmos_generated_python_world_context_index_source_owned :
    validateExprSpan .python balancePySource ⟨1146, 1163⟩
      (.index (.local "_WORLD") (.string "context")) = true := by
  decide +kernel

theorem kadmos_generated_python_world_context_index_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨1146, 1163⟩ : SourceSpan).text balancePySource)).toOption =
        some (.index (.local "_WORLD") (.string "context")) := by
  decide +kernel

theorem kadmos_generated_python_world_context_index_derives :
    ExprDerives .python balancePySource ⟨1146, 1163⟩
      (.index (.local "_WORLD") (.string "context")) :=
  validateExprSpan_sound kadmos_generated_python_world_context_index_source_owned

theorem kadmos_generated_python_nested_index_source_owned :
    validateExprSpan .python balancePySource ⟨11959, 11982⟩
      (.index (.index (.local "_WORLD") (.string "context"))
        (.local "name")) = true := by
  decide +kernel

theorem kadmos_generated_python_nested_index_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨11959, 11982⟩ : SourceSpan).text balancePySource)).toOption =
        some (.index (.index (.local "_WORLD") (.string "context"))
          (.local "name")) := by
  decide +kernel

theorem kadmos_generated_python_nested_index_key_mutation_rejected :
    validateExprSpan .python balancePySource ⟨11959, 11982⟩
      (.index (.index (.local "_WORLD") (.string "states"))
        (.local "name")) = false := by
  decide +kernel

private def tsBoundDefinitionNonNull : TargetExpr :=
  .nonNull (.index (.local "contextDefinitions") (.local "name"))

theorem kadmos_generated_ts_nonnull_index_source_owned :
    validateExprSpan .ts balanceTsSource ⟨11516, 11541⟩
      tsBoundDefinitionNonNull = true := by
  decide +kernel

theorem kadmos_generated_ts_nonnull_index_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨11516, 11541⟩ : SourceSpan).text balanceTsSource)).toOption =
        some tsBoundDefinitionNonNull := by
  decide +kernel

theorem kadmos_generated_ts_nonnull_index_derives :
    ExprDerives .ts balanceTsSource ⟨11516, 11541⟩
      tsBoundDefinitionNonNull :=
  validateExprSpan_sound kadmos_generated_ts_nonnull_index_source_owned

theorem kadmos_generated_ts_nonnull_source_mutation_rejected :
    validateExprText .ts "contextDefinitions[name]"
      tsBoundDefinitionNonNull = false := by
  decide +kernel

private def tsDepthLimitExpr : TargetExpr :=
  .binary .gt (.local "depth") (.integer 128)

private def tsSeenSizeLimitExpr : TargetExpr :=
  .binary .ge (.property (.local "seen") "size") (.integer 128)

theorem kadmos_generated_ts_depth_comparison_owned :
    validateExprSpan .ts balanceTsSource ⟨5853, 5864⟩
      tsDepthLimitExpr = true := by
  decide +kernel

theorem kadmos_generated_python_depth_comparison_owned :
    validateExprSpan .python balancePySource ⟨6489, 6500⟩
      tsDepthLimitExpr = true := by
  decide +kernel

theorem kadmos_generated_ts_size_comparison_owned :
    validateExprSpan .ts balanceTsSource ⟨6360, 6376⟩
      tsSeenSizeLimitExpr = true := by
  decide +kernel

theorem kadmos_generated_ts_depth_comparison_derives :
    ExprDerives .ts balanceTsSource ⟨5853, 5864⟩ tsDepthLimitExpr :=
  validateExprSpan_sound kadmos_generated_ts_depth_comparison_owned

theorem kadmos_generated_python_depth_comparison_derives :
    ExprDerives .python balancePySource ⟨6489, 6500⟩ tsDepthLimitExpr :=
  validateExprSpan_sound kadmos_generated_python_depth_comparison_owned

theorem kadmos_generated_ts_size_comparison_derives :
    ExprDerives .ts balanceTsSource ⟨6360, 6376⟩ tsSeenSizeLimitExpr :=
  validateExprSpan_sound kadmos_generated_ts_size_comparison_owned

theorem kadmos_generated_ts_depth_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨5853, 5864⟩ : SourceSpan).text balanceTsSource)).toOption =
        some tsDepthLimitExpr := by
  decide +kernel

theorem kadmos_generated_python_depth_raw_candidate_matches :
    (parseTargetExpr .python
      ((⟨6489, 6500⟩ : SourceSpan).text balancePySource)).toOption =
        some tsDepthLimitExpr := by
  decide +kernel

theorem kadmos_generated_ts_size_raw_candidate_matches :
    (parseTargetExpr .ts
      ((⟨6360, 6376⟩ : SourceSpan).text balanceTsSource)).toOption =
        some tsSeenSizeLimitExpr := by
  decide +kernel

theorem kadmos_generated_comparison_target_mutation_rejected :
    validateExprText .ts "depth > 128"
      (.binary .ge (.local "depth") (.integer 128)) = false := by
  decide +kernel

theorem kadmos_generated_comparison_precedence_mutation_rejected :
    validateExprText .ts "a > b - c"
      (.binary .sub (.binary .gt (.local "a") (.local "b"))
        (.local "c")) = false := by
  decide +kernel

theorem kadmos_generated_comparison_wrong_precedence_not_grammatical :
    ¬ ExprSyntax .ts "a > b - c"
      (.binary .sub (.binary .gt (.local "a") (.local "b"))
        (.local "c")) :=
  ExprSyntax.no_sub_after_gt

#print axioms kadmos_generated_ts_depth_comparison_derives
#print axioms kadmos_generated_python_depth_comparison_derives
#print axioms kadmos_generated_ts_size_comparison_derives
#print axioms kadmos_generated_comparison_wrong_precedence_not_grammatical

private def sequenceA : TargetStmt := .doExpr (.local "a")
private def sequenceB : TargetStmt := .doExpr (.local "b")
private def sequenceC : TargetStmt := .doExpr (.local "c")

private theorem sequenceASyntax :
    StmtSyntax .ts .function "a;" sequenceA :=
  .tsDo (ExprSyntax.local (name := "a")
    (expressionIdentifierCheck_sound (by decide +kernel)))

private theorem sequenceBSyntax :
    StmtSyntax .ts .function "b;" sequenceB :=
  .tsDo (ExprSyntax.local (name := "b")
    (expressionIdentifierCheck_sound (by decide +kernel)))

private theorem sequenceCSyntax :
    StmtSyntax .ts .function "c;" sequenceC :=
  .tsDo (ExprSyntax.local (name := "c")
    (expressionIdentifierCheck_sound (by decide +kernel)))

theorem kadmos_generated_right_nested_sequence_derives :
    StmtSyntax .ts .body "a;\n  b;\n  c;"
      (.sequence sequenceA (.sequence sequenceB
        (.sequence sequenceC .empty))) :=
  .tsSequence (by simp [SingleStatement, sequenceA]) sequenceASyntax
    (.tsSequence (by simp [SingleStatement, sequenceB]) sequenceBSyntax
      (.tsFinal (by simp [SingleStatement, sequenceC]) sequenceCSyntax))

theorem kadmos_generated_left_nested_sequence_not_grammatical :
    ¬ StmtSyntax .ts .body "a;\n  b;\n  c;"
      (.sequence (.sequence sequenceA (.sequence sequenceB .empty))
        (.sequence sequenceC .empty)) :=
  StmtSyntax.no_nested_sequence_first

#print axioms kadmos_generated_right_nested_sequence_derives
#print axioms kadmos_generated_left_nested_sequence_not_grammatical

theorem kadmos_generated_python_dedented_line_rejected :
    suiteLinesWithin "        " "return 1\n    return 2" = false := by
  decide +kernel

theorem kadmos_generated_unbraced_ts_if_cannot_swallow_sibling :
    ¬ StmtSyntax .ts .function "if (true) a;\n  b;"
      (.ifThenElse (.bool true)
        (.sequence sequenceA (.sequence sequenceB .empty)) .empty) :=
  StmtSyntax.no_unbraced_ts_sequence

#print axioms kadmos_generated_unbraced_ts_if_cannot_swallow_sibling

-- A postfix node cannot absorb an unparenthesized lower-precedence receiver.
theorem kadmos_generated_sub_property_receiver_rejected :
    validateExprText .ts "balance - event.amount"
      (.property (.binary .sub (.local "balance") (.local "event")) "amount") = false := by
  decide +kernel

theorem kadmos_generated_sub_call_callee_rejected :
    validateExprText .ts "a - f(x)"
      (.call (.binary .sub (.local "a") (.local "f"))
        (.sequence (.local "x") .empty)) = false := by
  decide +kernel

theorem kadmos_generated_typeof_property_receiver_rejected :
    validateExprText .ts "typeof event.amount"
      (.property (.unary .typeof (.local "event")) "amount") = false := by
  decide +kernel

theorem kadmos_generated_adjacent_ts_templates_rejected :
    validateExprText .ts "`a` + `b`"
      (.formatted (.formatPart "a` + `b" .empty .empty)) = false := by
  decide +kernel

theorem kadmos_generated_adjacent_python_fstrings_rejected :
    validateExprText .python "f\"a\" + f\"b\""
      (.formatted (.formatPart "a\" + f\"b" .empty .empty)) = false := by
  decide +kernel


theorem kadmos_generated_sub_postfix_not_grammatical {lang source a b name} :
    ¬ ExprSyntax lang source (.property (.binary .sub a b) name) := by
  intro h
  cases h with
  | property _ _ _ hPower _ => simp [exprBindingPower] at hPower

theorem kadmos_generated_sub_callee_not_grammatical {lang source a b args} :
    ¬ ExprSyntax lang source (.call (.binary .sub a b) args) := by
  intro h
  cases h with
  | call _ _ _ _ _ hPower => simp [exprBindingPower] at hPower

theorem kadmos_generated_typeof_postfix_not_grammatical {source value name} :
    ¬ ExprSyntax .ts source (.property (.unary .typeof value) name) := by
  intro h
  cases h with
  | property _ _ _ hPower _ => simp [exprBindingPower] at hPower

#print axioms kadmos_generated_sub_postfix_not_grammatical
#print axioms kadmos_generated_sub_callee_not_grammatical

-- The next physical statement must be deeper than a suite-opening header.
theorem kadmos_generated_python_missing_nested_suite_rejected :
    suiteLinesWithin "    "
      "if True:\n        if True:\n        return True" = false := by
  decide +kernel

theorem kadmos_generated_python_nested_suite_owned :
    suiteLinesWithin "    "
      "if True:\n        if True:\n            return True" = true := by
  decide +kernel


theorem kadmos_generated_single_statement_cannot_be_list {lang source first rest} :
    ¬ StmtSyntax lang .function source (.sequence first rest) := by
  intro h
  cases h

theorem kadmos_generated_bare_return_cannot_be_body {lang source value} :
    ¬ StmtSyntax lang .body source (.returnValue value) := by
  intro h
  cases h

theorem kadmos_generated_single_return_owned :
    validateStmtText .ts .function "return true;" (.returnValue (.bool true)) = true := by
  decide +kernel

theorem kadmos_generated_body_return_owned :
    validateStmtText .ts .body "return true;"
      (.sequence (.returnValue (.bool true)) .empty) = true := by
  decide +kernel

theorem kadmos_generated_body_bare_return_rejected :
    validateStmtText .ts .body "return true;" (.returnValue (.bool true)) = false := by
  decide +kernel

#print axioms kadmos_generated_single_statement_cannot_be_list
#print axioms kadmos_generated_bare_return_cannot_be_body

theorem kadmos_generated_empty_python_suite_rejected :
    suiteLinesWithin "    " "" = false := by decide +kernel

theorem kadmos_generated_comment_only_python_suite_rejected :
    suiteLinesWithin "    " "# no body" = false := by decide +kernel

theorem kadmos_generated_python_blank_line_is_not_a_suite :
    suiteLinesWithin "    " "if True:\n\n    return True" = false := by decide +kernel

theorem kadmos_generated_typeof_binary_child_not_grammatical {source a b} :
    ¬ ExprSyntax .ts source (.unary .typeof (.binary .sub a b)) := by
  intro h
  cases h with
  | tsTypeof _ hPower => simp [exprBindingPower] at hPower

theorem kadmos_generated_new_binary_child_not_grammatical {source a b} :
    ¬ ExprSyntax .ts source (.newExpr (.binary .sub a b)) := by
  intro h
  cases h with
  | tsNew _ hPower => simp [exprBindingPower] at hPower

private def missingPythonSuiteBody : TargetStmt :=
  .sequence (.ifThenElse (.bool true)
    (.sequence (.ifThenElse (.bool true)
      (.sequence (.returnValue (.bool true)) .empty) .empty) .empty) .empty) .empty

theorem kadmos_generated_missing_python_function_suite_rejected :
    validateFunctionText .python
      "def f(x: Any) -> bool:\n    if True:\n        if True:\n        return True"
      "if True:\n        if True:\n        return True"
      ⟨"f", [⟨"x", none⟩], missingPythonSuiteBody⟩ = false := by
  decide +kernel

theorem kadmos_generated_equal_indent_function_suite_rejected :
    validateFunctionText .python
      "def f(x: Any) -> bool:\n    if True:\n    return True"
      "if True:\n    return True"
      ⟨"f", [⟨"x", none⟩], .sequence (.ifThenElse (.bool true)
        (.sequence (.returnValue (.bool true)) .empty) .empty) .empty⟩ = false := by
  decide +kernel

theorem kadmos_generated_unmatched_python_format_close_rejected :
    validateExprText .python "f\"a}\""
      (.formatted (.formatPart "a}" .empty .empty)) = false := by decide +kernel

theorem kadmos_generated_ts_boolean_format_local_rejected :
    validateExprText .ts "`${true}`"
      (.formatted (.formatPart "" (.local "true") .empty)) = false := by decide +kernel

theorem kadmos_generated_python_boolean_format_local_rejected :
    validateExprText .python "f\"{True}\""
      (.formatted (.formatPart "" (.local "True") .empty)) = false := by decide +kernel

theorem kadmos_generated_ts_receiver_format_owned :
    validateExprText .ts "`${this}`"
      (.formatted (.formatPart "" (.local "this") .empty)) = true := by decide +kernel

theorem kadmos_generated_python_format_close_not_grammatical {source} :
    ¬ ExprSyntax .python source
      (.formatted (.formatPart "a}" .empty .empty)) := by
  intro h
  cases h with
  | formatted _ hParts _ =>
      cases hParts with
      | literal _ _ hLiteral =>
          have hNo : formatLiteralCheck .python "a}" = false := by decide +kernel
          rw [hNo] at hLiteral
          cases hLiteral

theorem kadmos_generated_ts_format_boolean_not_grammatical {source text rest} :
    ¬ ExprSyntax .ts source
      (.formatted (.formatPart text (.local "true") rest)) := by
  intro h
  cases h with
  | formatted _ hParts _ =>
      cases hParts with
      | hole _ hName _ _ =>
          rcases hName with hThis | hLocal
          · exact (by decide : ("true" : String) ≠ "this") hThis.2
          · exact hLocal.2 (by decide)

theorem kadmos_generated_postincrement_receiver_rejected :
    validateExprText .ts "x++.y" (.property (.postIncrement "x") "y") = false := by decide +kernel

theorem kadmos_generated_postincrement_receiver_not_grammatical {lang source name field} :
    ¬ ExprSyntax lang source (.property (.postIncrement name) field) := by
  intro h
  cases h with
  | property _ _ _ hPower _ => simp [exprBindingPower] at hPower

theorem kadmos_generated_python_comparison_chain_rejected :
    validateFunctionExpr .python "a > b is not c"
      (.binary .isNotIdentity (.binary .gt (.local "a") (.local "b")) (.local "c")) = false := by decide +kernel

theorem kadmos_generated_python_nested_gt_rejected :
    validateExprText .python "a > b > c"
      (.binary .gt (.binary .gt (.local "a") (.local "b")) (.local "c")) = false := by decide +kernel

theorem kadmos_generated_python_chain_not_grammatical {source a b c} :
    ¬ ExprSyntax .python source (.binary .isNotIdentity (.binary .gt a b) c) := by
  intro h
  cases h with
  | pythonIsNot _ _ hPower _ => simp [exprBindingPower] at hPower

theorem kadmos_generated_function_header_cannot_own_body :
    functionBodyLocatedCheck .python ⟨0,28⟩ ⟨4,5⟩
      ⟨"f", [⟨"x", none⟩], .sequence (.doExpr (.local "f")) .empty⟩ = false := by decide +kernel

theorem kadmos_generated_function_body_position_owned :
    functionBodyLocatedCheck .python ⟨0,28⟩ ⟨27,28⟩
      ⟨"f", [⟨"x", none⟩], .sequence (.doExpr (.local "f")) .empty⟩ = true := by decide +kernel

theorem kadmos_generated_python_statement_must_start_line :
    validateStmtSpan .python .function "x = return True" ⟨4,15⟩
      (.returnValue (.bool true)) = false := by decide +kernel


theorem kadmos_generated_ts_integral_member_dot_rejected :
    validateExprText .ts "1.foo" (.property (.integer 1) "foo") = false := by decide +kernel

theorem kadmos_generated_python_integral_member_dot_rejected :
    validateExprText .python "1.foo" (.property (.integer 1) "foo") = false := by decide +kernel

-- Empty list sentinels are not executable expression nodes.
theorem kadmos_generated_empty_runtime_expression_rejected :
    validateExprText .python "" .empty = false := by decide +kernel

theorem kadmos_generated_python_ghost_statement_rejected :
    validateStmtText .python .function "" (.doExpr .empty) = false := by decide +kernel

theorem kadmos_generated_python_trailing_ghost_rejected :
    validateStmtText .python .body "x\n    "
      (.sequence (.doExpr (.local "x"))
        (.sequence (.doExpr .empty) .empty)) = false := by decide +kernel

theorem kadmos_generated_ts_empty_operand_rejected :
    validateExprText .ts " - x" (.binary .sub .empty (.local "x")) = false := by decide +kernel

theorem kadmos_generated_empty_arguments_retained :
    validateArgumentText .python "" .empty = true := by decide +kernel

theorem kadmos_generated_empty_call_retained :
    validateExprText .python "f()" (.call (.local "f") .empty) = true := by decide +kernel

theorem kadmos_generated_empty_expression_not_grammatical {lang source} :
    ¬ ExprSyntax lang source .empty := by
  intro h
  cases h

theorem kadmos_generated_python_ghost_not_grammatical {source} :
    ¬ StmtSyntax .python .function source (.doExpr .empty) := by
  intro h
  cases h with
  | pythonDo hExpr => exact ExprSyntax.no_empty hExpr
