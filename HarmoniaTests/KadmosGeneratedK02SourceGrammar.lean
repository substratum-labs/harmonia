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
    | call _ _ _ _ hArgs => cases hArgs
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
