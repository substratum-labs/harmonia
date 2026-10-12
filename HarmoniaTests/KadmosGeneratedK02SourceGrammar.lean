import Harmonia.Applications.Kadmos.Generated.SourceValidator

open Harmonia.Applications.Kadmos.Generated

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
  have aux : ∀ source, ¬ ExprSyntax .ts source (.local "true") := by
    intro source h
    cases h with
    | «local» hName => exact hName.2 (by decide)
  exact aux _

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
    | call _ hArgs => cases hArgs
  exact aux _

theorem kadmos_generated_call_single_argument_owned :
    validateExprText .ts "f(x)"
      (.call (.local "f") (.sequence (.local "x") .empty)) = true := by
  decide +kernel

theorem kadmos_generated_argument_sort_sound :
    ArgumentSyntax .ts "x" (.sequence (.local "x") .empty) :=
  validateArgumentText_sound .ts "x" (.sequence (.local "x") .empty)
    (by decide +kernel)

theorem kadmos_generated_sub_right_association_rejected :
    validateExprText .ts "a - b - c"
      (.binary .sub (.local "a")
        (.binary .sub (.local "b") (.local "c"))) = false := by
  decide +kernel
