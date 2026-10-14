import Harmonia.Applications.Kadmos.Generated.SourceStatementCertificate
import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser
import Harmonia.Applications.Kadmos.Generated.TargetTSStatementParser
import Harmonia.Applications.Kadmos.Generated.TargetStatementParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

private def tsSeenAddExpr : TargetExpr :=
  .call (.property (.local "seen") "add")
    (.sequence (.local "raw") .empty)

private def pythonSeenAddExpr : TargetExpr :=
  .call (.property (.local "seen") "add")
    (.sequence (.local "identity") .empty)

theorem kadmos_generated_ts_seen_add_raw_expr_matches :
    (parseTargetExpr .ts ((⟨6448, 6461⟩ : SourceSpan).text balanceTsSource)).toOption =
      some tsSeenAddExpr := by
  decide +kernel

theorem kadmos_generated_ts_seen_add_raw_statement_matches :
    (parseTSBlock ((⟨6448, 6462⟩ : SourceSpan).text balanceTsSource)).toOption =
      some (.sequence (.doExpr tsSeenAddExpr) .empty) := by
  decide +kernel

theorem kadmos_generated_ts_seen_add_statement_certificate_checked :
    validateStmtCertificate .ts balanceTsSource ⟨6448, 6462⟩
      (.doExpr tsSeenAddExpr) (.doExpr ⟨6448, 6461⟩) = true := by
  decide +kernel

theorem kadmos_generated_ts_seen_add_statement_certificate_sound :
    StmtDerives .ts .function balanceTsSource ⟨6448, 6462⟩
      (.doExpr tsSeenAddExpr) :=
  validateStmtCertificate_sound
    kadmos_generated_ts_seen_add_statement_certificate_checked

theorem kadmos_generated_ts_seen_add_target_mutation_rejected :
    validateStmtCertificate .ts balanceTsSource ⟨6448, 6462⟩
      (.doExpr (.call (.property (.local "seen") "idealAdd")
        (.sequence (.local "raw") .empty)))
      (.doExpr ⟨6448, 6461⟩) = false := by
  decide +kernel

theorem kadmos_generated_python_seen_add_raw_expr_matches :
    (parseTargetExpr .python ((⟨7353, 7371⟩ : SourceSpan).text balancePySource)).toOption =
      some pythonSeenAddExpr := by
  decide +kernel

theorem kadmos_generated_python_seen_add_raw_statement_matches :
    (parsePythonBlock
      ((⟨7353, 7371⟩ : SourceSpan).text balancePySource) 0).toOption =
      some (.sequence (.doExpr pythonSeenAddExpr) .empty) := by
  decide +kernel

theorem kadmos_generated_python_seen_add_statement_certificate_checked :
    validateStmtCertificate .python balancePySource ⟨7353, 7371⟩
      (.doExpr pythonSeenAddExpr) (.doExpr ⟨7353, 7371⟩) = true := by
  decide +kernel

theorem kadmos_generated_python_seen_add_statement_certificate_sound :
    StmtDerives .python .function balancePySource ⟨7353, 7371⟩
      (.doExpr pythonSeenAddExpr) :=
  validateStmtCertificate_sound
    kadmos_generated_python_seen_add_statement_certificate_checked

theorem kadmos_generated_python_seen_add_argument_mutation_rejected :
    validateStmtCertificate .python balancePySource ⟨7353, 7371⟩
      (.doExpr (.call (.property (.local "seen") "add")
        (.sequence (.local "raw") .empty)))
      (.doExpr ⟨7353, 7371⟩) = false := by
  decide +kernel

theorem kadmos_generated_ts_index_binding_owned :
    validateStmtCertificate .ts balanceTsSource ⟨2695, 2709⟩
      (.letLocal "index" true (.integer 0))
      (.localBinding ⟨2707, 2708⟩) = true := by
  decide +kernel

theorem kadmos_generated_ts_index_binding_raw_statement_matches :
    (parseTSBlock ((⟨2695, 2709⟩ : SourceSpan).text balanceTsSource)).toOption =
      some (.sequence (.letLocal "index" true (.integer 0)) .empty) := by
  decide +kernel

theorem kadmos_generated_ts_index_binding_derives :
    StmtDerives .ts .function balanceTsSource ⟨2695, 2709⟩
      (.letLocal "index" true (.integer 0)) :=
  validateStmtCertificate_sound kadmos_generated_ts_index_binding_owned

theorem kadmos_generated_ts_index_binding_mutability_rejected :
    validateStmtCertificate .ts balanceTsSource ⟨2695, 2709⟩
      (.letLocal "index" false (.integer 0))
      (.localBinding ⟨2707, 2708⟩) = false := by
  decide +kernel

theorem kadmos_generated_python_position_binding_owned :
    validateStmtCertificate .python balancePySource ⟨2907, 2919⟩
      (.assign (.local "position") (.integer 0))
      (.localBinding ⟨2918, 2919⟩) = true := by
  decide +kernel

theorem kadmos_generated_python_position_binding_raw_statement_matches :
    (parsePythonBlock
      ((⟨2907, 2919⟩ : SourceSpan).text balancePySource) 0).toOption =
      some (.sequence (.assign (.local "position") (.integer 0)) .empty) := by
  decide +kernel

theorem kadmos_generated_python_position_binding_derives :
    StmtDerives .python .function balancePySource ⟨2907, 2919⟩
      (.assign (.local "position") (.integer 0)) :=
  validateStmtCertificate_sound kadmos_generated_python_position_binding_owned

theorem kadmos_generated_python_position_name_mutation_rejected :
    validateStmtCertificate .python balancePySource ⟨2907, 2919⟩
      (.assign (.local "index") (.integer 0))
      (.localBinding ⟨2918, 2919⟩) = false := by
  decide +kernel

theorem kadmos_generated_ts_index_postincrement_owned :
    validateStmtCertificate .ts balanceTsSource ⟨3658, 3666⟩
      (.doExpr (.postIncrement "index")) (.doExpr ⟨3658, 3665⟩) = true := by
  decide +kernel

theorem kadmos_generated_ts_index_postincrement_raw_statement_matches :
    (parseTSBlock ((⟨3658, 3666⟩ : SourceSpan).text balanceTsSource)).toOption =
      some (.sequence (.doExpr (.postIncrement "index")) .empty) := by
  decide +kernel

theorem kadmos_generated_ts_index_postincrement_derives :
    StmtDerives .ts .function balanceTsSource ⟨3658, 3666⟩
      (.doExpr (.postIncrement "index")) :=
  validateStmtCertificate_sound kadmos_generated_ts_index_postincrement_owned

theorem kadmos_generated_ts_index_postincrement_name_mutation_rejected :
    validateStmtCertificate .ts balanceTsSource ⟨3658, 3666⟩
      (.doExpr (.postIncrement "position"))
      (.doExpr ⟨3658, 3665⟩) = false := by
  decide +kernel

theorem kadmos_generated_python_position_augment_owned :
    validateStmtCertificate .python balancePySource ⟨3132, 3145⟩
      (.augment (.local "position") .add (.integer 1))
      (.augmentLocal ⟨3144, 3145⟩) = true := by
  decide +kernel

theorem kadmos_generated_python_position_augment_raw_statement_matches :
    (parsePythonBlock
      ((⟨3132, 3145⟩ : SourceSpan).text balancePySource) 0).toOption =
      some (.sequence (.augment (.local "position") .add (.integer 1))
        .empty) := by
  decide +kernel

theorem kadmos_generated_python_position_augment_derives :
    StmtDerives .python .function balancePySource ⟨3132, 3145⟩
      (.augment (.local "position") .add (.integer 1)) :=
  validateStmtCertificate_sound kadmos_generated_python_position_augment_owned

theorem kadmos_generated_python_position_augment_operator_mutation_rejected :
    validateStmtCertificate .python balancePySource ⟨3132, 3145⟩
      (.augment (.local "position") .sub (.integer 1))
      (.augmentLocal ⟨3144, 3145⟩) = false := by
  decide +kernel

#print axioms kadmos_generated_ts_seen_add_statement_certificate_sound
#print axioms kadmos_generated_python_seen_add_statement_certificate_sound
#print axioms kadmos_generated_ts_index_binding_derives
#print axioms kadmos_generated_python_position_binding_derives
#print axioms kadmos_generated_ts_index_postincrement_derives
#print axioms kadmos_generated_python_position_augment_derives

private def tsDepthLimit : TargetExpr :=
  .binary .gt (.local "depth") (.integer 128)

private def tsDepthError : TargetExpr :=
  .newExpr (.call (.local "Error")
    (.sequence (.string "SECURITY_VIOLATION: payload depth exceeded") .empty))

private def tsDepthRefusal : TargetStmt :=
  .ifThenElse tsDepthLimit (.throwValue tsDepthError) .empty

theorem kadmos_generated_ts_depth_if_raw_statement_matches :
    (parseTSBlock ((⟨5849, 5928⟩ : SourceSpan).text balanceTsSource)).toOption =
      some (.sequence tsDepthRefusal .empty) := by
  decide +kernel

theorem kadmos_generated_ts_depth_if_certificate_checked :
    validateStmtCertificate .ts balanceTsSource ⟨5849, 5928⟩
      tsDepthRefusal (.ifThen ⟨5853, 5864⟩ ⟨5866, 5928⟩
        (.throwExpr ⟨5872, 5927⟩)) = true := by
  decide +kernel

theorem kadmos_generated_ts_depth_if_derives :
    StmtDerives .ts .function balanceTsSource ⟨5849, 5928⟩
      tsDepthRefusal :=
  validateStmtCertificate_sound kadmos_generated_ts_depth_if_certificate_checked

theorem kadmos_generated_ts_depth_if_wrong_comparison_rejected :
    validateStmtCertificate .ts balanceTsSource ⟨5849, 5928⟩
      (.ifThenElse (.binary .ge (.local "depth") (.integer 128))
        (.throwValue tsDepthError) .empty)
      (.ifThen ⟨5853, 5864⟩ ⟨5866, 5928⟩
        (.throwExpr ⟨5872, 5927⟩)) = false := by
  decide +kernel

#print axioms kadmos_generated_ts_depth_if_derives

private def pythonDepthError : TargetExpr :=
  .call (.local "ValueError")
    (.sequence (.string "SECURITY_VIOLATION: payload depth exceeded") .empty)

private def pythonDepthRefusal : TargetStmt :=
  .ifThenElse tsDepthLimit
    (.sequence (.throwValue pythonDepthError) .empty) .empty

theorem kadmos_generated_python_depth_if_raw_statement_matches :
    (parsePythonLines (pythonLines
      ("        " ++ (⟨6486, 6576⟩ : SourceSpan).text balancePySource))
      8).toOption = some (.sequence pythonDepthRefusal .empty) := by
  decide +kernel

theorem kadmos_generated_python_depth_if_certificate_checked :
    validateStmtCertificate .python balancePySource ⟨6486, 6576⟩
      pythonDepthRefusal
      (.ifThenIndented ⟨6489, 6500⟩ ⟨6514, 6576⟩ "            "
        (.final ⟨6514, 6576⟩ (.throwExpr ⟨6520, 6576⟩))) = true := by
  decide +kernel

theorem kadmos_generated_python_depth_if_derives :
    StmtDerives .python .function balancePySource ⟨6486, 6576⟩
      pythonDepthRefusal :=
  validateStmtCertificate_sound
    kadmos_generated_python_depth_if_certificate_checked

theorem kadmos_generated_python_depth_if_indent_mutation_rejected :
    validateStmtCertificate .python balancePySource ⟨6486, 6576⟩
      pythonDepthRefusal
      (.ifThenIndented ⟨6489, 6500⟩ ⟨6514, 6576⟩ "        "
        (.final ⟨6514, 6576⟩ (.throwExpr ⟨6520, 6576⟩))) = false := by
  decide +kernel

#print axioms kadmos_generated_python_depth_if_derives

theorem kadmos_generated_python_certificate_owns_absolute_indent :
    validateStmtCertificate .python
      "def f(x: Any) -> bool:\n    if True:\n    return True" ⟨27,51⟩
      (.ifThenElse (.bool true) (.sequence (.returnValue (.bool true)) .empty) .empty)
      (.ifThenIndented ⟨30,34⟩ ⟨40,51⟩ "    "
        (.final ⟨40,51⟩ (.returnExpr ⟨47,51⟩))) = false := by decide +kernel

-- Constructor/reset publication assignments must derive their actual lvalues.
theorem kadmos_generated_ts_busy_assignment_owned :
    validateStmtCertificate .ts balanceTsSource ⟨9987,10005⟩
      (.assign (.property (.local "this") "#busy") (.bool true))
      (.assignment ⟨9987,9997⟩ ⟨10000,10004⟩) = true := by
  decide +kernel

theorem kadmos_generated_python_busy_assignment_owned :
    validateStmtCertificate .python balancePySource ⟨10824,10841⟩
      (.assign (.property (.local "self") "_busy") (.bool true))
      (.assignment ⟨10824,10834⟩ ⟨10837,10841⟩) = true := by
  decide +kernel

theorem kadmos_generated_ts_context_assignment_owned :
    validateStmtCertificate .ts balanceTsSource ⟨12062,12088⟩
      (.assign (.property (.local "this") "#context") (.local "candidate"))
      (.assignment ⟨12062,12075⟩ ⟨12078,12087⟩) = true := by
  decide +kernel

theorem kadmos_generated_python_context_assignment_owned :
    validateStmtCertificate .python balancePySource ⟨12359,12385⟩
      (.assign (.property (.local "self") "__context") (.local "candidate"))
      (.assignment ⟨12359,12373⟩ ⟨12376,12385⟩) = true := by
  decide +kernel

theorem kadmos_generated_ts_assignment_wrong_private_field_rejected :
    validateStmtCertificate .ts balanceTsSource ⟨9987,10005⟩
      (.assign (.property (.local "this") "busy") (.bool true))
      (.assignment ⟨9987,9997⟩ ⟨10000,10004⟩) = false := by
  decide +kernel

theorem kadmos_generated_python_assignment_wrong_receiver_rejected :
    validateStmtCertificate .python balancePySource ⟨10824,10841⟩
      (.assign (.property (.local "other") "_busy") (.bool true))
      (.assignment ⟨10824,10834⟩ ⟨10837,10841⟩) = false := by
  decide +kernel

theorem kadmos_generated_assignment_child_span_alias_rejected :
    validateStmtCertificate .ts balanceTsSource ⟨9987,10005⟩
      (.assign (.property (.local "this") "#busy") (.bool true))
      (.assignment ⟨9987,9997⟩ ⟨9987,9997⟩) = false := by
  decide +kernel

theorem kadmos_generated_ts_busy_assignment_derives :
    StmtDerives .ts .function balanceTsSource ⟨9987,10005⟩
      (.assign (.property (.local "this") "#busy") (.bool true)) :=
  validateStmtCertificate_sound kadmos_generated_ts_busy_assignment_owned

#print axioms kadmos_generated_ts_busy_assignment_derives

theorem kadmos_generated_python_busy_assignment_derives :
    StmtDerives .python .function balancePySource ⟨10824,10841⟩
      (.assign (.property (.local "self") "_busy") (.bool true)) :=
  validateStmtCertificate_sound kadmos_generated_python_busy_assignment_owned

#print axioms kadmos_generated_python_busy_assignment_derives

theorem kadmos_generated_ts_context_assignment_derives :
    StmtDerives .ts .function balanceTsSource ⟨12062,12088⟩
      (.assign (.property (.local "this") "#context") (.local "candidate")) :=
  validateStmtCertificate_sound kadmos_generated_ts_context_assignment_owned

#print axioms kadmos_generated_ts_context_assignment_derives

theorem kadmos_generated_python_context_assignment_derives :
    StmtDerives .python .function balancePySource ⟨12359,12385⟩
      (.assign (.property (.local "self") "__context") (.local "candidate")) :=
  validateStmtCertificate_sound kadmos_generated_python_context_assignment_owned

#print axioms kadmos_generated_python_context_assignment_derives

theorem kadmos_generated_ts_busy_assignment_raw_matches :
    (parseTSBlock ((⟨9987,10005⟩ : SourceSpan).text balanceTsSource)).toOption =
      some (.sequence (.assign (.property (.local "this") "#busy") (.bool true)) .empty) := by
  decide +kernel

theorem kadmos_generated_python_context_assignment_raw_matches :
    (parsePythonBlock ((⟨12359,12385⟩ : SourceSpan).text balancePySource) 0).toOption =
      some (.sequence (.assign (.property (.local "self") "__context")
        (.local "candidate")) .empty) := by
  decide +kernel

-- Optional receiver chains are reads, never TS writable assignment targets.
theorem kadmos_generated_ts_optional_property_assignment_rejected :
    validateAssignmentTarget .ts "a?.b.c"
      (.property (.optionalProperty (.local "a") "b") "c") = false := by
  decide +kernel

theorem kadmos_generated_ts_optional_index_assignment_rejected :
    validateAssignmentTarget .ts "a?.b[0]"
      (.index (.optionalProperty (.local "a") "b") (.integer 0)) = false := by
  decide +kernel

theorem kadmos_generated_ts_optional_call_assignment_rejected :
    validateAssignmentTarget .ts "a?.b().c"
      (.property (.call (.optionalProperty (.local "a") "b") .empty) "c") = false := by
  decide +kernel

theorem kadmos_generated_ts_optional_assignment_certificate_rejected :
    validateStmtCertificate .ts "a?.b.c = true;" ⟨0,14⟩
      (.assign (.property (.optionalProperty (.local "a") "b") "c") (.bool true))
      (.assignment ⟨0,6⟩ ⟨9,13⟩) = false := by
  decide +kernel

theorem kadmos_generated_ts_optional_chain_read_retained :
    validateFunctionExpr .ts "a?.b.c"
      (.property (.optionalProperty (.local "a") "b") "c") = true := by
  decide +kernel

theorem kadmos_generated_ts_optional_index_key_assignment_retained :
    validateAssignmentTarget .ts "a[b?.c]"
      (.index (.local "a") (.optionalProperty (.local "b") "c")) = true := by
  decide +kernel

theorem kadmos_generated_ts_optional_call_argument_assignment_retained :
    validateAssignmentTarget .ts "f(a?.b).c"
      (.property (.call (.local "f")
        (.sequence (.optionalProperty (.local "a") "b") .empty)) "c") = true := by
  decide +kernel

theorem kadmos_generated_ts_optional_assignment_not_grammatical :
    ¬ AssignmentTargetSyntax .ts "a?.b.c"
      (.property (.optionalProperty (.local "a") "b") "c") := by
  intro h
  cases h with
  | property _ hWritable => exact hWritable rfl

#print axioms kadmos_generated_ts_optional_assignment_not_grammatical
#print axioms writableReceiverChainCheck_sound
