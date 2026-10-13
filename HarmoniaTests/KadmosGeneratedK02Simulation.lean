import Harmonia.Applications.Kadmos.Generated.BalanceSimulation

open Harmonia.Applications.Kadmos.Generated

-- A binary tree has depth rank one even though its trace has five steps.
theorem kadmos_generated_simulation_binary_depth {program machine frame} :
    DepthDerivesExpr program machine frame
      (.binary .strictEq (.bool true) (.bool false))
      ⟨machine, .ok (.bool false)⟩ 1 := by
  exact .binary (by decide) (.bool true) (.bool false) (by rfl)

theorem kadmos_generated_simulation_binary_adequate {program machine frame} :
    evalExpr 2 program machine frame
      (.binary .strictEq (.bool true) (.bool false)) =
      .ok ⟨machine, .ok (.bool false)⟩ :=
  evalExpr_adequate kadmos_generated_simulation_binary_depth (by decide)

theorem kadmos_generated_simulation_binary_runs {program machine frame} :
    ExprRuns program machine frame
      (.binary .strictEq (.bool true) (.bool false))
      ⟨machine, .ok (.bool false)⟩ :=
  expr_path_runs kadmos_generated_simulation_binary_depth

theorem kadmos_generated_heap_empty (lang : TargetLang) :
    HeapWF lang TargetMachine.empty := by cases lang <;> decide +kernel

theorem kadmos_generated_heap_hosts (lang : TargetLang) :
    HeapWF lang (initialHostMachine lang) := by cases lang <;> decide +kernel

theorem kadmos_generated_heap_bad_fresh_counter :
    ¬ HeapWF .ts { TargetMachine.empty with nextObject := 1 } := by decide +kernel

theorem kadmos_generated_heap_dangling_context :
    ¬ HeapWF .ts { TargetMachine.empty with
      checker := { TargetMachine.empty.checker with context := 2 } } := by decide +kernel

theorem kadmos_generated_heap_duplicate_address :
    ¬ HeapWF .ts { TargetMachine.empty with
      objects := TargetMachine.empty.objects ++ TargetMachine.empty.objects } := by decide +kernel

theorem kadmos_generated_simulation_insufficient_depth {program machine frame} :
    evalExpr 1 program machine frame
      (.binary .strictEq (.bool true) (.bool false)) = .error .exhaustedFuel := by
  simp [evalExpr, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem kadmos_generated_simulation_sound {program machine frame} :
    ∃ rank, DepthDerivesExpr program machine frame
      (.binary .strictEq (.bool true) (.bool false))
      ⟨machine, .ok (.bool false)⟩ rank ∧ rank < 2 :=
  evalScalar_sound (.binary (by decide) (.bool true) (.bool false))
    kadmos_generated_simulation_binary_adequate

private def numericError : TargetValue := .exception "TypeError" "expected numeric operands"
private def badSub : TargetExpr := .binary .sub (.string "x") (.bool false)

theorem kadmos_generated_simulation_raised_left {program machine frame} :
    DepthDerivesExpr program machine frame
      (.binary .strictEq badSub (.bool true)) ⟨machine, .error numericError⟩ 2 :=
  .binaryLeftRaised (.binary (by decide) (.string "x") (.bool false) (by rfl))

theorem kadmos_generated_simulation_raised_right {program machine frame} :
    DepthDerivesExpr program machine frame
      (.binary .strictEq (.bool true) badSub) ⟨machine, .error numericError⟩ 2 :=
  .binaryRightRaised (.bool true)
    (.binary (by decide) (.string "x") (.bool false) (by rfl))

theorem kadmos_generated_simulation_left_error_adequate {program machine frame} :
    evalExpr 3 program machine frame (.binary .strictEq badSub (.bool true)) =
      .ok ⟨machine, .error numericError⟩ :=
  evalExpr_adequate kadmos_generated_simulation_raised_left (by decide)

theorem kadmos_generated_simulation_right_error_runs {program machine frame} :
    ExprRuns program machine frame (.binary .strictEq (.bool true) badSub)
      ⟨machine, .error numericError⟩ :=
  expr_path_runs kadmos_generated_simulation_raised_right

#print axioms evalExpr_adequate
#print axioms evalScalar_sound
#print axioms expr_path_runs

private def missingGeneratorState : TargetMachine :=
  let (m, _) := allocObject TargetMachine.empty
    ⟨.pythonGenerator, none, [], [], [], false, false⟩
  m

theorem kadmos_generated_heap_generator_requires_state :
    ¬ HeapWF .python missingGeneratorState := by decide +kernel

-- The converse direction rejects a state table referring to a non-generator.
private def staleGeneratorState : TargetMachine :=
  { TargetMachine.empty with generators := [(1,
    ⟨.bool true, [], .empty, [], ⟨"generator", [], [], [], none, .normal⟩⟩)] }

theorem kadmos_generated_heap_generator_requires_object :
    ¬ HeapWF .python staleGeneratorState := by decide +kernel
