import Harmonia.Applications.Kadmos.Generated.BalanceSimulation

open Harmonia.Applications.Kadmos.Generated

-- Constructor/module bindings need physical cell allocation and lexical writes.
theorem kadmos_generated_let_local_depth {program m f name mutable n} :
    DepthDerivesStmt program m f (.letLocal name mutable (.integer n))
      ⟨(allocCell m (integerValue program.lang n) mutable).1,
        { f with locals := (name, m.nextCell) :: f.locals }, .normal⟩ 1 :=
  .letLocal (.integer n)

theorem kadmos_generated_assign_existing_depth {program m f name n ref final}
    (ha : (f.locals.lookup name).orElse (fun _ =>
      (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) = some ref)
    (hw : writeCell m ref (integerValue program.lang n) = .ok final) :
    DepthDerivesStmt program m f (.assign (.local name) (.integer n))
      ⟨final, f, .normal⟩ 1 :=
  .assignLocal (.integer n) ha hw

theorem kadmos_generated_assign_python_fresh_depth {program m f name n}
    (hl : program.lang = .python)
    (ha : (f.locals.lookup name).orElse (fun _ =>
      (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) = none) :
    DepthDerivesStmt program m f (.assign (.local name) (.integer n))
      ⟨(allocCell m (integerValue program.lang n) true).1,
        { f with locals := (name, m.nextCell) :: f.locals }, .normal⟩ 1 :=
  .assignPythonLocal hl (.integer n) ha

theorem kadmos_generated_expression_statement_depth {program m f n} :
    DepthDerivesStmt program m f (.doExpr (.integer n)) ⟨m, f, .normal⟩ 1 :=
  .doExpr (.integer n)

theorem kadmos_generated_lexical_sound {program m f name n out k}
    (he : execStmt k program m f (.assign (.local name) (.integer n)) = .ok out) :
    ∃ rank, DepthDerivesStmt program m f (.assign (.local name) (.integer n)) out rank ∧
      rank < k :=
  execLexical_sound (.assignLocal (.integer n)) he

theorem kadmos_generated_nonlocal_depth {program m f name}
    (hc : (f.captures.lookup name).isSome = true) :
    DepthDerivesStmt program m f (.nonlocalNames [name]) ⟨m, f, .normal⟩ 0 :=
  .nonlocalNames (by simpa using hc)

#print axioms execLexical_sound

theorem kadmos_generated_let_local_adequate {program m f name mutable n} :
    execStmt 2 program m f (.letLocal name mutable (.integer n)) =
      .ok ⟨(allocCell m (integerValue program.lang n) mutable).1,
        { f with locals := (name, m.nextCell) :: f.locals }, .normal⟩ :=
  execStmt_adequate kadmos_generated_let_local_depth (by decide)

theorem kadmos_generated_let_local_runs {program m f name mutable n} :
    StmtRuns program m f (.letLocal name mutable (.integer n))
      ⟨(allocCell m (integerValue program.lang n) mutable).1,
        { f with locals := (name, m.nextCell) :: f.locals }, .normal⟩ :=
  stmt_path_runs kadmos_generated_let_local_depth

theorem kadmos_generated_assign_existing_adequate {program m f name n ref final}
    (ha : (f.locals.lookup name).orElse (fun _ =>
      (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) = some ref)
    (hw : writeCell m ref (integerValue program.lang n) = .ok final) :
    execStmt 2 program m f (.assign (.local name) (.integer n)) = .ok ⟨final, f, .normal⟩ :=
  execStmt_adequate (kadmos_generated_assign_existing_depth ha hw) (by decide)

theorem kadmos_generated_assign_python_fresh_runs {program m f name n}
    (hl : program.lang = .python)
    (ha : (f.locals.lookup name).orElse (fun _ =>
      (f.captures.lookup name).orElse (fun _ => m.globals.lookup name)) = none) :
    StmtRuns program m f (.assign (.local name) (.integer n))
      ⟨(allocCell m (integerValue program.lang n) true).1,
        { f with locals := (name, m.nextCell) :: f.locals }, .normal⟩ :=
  stmt_path_runs (kadmos_generated_assign_python_fresh_depth hl ha)

theorem kadmos_generated_nonlocal_adequate {program m f name}
    (hc : (f.captures.lookup name).isSome = true) :
    execStmt 1 program m f (.nonlocalNames [name]) = .ok ⟨m, f, .normal⟩ :=
  execStmt_adequate (kadmos_generated_nonlocal_depth hc) (by decide)

theorem kadmos_generated_let_local_insufficient_depth {program m f name mutable n} :
    execStmt 1 program m f (.letLocal name mutable (.integer n)) = .error .exhaustedFuel := by
  simp [execStmt, evalExpr, Bind.bind, Pure.pure, Except.bind, Except.pure]

-- A declaration shadows the captured cursor by allocating a fresh cell;
-- assigning the captured cursor instead keeps the original address.
private def cursorFrame : TargetFrame := ⟨"parse", [], [], [("position", 0)], none, .normal⟩
private def cursorMachine (lang : TargetLang) : TargetMachine :=
  (allocCell TargetMachine.empty (integerValue lang 0) true).1

theorem kadmos_generated_cursor_write {program n} :
    ∃ out, execStmt 2 program (cursorMachine program.lang) cursorFrame
      (.assign (.local "position") (.integer n)) = .ok out ∧
      readCell out.machine 0 = .ok (integerValue program.lang n) ∧
      out.frame = cursorFrame ∧ out.machine.nextCell = 1 := by
  have hv := evalExpr_adequate (DepthDerivesExpr.integer
    (program := program) (m := cursorMachine program.lang) (f := cursorFrame) n)
    (by decide : 0 < 1)
  simp only [execStmt, hv, Bind.bind, Pure.pure, Except.bind, Except.pure]
  simp [cursorMachine, cursorFrame, allocCell, writeCell, readCell, List.lookup,
    integerValue, TargetMachine.empty, Option.orElse, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem kadmos_generated_cursor_shadow {program n} :
    ∃ out, execStmt 2 program (cursorMachine program.lang) cursorFrame
      (.letLocal "position" true (.integer n)) = .ok out ∧
      out.frame.locals.lookup "position" = some 1 ∧
      out.frame.captures.lookup "position" = some 0 ∧
      readCell out.machine 0 = .ok (integerValue program.lang 0) ∧
      readCell out.machine 1 = .ok (integerValue program.lang n) := by
  rw [kadmos_generated_let_local_adequate]
  simp [cursorMachine, cursorFrame, allocCell, readCell, List.lookup,
    integerValue, TargetMachine.empty, Option.orElse, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem kadmos_generated_ts_unknown_assignment {program n}
    (hl : program.lang = .ts) :
    execStmt 2 program TargetMachine.empty cursorFrame
      (.assign (.local "missing") (.integer n)) = .error (.unboundLocal "missing") := by
  have hv := evalExpr_adequate (DepthDerivesExpr.integer
    (program := program) (m := TargetMachine.empty) (f := cursorFrame) n)
    (by decide : 0 < 1)
  simp only [execStmt, hv, Bind.bind, Pure.pure, Except.bind, Except.pure]
  simp [hl, cursorFrame, TargetMachine.empty, List.lookup, Option.orElse,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem kadmos_generated_immutable_assignment {program n} :
    execStmt 2 program (allocCell TargetMachine.empty .null false).1 cursorFrame
      (.assign (.local "position") (.integer n)) = .error (.immutableCell 0) := by
  have hv := evalExpr_adequate (DepthDerivesExpr.integer
    (program := program) (m := (allocCell TargetMachine.empty .null false).1)
    (f := cursorFrame) n) (by decide : 0 < 1)
  simp only [execStmt, hv, Bind.bind, Pure.pure, Except.bind, Except.pure]
  simp [cursorFrame, allocCell, writeCell, TargetMachine.empty, List.lookup, Option.orElse,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem kadmos_generated_nonlocal_missing {program} :
    execStmt 1 program TargetMachine.empty cursorFrame (.nonlocalNames ["missing"]) =
      .error (.unboundLocal "missing") := by
  simp [execStmt, cursorFrame, Bind.bind, Pure.pure, Except.bind, Except.pure]

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

theorem kadmos_generated_lexical_raised_paths {program m f name mutable} :
    DepthDerivesStmt program m f (.letLocal name mutable badSub)
      ⟨m, f, .raised numericError⟩ 2 ∧
    DepthDerivesStmt program m f (.assign (.local name) badSub)
      ⟨m, f, .raised numericError⟩ 2 ∧
    DepthDerivesStmt program m f (.doExpr badSub)
      ⟨m, f, .raised numericError⟩ 2 := by
  have he : DepthDerivesExpr program m f badSub ⟨m, .error numericError⟩ 1 :=
    .binary (by decide) (.string "x") (.bool false) rfl
  exact ⟨.letLocalRaised he, .assignLocalRaised he, .doExprRaised he⟩

theorem kadmos_generated_lexical_raised_adequate {program m f name mutable} :
    execStmt 3 program m f (.letLocal name mutable badSub) = .ok ⟨m, f, .raised numericError⟩ ∧
    execStmt 3 program m f (.assign (.local name) badSub) = .ok ⟨m, f, .raised numericError⟩ ∧
    execStmt 3 program m f (.doExpr badSub) = .ok ⟨m, f, .raised numericError⟩ := by
  obtain ⟨hl, ha, hd⟩ := kadmos_generated_lexical_raised_paths (program := program)
    (m := m) (f := f) (name := name) (mutable := mutable)
  exact ⟨execStmt_adequate hl (by decide), execStmt_adequate ha (by decide),
    execStmt_adequate hd (by decide)⟩

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

-- Mutating statement paths preserve returned control through busy clearing.
theorem kadmos_generated_finally_return_depth {program m f} :
    DepthDerivesStmt program m f
      (.tryCatchFinally (.returnValue (.bool true)) none none .empty
        (.assign (.field "busy") (.bool false)))
      ⟨{ m with checker := { m.checker with busy := false } }, f,
        .returned (.bool true)⟩ 2 := by
  exact .finallyNormal (.returnValue (.bool true)) (by rfl)
    (.assignField (.bool false) (by simp [writeCheckerField]))

theorem kadmos_generated_finally_return_adequate {program m f} :
    execStmt 3 program m f
      (.tryCatchFinally (.returnValue (.bool true)) none none .empty
        (.assign (.field "busy") (.bool false))) =
      .ok ⟨{ m with checker := { m.checker with busy := false } }, f,
        .returned (.bool true)⟩ :=
  execStmt_adequate kadmos_generated_finally_return_depth (by decide)

theorem kadmos_generated_finally_return_runs {program m f} :
    StmtRuns program m f
      (.tryCatchFinally (.returnValue (.bool true)) none none .empty
        (.assign (.field "busy") (.bool false)))
      ⟨{ m with checker := { m.checker with busy := false } }, f,
        .returned (.bool true)⟩ := stmt_path_runs kadmos_generated_finally_return_depth

theorem kadmos_generated_finally_override_depth {program m f} :
    DepthDerivesStmt program m f
      (.tryCatchFinally (.returnValue (.bool true)) none none .empty .returnVoid)
      ⟨m, f, .returned .undefined⟩ 2 :=
  .finallyOverride (.returnValue (.bool true)) (by rfl) .returnVoid (by intro h; cases h)

theorem kadmos_generated_sequence_exit_skips_tail {program m f} :
    DepthDerivesStmt program m f
      (.sequence .returnVoid (.assign (.field "state") (.bool false)))
      ⟨m, f, .returned .undefined⟩ 1 :=
  .sequenceExit .returnVoid (by intro h; cases h)

#print axioms execStmt_adequate
#print axioms stmt_path_runs
#print axioms BalanceRep.view
#print axioms balanceRepCheck_sound

-- Caught return and rethrow retain the outcome control after frame clearing.
theorem kadmos_generated_caught_return_depth {program m f} :
    DepthDerivesStmt program m f
      (.tryCatchFinally (.throwValue (.string "boom")) (some "any") (some "e")
        (.returnValue (.bool true)) (.assign (.field "busy") (.bool false)))
      ⟨{ (bindCatchFrame m f (some "e") (.string "boom")).1 with
          checker := { m.checker with busy := false } },
        { (bindCatchFrame m f (some "e") (.string "boom")).2 with control := .normal },
        .returned (.bool true)⟩ 2 := by
  exact .caughtFinallyNormal (.throwValue (.string "boom")) (by rfl)
    (.returnValue (.bool true)) (.assignField (.bool false) (by simp [writeCheckerField, bindCatchFrame, allocCell]))

theorem kadmos_generated_caught_return_adequate {program m f} :
    execStmt 3 program m f
      (.tryCatchFinally (.throwValue (.string "boom")) (some "any") (some "e")
        (.returnValue (.bool true)) (.assign (.field "busy") (.bool false))) =
      .ok ⟨{ (bindCatchFrame m f (some "e") (.string "boom")).1 with
          checker := { m.checker with busy := false } },
        { (bindCatchFrame m f (some "e") (.string "boom")).2 with control := .normal },
        .returned (.bool true)⟩ :=
  execStmt_adequate kadmos_generated_caught_return_depth (by decide)

theorem kadmos_generated_caught_rethrow_depth {program m f} :
    DepthDerivesStmt program m f
      (.tryCatchFinally (.throwValue (.string "boom")) (some "Exception") none
        .rethrow (.assign (.field "_busy") (.bool false)))
      ⟨{ m with checker := { m.checker with busy := false } },
        { f with control := .normal }, .raised (.string "boom")⟩ 2 := by
  exact .caughtFinallyNormal (.throwValue (.string "boom")) (by rfl)
    (.rethrow (by rfl)) (.assignField (.bool false) (by simp [writeCheckerField, bindCatchFrame]))

theorem kadmos_generated_caught_override_depth {program m f} :
    DepthDerivesStmt program m f
      (.tryCatchFinally (.throwValue (.string "boom")) (some "any") none
        .returnVoid (.throwValue (.string "cleanup")))
      ⟨m, { f with control := .normal }, .raised (.string "cleanup")⟩ 2 := by
  exact .caughtFinallyOverride (.throwValue (.string "boom")) (by rfl)
    .returnVoid (.throwValue (.string "cleanup")) (by intro h; cases h)

theorem kadmos_generated_catch_binder_fresh {m f errorValue} :
    (bindCatchFrame m f (some "e") errorValue).1.nextCell = m.nextCell + 1 ∧
    (bindCatchFrame m f (some "e") errorValue).2.locals = ("e", m.nextCell) :: f.locals ∧
    readCell (bindCatchFrame m f (some "e") errorValue).1 m.nextCell = .ok errorValue := by
  simp [bindCatchFrame, allocCell, readCell]

private def equalityTree : Nat → TargetExpr
  | 0 => .bool true
  | n + 1 => .binary .strictEq (equalityTree n) (equalityTree n)

private def equalityTreeTrace : Nat → Nat
  | 0 => 1
  | n + 1 => 3 + 2 * equalityTreeTrace n

private theorem equalityTree_depth {program m f} (n : Nat) :
    DepthDerivesExpr program m f (equalityTree n) ⟨m, .ok (.bool true)⟩ n := by
  induction n with
  | zero => exact .bool true
  | succ n ih =>
      simpa [equalityTree, Nat.add_comm] using DepthDerivesExpr.binary (op := .strictEq) (result := .ok (.bool true)) (by decide) ih ih (by rfl)

private theorem equalityTree_counted {program m f} (n : Nat)
    (c : List ResumeFrame) :
    CountedRuns program ⟨m, f, .eval (equalityTree n), c⟩
      ⟨m, f, .value (.bool true), c⟩ (equalityTreeTrace n) := by
  induction n generalizing c with
  | zero => exact .single (.bool true)
  | succ n ih =>
      have count : (((1 + equalityTreeTrace n) + 1) + equalityTreeTrace n) + 1 =
          equalityTreeTrace (n + 1) := by simp only [equalityTreeTrace]; omega
      rw [← count]
      exact ((((CountedRuns.single .binaryEnter).trans (ih _)).trans
        (.single .binaryNext)).trans (ih _)).trans
          (.single (SmallStep.binaryFinish (program := program) (m := m)
            (op := .strictEq) (left := .bool true) (right := .bool true)
            (result := .ok (.bool true)) (by decide) (by rfl)))

-- 253 relation steps, rank 6, executor depth 7: neither meter is fuel=253.
theorem kadmos_generated_trace_exceeds_depth_budget {program m f} :
    CountedRuns program ⟨m, f, .eval (equalityTree 6), []⟩
        ⟨m, f, .value (.bool true), []⟩ 253 ∧
      evalExpr 7 program m f (equalityTree 6) = .ok ⟨m, .ok (.bool true)⟩ := by
  exact ⟨equalityTree_counted 6 [], evalExpr_adequate (equalityTree_depth 6) (by decide)⟩

-- Local/captured-cell reads must be semantic leaves, not assumed helper calls.
theorem kadmos_generated_local_depth {program m f name value}
    (h : localValue m f name = .ok value) :
    DepthDerivesExpr program m f (.local name) ⟨m, .ok value⟩ 0 :=
  .localRead h

theorem kadmos_generated_guard_short_circuit {program m f} :
    DepthDerivesStmt program m f
      (.ifThenElse (.bool false) (.throwValue (.string "unreachable")) .returnVoid)
      ⟨m, f, .returned .undefined⟩ 1 :=
  .ifFalse (.bool false) rfl .returnVoid

theorem kadmos_generated_guard_short_circuit_adequate {program m f} :
    execStmt 2 program m f
      (.ifThenElse (.bool false) (.throwValue (.string "unreachable")) .returnVoid) =
      .ok ⟨m, f, .returned .undefined⟩ :=
  execStmt_adequate kadmos_generated_guard_short_circuit (by decide)

-- The discarded arm can lack an evaluator derivation entirely.
theorem kadmos_generated_if_true_unreachable {program m f} :
    DepthDerivesStmt program m f
      (.ifThenElse (.bool true) .returnVoid (.whileDo (.bool true) .empty))
      ⟨m, f, .returned .undefined⟩ 1 :=
  .ifTrue (.bool true) rfl .returnVoid

theorem kadmos_generated_if_condition_raises {program m f} :
    DepthDerivesStmt program m f
      (.ifThenElse badSub (.whileDo (.bool true) .empty) (.whileDo (.bool true) .empty))
      ⟨m, f, .raised numericError⟩ 2 :=
  .ifRaised (.binary (by decide) (.string "x") (.bool false) rfl)

theorem kadmos_generated_if_runs {program m f} :
    StmtRuns program m f
      (.ifThenElse (.bool false) (.throwValue (.string "unreachable")) .returnVoid)
      ⟨m, f, .returned .undefined⟩ :=
  stmt_path_runs kadmos_generated_guard_short_circuit

theorem kadmos_generated_local_read_sound {program m f name out k}
    (h : evalExpr k program m f (.local name) = .ok out) :
    ∃ rank, DepthDerivesExpr program m f (.local name) out rank ∧ rank < k :=
  evalScalar_sound (.localRead name) h

-- Captured locals read the current shared cell, and local shadowing wins.
theorem kadmos_generated_capture_reads_current_cell :
    localValue { TargetMachine.empty with cells := [(0, .number .pyInt 7)] }
      ⟨"nested", [], [], [("position", 0)], none, .normal⟩ "position" =
      .ok (.number .pyInt 7) := by decide +kernel

theorem kadmos_generated_local_shadows_capture :
    localValue { TargetMachine.empty with
      cells := [(0, .number .pyInt 1), (1, .number .pyInt 7)] }
      ⟨"nested", [], [("position", 0)], [("position", 1)], none, .normal⟩ "position" =
      .ok (.number .pyInt 1) := by decide +kernel

theorem kadmos_generated_dangling_local_does_not_fallback :
    localValue { TargetMachine.empty with cells := [(1, .number .pyInt 7)] }
      ⟨"nested", [], [("position", 0)], [("position", 1)], none, .normal⟩ "position" =
      .error (.danglingCell 0) := by decide +kernel

-- Different derivation ranks must not select different executable outcomes.
theorem kadmos_generated_expr_paths_deterministic {program m f expr out₁ out₂ r₁ r₂}
    (h₁ : DepthDerivesExpr program m f expr out₁ r₁)
    (h₂ : DepthDerivesExpr program m f expr out₂ r₂) : out₁ = out₂ :=
  h₁.deterministic h₂

theorem kadmos_generated_stmt_paths_deterministic {program m f stmt out₁ out₂ r₁ r₂}
    (h₁ : DepthDerivesStmt program m f stmt out₁ r₁)
    (h₂ : DepthDerivesStmt program m f stmt out₂ r₂) : out₁ = out₂ :=
  h₁.deterministic h₂
