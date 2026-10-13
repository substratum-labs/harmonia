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

-- Property evaluation owns a receiver edge, including receiver-bound methods.
theorem kadmos_generated_property_depth {program m f name key receiver out}
    (hl : localValue m f name = .ok receiver)
    (hp : readPropertyValue program.lang m receiver key = .ok out) :
    DepthDerivesExpr program m f (.property (.local name) key) out 1 :=
  .property (.localRead hl) hp

theorem kadmos_generated_property_adequate {program m f name key receiver out}
    (hl : localValue m f name = .ok receiver)
    (hp : readPropertyValue program.lang m receiver key = .ok out) :
    evalExpr 2 program m f (.property (.local name) key) = .ok out :=
  evalExpr_adequate (kadmos_generated_property_depth hl hp) (by decide)

-- One-field dict/object syntax has two executor edges before its value.
theorem kadmos_generated_object_one_depth {program m f key n final}
    (hw : writeOwn (allocObject m (literalObject program.lang m)).1 m.nextObject
      key (integerValue program.lang n) = .ok final) :
    DepthDerivesExpr program m f (.object (.objectEntry key (.integer n) .empty))
      ⟨final, .ok (.object m.nextObject)⟩ 2 := .objectOne (.integer n) hw

-- Empty and cons argument spines are separate fuel-matching entries.
theorem kadmos_generated_args_empty_depth {program m f} :
    DepthDerivesArgs program m f .empty ⟨m, .ok []⟩ 0 := .empty

theorem kadmos_generated_args_one_depth {program m f n} :
    DepthDerivesArgs program m f (.sequence (.integer n) .empty)
      ⟨m, .ok [integerValue program.lang n]⟩ 1 := .cons (.integer n) .empty

-- A user closure call executes its stored low-level return body.
theorem kadmos_generated_call_empty_depth {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    DepthDerivesExpr program m f (.call expr .empty) ⟨m, .ok (.bool true)⟩ 2 := by
  have hparams : DepthBindsProvided program m (closureFrame closure) closure.params
      closure.pythonDefaults [] m (closureFrame closure) 0 := by
    rw [hp]; exact .empty
  have hbody : DepthDerivesStmt program m (closureFrame closure) closure.body
      ⟨m, closureFrame closure, .returned (.bool true)⟩ 1 := by
    rw [hb]; exact .returnValue (.bool true)
  exact .callClosure he .empty hc hparams hbody rfl

theorem kadmos_generated_fields_two_depth {program m f ref x y middle final}
    (hx : writeOwn m ref "x" (integerValue program.lang x) = .ok middle)
    (hy : writeOwn middle ref "y" (integerValue program.lang y) = .ok final) :
    DepthDerivesFields program m f ref
      (.objectEntry "x" (.integer x) (.objectEntry "y" (.integer y) .empty))
      ⟨final, .ok (.object ref)⟩ 2 :=
  .entry (.integer x) hx (.entry (.integer y) hy .empty)

theorem kadmos_generated_builtin_call_depth {program m f expr}
    (hl : program.lang = .ts)
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.builtin .jsIsSafeInteger)⟩ 0) :
    DepthDerivesExpr program m f (.call expr (.sequence (.integer 0) .empty))
      ⟨m, .ok (.bool true)⟩ 2 := by
  apply DepthDerivesExpr.callBuiltin he (.cons (.integer 0) .empty)
    ⟨by decide, by decide, by decide⟩
  rw [hl]
  rfl

-- Reading a method really allocates a new closure bound to this checker.
theorem kadmos_generated_method_property {lang m key ref closure error}
    (hf : readCheckerField m key = .error error)
    (hm : m.classMethods.lookup key = some ref)
    (hc : closureAt m ref = .ok closure) :
    readPropertyValue lang m (.object m.checkerRef) key =
      .ok ⟨(allocClosure m { closure with receiver := some m.checkerRef }).1,
        .ok (.closure m.nextClosure)⟩ := by
  simp [readPropertyValue, hf, hm, hc, allocClosure,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  rfl

theorem kadmos_generated_this_property_depth {program m f key out}
    (hf : f.receiver = some m.checkerRef)
    (hp : readPropertyValue program.lang m (.object m.checkerRef) key = .ok out) :
    DepthDerivesExpr program m f (.property (.local "this") key) out 1 :=
  .property (.localRead (by simp [localValue, hf])) hp

theorem kadmos_generated_self_property_depth {program m f key out}
    (hf : f.receiver = some m.checkerRef)
    (hp : readPropertyValue program.lang m (.object m.checkerRef) key = .ok out) :
    DepthDerivesExpr program m f (.property (.local "self") key) out 1 :=
  .property (.localRead (by simp [localValue, hf])) hp

-- One supplied parameter is stored at a fresh cell even when it has a default.
theorem kadmos_generated_bind_one {program m f param defaults n} :
    DepthBindsProvided program m f [param] defaults [integerValue program.lang n]
      (allocCell m (integerValue program.lang n) true).1
      { f with locals := (param.name, m.nextCell) :: f.locals } 1 := by
  exact .cons (by cases hl : program.lang <;> simp [integerValue, hl]) .empty

theorem kadmos_generated_bind_one_adequate {program m f param defaults n} :
    bindCallParams 2 program m f [param] defaults [integerValue program.lang n] =
      .ok ⟨(allocCell m (integerValue program.lang n) true).1,
        { f with locals := (param.name, m.nextCell) :: f.locals }, .ok ()⟩ :=
  bindProvided_adequate kadmos_generated_bind_one (by decide)

-- TS undefined must take default selection, so it is outside provided-only rules.
theorem kadmos_generated_bind_undefined_excluded {program m f param defaults final ff r}
    (hl : program.lang = .ts) :
    ¬ DepthBindsProvided program m f [param] defaults [.undefined] final ff r := by
  intro h
  cases h with
  | cons hn ht => simp [hl] at hn

-- A returned body needs depth two, in addition to the outer call edge.
theorem kadmos_generated_call_empty_adequate {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    evalExpr 3 program m f (.call expr .empty) = .ok ⟨m, .ok (.bool true)⟩ :=
  evalExpr_adequate (kadmos_generated_call_empty_depth he hc hp hb) (by decide)

theorem kadmos_generated_call_empty_runs {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    ExprRuns program m f (.call expr .empty) ⟨m, .ok (.bool true)⟩ :=
  expr_path_runs (kadmos_generated_call_empty_depth he hc hp hb)

#print axioms evalFields_adequate
#print axioms evalArgs_adequate
#print axioms bindProvided_adequate
#print axioms args_path_runs_cont
#print axioms fields_path_runs_cont

theorem kadmos_generated_property_sound {program m f receiver key out k}
    (hs : ScalarSyntax receiver)
    (he : evalExpr k program m f (.property receiver key) = .ok out) :
    ∃ rank, DepthDerivesExpr program m f (.property receiver key) out rank ∧ rank < k :=
  evalProperty_sound hs he

-- Callee, argument, binding and body share predecessor depth, rather than sum it.
theorem kadmos_generated_call_echo_depth {program m bound f expr ref closure n}
    (he : DepthDerivesExpr program m f expr ⟨bound, .ok (.closure ref)⟩ 1)
    (hc : closureAt bound ref = .ok closure)
    (hp : closure.params = [⟨"seed", none⟩])
    (hb : closure.body = .returnValue (.local "seed")) :
    DepthDerivesExpr program m f (.call expr (.sequence (.integer n) .empty))
      ⟨(allocCell bound (integerValue program.lang n) true).1,
        .ok (integerValue program.lang n)⟩ 2 := by
  let final := (allocCell bound (integerValue program.lang n) true).1
  let ff := { closureFrame closure with locals := [("seed", bound.nextCell)] }
  have hparams : DepthBindsProvided program bound (closureFrame closure) closure.params
      closure.pythonDefaults [integerValue program.lang n] final ff 1 := by
    rw [hp]; exact kadmos_generated_bind_one
  have hread : localValue final ff "seed" = .ok (integerValue program.lang n) := by
    simp [final, ff, closureFrame, allocCell, localValue, readCell, List.lookup]
  have hbody : DepthDerivesStmt program final ff closure.body
      ⟨final, ff, .returned (integerValue program.lang n)⟩ 1 := by
    rw [hb]; exact .returnValue (.localRead hread)
  exact .callClosure he (.cons (.integer n) .empty) hc hparams hbody rfl

theorem kadmos_generated_call_echo_adequate {program m bound f expr ref closure n}
    (he : DepthDerivesExpr program m f expr ⟨bound, .ok (.closure ref)⟩ 1)
    (hc : closureAt bound ref = .ok closure)
    (hp : closure.params = [⟨"seed", none⟩])
    (hb : closure.body = .returnValue (.local "seed")) :
    evalExpr 3 program m f (.call expr (.sequence (.integer n) .empty)) =
      .ok ⟨(allocCell bound (integerValue program.lang n) true).1,
        .ok (integerValue program.lang n)⟩ :=
  evalExpr_adequate (kadmos_generated_call_echo_depth he hc hp hb) (by decide)

-- A raised argument never enters the closure or binds its parameters.
theorem kadmos_generated_call_argument_raises {program m f expr ref}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0) :
    DepthDerivesExpr program m f (.call expr (.sequence badSub .empty))
      ⟨m, .error numericError⟩ 3 :=
  .callArgsRaised he (.headRaised (.binary (by decide) (.string "x") (.bool false) rfl))

-- A source exception thrown by the body is transported to the caller frame.
theorem kadmos_generated_call_body_raises {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .throwValue (.string "body")) :
    DepthDerivesExpr program m f (.call expr .empty)
      ⟨m, .error (.string "body")⟩ 2 := by
  have hparams : DepthBindsProvided program m (closureFrame closure) closure.params
      closure.pythonDefaults [] m (closureFrame closure) 0 := by
    rw [hp]; exact .empty
  have hbody : DepthDerivesStmt program m (closureFrame closure) closure.body
      ⟨m, closureFrame closure, .raised (.string "body")⟩ 1 := by
    rw [hb]; exact .throwValue (.string "body")
  exact .callClosure he .empty hc hparams hbody rfl

#print axioms evalProperty_sound
#print axioms evalScalar_machine_eq

-- Calling the bound method uses the allocated receiver-bearing closure.
theorem kadmos_generated_method_call_depth {program m f name ref closure error}
    (hf : f.receiver = some m.checkerRef)
    (hr : readCheckerField m name = .error error)
    (hm : m.classMethods.lookup name = some ref)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    DepthDerivesExpr program m f (.call (.property (.local "this") name) .empty)
      ⟨(allocClosure m { closure with receiver := some m.checkerRef }).1,
        .ok (.bool true)⟩ 2 := by
  let method := { closure with receiver := some m.checkerRef }
  let bound := (allocClosure m method).1
  have he : DepthDerivesExpr program m f (.property (.local "this") name)
      ⟨bound, .ok (.closure m.nextClosure)⟩ 1 :=
    kadmos_generated_this_property_depth hf (kadmos_generated_method_property hr hm hc)
  have hlookup : closureAt bound m.nextClosure = .ok method := by
    simp [bound, closureAt, allocClosure, List.lookup]
  have hparams : DepthBindsProvided program bound (closureFrame method) method.params
      method.pythonDefaults [] bound (closureFrame method) 0 := by
    change DepthBindsProvided program bound (closureFrame method) closure.params
      closure.pythonDefaults [] bound (closureFrame method) 0
    rw [hp]; exact .empty
  have hbody : DepthDerivesStmt program bound (closureFrame method) method.body
      ⟨bound, closureFrame method, .returned (.bool true)⟩ 1 := by
    change DepthDerivesStmt program bound (closureFrame method) closure.body _ 1
    rw [hb]; exact .returnValue (.bool true)
  exact .callClosure he .empty hlookup hparams hbody rfl

-- The relation's direct-host transition must not bypass generator/callback code.
theorem kadmos_generated_next_not_direct_host : ¬ DirectHostDispatch .next none := by
  simp [DirectHostDispatch]

theorem kadmos_generated_map_not_direct_host {receiver} :
    ¬ DirectHostDispatch .arrayMap (some receiver) := by simp [DirectHostDispatch]

theorem kadmos_generated_call_empty_insufficient_depth {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    evalExpr 2 program m f (.call expr .empty) = .error .exhaustedFuel := by
  simp [evalExpr, evalExpr_adequate he (by decide : 0 < 1), evalArgValues,
    callClosure, hc, hp, hb, bindCallParams, execStmt,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem kadmos_generated_property_method_allocates {lang m key ref closure error}
    (hf : readCheckerField m key = .error error)
    (hm : m.classMethods.lookup key = some ref)
    (hc : closureAt m ref = .ok closure) :
    ∃ out, readPropertyValue lang m (.object m.checkerRef) key = .ok out ∧
      out.machine.nextClosure = m.nextClosure + 1 ∧ out.machine ≠ m := by
  refine ⟨_, kadmos_generated_method_property hf hm hc, rfl, ?_⟩
  intro he
  have hn := congrArg TargetMachine.nextClosure he
  change m.nextClosure + 1 = m.nextClosure at hn
  exact (Nat.ne_of_lt (Nat.lt_succ_self m.nextClosure)) hn.symm

-- Statement trace/adequacy includes a call child and restores the caller frame.
theorem kadmos_generated_statement_call_depth {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    DepthDerivesStmt program m f (.doExpr (.call expr .empty)) ⟨m, f, .normal⟩ 3 :=
  .doExpr (kadmos_generated_call_empty_depth he hc hp hb)

theorem kadmos_generated_statement_call_runs {program m f expr ref closure}
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.closure ref)⟩ 0)
    (hc : closureAt m ref = .ok closure)
    (hp : closure.params = []) (hb : closure.body = .returnValue (.bool true)) :
    StmtRuns program m f (.doExpr (.call expr .empty)) ⟨m, f, .normal⟩ :=
  stmt_path_runs (kadmos_generated_statement_call_depth he hc hp hb)

-- Review regression: a valid primitive call must be derived, with no host-success premise.
theorem kadmos_generated_builtin_dispatch_valid {program m f expr}
    (hl : program.lang = .ts)
    (he : DepthDerivesExpr program m f expr ⟨m, .ok (.builtin .jsIsSafeInteger)⟩ 0) :
    DepthDerivesExpr program m f (.call expr (.sequence (.integer 0) .empty))
      ⟨m, .ok (.bool true)⟩ 2 :=
  kadmos_generated_builtin_call_depth hl he

private def safeHostMachine : TargetMachine :=
  { (allocCell TargetMachine.empty (.builtin .jsIsSafeInteger) true).1 with
    globals := [("isSafe", 0)] }

private def safeHostFrame : TargetFrame := ⟨"host", [], [], [], none, .normal⟩

-- A concrete satisfiable callee binding, with no assumed hostCall success.
private theorem safeHostCallee {program} :
    DepthDerivesExpr program safeHostMachine safeHostFrame (.global "isSafe")
      ⟨safeHostMachine, .ok (.builtin .jsIsSafeInteger)⟩ 0 := by
  apply DepthDerivesExpr.global
  simp [safeHostMachine, safeHostFrame, localValue, allocCell, readCell,
    TargetMachine.empty, List.lookup]

theorem kadmos_generated_builtin_valid_adequate {program}
    (hl : program.lang = .ts) :
    evalExpr 3 program safeHostMachine safeHostFrame
      (.call (.global "isSafe") (.sequence (.integer 0) .empty)) =
      .ok ⟨safeHostMachine, .ok (.bool true)⟩ :=
  evalExpr_adequate (kadmos_generated_builtin_call_depth hl safeHostCallee) (by decide)

theorem kadmos_generated_builtin_valid_runs {program}
    (hl : program.lang = .ts) :
    ExprRuns program safeHostMachine safeHostFrame
      (.call (.global "isSafe") (.sequence (.integer 0) .empty))
      ⟨safeHostMachine, .ok (.bool true)⟩ :=
  expr_path_runs (kadmos_generated_builtin_call_depth hl safeHostCallee)

theorem kadmos_generated_builtin_invalid_arity {lang m} :
    hostCall lang m .jsIsSafeInteger none [] =
      .error (.unsupportedHostPrimitive .jsIsSafeInteger) := by rfl

#print axioms kadmos_generated_property_method_allocates
