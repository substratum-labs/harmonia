import Harmonia.Applications.Kadmos.Generated.BalanceStepSource

/-! Actual Python guard call opening and fixed-source tokenization. -/
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

theorem balanceStep_py_guard_call (b n : Int) :
    balanceStepGuardRun .python b n =
    evalExpr 65 (balanceProgram .python) (balanceStepPyPrefix b n)
      balanceStepPyPrefixFrame balanceStepPyGuardSyntax := by
  unfold balanceStepGuardRun
  rw [balanceStep_py_guard_source]
  rfl



set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option Elab.async false

/-- Literal argument syntax, linked to the actual source by balanceStep_py_guard_source. -/
def balanceStep_py_guard_args : TargetExpr :=
 .sequence (.index (.local "transition") (.string "guard"))
   (.sequence (.call (.local "environment")
      (.sequence (.local "previous") (.sequence (.local "original_context") .empty))) .empty)

def balanceStep_py_guard_argument_machine (b n : Int) : TargetMachine :=
 let m := balanceStepPyPrefix b n
 { m with
   cells := [(179, .object 104), (178, .string "Ready")] ++ m.cells
   writableCells := [(179, true), (178, true)] ++ m.writableCells
   objects := [(124, ⟨.pythonDict, none,
     [("balance", ⟨some (.number .pyInt b), none, none, true, true, true⟩),
      ("state", ⟨some (.string "Ready"), none, none, true, true, true⟩),
      ("event", ⟨some (.object 114), none, none, true, true, true⟩),
      ("request", ⟨some (.object 114), none, none, true, true, true⟩)],
     [], [], false, false⟩)] ++ m.objects
   nextCell := 180
   nextObject := 125 }

theorem balanceStep_py_guard_arguments (b n : Int) :
 evalArgValues 64 (balanceProgram .python) (balanceStepPyPrefix b n)
   balanceStepPyPrefixFrame balanceStep_py_guard_args =
   .ok ⟨balanceStep_py_guard_argument_machine b n,
     .ok [.string "event.amount > 0", .object 124]⟩ := by
 simp only [balanceStep_py_guard_args, balanceStep_py_guard_argument_machine,
   balanceStepPyPrefix, balanceStepPyPrefixFrame, balanceCanonicalConstructed,
   balanceInvariantPyCopied, balanceInvariantPyReset, balanceInvariantPyBound,
   balanceInvariantPyFinal]
 rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

def balanceStep_py_evaluate_closure : TargetClosure :=
 ((closureAt (balanceCanonicalConstructed .python 0) 5).toOption).getD
   ⟨"", [], [], .empty, [], none⟩

def balanceStep_py_guard_body_machine (b n : Int) : TargetMachine :=
 let m := balanceStep_py_guard_argument_machine b n
 { m with
   cells := [(181, .object 124), (180, .string "event.amount > 0")] ++ m.cells
   writableCells := [(181, true), (180, true)] ++ m.writableCells
   nextCell := 182 }

def balanceStep_py_guard_body_frame : TargetFrame :=
 { closureFrame balanceStep_py_evaluate_closure with
   locals := [("environment", 181), ("expression", 180)] }

theorem balanceStep_py_guard_closure (b n : Int) :
 closureAt (balanceStep_py_guard_argument_machine b n) 5 = .ok balanceStep_py_evaluate_closure := by rfl

theorem balanceStep_py_guard_bind (b n : Int) :
 bindCallParams 64 (balanceProgram .python) (balanceStep_py_guard_argument_machine b n)
   (closureFrame balanceStep_py_evaluate_closure) balanceStep_py_evaluate_closure.params
   balanceStep_py_evaluate_closure.pythonDefaults [.string "event.amount > 0", .object 124] =
   .ok ⟨balanceStep_py_guard_body_machine b n, balanceStep_py_guard_body_frame, .ok ()⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl



set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option Elab.async false

private theorem evalCall_open_eq {k : Nat} {program : TargetProgram}
    {m middle bound final : TargetMachine} {f ff : TargetFrame}
    {callee args : TargetExpr} {ref : ClosureRef} {closure : TargetClosure}
    {values : List TargetValue}
    (he : evalExpr k program m f callee = .ok ⟨middle, .ok (.closure ref)⟩)
    (ha : evalArgValues k program middle f args = .ok ⟨bound, .ok values⟩)
    (hc : closureAt bound ref = .ok closure)
    (hb : bindCallParams k program bound (closureFrame closure) closure.params
      closure.pythonDefaults values = .ok ⟨final, ff, .ok ()⟩) :
    evalExpr (k+1) program m f (.call callee args) = (do
      let out ← execStmt k program final ff closure.body
      closureResult program.lang out) := by
  simp only [evalExpr, he, ha, Bind.bind, Except.bind, Pure.pure, Except.pure,
    callClosure, hc]
  change (do
    let bindings ← bindCallParams k program bound (closureFrame closure)
      closure.params closure.pythonDefaults values
    match bindings.result with
    | .error e => pure ⟨bindings.machine, .error e⟩
    | .ok _ => do
      let result ← execStmt k program bindings.machine bindings.frame closure.body
      closureResult program.lang result : Except TargetError ExprOutcome) = _
  simp only [hb, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem balanceStep_py_guard_open (b n : Int) :
 balanceStepGuardRun .python b n = (do
   let out ← execStmt 64 (balanceProgram .python) (balanceStep_py_guard_body_machine b n)
     balanceStep_py_guard_body_frame (balanceSourceBody (balanceProgram .python) "module.evaluate_world")
   closureResult .python out) := by
 rw [balanceStep_py_guard_call]
 change evalExpr 65 (balanceProgram .python) (balanceStepPyPrefix b n)
   balanceStepPyPrefixFrame (.call (.local "evaluate_world") balanceStep_py_guard_args) = _
 have he : evalExpr 64 (balanceProgram .python) (balanceStepPyPrefix b n)
     balanceStepPyPrefixFrame (.local "evaluate_world") =
     .ok ⟨balanceStepPyPrefix b n, .ok (.closure 5)⟩ := by with_unfolding_all rfl
 rw [evalCall_open_eq he (balanceStep_py_guard_arguments b n)
   (balanceStep_py_guard_closure b n) (balanceStep_py_guard_bind b n)]
 have hbody : balanceStep_py_evaluate_closure.body =
     balanceSourceBody (balanceProgram .python) "module.evaluate_world" := by rfl
 rw [hbody, balanceProgram_lang]


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option Elab.async false

def balanceStep_py_tokenized_machine (b n : Int) : TargetMachine :=
 let m := balanceStep_py_guard_body_machine b n
 { m with
   cells := [(184, .regexMatch ⟨"0", 15, 16, []⟩), (183, .number .pyInt 16),
     (182, .object 125)] ++ m.cells
   writableCells := [(184, true), (183, true), (182, true)] ++ m.writableCells
   objects := [(125, ⟨.pythonList, none, [],
     [.string "event", .string ".", .string "amount", .string ">", .string "0"],
     [], false, false⟩)] ++ m.objects
   nextCell := 185
   nextObject := 126 }

def balanceStep_py_tokenized_frame : TargetFrame :=
 { balanceStep_py_guard_body_frame with
   locals := [("match", 184), ("offset", 183), ("tokens", 182)] ++ balanceStep_py_guard_body_frame.locals }

theorem balanceStep_py_tokenization (b n : Int) :
 execStmt 64 (balanceProgram .python) (balanceStep_py_guard_body_machine b n)
   balanceStep_py_guard_body_frame
   (takeStepStmts 5 (balanceSourceBody (balanceProgram .python) "module.evaluate_world")) =
   .ok ⟨balanceStep_py_tokenized_machine b n, balanceStep_py_tokenized_frame, .normal⟩ := by
 simp only [balanceStep_py_tokenized_machine, balanceStep_py_tokenized_frame,
   balanceStep_py_guard_body_machine, balanceStep_py_guard_body_frame, balanceStep_py_evaluate_closure,
   balanceStep_py_guard_argument_machine, balanceStepPyPrefix, balanceStepPyPrefixFrame,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal]
 rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option Elab.async false

theorem balanceStep_py_token_prefix_shape :
 stepPrefixShape 5 (balanceSourceBody (balanceProgram .python) "module.evaluate_world") = true := by
 rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

theorem balanceStep_py_guard_after_tokens (b n : Int) :
 balanceStepGuardRun .python b n = (do
   let out ← execStmt 59 (balanceProgram .python) (balanceStep_py_tokenized_machine b n)
     balanceStep_py_tokenized_frame
     (dropStmts 5 (balanceSourceBody (balanceProgram .python) "module.evaluate_world"))
   closureResult .python out) := by
 rw [balanceStep_py_guard_open]
 rw [execStepPrefix_normal 5 58 (balanceProgram .python)
   (balanceStep_py_guard_body_machine b n) balanceStep_py_guard_body_frame
   (balanceSourceBody (balanceProgram .python) "module.evaluate_world")
   (balanceStep_py_tokenized_machine b n) balanceStep_py_tokenized_frame
   balanceStep_py_token_prefix_shape (balanceStep_py_tokenization b n)]


end Harmonia.Applications.Kadmos.Generated
