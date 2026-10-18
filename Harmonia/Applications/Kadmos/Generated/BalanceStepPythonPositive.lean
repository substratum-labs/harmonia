import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonPositiveModels

/-! Symbolic positive Python DEBIT execution. Source-stage cuts retain the
original parser, effect checks, bounds, invariant, rollback/commit, and finally.
Balances and amounts range over the safe integer domain; subtraction is proved
safe from those hypotheses. The public results use the repository's native
`evalExpr` / `targetStep` API and the literal model verdicts 157 and 167. -/
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false
set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option pp.maxSteps 100

private def pyPositiveTail := dropStmts 21 (balanceStepProtected .python).body
private def pyPositiveGuardMachine (b n : Int) : TargetMachine :=
 (allocCell (balanceStepPyGuard b n) (.bool true) true).1
private def pyPositiveGuardFrame : TargetFrame :=
 { balanceStepPyPrefixFrame with locals := ("guard", 200) :: balanceStepPyPrefixFrame.locals }

private theorem py_guard_skip (program : TargetProgram) (hlang : program.lang = .python)
 (m : TargetMachine) (hm : m.nextCell = 200) :
 execStmt 66 program (allocCell m (.bool true) true).1
 pyPositiveGuardFrame
 (.sequence (.ifThenElse (.binary .isNotIdentity (.local "guard") (.bool true))
   (.sequence (.returnValue (.call (.local "reject")
     (.sequence (.string "GUARD_FAILED") (.sequence (.string "Guard condition failed") .empty)))) .empty)
   .empty) .empty) = .ok ⟨(allocCell m (.bool true) true).1,pyPositiveGuardFrame,.normal⟩ := by
 rcases program with ⟨lang,a,b,c,d,e⟩
 cases hlang
 simp only [allocCell,hm]
 with_unfolding_all rfl

private def pyProtected : ProtectedSyntax :=
 protectedSyntax (firstStmt (dropStmts 5 (restStmt (restStmt
   (balanceSourceBody BalancePrograms.balancePyProgram "WorldChecker.step")))))
private theorem py_protected_source : balanceStepProtected .python = pyProtected :=
 (congrArg (fun body => protectedSyntax (firstStmt (dropStmts 5
   (restStmt (restStmt body))))) (balanceStep_stored_source .python)).trans
 (congrArg (fun program => protectedSyntax (firstStmt (dropStmts 5
   (restStmt (restStmt (balanceSourceBody program "WorldChecker.step"))))))
   (balanceProgram_of_parse BalancePrograms.balancePyProgram_source))

private def pyGuard := protectedSyntax (firstStmt pyPositiveTail)
private def pyGuardLiteral := protectedSyntax (firstStmt (dropStmts 21 pyProtected.body))
private theorem py_guard_literal : pyGuard = pyGuardLiteral :=
 congrArg (fun p : ProtectedSyntax => protectedSyntax (firstStmt (dropStmts 21 p.body))) py_protected_source
private theorem py_guard_source : firstStmt pyPositiveTail = pyGuard.stmt :=
 Eq.mpr (congrArg (fun p : ProtectedSyntax =>
   firstStmt (dropStmts 21 p.body) = (protectedSyntax (firstStmt (dropStmts 21 p.body))).stmt)
   py_protected_source) (by with_unfolding_all rfl)
private theorem py_guard_body_source : pyGuard.body = .sequence (firstStmt pyGuard.body) (restStmt pyGuard.body) :=
 Eq.mpr (congrArg (fun p : ProtectedSyntax => p.body = .sequence (firstStmt p.body) (restStmt p.body))
   py_guard_literal) (by with_unfolding_all rfl)
private theorem py_guard_assign_source : firstStmt pyGuard.body = .assign (.local "guard") (balanceStepGuardExpression .python) :=
 ((congrArg (fun p : ProtectedSyntax => firstStmt p.body) py_guard_literal).trans
   (show firstStmt pyGuardLiteral.body = .assign (.local "guard") balanceStepPyGuardSyntax from by with_unfolding_all rfl)).trans
 (congrArg (fun e => TargetStmt.assign (.local "guard") e) balanceStep_py_guard_source.symm)
private theorem py_guard_rest_source : restStmt pyGuard.body = .sequence
 (.ifThenElse (.binary .isNotIdentity (.local "guard") (.bool true))
   (.sequence (.returnValue (.call (.local "reject")
     (.sequence (.string "GUARD_FAILED") (.sequence (.string "Guard condition failed") .empty)))) .empty)
   .empty) .empty :=
 (congrArg (fun p : ProtectedSyntax => restStmt p.body) py_guard_literal).trans (by with_unfolding_all rfl)
private theorem py_guard_cleanup_source : pyGuard.cleanup = .empty :=
 (congrArg ProtectedSyntax.cleanup py_guard_literal).trans (by with_unfolding_all rfl)

private theorem py_assign_guard {program : TargetProgram} {initial final : TargetMachine}
 {expr : TargetExpr} (hlang : program.lang = .python)
 (he : evalExpr 65 program initial balanceStepPyPrefixFrame expr = .ok ⟨final,.ok (.bool true)⟩)
 (hl : (balanceStepPyPrefixFrame.locals.lookup "guard").orElse (fun _ =>
   (balanceStepPyPrefixFrame.captures.lookup "guard").orElse (fun _ => initial.globals.lookup "guard")) = none)
 (hn : final.nextCell = 200) :
 execStmt 66 program initial balanceStepPyPrefixFrame (.assign (.local "guard") expr) =
 .ok ⟨(allocCell final (.bool true) true).1,pyPositiveGuardFrame,.normal⟩ := by
 rw [execStmt.eq_def]
 dsimp only
 rw [he]
 dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
 rw [hl]
 simp only [hlang,show (TargetLang.python == TargetLang.ts) = false from rfl,
   Bool.false_eq_true,↓reduceIte]
 simp only [allocCell,hn,pyPositiveGuardFrame]
private theorem py_guard_assignment_execute (b n : Int)
 (hn : n.natAbs ≤ 9007199254740991) (hp : 0 < n) :
 execStmt 66 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame
 (firstStmt pyGuard.body) = .ok ⟨pyPositiveGuardMachine b n,pyPositiveGuardFrame,.normal⟩ :=
 (congrArg (execStmt 66 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame)
   py_guard_assign_source).trans
 (py_assign_guard (balanceProgram_lang .python)
   (by simpa only [decide_eq_true hp] using (balanceStep_py_guard_execute b n hn))
   (by with_unfolding_all rfl) rfl)

private theorem seq_normal {program m middle final f mf ff first rest k}
 (hfirst : execStmt k program m f first = .ok ⟨middle,mf,.normal⟩)
 (hrest : execStmt k program middle mf rest = .ok ⟨final,ff,.normal⟩) :
 execStmt (k+1) program m f (.sequence first rest) = .ok ⟨final,ff,.normal⟩ := by
 rw [execSequence_eq k,hfirst]
 exact hrest
private theorem protected_normal {program m final f ff k} {p : ProtectedSyntax}
 (hbody : execStmt k program m f p.body = .ok ⟨final,ff,.normal⟩)
 (hcleanup : execStmt k program final ff p.cleanup = .ok ⟨final,ff,.normal⟩) :
 execStmt (k+1) program m f p.stmt = .ok ⟨final,ff,.normal⟩ := by
 rw [execProtectedSyntax_eq k,hbody]
 dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
 rw [hcleanup]
private theorem py_guard_body_execute (b n : Int)
 (hn : n.natAbs ≤ 9007199254740991) (hp : 0 < n) :
 execStmt 67 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame
 pyGuard.body = .ok ⟨pyPositiveGuardMachine b n,pyPositiveGuardFrame,.normal⟩ :=
 (congrArg (execStmt 67 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame)
   py_guard_body_source).trans
 (seq_normal (py_guard_assignment_execute b n hn hp)
   ((congrArg (execStmt 66 (balanceProgram .python) (pyPositiveGuardMachine b n) pyPositiveGuardFrame)
      py_guard_rest_source).trans
    (py_guard_skip (balanceProgram .python) (balanceProgram_lang .python) (balanceStepPyGuard b n) rfl)))
private theorem py_positive_guard_execute (b n : Int)
 (hn : n.natAbs ≤ 9007199254740991) (hp : 0 < n) :
 execStmt 68 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame
   (firstStmt pyPositiveTail) = .ok ⟨pyPositiveGuardMachine b n, pyPositiveGuardFrame, .normal⟩ :=
 (congrArg (execStmt 68 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame)
   py_guard_source).trans
 (protected_normal (py_guard_body_execute b n hn hp)
   ((congrArg (execStmt 67 (balanceProgram .python) (pyPositiveGuardMachine b n) pyPositiveGuardFrame)
     py_guard_cleanup_source).trans (by with_unfolding_all rfl)))

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


private theorem evalHost_call_eq {k : Nat} {program : TargetProgram}
 {m middle bound : TargetMachine} {f : TargetFrame} {callee args : TargetExpr}
 {id : BuiltinId} {values : List TargetValue}
 (he : evalExpr k program m f callee = .ok ⟨middle, .ok (.builtin id)⟩)
 (ha : evalArgValues k program middle f args = .ok ⟨bound, .ok values⟩)
 (hi : (id == .next) = false ∧ (id == .tuple) = false ∧ (id == .list) = false) :
 evalExpr (k+1) program m f (.call callee args) = hostCall program.lang bound id none values := by
 rw [evalExpr.eq_def]
 simp only [he,ha,Bind.bind,Except.bind,hi.1,hi.2.1,hi.2.2,Bool.false_eq_true,↓reduceIte]

/-- Allocation slices of the fixed post-effect heap, before symbolic checks. -/
private def pyStage (b n : Int) (nc no nk : Nat) (pos : Int := 0)
 (left : TargetValue := .undefined) (done : Bool := false) : TargetMachine :=
 let m := balanceStepPyBoundsRejected b n
 { balanceStepPyPrefix b n with
   cells := (m.cells.drop (237-nc)).map (fun e =>
     if e.1 == 158 then (158, if done then .number .pyFloat (b-n) else .object 102)
     else if e.1 == 211 then (211, .number .pyInt pos)
     else if e.1 == 215 then (215, left) else e)
   objects := (m.objects.drop (158-no)).map (fun e =>
     if e.1 == 134 && !done then
       (134, ⟨.pythonDict, none, [("balance", ⟨some (.number .pyInt b),none,none,true,true,true⟩)],[],[],false,false⟩)
     else e)
   closures := m.closures.drop (35-nk)
   writableCells := m.writableCells.drop (237-nc)
   nextCell := nc, nextObject := no, nextClosure := nk }
private def pyEffectsFrame : TargetFrame :=
 { pyPositiveGuardFrame with locals := ("candidate",201)::pyPositiveGuardFrame.locals }
private def pyLoopFrame : TargetFrame :=
 { pyEffectsFrame with locals := ("effect",202)::pyEffectsFrame.locals }
private def pyEffectFrame : TargetFrame :=
 { pyLoopFrame with locals := ("match",203)::pyLoopFrame.locals }
private def pyEffects := takeStepStmts 2 (restStmt (dropStmts 21 pyProtected.body))
private def pyEffectFor := firstStmt (protectedSyntax (firstStmt (restStmt pyEffects))).body
private def pyEffectBody := match pyEffectFor with | .forDo _ _ s => s | _ => .empty
private def pyWorldCall := match firstStmt (dropStmts 2 pyEffectBody) with
 | .assign _ e => e | _ => .undefined
private def pyWorldBody := balanceSourceBody BalancePrograms.balancePyProgram "module.evaluate_world"
private def pyParseBody := balanceSourceBody BalancePrograms.balancePyProgram "module.evaluate_world.parse"
private def pyParseLoop := firstStmt (dropStmts 5 pyParseBody)
private def pyParseLoopBody := match pyParseLoop with | .whileDo _ s => s | _ => .empty
private def pyClosure (ref : Nat) : TargetClosure :=
 (closureAt (balanceStepPyBoundsRejected 0 0) ref).toOption.getD ⟨"",[],[],.empty,[],none⟩
private def pyWorldFrame : TargetFrame :=
 { closureFrame (pyClosure 5) with locals := [("environment",207),("expression",206)] }
private def pyTokenFrame : TargetFrame :=
 { pyWorldFrame with locals := [("match",210),("offset",209),("tokens",208)] ++ pyWorldFrame.locals }
private def pyWorldReadyFrame : TargetFrame :=
 { pyTokenFrame with locals := [("parse",212),("position",211)] ++ pyTokenFrame.locals }
private def pyParseFrame : TargetFrame :=
 { closureFrame (pyClosure 33) with locals := [("minimum",213)] }
private def pyParseReadyFrame : TargetFrame :=
 { pyParseFrame with locals := [("left",215),("token",214)] ++ pyParseFrame.locals }
private def pyArithmeticFrame : TargetFrame :=
 { pyParseReadyFrame with locals := [("right",222),("rank",217),("operator",216)] ++ pyParseReadyFrame.locals }
private theorem py_guard_stage (b n : Int) (hp : 0<n) :
 pyPositiveGuardMachine b n = pyStage b n 201 134 33 := by
 simp only [pyPositiveGuardMachine,balanceStepPyGuard,decide_eq_true hp]
 with_unfolding_all rfl
private theorem py_candidate_execute (b n : Int) (hp : 0<n) :
 execStmt 67 (balanceProgram .python) (pyPositiveGuardMachine b n) pyPositiveGuardFrame
 (firstStmt pyEffects) = .ok ⟨pyStage b n 202 135 33,pyEffectsFrame,.normal⟩ := by
 rw [py_guard_stage b n hp]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl
private theorem py_effect_prefix (b n : Int) :
 execStmt 62 (balanceProgram .python) (pyStage b n 203 135 33) pyLoopFrame
 (takeStepStmts 2 pyEffectBody) = .ok ⟨pyStage b n 204 135 33,pyEffectFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl
private theorem py_effect_tokenization (b n : Int) :
 execStmt 57 (balanceProgram .python) (pyStage b n 208 136 33) pyWorldFrame
 (takeStepStmts 5 pyWorldBody) = .ok ⟨pyStage b n 211 137 33,pyTokenFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl
private theorem py_effect_parse_install (b n : Int) :
 execStmt 52 (balanceProgram .python) (pyStage b n 211 137 33) pyTokenFrame
 (takeStepStmts 2 (dropStmts 5 pyWorldBody)) =
 .ok ⟨pyStage b n 213 137 34,pyWorldReadyFrame,.normal⟩ := by
 simp only [pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal, pyClosure]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl
private theorem py_parse_prefix (b n : Int) :
 execStmt 47 (balanceProgram .python) (pyStage b n 214 137 34) pyParseFrame
 (takeStepStmts 5 pyParseBody) =
 .ok ⟨pyStage b n 216 139 34 1 (.number .pyInt b),pyParseReadyFrame,.normal⟩ := by
 simp only [pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal, pyClosure]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_parse_loop_prefix_fixed (b n : Int) :
 execStmt 40 (balanceProgram .python) (pyStage b n 216 139 34 1 (.number .pyInt b)) pyParseReadyFrame
 (takeStepStmts 5 pyParseLoopBody) =
 .ok ⟨pyStage b n 223 141 34 5 (.number .pyInt b),pyArithmeticFrame,.normal⟩ := by
 simp only [pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal, pyClosure]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private def pyNumberBody := balanceSourceBody BalancePrograms.balancePyProgram "module._number"
private def pyFloatExpr : TargetExpr := .call (.local "float") (.sequence (.local "value") .empty)

private def pyNumberLeftFrame : TargetFrame :=
 { closureFrame (pyClosure 2) with locals := [("value",223)] }
private def pyNumberLeft : TargetExpr := .call (.local "_number") (.sequence (.local "left") .empty)
private theorem py_number_left (b n : Int) (hx : b.natAbs ≤ 9007199254740991) :
 evalExpr 23 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b)) pyArithmeticFrame pyNumberLeft =
 .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b), .ok (.number .pyFloat b)⟩ := by
 have he : evalExpr 22 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b)) pyArithmeticFrame (.local "_number") =
   .ok ⟨pyStage b n 223 143 34 5 (.number .pyInt b), .ok (.closure 2)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 22 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b)) pyArithmeticFrame
   (.sequence (.local "left") .empty) = .ok ⟨pyStage b n 223 143 34 5 (.number .pyInt b),.ok [.number .pyInt b]⟩ := by
   with_unfolding_all rfl
 have hc : closureAt (pyStage b n 223 143 34 5 (.number .pyInt b)) 2 = .ok (pyClosure 2) := by with_unfolding_all rfl
 have hb : bindCallParams 22 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b)) (closureFrame (pyClosure 2))
   (pyClosure 2).params (pyClosure 2).pythonDefaults [.number .pyInt b] =
   .ok ⟨pyStage b n 224 143 34 5 (.number .pyInt b),pyNumberLeftFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pyNumberLeft,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 2).body = pyNumberBody := by
   change balanceSourceBody (balanceProgram .python) "module._number" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]
 have hshape : pyNumberBody = .sequence (firstStmt pyNumberBody) (restStmt pyNumberBody) := by
   with_unfolding_all rfl
 have hp : execStmt 21 (balanceProgram .python) (pyStage b n 224 143 34 5 (.number .pyInt b)) pyNumberLeftFrame (firstStmt pyNumberBody) =
   .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b),pyNumberLeftFrame,.normal⟩ := by
   simp only [pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal,
   pyEffects, pyEffectBody, pyEffectFor, pyPositiveTail, balanceStepProtected,
   balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source,
   pyWorldBody, pyParseBody, pyParseLoop, pyParseLoopBody]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hf : evalExpr 19 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) pyNumberLeftFrame pyFloatExpr =
   .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b),.ok (.number .pyFloat b)⟩ := by
   have he : evalExpr 18 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) pyNumberLeftFrame (.local "float") =
     .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b),.ok (.builtin .float)⟩ := by with_unfolding_all rfl
   have ha : evalArgValues 18 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) pyNumberLeftFrame
     (.sequence (.local "value") .empty) = .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b),.ok [.number .pyInt b]⟩ := by
     with_unfolding_all rfl
   rw [pyFloatExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_float_exact_tag _ _ _ hx]
   with_unfolding_all rfl
 have ht : restStmt pyNumberBody = .sequence (.returnValue pyFloatExpr) .empty := by
   with_unfolding_all rfl
 rw [hshape,execSequence_eq 21,hp]
 dsimp only [Bind.bind,Except.bind]
 rw [ht,execSequence_eq 20,execStmt.eq_def]
 dsimp only
 rw [hf]
 with_unfolding_all rfl

private def pyNumberRightFrame : TargetFrame :=
 { closureFrame (pyClosure 2) with locals := [("value",224)] }
private def pyNumberRight : TargetExpr := .call (.local "_number") (.sequence (.local "right") .empty)
private theorem py_number_right (b n : Int) (hx : n.natAbs ≤ 9007199254740991) :
 evalExpr 23 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) pyArithmeticFrame pyNumberRight =
 .ok ⟨pyStage b n 225 145 34 5 (.number .pyInt b), .ok (.number .pyFloat n)⟩ := by
 have he : evalExpr 22 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) pyArithmeticFrame (.local "_number") =
   .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b), .ok (.closure 2)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 22 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) pyArithmeticFrame
   (.sequence (.local "right") .empty) = .ok ⟨pyStage b n 224 144 34 5 (.number .pyInt b),.ok [.number .pyFloat n]⟩ := by
   with_unfolding_all rfl
 have hc : closureAt (pyStage b n 224 144 34 5 (.number .pyInt b)) 2 = .ok (pyClosure 2) := by with_unfolding_all rfl
 have hb : bindCallParams 22 (balanceProgram .python) (pyStage b n 224 144 34 5 (.number .pyInt b)) (closureFrame (pyClosure 2))
   (pyClosure 2).params (pyClosure 2).pythonDefaults [.number .pyFloat n] =
   .ok ⟨pyStage b n 225 144 34 5 (.number .pyInt b),pyNumberRightFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pyNumberRight,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 2).body = pyNumberBody := by
   change balanceSourceBody (balanceProgram .python) "module._number" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]
 have hshape : pyNumberBody = .sequence (firstStmt pyNumberBody) (restStmt pyNumberBody) := by
   with_unfolding_all rfl
 have hp : execStmt 21 (balanceProgram .python) (pyStage b n 225 144 34 5 (.number .pyInt b)) pyNumberRightFrame (firstStmt pyNumberBody) =
   .ok ⟨pyStage b n 225 145 34 5 (.number .pyInt b),pyNumberRightFrame,.normal⟩ := by
   simp only [pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal,
   pyEffects, pyEffectBody, pyEffectFor, pyPositiveTail, balanceStepProtected,
   balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source,
   pyWorldBody, pyParseBody, pyParseLoop, pyParseLoopBody]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hf : evalExpr 19 (balanceProgram .python) (pyStage b n 225 145 34 5 (.number .pyInt b)) pyNumberRightFrame pyFloatExpr =
   .ok ⟨pyStage b n 225 145 34 5 (.number .pyInt b),.ok (.number .pyFloat n)⟩ := by
   have he : evalExpr 18 (balanceProgram .python) (pyStage b n 225 145 34 5 (.number .pyInt b)) pyNumberRightFrame (.local "float") =
     .ok ⟨pyStage b n 225 145 34 5 (.number .pyInt b),.ok (.builtin .float)⟩ := by with_unfolding_all rfl
   have ha : evalArgValues 18 (balanceProgram .python) (pyStage b n 225 145 34 5 (.number .pyInt b)) pyNumberRightFrame
     (.sequence (.local "value") .empty) = .ok ⟨pyStage b n 225 145 34 5 (.number .pyInt b),.ok [.number .pyFloat n]⟩ := by
     with_unfolding_all rfl
   rw [pyFloatExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_float_exact_tag _ _ _ hx]
   with_unfolding_all rfl
 have ht : restStmt pyNumberBody = .sequence (.returnValue pyFloatExpr) .empty := by
   with_unfolding_all rfl
 rw [hshape,execSequence_eq 21,hp]
 dsimp only [Bind.bind,Except.bind]
 rw [ht,execSequence_eq 20,execStmt.eq_def]
 dsimp only
 rw [hf]
 with_unfolding_all rfl

private theorem evalSub_eq {k : Nat} {program : TargetProgram} {m middle final : TargetMachine}
 {f : TargetFrame} {left right : TargetExpr} {b n : Int}
 (hl : program.lang = .python)
 (he : evalExpr k program m f left = .ok ⟨middle,.ok (.number .pyFloat b)⟩)
 (hr : evalExpr k program middle f right = .ok ⟨final,.ok (.number .pyFloat n)⟩)
 (hv : binaryValue .python final .sub (.number .pyFloat b) (.number .pyFloat n) =
   .ok (.ok (.number .pyFloat (b-n)))) :
 evalExpr (k+1) program m f (.binary .sub left right) =
 .ok ⟨final,.ok (.number .pyFloat (b-n))⟩ := by
 rw [evalExpr.eq_def]
 simp only [he,hr,Bind.bind,Except.bind,hl,hv]
 with_unfolding_all rfl

private theorem py_arithmetic (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 24 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
 pyArithmeticFrame (.binary .sub pyNumberLeft pyNumberRight) =
 .ok ⟨pyStage b n 225 145 34 5 (.number .pyInt b),.ok (.number .pyFloat (b-n))⟩ :=
 evalSub_eq (balanceProgram_lang .python) (py_number_left b n hb)
   (py_number_right b n hn) (binary_sub_py_float_safe _ b n hs)

private theorem execIf_bool_eq {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {cond : TargetExpr} {yes no : TargetStmt} {value : Bool}
 (_hl : program.lang = .python)
 (he : evalExpr k program m f cond = .ok ⟨middle,.ok (.bool value)⟩) :
 execStmt (k+1) program m f (.ifThenElse cond yes no) =
 execStmt k program middle f (if value then yes else no) := by
 rw [execStmt.eq_def]
 simp only [he,Bind.bind,Except.bind,_hl,sourceTruthy]
 cases value <;> rfl

private theorem execAssign_existing_eq {k : Nat} {program : TargetProgram} {m middle final : TargetMachine}
 {f : TargetFrame} {name : String} {expr : TargetExpr} {value : TargetValue} {ref : Nat}
 (he : evalExpr k program m f expr = .ok ⟨middle,.ok value⟩)
 (ha : (f.locals.lookup name).orElse (fun _ => (f.captures.lookup name).orElse
   (fun _ => m.globals.lookup name)) = some ref)
 (hw : writeCell middle ref value = .ok final) :
 execStmt (k+1) program m f (.assign (.local name) expr) = .ok ⟨final,f,.normal⟩ := by
 rw [execStmt.eq_def]
 simp only [he,ha,hw,Bind.bind,Except.bind,Pure.pure,Except.pure]

private def pyDispatch (i : Nat) : TargetStmt :=
 match i with
 | 0 => firstStmt (dropStmts 5 pyParseLoopBody)
 | i+1 => match pyDispatch i with | .ifThenElse _ _ no => no | _ => .empty
private def pyDispatchCond (i : Nat) := match pyDispatch i with | .ifThenElse c _ _ => c | _ => .undefined
private def pyDispatchYes (i : Nat) := match pyDispatch i with | .ifThenElse _ yes _ => yes | _ => .empty

private theorem py_dispatch_shape (i : Nat) (hi : i ≤ 7) :
 pyDispatch i = .ifThenElse (pyDispatchCond i) (pyDispatchYes i) (pyDispatch (i+1)) := by
 have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
 rcases hi with h|h|h|h|h|h|h|h <;> subst i <;> with_unfolding_all rfl

private theorem py_dispatch_conditions (b n : Int) (i : Nat) (hi : i ≤ 7) :
 evalExpr (33-i) (balanceProgram .python)
 (pyStage b n 223 (141 + min i 2) 34 5 (.number .pyInt b)) pyArithmeticFrame (pyDispatchCond i) =
 .ok ⟨pyStage b n 223 (141 + min (i+1) 2) 34 5 (.number .pyInt b),.ok (.bool (i == 7))⟩ := by
 have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
 rcases hi with h|h|h|h|h|h|h|h <;> subst i <;>
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source] <;>
 with_unfolding_all rfl

private theorem py_dispatch_skip (b n : Int) (i : Nat) (hi : i < 7) :
 execStmt (34-i) (balanceProgram .python)
 (pyStage b n 223 (141 + min i 2) 34 5 (.number .pyInt b)) pyArithmeticFrame (pyDispatch i) =
 execStmt (33-i) (balanceProgram .python)
 (pyStage b n 223 (141 + min (i+1) 2) 34 5 (.number .pyInt b)) pyArithmeticFrame (pyDispatch (i+1)) := by
 have hf : 34-i = (33-i)+1 := by omega
 rw [hf,py_dispatch_shape i (by omega),execIf_bool_eq (balanceProgram_lang .python)
   (py_dispatch_conditions b n i (by omega))]
 have h : (i == 7) = false := by simp; omega
 rw [h]
 rfl

private def pyArithmeticDone (b n : Int) := pyStage b n 225 145 34 5 (.number .pyFloat (b-n))

private theorem py_minus_assign (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 25 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
 pyArithmeticFrame (.assign (.local "left") (.binary .sub pyNumberLeft pyNumberRight)) =
 .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.normal⟩ :=
 execAssign_existing_eq (py_arithmetic b n hb hn hs) (by with_unfolding_all rfl)
   (by with_unfolding_all rfl)

private theorem py_minus_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 27 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
 pyArithmeticFrame (pyDispatch 7) = .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.normal⟩ := by
 have he : evalExpr 26 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
   pyArithmeticFrame (pyDispatchCond 7) = .ok ⟨pyStage b n 223 143 34 5 (.number .pyInt b),.ok (.bool true)⟩ := by
   simpa using py_dispatch_conditions b n 7 (by decide)
 rw [py_dispatch_shape 7 (by decide),execIf_bool_eq (balanceProgram_lang .python) he]
 have shape : pyDispatchYes 7 = .sequence
   (.assign (.local "left") (.binary .sub pyNumberLeft pyNumberRight)) .empty := by with_unfolding_all rfl
 change execStmt 26 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
   pyArithmeticFrame (pyDispatchYes 7) = _
 rw [shape,execSequence_eq 25,py_minus_assign b n hb hn hs]
 with_unfolding_all rfl

private theorem py_dispatch_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 35 (balanceProgram .python) (pyStage b n 223 141 34 5 (.number .pyInt b))
 pyArithmeticFrame (dropStmts 5 pyParseLoopBody) = .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.normal⟩ := by
 have shape : dropStmts 5 pyParseLoopBody = .sequence (pyDispatch 0) .empty := by with_unfolding_all rfl
 rw [shape,execSequence_eq 34]
 have h : execStmt 34 (balanceProgram .python) (pyStage b n 223 141 34 5 (.number .pyInt b))
   pyArithmeticFrame (pyDispatch 0) = .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.normal⟩ := by
   have h0 : execStmt 34 (balanceProgram .python) (pyStage b n 223 141 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 0) =
     execStmt 33 (balanceProgram .python) (pyStage b n 223 142 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 1) := by simpa using py_dispatch_skip b n 0 (by decide)
   have h1 : execStmt 33 (balanceProgram .python) (pyStage b n 223 142 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 1) =
     execStmt 32 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 2) := by simpa using py_dispatch_skip b n 1 (by decide)
   have h2 : execStmt 32 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 2) =
     execStmt 31 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 3) := by simpa using py_dispatch_skip b n 2 (by decide)
   have h3 : execStmt 31 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 3) =
     execStmt 30 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 4) := by simpa using py_dispatch_skip b n 3 (by decide)
   have h4 : execStmt 30 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 4) =
     execStmt 29 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 5) := by simpa using py_dispatch_skip b n 4 (by decide)
   have h5 : execStmt 29 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 5) =
     execStmt 28 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 6) := by simpa using py_dispatch_skip b n 5 (by decide)
   have h6 : execStmt 28 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 6) =
     execStmt 27 (balanceProgram .python) (pyStage b n 223 143 34 5 (.number .pyInt b))
     pyArithmeticFrame (pyDispatch 7) := by simpa using py_dispatch_skip b n 6 (by decide)
   rw [h0, h1, h2, h3, h4, h5, h6]
   exact py_minus_run b n hb hn hs
 rw [h]
 with_unfolding_all rfl

private theorem seq_after_normal {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f mf : TargetFrame} {first rest : TargetStmt}
 (he : execStmt k program m f first = .ok ⟨middle,mf,.normal⟩) :
 execStmt (k+1) program m f (.sequence first rest) = execStmt k program middle mf rest := by
 rw [execSequence_eq k,he]
 rfl

private theorem execWhile_normal_eq {k : Nat} {program : TargetProgram} {m middle final : TargetMachine}
 {f ff : TargetFrame} {cond : TargetExpr} {body : TargetStmt}
 (_hl : program.lang = .python)
 (hc : evalExpr k program m f cond = .ok ⟨middle,.ok (.bool true)⟩)
 (hb : execStmt k program middle f body = .ok ⟨final,ff,.normal⟩) :
 execStmt (k+1) program m f (.whileDo cond body) = execStmt k program final ff (.whileDo cond body) := by
 rw [execStmt.eq_def]
 simp only [hc,hb,Bind.bind,Except.bind,_hl,sourceTruthy]
 rfl

private theorem execAssign_fresh_eq {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {name : String} {expr : TargetExpr} {value : TargetValue}
 (hl : program.lang = .python)
 (he : evalExpr k program m f expr = .ok ⟨middle,.ok value⟩)
 (ha : (f.locals.lookup name).orElse (fun _ => (f.captures.lookup name).orElse
   (fun _ => m.globals.lookup name)) = none) :
 execStmt (k+1) program m f (.assign (.local name) expr) =
 .ok ⟨(allocCell middle value true).1,{f with locals := (name,middle.nextCell)::f.locals},.normal⟩ := by
 rw [execStmt.eq_def]
 simp only [he,ha,hl,Bind.bind,Except.bind,Pure.pure,Except.pure]
 rfl

private theorem py_loop_body_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 40 (balanceProgram .python) (pyStage b n 216 139 34 1 (.number .pyInt b))
 pyParseReadyFrame pyParseLoopBody = .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.normal⟩ := by
 rw [execStepPrefix_normal 5 34 _ _ _ _ _ _ (by with_unfolding_all rfl)
   (py_parse_loop_prefix_fixed b n)]
 exact py_dispatch_run b n hb hn hs

private theorem py_parse_loop_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 41 (balanceProgram .python) (pyStage b n 216 139 34 1 (.number .pyInt b))
 pyParseReadyFrame pyParseLoop = .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.normal⟩ := by
 let cond : TargetExpr := .binary .lt (.local "position") (.call (.local "len") (.sequence (.local "tokens") .empty))
 have shape : pyParseLoop = .whileDo cond pyParseLoopBody := by with_unfolding_all rfl
 have hc : evalExpr 40 (balanceProgram .python) (pyStage b n 216 139 34 1 (.number .pyInt b))
   pyParseReadyFrame cond = .ok ⟨pyStage b n 216 139 34 1 (.number .pyInt b),.ok (.bool true)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape,execWhile_normal_eq (balanceProgram_lang .python) hc (py_loop_body_run b n hb hn hs)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_parse_body_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 47 (balanceProgram .python) (pyStage b n 214 137 34) pyParseFrame pyParseBody =
 .ok ⟨pyArithmeticDone b n,pyArithmeticFrame,.returned (.number .pyFloat (b-n))⟩ := by
 rw [execStepPrefix_normal 5 41 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_parse_prefix b n)]
 have shape : dropStmts 5 pyParseBody = .sequence pyParseLoop (restStmt (dropStmts 5 pyParseBody)) := by
   with_unfolding_all rfl
 rw [shape,seq_after_normal (py_parse_loop_run b n hb hn hs)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_parse_open (b n : Int) :
 evalExpr 48 (balanceProgram .python) (pyStage b n 213 137 34) pyWorldReadyFrame (.call (.local "parse") .empty) =
 (do let out ← execStmt 47 (balanceProgram .python) (pyStage b n 214 137 34) pyParseFrame pyParseBody
     closureResult .python out) := by
 have he : evalExpr 47 (balanceProgram .python) (pyStage b n 213 137 34) pyWorldReadyFrame (.local "parse") =
   .ok ⟨pyStage b n 213 137 34,.ok (.closure 33)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 47 (balanceProgram .python) (pyStage b n 213 137 34) pyWorldReadyFrame .empty =
   .ok ⟨pyStage b n 213 137 34,.ok []⟩ := by with_unfolding_all rfl
 have hc : closureAt (pyStage b n 213 137 34) 33 = .ok (pyClosure 33) := by with_unfolding_all rfl
 have hb : bindCallParams 47 (balanceProgram .python) (pyStage b n 213 137 34) (closureFrame (pyClosure 33))
   (pyClosure 33).params (pyClosure 33).pythonDefaults [] = .ok ⟨pyStage b n 214 137 34,pyParseFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 33).body = pyParseBody := by
   change balanceSourceBody (balanceProgram .python) "module.evaluate_world.parse" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem py_parse_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 48 (balanceProgram .python) (pyStage b n 213 137 34) pyWorldReadyFrame (.call (.local "parse") .empty) =
 .ok ⟨pyArithmeticDone b n,.ok (.number .pyFloat (b-n))⟩ := by
 rw [py_parse_open,py_parse_body_run b n hb hn hs]
 with_unfolding_all rfl

private def pyWorldResult (b n : Int) := pyStage b n 226 145 34 5 (.number .pyFloat (b-n))
private def pyWorldResultFrame : TargetFrame := {pyWorldReadyFrame with locals := ("result",225)::pyWorldReadyFrame.locals}

private theorem py_world_result_assign (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 49 (balanceProgram .python) (pyStage b n 213 137 34) pyWorldReadyFrame
 (.assign (.local "result") (.call (.local "parse") .empty)) =
 .ok ⟨pyWorldResult b n,pyWorldResultFrame,.normal⟩ :=
 (execAssign_fresh_eq (balanceProgram_lang .python) (py_parse_run b n hb hn hs)
   (by with_unfolding_all rfl)).trans (by with_unfolding_all rfl)

private theorem py_world_body_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 57 (balanceProgram .python) (pyStage b n 208 136 33) pyWorldFrame pyWorldBody =
 .ok ⟨pyWorldResult b n,pyWorldResultFrame,.returned (.number .pyFloat (b-n))⟩ := by
 rw [execStepPrefix_normal 5 51 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_effect_tokenization b n)]
 rw [execStepPrefix_normal 2 49 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_effect_parse_install b n)]
 have shape : dropStmts 2 (dropStmts 5 pyWorldBody) = .sequence
   (.assign (.local "result") (.call (.local "parse") .empty)) (restStmt (dropStmts 7 pyWorldBody)) := by
   with_unfolding_all rfl
 rw [shape,seq_after_normal (py_world_result_assign b n hb hn hs)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_world_open (b n : Int) :
 evalExpr 58 (balanceProgram .python) (pyStage b n 204 135 33) pyEffectFrame pyWorldCall =
 (do let out ← execStmt 57 (balanceProgram .python) (pyStage b n 208 136 33) pyWorldFrame pyWorldBody
     closureResult .python out) := by
 let args : TargetExpr := match pyWorldCall with | .call _ a => a | _ => .empty
 have shape : pyWorldCall = .call (.local "evaluate_world") args := by with_unfolding_all rfl
 have he : evalExpr 57 (balanceProgram .python) (pyStage b n 204 135 33) pyEffectFrame (.local "evaluate_world") =
   .ok ⟨pyStage b n 204 135 33,.ok (.closure 5)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 57 (balanceProgram .python) (pyStage b n 204 135 33) pyEffectFrame args =
   .ok ⟨pyStage b n 206 136 33,.ok [.string "balance - event.amount",.object 135]⟩ := by
   simp only [pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
     balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
     balanceInvariantPyBound, balanceInvariantPyFinal]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hc : closureAt (pyStage b n 206 136 33) 5 = .ok (pyClosure 5) := by with_unfolding_all rfl
 have hb : bindCallParams 57 (balanceProgram .python) (pyStage b n 206 136 33) (closureFrame (pyClosure 5))
   (pyClosure 5).params (pyClosure 5).pythonDefaults [.string "balance - event.amount",.object 135] =
   .ok ⟨pyStage b n 208 136 33,pyWorldFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 5).body = pyWorldBody := by
   change balanceSourceBody (balanceProgram .python) "module.evaluate_world" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem py_world_run (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 58 (balanceProgram .python) (pyStage b n 204 135 33) pyEffectFrame pyWorldCall =
 .ok ⟨pyWorldResult b n,.ok (.number .pyFloat (b-n))⟩ := by
 rw [py_world_open,py_world_body_run b n hb hn hs]
 with_unfolding_all rfl

private def pyEffectValueMachine (b n : Int) : TargetMachine :=
 {pyWorldResult b n with cells := (pyWorldResult b n).cells.map fun (e : Nat × TargetValue) =>
   if e.1 == 158 then (158,.number .pyFloat (b-n)) else e}
private def pyEffectsDone (b n : Int) := pyStage b n 227 146 34 5 (.number .pyFloat (b-n)) true

private theorem py_effect_value_assign (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 59 (balanceProgram .python) (pyStage b n 204 135 33) pyEffectFrame
 (firstStmt (dropStmts 2 pyEffectBody)) = .ok ⟨pyEffectValueMachine b n,pyEffectFrame,.normal⟩ := by
 have shape : firstStmt (dropStmts 2 pyEffectBody) = .assign (.local "value") pyWorldCall := by
   with_unfolding_all rfl
 rw [shape]
 exact execAssign_existing_eq (py_world_run b n hb hn hs) (by with_unfolding_all rfl)
   (by with_unfolding_all rfl)

private theorem evalAnd_true_eq {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {a b : TargetExpr}
 (he : evalExpr k program m f a = .ok ⟨middle,.ok (.bool true)⟩) :
 evalExpr (k+1) program m f (.andThen a b) = evalExpr k program middle f b := by
 rw [evalExpr.eq_def]
 simp only [he,Bind.bind,Except.bind,sourceTruthy]
 rfl

private theorem evalBinary_eq {k : Nat} {program : TargetProgram} {m middle final : TargetMachine}
 {f : TargetFrame} {a b : TargetExpr} {av bv v : TargetValue} {op : BinaryOp}
 (hl : program.lang = .python) (ho : (op == .add) = false)
 (ha : evalExpr k program m f a = .ok ⟨middle,.ok av⟩)
 (hb : evalExpr k program middle f b = .ok ⟨final,.ok bv⟩)
 (hv : binaryValue .python final op av bv = .ok (.ok v)) :
 evalExpr (k+1) program m f (.binary op a b) = .ok ⟨final,.ok v⟩ := by
 rw [evalExpr.eq_def]
 simp only [ha,hb,hl,ho,Bind.bind,Except.bind,Bool.and_false,Bool.false_eq_true,↓reduceIte,hv]
 with_unfolding_all rfl

private theorem evalProperty_eq {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {receiver : TargetExpr} {value : TargetValue} {name : String}
 (he : evalExpr k program m f receiver = .ok ⟨middle,.ok value⟩) :
 evalExpr (k+1) program m f (.property receiver name) = readPropertyValue program.lang middle value name := by
 rw [evalExpr.eq_def]
 simp only [he,Bind.bind,Except.bind]

private theorem evalBoundHost_eq {k : Nat} {program : TargetProgram} {m middle bound : TargetMachine}
 {f : TargetFrame} {callee args : TargetExpr} {id : BuiltinId} {receiver : TargetValue} {values : List TargetValue}
 (he : evalExpr k program m f callee = .ok ⟨middle,.ok (.boundBuiltin id receiver)⟩)
 (ha : evalArgValues k program middle f args = .ok ⟨bound,.ok values⟩)
 (hi : (id == .arrayFind) = false ∧ (id == .arraySome) = false ∧ (id == .arrayMap) = false) :
 evalExpr (k+1) program m f (.call callee args) = hostCall program.lang bound id (some receiver) values := by
 rw [evalExpr.eq_def]
 simp only [he,ha,Bind.bind,Except.bind,hi.1,hi.2.1,hi.2.2,Bool.false_or,Bool.false_eq_true,↓reduceIte]

private theorem evalArgs_one {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {expr : TargetExpr} {value : TargetValue}
 (he : evalExpr (k+1) program m f expr = .ok ⟨middle,.ok value⟩) :
 evalArgValues (k+2) program m f (.sequence expr .empty) = .ok ⟨middle,.ok [value]⟩ := by
 rw [evalArgValues.eq_def]
 simp only [he,Bind.bind,Except.bind]
 rw [evalArgValues.eq_def]
 with_unfolding_all rfl

private theorem execReturn_eq {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {expr : TargetExpr} {value : TargetValue}
 (he : evalExpr k program m f expr = .ok ⟨middle,.ok value⟩) :
 execStmt (k+1) program m f (.returnValue expr) = .ok ⟨middle,f,.returned value⟩ := by
 rw [execStmt.eq_def]
 simp only [he,Bind.bind,Except.bind,Pure.pure,Except.pure]

private def pySafeBody := balanceSourceBody BalancePrograms.balancePyProgram "module._safe_integer"
private def pySafeCond := match firstStmt pySafeBody with | .returnValue e => e | _ => .undefined
private def pySafePrefix := match pySafeCond with | .andThen (.andThen e _) _ => e | _ => .undefined
private def pySafeInteger := match pySafeCond with | .andThen (.andThen _ e) _ => e | _ => .undefined
private def pySafeBoundExpr := match pySafeCond with | .andThen _ e => e | _ => .undefined
private def pySafeBound (b n : Int) : TargetMachine :=
 (allocCell (pyEffectValueMachine b n) (.number .pyFloat (b-n)) true).1
private def pySafeFrame : TargetFrame := {closureFrame (pyClosure 4) with locals := [("value",226)]}
private def pySafeTyped (b n : Int) : TargetMachine :=
 (allocObject (pySafeBound b n) ⟨.pythonTuple,none,[],[.builtin .int,.builtin .float],[],false,false⟩).1

private theorem py_safe_float (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 48 (balanceProgram .python) (pySafeTyped b n) pySafeFrame pyFloatExpr =
 .ok ⟨pySafeTyped b n,.ok (.number .pyFloat (b-n))⟩ := by
 have he : evalExpr 47 (balanceProgram .python) (pySafeTyped b n) pySafeFrame (.local "float") =
   .ok ⟨pySafeTyped b n,.ok (.builtin .float)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 47 (balanceProgram .python) (pySafeTyped b n) pySafeFrame (.sequence (.local "value") .empty) =
   .ok ⟨pySafeTyped b n,.ok [.number .pyFloat (b-n)]⟩ := by with_unfolding_all rfl
 rw [pyFloatExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_float_exact_tag _ _ _ hs]
 with_unfolding_all rfl

private theorem py_safe_prefix (b n : Int) :
 evalExpr 50 (balanceProgram .python) (pySafeBound b n) pySafeFrame pySafePrefix =
 .ok ⟨pySafeTyped b n,.ok (.bool true)⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_safe_integer (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 50 (balanceProgram .python) (pySafeTyped b n) pySafeFrame pySafeInteger =
 .ok ⟨pySafeTyped b n,.ok (.bool true)⟩ := by
 have he : evalExpr 49 (balanceProgram .python) (pySafeTyped b n) pySafeFrame
   (.property pyFloatExpr "is_integer") =
   .ok ⟨pySafeTyped b n,.ok (.boundBuiltin .isInteger (.number .pyFloat (b-n)))⟩ :=
   (evalProperty_eq (py_safe_float b n hs)).trans (by
     rw [balanceProgram_lang]
     with_unfolding_all rfl)
 have ha : evalArgValues 49 (balanceProgram .python) (pySafeTyped b n) pySafeFrame .empty =
   .ok ⟨pySafeTyped b n,.ok []⟩ := by with_unfolding_all rfl
 have shape : pySafeInteger = .call (.property pyFloatExpr "is_integer") .empty := by with_unfolding_all rfl
 rw [shape,evalBoundHost_eq he ha (by decide),balanceProgram_lang]
 with_unfolding_all rfl

private theorem py_safe_abs (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 50 (balanceProgram .python) (pySafeTyped b n) pySafeFrame
 (.call (.local "abs") (.sequence pyFloatExpr .empty)) =
 .ok ⟨pySafeTyped b n,.ok (.number .pyFloat (b-n).natAbs)⟩ := by
 have he : evalExpr 49 (balanceProgram .python) (pySafeTyped b n) pySafeFrame (.local "abs") =
   .ok ⟨pySafeTyped b n,.ok (.builtin .abs)⟩ := by with_unfolding_all rfl
 rw [evalHost_call_eq he (evalArgs_one (py_safe_float b n hs)) (by decide),balanceProgram_lang]
 with_unfolding_all rfl

private theorem py_safe_bound (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 51 (balanceProgram .python) (pySafeTyped b n) pySafeFrame pySafeBoundExpr =
 .ok ⟨pySafeTyped b n,.ok (.bool true)⟩ := by
 have hr : evalExpr 50 (balanceProgram .python) (pySafeTyped b n) pySafeFrame (.local "_MAX_INTEGER") =
   .ok ⟨pySafeTyped b n,.ok (.number .pyInt 9007199254740991)⟩ := by with_unfolding_all rfl
 have hv : binaryValue .python (pySafeTyped b n) .le (.number .pyFloat (b-n).natAbs) (.number .pyInt 9007199254740991) =
   .ok (.ok (.bool true)) := by
   have h : (↑(b-n).natAbs : Int) ≤ 9007199254740991 := by omega
   with_unfolding_all change (Except.ok (Except.ok (.bool (decide ((↑(b-n).natAbs : Int) ≤ 9007199254740991)))) : Except TargetError (Except TargetValue TargetValue)) = _
   rw [decide_eq_true h]
 have shape : pySafeBoundExpr = .binary .le (.call (.local "abs") (.sequence pyFloatExpr .empty)) (.local "_MAX_INTEGER") := by with_unfolding_all rfl
 rw [shape]
 exact evalBinary_eq (balanceProgram_lang .python) (by decide) (py_safe_abs b n hs) hr hv

private theorem py_safe_condition (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 52 (balanceProgram .python) (pySafeBound b n) pySafeFrame pySafeCond =
 .ok ⟨pySafeTyped b n,.ok (.bool true)⟩ := by
 have shape : pySafeCond = .andThen (.andThen pySafePrefix pySafeInteger) pySafeBoundExpr := by with_unfolding_all rfl
 have hi : evalExpr 51 (balanceProgram .python) (pySafeBound b n) pySafeFrame (.andThen pySafePrefix pySafeInteger) =
   .ok ⟨pySafeTyped b n,.ok (.bool true)⟩ :=
   (evalAnd_true_eq (py_safe_prefix b n)).trans (py_safe_integer b n hs)
 rw [shape,evalAnd_true_eq hi]
 exact py_safe_bound b n hs

private theorem seq_return {k : Nat} {program : TargetProgram} {m final : TargetMachine}
 {f ff : TargetFrame} {first rest : TargetStmt} {value : TargetValue}
 (he : execStmt k program m f first = .ok ⟨final,ff,.returned value⟩) :
 execStmt (k+1) program m f (.sequence first rest) = .ok ⟨final,ff,.returned value⟩ := by
 rw [execSequence_eq k,he]
 rfl

private theorem evalNot_bool {k : Nat} {program : TargetProgram} {m final : TargetMachine}
 {f : TargetFrame} {expr : TargetExpr} {value : Bool}
 (he : evalExpr k program m f expr = .ok ⟨final,.ok (.bool value)⟩) :
 evalExpr (k+1) program m f (.unary .not expr) = .ok ⟨final,.ok (.bool (!value))⟩ := by
 rw [evalExpr.eq_def]
 simp only [he,Bind.bind,Except.bind,sourceTruthy]
 with_unfolding_all rfl

private theorem evalConditional_bool {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {cond yes no : TargetExpr} {value : Bool}
 (he : evalExpr k program m f cond = .ok ⟨middle,.ok (.bool value)⟩) :
 evalExpr (k+1) program m f (.conditional cond yes no) =
 evalExpr k program middle f (if value then yes else no) := by
 rw [evalExpr.eq_def]
 simp only [he,Bind.bind,Except.bind,sourceTruthy]
 cases value <;> rfl

private def pySafeCall : TargetExpr := .call (.local "_safe_integer") (.sequence (.local "value") .empty)

private theorem py_safe_call (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 55 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame pySafeCall =
 .ok ⟨pySafeTyped b n,.ok (.bool true)⟩ := by
 have he : evalExpr 54 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame (.local "_safe_integer") =
   .ok ⟨pyEffectValueMachine b n,.ok (.closure 4)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 54 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame
   (.sequence (.local "value") .empty) = .ok ⟨pyEffectValueMachine b n,.ok [.number .pyFloat (b-n)]⟩ := by with_unfolding_all rfl
 have hc : closureAt (pyEffectValueMachine b n) 4 = .ok (pyClosure 4) := by with_unfolding_all rfl
 have hb : bindCallParams 54 (balanceProgram .python) (pyEffectValueMachine b n) (closureFrame (pyClosure 4))
   (pyClosure 4).params (pyClosure 4).pythonDefaults [.number .pyFloat (b-n)] =
   .ok ⟨pySafeBound b n,pySafeFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pySafeCall,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 4).body = pySafeBody := by
   change balanceSourceBody (balanceProgram .python) "module._safe_integer" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]
 have shape : pySafeBody = .sequence (.returnValue pySafeCond) .empty := by with_unfolding_all rfl
 rw [shape,seq_return (execReturn_eq (py_safe_condition b n hs))]
 with_unfolding_all rfl

private def pyEffectTypeCond := match firstStmt (dropStmts 3 pyEffectBody) with
 | .ifThenElse e _ _ => e | _ => .undefined
private def pyEffectStringCond := match pyEffectTypeCond with | .conditional e _ _ => e | _ => .undefined

private theorem py_effect_type (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 57 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame pyEffectTypeCond =
 .ok ⟨pySafeTyped b n,.ok (.bool false)⟩ := by
 have hc : evalExpr 56 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame pyEffectStringCond =
   .ok ⟨pyEffectValueMachine b n,.ok (.bool false)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have shape : pyEffectTypeCond = .conditional pyEffectStringCond
   (.binary .isNotIdentity (.call (.local "type") (.sequence (.local "value") .empty)) (.local "str"))
   (.unary .not pySafeCall) := by with_unfolding_all rfl
 rw [shape,evalConditional_bool hc]
 exact evalNot_bool (py_safe_call b n hs)

private theorem py_effect_type_skip (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 58 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame (firstStmt (dropStmts 3 pyEffectBody)) =
 .ok ⟨pySafeTyped b n,pyEffectFrame,.normal⟩ := by
 let yes := match firstStmt (dropStmts 3 pyEffectBody) with | .ifThenElse _ s _ => s | _ => .empty
 have shape : firstStmt (dropStmts 3 pyEffectBody) = .ifThenElse pyEffectTypeCond yes .empty := by with_unfolding_all rfl
 rw [shape,execIf_bool_eq (balanceProgram_lang .python) (py_effect_type b n hs)]
 with_unfolding_all rfl

private def pyEffectIntExpr : TargetExpr := .call (.local "int") (.sequence (.local "value") .empty)

private theorem py_effect_int (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 55 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame pyEffectIntExpr =
 .ok ⟨pySafeTyped b n,.ok (.number .pyInt (b-n))⟩ := by
 have he : evalExpr 54 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame (.local "int") =
   .ok ⟨pySafeTyped b n,.ok (.builtin .int)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 54 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame (.sequence (.local "value") .empty) =
   .ok ⟨pySafeTyped b n,.ok [.number .pyFloat (b-n)]⟩ := by with_unfolding_all rfl
 rw [pyEffectIntExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_int_exact _ _ hs]
 with_unfolding_all rfl

-- The remaining assignment is sliced at its value expression.
private def pyEffectAssignedExpr := match firstStmt (dropStmts 4 pyEffectBody) with | .assign _ e => e | _ => .undefined

private theorem py_effect_assigned_value (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 56 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame pyEffectAssignedExpr =
 .ok ⟨pySafeTyped b n,.ok (.number .pyInt (b-n))⟩ := by
 let cond := match pyEffectAssignedExpr with | .conditional c _ _ => c | _ => .undefined
 have hc : evalExpr 55 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame cond =
   .ok ⟨pySafeTyped b n,.ok (.bool false)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have shape : pyEffectAssignedExpr = .conditional cond (.local "value") pyEffectIntExpr := by with_unfolding_all rfl
 rw [shape,evalConditional_bool hc]
 exact py_effect_int b n hs

private theorem execAssignIndex_eq {k : Nat} {program : TargetProgram} {m m1 m2 m3 final : TargetMachine}
 {f : TargetFrame} {receiver key expr : TargetExpr} {ref : Nat} {name : String} {value : TargetValue}
 (hr : evalExpr k program m f receiver = .ok ⟨m1,.ok (.object ref)⟩)
 (hk : evalExpr k program m1 f key = .ok ⟨m2,.ok (.string name)⟩)
 (he : evalExpr k program m2 f expr = .ok ⟨m3,.ok value⟩)
 (hw : writeOwn m3 ref name value = .ok final) :
 execStmt (k+1) program m f (.assign (.index receiver key) expr) = .ok ⟨final,f,.normal⟩ := by
 rw [execStmt.eq_def]
 simp only [hr,hk,he,hw,Bind.bind,Except.bind,Pure.pure,Except.pure]

private theorem py_effect_commit (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 57 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame (firstStmt (dropStmts 4 pyEffectBody)) =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 let key : TargetExpr := .call (.property (.local "match") "group") (.sequence (.integer 1) .empty)
 have shape : firstStmt (dropStmts 4 pyEffectBody) = .assign (.index (.local "candidate") key) pyEffectAssignedExpr := by with_unfolding_all rfl
 have hr : evalExpr 56 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame (.local "candidate") =
   .ok ⟨pySafeTyped b n,.ok (.object 134)⟩ := by with_unfolding_all rfl
 have hk : evalExpr 56 (balanceProgram .python) (pySafeTyped b n) pyEffectFrame key =
   .ok ⟨pySafeTyped b n,.ok (.string "balance")⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape]
 exact execAssignIndex_eq hr hk (py_effect_assigned_value b n hs) (by with_unfolding_all rfl)

private theorem py_effect_tail (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 59 (balanceProgram .python) (pyEffectValueMachine b n) pyEffectFrame (dropStmts 3 pyEffectBody) =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 have shape : dropStmts 3 pyEffectBody = .sequence (firstStmt (dropStmts 3 pyEffectBody))
   (.sequence (firstStmt (dropStmts 4 pyEffectBody)) .empty) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_effect_type_skip b n hs),seq_after_normal (py_effect_commit b n hs)]
 with_unfolding_all rfl

private theorem py_effect_body (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 62 (balanceProgram .python) (pyStage b n 203 135 33) pyLoopFrame pyEffectBody =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 rw [execStepPrefix_normal 2 59 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_effect_prefix b n)]
 have shape : dropStmts 2 pyEffectBody = .sequence (firstStmt (dropStmts 2 pyEffectBody)) (dropStmts 3 pyEffectBody) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_effect_value_assign b n hb hn hs)]
 exact py_effect_tail b n hs

private def pyForOneBound (m : TargetMachine) (f : TargetFrame) (name : String) (value : TargetValue) : TargetMachine × TargetFrame :=
 ((allocCell m value true).1,{f with locals := (name,m.nextCell)::f.locals})

local macro "simp_py_for" : tactic => do
 let stem := (Lean.Name.num `_private.Harmonia.Applications.Kadmos.Generated.TargetSemantics 0) ++
   `Harmonia.Applications.Kadmos.Generated
 let loop := Lean.mkIdent (stem ++ `execForItems)
 let bind := Lean.mkIdent (stem ++ `bindLoopValue)
 let one := Lean.mkIdent (stem ++ `bindOne)
 `(tactic| simp only [$loop:ident,$bind:ident,$one:ident])

private theorem execFor_py_one {k : Nat} {program : TargetProgram} {m source final : TargetMachine}
 {f ff : TargetFrame} {iterable : TargetExpr} {body : TargetStmt} {name : String}
 {ref : Nat} {obj : HeapObject} {item : TargetValue}
 (hlang : program.lang = .python)
 (he : evalExpr (k+2) program m f iterable = .ok ⟨source,.ok (.object ref)⟩)
 (hl : objectAt source ref = .ok obj) (hk : obj.kind = .pythonTuple)
 (hi : obj.items = [item]) (hf : f.locals.lookup name = none)
 (hb : execStmt (k+1) program (pyForOneBound source f name item).1 (pyForOneBound source f name item).2 body =
   .ok ⟨final,ff,.normal⟩) :
 execStmt (k+3) program m f (.forDo [name] iterable body) = .ok ⟨final,ff,.normal⟩ := by
 rw [execStmt.eq_def]
 simp only [he,hl,hk,hi,Bind.bind,Except.bind]
 simp_py_for
 simp only [hlang,hf,show (TargetLang.python == TargetLang.python) = true from rfl,
   show (TargetLang.python == TargetLang.ts) = false from rfl,
   Bool.false_eq_true,↓reduceIte,Bind.bind,Except.bind,Pure.pure,Except.pure]
 change (do
   let result ← execStmt (k+1) program (pyForOneBound source f name item).1 (pyForOneBound source f name item).2 body
   match result.control with
   | .normal | .continued "loop" => _
   | .broke "loop" => _
   | _ => _) = _
 rw [hb]
 simp only [Bind.bind,Except.bind,hlang] <;> rfl

private def pyEffectList : HeapObject := (objectAt (pyStage 0 0 202 135 33) 60).toOption.getD ⟨.pythonTuple,none,[],[],[],false,false⟩

private theorem py_effect_for (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 64 (balanceProgram .python) (pyStage b n 202 135 33) pyEffectsFrame pyEffectFor =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 let iterable : TargetExpr := .index (.local "transition") (.string "effects")
 have shape : pyEffectFor = .forDo ["effect"] iterable pyEffectBody := by with_unfolding_all rfl
 have he : evalExpr 63 (balanceProgram .python) (pyStage b n 202 135 33) pyEffectsFrame iterable =
   .ok ⟨pyStage b n 202 135 33,.ok (.object 60)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hl : objectAt (pyStage b n 202 135 33) 60 = .ok pyEffectList := by with_unfolding_all rfl
 have hk : pyEffectList.kind = .pythonTuple := by with_unfolding_all rfl
 have hi : pyEffectList.items = [.string "balance = balance - event.amount"] := by with_unfolding_all rfl
 rw [shape]
 exact execFor_py_one (balanceProgram_lang .python) he hl hk hi (by with_unfolding_all rfl)
   (by exact py_effect_body b n hb hn hs)

private def pyEffectProtected := protectedSyntax (firstStmt (restStmt pyEffects))

private theorem py_effects_protected (b n : Int)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 66 (balanceProgram .python) (pyStage b n 202 135 33) pyEffectsFrame pyEffectProtected.stmt =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 have shape : pyEffectProtected.body = .sequence pyEffectFor .empty := by with_unfolding_all rfl
 have body : execStmt 65 (balanceProgram .python) (pyStage b n 202 135 33) pyEffectsFrame pyEffectProtected.body =
   .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
   rw [shape,seq_after_normal (py_effect_for b n hb hn hs)]
   with_unfolding_all rfl
 exact protected_normal body (by
   have shape : pyEffectProtected.cleanup = .empty := by with_unfolding_all rfl
   rw [shape]
   with_unfolding_all rfl)

private theorem py_effects_prefix (b n : Int) (hp : 0<n)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 68 (balanceProgram .python) (pyPositiveGuardMachine b n) pyPositiveGuardFrame pyEffects =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 have shape : pyEffects = .sequence (firstStmt pyEffects) (.sequence pyEffectProtected.stmt .empty) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_candidate_execute b n hp),seq_after_normal (py_effects_protected b n hb hn hs)]
 with_unfolding_all rfl

private def pyPositivePrefix := takeStepStmts 3 pyPositiveTail

private theorem py_positive_prefix (b n : Int) (hp : 0<n)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 69 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame pyPositivePrefix =
 .ok ⟨pyEffectsDone b n,pyEffectFrame,.normal⟩ := by
 have shape : pyPositivePrefix = .sequence (firstStmt pyPositiveTail) pyEffects :=
   Eq.mpr (congrArg (fun p : ProtectedSyntax => takeStepStmts 3 (dropStmts 21 p.body) =
     .sequence (firstStmt (dropStmts 21 p.body)) (takeStepStmts 2 (restStmt (dropStmts 21 pyProtected.body))))
     py_protected_source) (by with_unfolding_all rfl)
 rw [shape,seq_after_normal (py_positive_guard_execute b n hn hp)]
 exact py_effects_prefix b n hp hb hn hs

private def pyPostTail := dropStmts 24 pyProtected.body

private theorem py_positive_tail_source : dropStmts 3 pyPositiveTail = pyPostTail :=
 (congrArg (fun p : ProtectedSyntax => dropStmts 3 (dropStmts 21 p.body)) py_protected_source).trans
   (by with_unfolding_all rfl)

private theorem py_positive_tail_cut (b n : Int) (hp : 0<n)
 (hb : b.natAbs ≤ 9007199254740991) (hn : n.natAbs ≤ 9007199254740991)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 69 (balanceProgram .python) (balanceStepPyPrefix b n) balanceStepPyPrefixFrame pyPositiveTail =
 execStmt 66 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame pyPostTail := by
 have shape : stepPrefixShape 3 pyPositiveTail = true :=
   Eq.mpr (congrArg (fun p : ProtectedSyntax => stepPrefixShape 3 (dropStmts 21 p.body) = true)
     py_protected_source) (by with_unfolding_all rfl)
 rw [execStepPrefix_normal 3 65 _ _ _ _ _ _ shape (py_positive_prefix b n hp hb hn hs),py_positive_tail_source]

private def pyBS (b n : Int) (nc no : Nat) : TargetMachine := pyStage b n nc no 35 5 (.number .pyFloat (b-n)) true
private def pyBoundsBody := balanceSourceBody BalancePrograms.balancePyProgram "WorldChecker._bounds"
private def pyBoundsFor := firstStmt pyBoundsBody
private def pyBoundsLoopBody := match pyBoundsFor with | .forDo _ _ s => s | _ => .empty
private def pyBoundsFrame : TargetFrame := {closureFrame (pyClosure 34) with locals := [("values",227)]}
private def pyBoundsLoopFrame : TargetFrame := {pyBoundsFrame with locals := [("definition",229),("name",228)]++pyBoundsFrame.locals}
private def pyBoundsValueFrame : TargetFrame := {pyBoundsLoopFrame with locals := ("value",230)::pyBoundsLoopFrame.locals}
private def pyBoundsSafeBound (b n : Int) : TargetMachine := pyBS b n 232 148
private def pyBoundsSafeTyped (b n : Int) : TargetMachine := pyBS b n 232 149
private def pyBoundsSafeFrame : TargetFrame := {closureFrame (pyClosure 4) with locals := [("value",231)]}
private theorem py_bounds_safe_float (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 48 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame pyFloatExpr =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyFloat (b-n))⟩ := by
 have he : evalExpr 47 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame (.local "float") =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.builtin .float)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 47 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame (.sequence (.local "value") .empty) =
   .ok ⟨pyBoundsSafeTyped b n,.ok [.number .pyInt (b-n)]⟩ := by with_unfolding_all rfl
 rw [pyFloatExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_float_exact_tag _ _ _ hs]
 with_unfolding_all rfl

private theorem py_bounds_safe_prefix (b n : Int) :
 evalExpr 50 (balanceProgram .python) (pyBoundsSafeBound b n) pyBoundsSafeFrame pySafePrefix =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_bounds_safe_integer (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 50 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame pySafeInteger =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
 have he : evalExpr 49 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame
   (.property pyFloatExpr "is_integer") =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.boundBuiltin .isInteger (.number .pyFloat (b-n)))⟩ :=
   (evalProperty_eq (py_bounds_safe_float b n hs)).trans (by
     rw [balanceProgram_lang]
     with_unfolding_all rfl)
 have ha : evalArgValues 49 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame .empty =
   .ok ⟨pyBoundsSafeTyped b n,.ok []⟩ := by with_unfolding_all rfl
 have shape : pySafeInteger = .call (.property pyFloatExpr "is_integer") .empty := by with_unfolding_all rfl
 rw [shape,evalBoundHost_eq he ha (by decide),balanceProgram_lang]
 with_unfolding_all rfl

private theorem py_bounds_safe_abs (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 50 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame
 (.call (.local "abs") (.sequence pyFloatExpr .empty)) =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyFloat (b-n).natAbs)⟩ := by
 have he : evalExpr 49 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame (.local "abs") =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.builtin .abs)⟩ := by with_unfolding_all rfl
 rw [evalHost_call_eq he (evalArgs_one (py_bounds_safe_float b n hs)) (by decide),balanceProgram_lang]
 with_unfolding_all rfl

private theorem py_bounds_safe_bound (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 51 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame pySafeBoundExpr =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
 have hr : evalExpr 50 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsSafeFrame (.local "_MAX_INTEGER") =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyInt 9007199254740991)⟩ := by with_unfolding_all rfl
 have hv : binaryValue .python (pyBoundsSafeTyped b n) .le (.number .pyFloat (b-n).natAbs) (.number .pyInt 9007199254740991) =
   .ok (.ok (.bool true)) := by
   have h : (↑(b-n).natAbs : Int) ≤ 9007199254740991 := by omega
   with_unfolding_all change (Except.ok (Except.ok (.bool (decide ((↑(b-n).natAbs : Int) ≤ 9007199254740991)))) : Except TargetError (Except TargetValue TargetValue)) = _
   rw [decide_eq_true h]
 have shape : pySafeBoundExpr = .binary .le (.call (.local "abs") (.sequence pyFloatExpr .empty)) (.local "_MAX_INTEGER") := by with_unfolding_all rfl
 rw [shape]
 exact evalBinary_eq (balanceProgram_lang .python) (by decide) (py_bounds_safe_abs b n hs) hr hv

private theorem py_bounds_safe_condition (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 52 (balanceProgram .python) (pyBoundsSafeBound b n) pyBoundsSafeFrame pySafeCond =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
 have shape : pySafeCond = .andThen (.andThen pySafePrefix pySafeInteger) pySafeBoundExpr := by with_unfolding_all rfl
 have hi : evalExpr 51 (balanceProgram .python) (pyBoundsSafeBound b n) pyBoundsSafeFrame (.andThen pySafePrefix pySafeInteger) =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ :=
   (evalAnd_true_eq (py_bounds_safe_prefix b n)).trans (py_bounds_safe_integer b n hs)
 rw [shape,evalAnd_true_eq hi]
 exact py_bounds_safe_bound b n hs

private theorem py_bounds_safe_call (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 55 (balanceProgram .python) (pyBS b n 231 148) pyBoundsValueFrame pySafeCall =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
 have he : evalExpr 54 (balanceProgram .python) (pyBS b n 231 148) pyBoundsValueFrame (.local "_safe_integer") =
   .ok ⟨pyBS b n 231 148,.ok (.closure 4)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 54 (balanceProgram .python) (pyBS b n 231 148) pyBoundsValueFrame
   (.sequence (.local "value") .empty) = .ok ⟨pyBS b n 231 148,.ok [.number .pyInt (b-n)]⟩ := by with_unfolding_all rfl
 have hc : closureAt (pyBS b n 231 148) 4 = .ok (pyClosure 4) := by with_unfolding_all rfl
 have hb : bindCallParams 54 (balanceProgram .python) (pyBS b n 231 148) (closureFrame (pyClosure 4))
   (pyClosure 4).params (pyClosure 4).pythonDefaults [.number .pyInt (b-n)] =
   .ok ⟨pyBoundsSafeBound b n,pyBoundsSafeFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pySafeCall,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 4).body = pySafeBody := by
   change balanceSourceBody (balanceProgram .python) "module._safe_integer" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]
 have shape : pySafeBody = .sequence (.returnValue pySafeCond) .empty := by with_unfolding_all rfl
 rw [shape,seq_return (execReturn_eq (py_bounds_safe_condition b n hs))]
 with_unfolding_all rfl

private def pyBoundsTypeCond := match firstStmt (dropStmts 1 pyBoundsLoopBody) with
 | .ifThenElse e _ _ => e | _ => .undefined
private def pyBoundsStringCond := match pyBoundsTypeCond with | .conditional e _ _ => e | _ => .undefined

private theorem py_bounds_type (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 57 (balanceProgram .python) (pyBS b n 231 148) pyBoundsValueFrame pyBoundsTypeCond =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool false)⟩ := by
 have hc : evalExpr 56 (balanceProgram .python) (pyBS b n 231 148) pyBoundsValueFrame pyBoundsStringCond =
   .ok ⟨pyBS b n 231 148,.ok (.bool false)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have shape : pyBoundsTypeCond = .conditional pyBoundsStringCond
   (.binary .isNotIdentity (.call (.local "type") (.sequence (.local "value") .empty)) (.local "str"))
   (.unary .not pySafeCall) := by with_unfolding_all rfl
 rw [shape,evalConditional_bool hc]
 exact evalNot_bool (py_bounds_safe_call b n hs)

private theorem py_bounds_type_skip (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 58 (balanceProgram .python) (pyBS b n 231 148) pyBoundsValueFrame (firstStmt (dropStmts 1 pyBoundsLoopBody)) =
 .ok ⟨pyBoundsSafeTyped b n,pyBoundsValueFrame,.normal⟩ := by
 let yes := match firstStmt (dropStmts 1 pyBoundsLoopBody) with | .ifThenElse _ s _ => s | _ => .empty
 have shape : firstStmt (dropStmts 1 pyBoundsLoopBody) = .ifThenElse pyBoundsTypeCond yes .empty := by with_unfolding_all rfl
 rw [shape,execIf_bool_eq (balanceProgram_lang .python) (py_bounds_type b n hs)]
 with_unfolding_all rfl

private theorem py_bounds_value (b n : Int) :
 execStmt 59 (balanceProgram .python) (pyBS b n 230 148) pyBoundsLoopFrame (firstStmt pyBoundsLoopBody) =
 .ok ⟨pyBS b n 231 148,pyBoundsValueFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem evalOr_bool_eq {k : Nat} {program : TargetProgram} {m middle : TargetMachine}
 {f : TargetFrame} {a b : TargetExpr} {value : Bool}
 (he : evalExpr k program m f a = .ok ⟨middle,.ok (.bool value)⟩) :
 evalExpr (k+1) program m f (.orElse a b) =
 if value then .ok ⟨middle,.ok (.bool true)⟩ else evalExpr k program middle f b := by
 rw [evalExpr.eq_def]
 simp only [he,Bind.bind,Except.bind,sourceTruthy]
 cases value <;> rfl

private def pyBoundsCond := match firstStmt (dropStmts 2 pyBoundsLoopBody) with | .ifThenElse e _ _ => e | _ => .undefined
private def pyBoundsMin := match pyBoundsCond with | .orElse e _ => e | _ => .undefined
private def pyBoundsMax := match pyBoundsCond with | .orElse _ e => e | _ => .undefined

private theorem py_bounds_min (b n : Int) :
 evalExpr 55 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsMin =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool (decide (b-n<0)))⟩ := by
 let has : TargetExpr := .binary .inObject (.string "min") (.local "definition")
 let comparison : TargetExpr := .binary .lt (.local "value") (.index (.local "definition") (.string "min"))
 have shape : pyBoundsMin = .andThen has comparison := by with_unfolding_all rfl
 have hh : evalExpr 54 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame has =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hl : evalExpr 53 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame (.local "value") =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyInt (b-n))⟩ := by with_unfolding_all rfl
 have hr : evalExpr 53 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame (.index (.local "definition") (.string "min")) =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyInt 0)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hv : binaryValue .python (pyBoundsSafeTyped b n) .lt (.number .pyInt (b-n)) (.number .pyInt 0) =
   .ok (.ok (.bool (decide (b-n<0)))) := by with_unfolding_all rfl
 rw [shape,evalAnd_true_eq hh]
 exact evalBinary_eq (balanceProgram_lang .python) (by decide) hl hr hv

private theorem py_bounds_max (b n : Int) :
 evalExpr 55 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsMax =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool (decide (9007199254740991<b-n)))⟩ := by
 let has : TargetExpr := .binary .inObject (.string "max") (.local "definition")
 let comparison : TargetExpr := .binary .gt (.local "value") (.index (.local "definition") (.string "max"))
 have shape : pyBoundsMax = .andThen has comparison := by with_unfolding_all rfl
 have hh : evalExpr 54 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame has =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hl : evalExpr 53 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame (.local "value") =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyInt (b-n))⟩ := by with_unfolding_all rfl
 have hr : evalExpr 53 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame (.index (.local "definition") (.string "max")) =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.number .pyInt 9007199254740991)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hv : binaryValue .python (pyBoundsSafeTyped b n) .gt (.number .pyInt (b-n)) (.number .pyInt 9007199254740991) =
   .ok (.ok (.bool (decide (9007199254740991<b-n)))) := by with_unfolding_all rfl
 rw [shape,evalAnd_true_eq hh]
 exact evalBinary_eq (balanceProgram_lang .python) (by decide) hl hr hv

private theorem py_bounds_condition_reject (b n : Int) (hlt : b<n) :
 evalExpr 56 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsCond =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
 have shape : pyBoundsCond = .orElse pyBoundsMin pyBoundsMax := by with_unfolding_all rfl
 have h : evalExpr 55 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsMin =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.bool true)⟩ := by
   rw [py_bounds_min,decide_eq_true (by omega : b-n<0)]
 rw [shape,evalOr_bool_eq h]
 rfl

private theorem py_bounds_condition_valid (b n : Int) (hle : n≤b) (hmax : b-n≤9007199254740991) :
 evalExpr 56 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsCond =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.bool false)⟩ := by
 have shape : pyBoundsCond = .orElse pyBoundsMin pyBoundsMax := by with_unfolding_all rfl
 have h : evalExpr 55 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsMin =
   .ok ⟨pyBoundsSafeTyped b n,.ok (.bool false)⟩ := by
   rw [py_bounds_min,decide_eq_false (by omega : ¬b-n<0)]
 rw [shape,evalOr_bool_eq h]
 change evalExpr 55 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame pyBoundsMax = _
 rw [py_bounds_max,decide_eq_false (by omega : ¬9007199254740991<b-n)]

private theorem py_bounds_if_reject (b n : Int) (hlt : b<n) :
 execStmt 57 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame (firstStmt (dropStmts 2 pyBoundsLoopBody)) =
 .ok ⟨pyBoundsSafeTyped b n,pyBoundsValueFrame,.returned (.string "balance")⟩ := by
 have shape : firstStmt (dropStmts 2 pyBoundsLoopBody) = .ifThenElse pyBoundsCond
   (.sequence (.returnValue (.local "name")) .empty) .empty := by with_unfolding_all rfl
 rw [shape,execIf_bool_eq (balanceProgram_lang .python) (py_bounds_condition_reject b n hlt)]
 with_unfolding_all rfl

private theorem py_bounds_if_valid (b n : Int) (hle : n≤b) (hmax : b-n≤9007199254740991) :
 execStmt 57 (balanceProgram .python) (pyBoundsSafeTyped b n) pyBoundsValueFrame (firstStmt (dropStmts 2 pyBoundsLoopBody)) =
 .ok ⟨pyBoundsSafeTyped b n,pyBoundsValueFrame,.normal⟩ := by
 have shape : firstStmt (dropStmts 2 pyBoundsLoopBody) = .ifThenElse pyBoundsCond
   (.sequence (.returnValue (.local "name")) .empty) .empty := by with_unfolding_all rfl
 rw [shape,execIf_bool_eq (balanceProgram_lang .python) (py_bounds_condition_valid b n hle hmax)]
 with_unfolding_all rfl

private theorem py_bounds_loop_reject (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hlt : b<n) :
 execStmt 60 (balanceProgram .python) (pyBS b n 230 148) pyBoundsLoopFrame pyBoundsLoopBody =
 .ok ⟨pyBoundsSafeTyped b n,pyBoundsValueFrame,.returned (.string "balance")⟩ := by
 have shape : pyBoundsLoopBody = .sequence (firstStmt pyBoundsLoopBody)
   (.sequence (firstStmt (dropStmts 1 pyBoundsLoopBody)) (.sequence (firstStmt (dropStmts 2 pyBoundsLoopBody)) .empty)) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_bounds_value b n),seq_after_normal (py_bounds_type_skip b n hs)]
 exact seq_return (py_bounds_if_reject b n hlt)

private theorem py_bounds_loop_valid (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) (hmax : b-n≤9007199254740991) :
 execStmt 60 (balanceProgram .python) (pyBS b n 230 148) pyBoundsLoopFrame pyBoundsLoopBody =
 .ok ⟨pyBoundsSafeTyped b n,pyBoundsValueFrame,.normal⟩ := by
 have shape : pyBoundsLoopBody = .sequence (firstStmt pyBoundsLoopBody)
   (.sequence (firstStmt (dropStmts 1 pyBoundsLoopBody)) (.sequence (firstStmt (dropStmts 2 pyBoundsLoopBody)) .empty)) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_bounds_value b n),seq_after_normal (py_bounds_type_skip b n hs),
   seq_after_normal (py_bounds_if_valid b n hle hmax)]
 with_unfolding_all rfl

private def pyForControl (m : TargetMachine) (f : TargetFrame) (control : ControlResult) : Except TargetError StmtOutcome :=
 match control with
 | .normal | .continued "loop" | .broke "loop" => .ok ⟨m,f,.normal⟩
 | _ => .ok ⟨m,f,control⟩
private def pyForBoundsBound (m : TargetMachine) (f : TargetFrame) (left right : TargetValue) : TargetMachine × TargetFrame :=
 let a := allocCell m left true
 let z := allocCell a.1 right true
 (z.1,{f with locals := ("definition",m.nextCell+1)::("name",m.nextCell)::f.locals})

local macro "simp_bounds_for" : tactic => do
 let stem := (Lean.Name.num `_private.Harmonia.Applications.Kadmos.Generated.TargetSemantics 0) ++
   `Harmonia.Applications.Kadmos.Generated
 let loop := Lean.mkIdent (stem ++ `execForItems)
 let bind := Lean.mkIdent (stem ++ `bindLoopValue)
 let one := Lean.mkIdent (stem ++ `bindOne)
 `(tactic| simp only [$loop:ident,$bind:ident,$one:ident])

private theorem execFor_py_bounds {k : Nat} {program : TargetProgram} {m source final : TargetMachine}
 {f ff : TargetFrame} {iterable : TargetExpr} {body : TargetStmt}
 {ref pairRef : Nat} {obj pair : HeapObject} {left right : TargetValue} {control : ControlResult}
 (hlang : program.lang = .python)
 (he : evalExpr (k+2) program m f iterable = .ok ⟨source,.ok (.object ref)⟩)
 (hl : objectAt source ref = .ok obj) (hk : obj.kind = .pythonList)
 (hi : obj.items = [.object pairRef]) (hp : objectAt source pairRef = .ok pair) (hv : pair.items = [left,right])
 (hf : f.locals.lookup "name" = none) (hd : f.locals.lookup "definition" = none)
 (hb : execStmt (k+1) program (pyForBoundsBound source f left right).1 (pyForBoundsBound source f left right).2 body =
   .ok ⟨final,ff,control⟩) :
 execStmt (k+3) program m f (.forDo ["name","definition"] iterable body) = pyForControl final ff control := by
 rw [execStmt.eq_def]
 simp only [he,hl,hk,hi,Bind.bind,Except.bind]
 simp_bounds_for
 simp only [hlang,hp,hv,hf,hd,show (TargetLang.python == TargetLang.python) = true from rfl,
   show (TargetLang.python == TargetLang.ts) = false from rfl,
   Bool.false_eq_true,↓reduceIte,Bind.bind,Except.bind,Pure.pure,Except.pure]
 have hd' : List.lookup "definition" (("name",(allocCell source left true).2)::f.locals) = none := by
   change f.locals.lookup "definition" = none
   exact hd
 rw [hd']
 dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
 change (do
   let result ← execStmt (k+1) program (pyForBoundsBound source f left right).1 (pyForBoundsBound source f left right).2 body
   match result.control with
   | .normal | .continued "loop" => _
   | .broke "loop" => _
   | _ => _) = _
 rw [hb]
 with_unfolding_all rfl

private def pyBoundsList : HeapObject := (objectAt (pyBS 0 0 228 148) 147).toOption.getD ⟨.pythonList,none,[],[],[],false,false⟩
private def pyBoundsPair : HeapObject := (objectAt (pyBS 0 0 228 148) 146).toOption.getD ⟨.pythonTuple,none,[],[],[],false,false⟩

private theorem py_bounds_for_control (b n : Int) (control : ControlResult)
 (hb : execStmt 60 (balanceProgram .python) (pyBS b n 230 148) pyBoundsLoopFrame pyBoundsLoopBody =
   .ok ⟨pyBoundsSafeTyped b n,pyBoundsValueFrame,control⟩) :
 execStmt 62 (balanceProgram .python) (pyBS b n 228 146) pyBoundsFrame pyBoundsFor =
 pyForControl (pyBoundsSafeTyped b n) pyBoundsValueFrame control := by
 let iterable : TargetExpr := .call (.property (.index (.local "_WORLD") (.string "context")) "items") .empty
 have shape : pyBoundsFor = .forDo ["name","definition"] iterable pyBoundsLoopBody := by with_unfolding_all rfl
 have he : evalExpr 61 (balanceProgram .python) (pyBS b n 228 146) pyBoundsFrame iterable =
   .ok ⟨pyBS b n 228 148,.ok (.object 147)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape]
 exact execFor_py_bounds (balanceProgram_lang .python) he (by with_unfolding_all rfl)
   (by with_unfolding_all rfl) (by with_unfolding_all rfl)
   (show objectAt (pyBS b n 228 148) 146 = .ok pyBoundsPair from by with_unfolding_all rfl)
   (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) hb

private def pyBoundsCall : TargetExpr := .call (.property (.local "self") "_bounds") (.sequence (.local "candidate") .empty)

private theorem py_bounds_open (b n : Int) :
 evalExpr 64 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame pyBoundsCall =
 (do let out ← execStmt 63 (balanceProgram .python) (pyBS b n 228 146) pyBoundsFrame pyBoundsBody
     closureResult .python out) := by
 have he : evalExpr 63 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame (.property (.local "self") "_bounds") =
   .ok ⟨pyBS b n 227 146,.ok (.closure 34)⟩ := by
   simp only [pyEffectsDone,pyBS,pyStage,balanceStepPyBoundsRejected,balanceStepPyPrefix,
     balanceCanonicalConstructed,balanceInvariantPyCopied,balanceInvariantPyReset,balanceInvariantPyBound,balanceInvariantPyFinal]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 63 (balanceProgram .python) (pyBS b n 227 146) pyEffectFrame (.sequence (.local "candidate") .empty) =
   .ok ⟨pyBS b n 227 146,.ok [.object 134]⟩ := by with_unfolding_all rfl
 have hc : closureAt (pyBS b n 227 146) 34 = .ok (pyClosure 34) := by with_unfolding_all rfl
 have hb : bindCallParams 63 (balanceProgram .python) (pyBS b n 227 146) (closureFrame (pyClosure 34))
   (pyClosure 34).params (pyClosure 34).pythonDefaults [.object 134] = .ok ⟨pyBS b n 228 146,pyBoundsFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pyBoundsCall,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 34).body = pyBoundsBody := by
   change balanceSourceBody (balanceProgram .python) "WorldChecker._bounds" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem py_bounds_reject (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hlt : b<n) :
 evalExpr 64 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame pyBoundsCall =
 .ok ⟨pyBoundsSafeTyped b n,.ok (.string "balance")⟩ := by
 rw [py_bounds_open]
 have shape : pyBoundsBody = .sequence pyBoundsFor (restStmt pyBoundsBody) := by with_unfolding_all rfl
 rw [shape,seq_return (py_bounds_for_control b n _ (py_bounds_loop_reject b n hs hlt))]
 with_unfolding_all rfl

private theorem py_bounds_valid (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) (hmax : b-n≤9007199254740991) :
 evalExpr 64 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame pyBoundsCall =
 .ok ⟨pyBoundsSafeTyped b n,.ok .null⟩ := by
 rw [py_bounds_open]
 have shape : pyBoundsBody = .sequence pyBoundsFor (restStmt pyBoundsBody) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_bounds_for_control b n _ (py_bounds_loop_valid b n hs hle hmax))]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private def pyAS (b n : Int) (nc no nk : Nat) (pos : Int := 0) (left : TargetValue := .undefined) : TargetMachine :=
 let m := balanceStepPyAccepted b n
 {pyEffectsDone b n with
  cells := (m.cells.drop (258-nc)).map fun e =>
    if e.1 == 243 then (243,.number .pyInt pos) else if e.1 == 247 then (247,left) else e
  objects := m.objects.drop (169-no)
  closures := m.closures.drop (37-nk)
  writableCells := m.writableCells.drop (258-nc)
  nextCell := nc, nextObject := no, nextClosure := nk }
private def pyAClosure (ref : Nat) : TargetClosure :=
 (closureAt (balanceStepPyAccepted 0 0) ref).toOption.getD ⟨"",[],[],.empty,[],none⟩
private def pyPostBoundsFrame : TargetFrame := {pyEffectFrame with locals := ("invalid",232)::pyEffectFrame.locals}
private def pyInvFrame : TargetFrame := {closureFrame (pyAClosure 35) with locals := [("event",235),("values",234),("state",233)]}
private def pyInvReadyFrame : TargetFrame := {pyInvFrame with locals := ("environment",236)::pyInvFrame.locals}
private def pyInvLoopFrame : TargetFrame := {pyInvReadyFrame with locals := ("invariant",237)::pyInvReadyFrame.locals}
private def pyInvWorldFrame : TargetFrame := {closureFrame (pyClosure 5) with locals := [("environment",239),("expression",238)]}
private def pyInvTokenFrame : TargetFrame := {pyInvWorldFrame with locals := [("match",242),("offset",241),("tokens",240)]++pyInvWorldFrame.locals}
private def pyInvWorldReadyFrame : TargetFrame := {pyInvTokenFrame with locals := [("parse",244),("position",243)]++pyInvTokenFrame.locals}
private def pyInvParseFrame : TargetFrame := {closureFrame (pyAClosure 36) with locals := [("minimum",245)]}
private def pyInvParseReadyFrame : TargetFrame := {pyInvParseFrame with locals := [("left",247),("token",246)]++pyInvParseFrame.locals}
private def pyInvArithmeticFrame : TargetFrame := {pyInvParseReadyFrame with locals := [("right",253),("rank",249),("operator",248)]++pyInvParseReadyFrame.locals}

private theorem py_inv_tokenization (b n : Int) :
 execStmt 51 (balanceProgram .python) (pyAS b n 240 150 36) pyInvWorldFrame (takeStepStmts 5 pyWorldBody) =
 .ok ⟨pyAS b n 243 151 36,pyInvTokenFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_parse_install (b n : Int) :
 execStmt 46 (balanceProgram .python) (pyAS b n 243 151 36) pyInvTokenFrame (takeStepStmts 2 (dropStmts 5 pyWorldBody)) =
 .ok ⟨pyAS b n 245 151 37,pyInvWorldReadyFrame,.normal⟩ := by
 simp only [pyAS,balanceStepPyAccepted,pyEffectsDone,pyStage,balanceStepPyBoundsRejected,balanceStepPyPrefix,
   balanceCanonicalConstructed,balanceInvariantPyCopied,balanceInvariantPyReset,balanceInvariantPyBound,balanceInvariantPyFinal]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_parse_prefix (b n : Int) :
 execStmt 41 (balanceProgram .python) (pyAS b n 246 151 37) pyInvParseFrame (takeStepStmts 5 pyParseBody) =
 .ok ⟨pyAS b n 248 153 37 1 (.number .pyInt (b-n)),pyInvParseReadyFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_loop_prefix (b n : Int) :
 execStmt 34 (balanceProgram .python) (pyAS b n 248 153 37 1 (.number .pyInt (b-n))) pyInvParseReadyFrame
 (takeStepStmts 5 pyParseLoopBody) =
 .ok ⟨pyAS b n 254 155 37 3 (.number .pyInt (b-n)),pyInvArithmeticFrame,.normal⟩ := by
 simp only [pyAS,balanceStepPyAccepted,pyEffectsDone,pyStage,balanceStepPyBoundsRejected,balanceStepPyPrefix,
   balanceCanonicalConstructed,balanceInvariantPyCopied,balanceInvariantPyReset,balanceInvariantPyBound,balanceInvariantPyFinal]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private def pyInvNumberLeftFrame : TargetFrame :=
 { closureFrame (pyClosure 2) with locals := [("value",254)] }
private theorem py_inv_number_left (b n : Int) (hx : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 21 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame pyNumberLeft =
 .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)), .ok (.number .pyFloat (b-n))⟩ := by
 have he : evalExpr 20 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (.local "_number") =
   .ok ⟨pyAS b n 254 157 37 3 (.number .pyInt (b-n)), .ok (.closure 2)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 20 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame
   (.sequence (.local "left") .empty) = .ok ⟨pyAS b n 254 157 37 3 (.number .pyInt (b-n)),.ok [.number .pyInt (b-n)]⟩ := by
   with_unfolding_all rfl
 have hc : closureAt (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) 2 = .ok (pyClosure 2) := by with_unfolding_all rfl
 have hb : bindCallParams 20 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) (closureFrame (pyClosure 2))
   (pyClosure 2).params (pyClosure 2).pythonDefaults [.number .pyInt (b-n)] =
   .ok ⟨pyAS b n 255 157 37 3 (.number .pyInt (b-n)),pyInvNumberLeftFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pyNumberLeft,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 2).body = pyNumberBody := by
   change balanceSourceBody (balanceProgram .python) "module._number" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]
 have hshape : pyNumberBody = .sequence (firstStmt pyNumberBody) (restStmt pyNumberBody) := by
   with_unfolding_all rfl
 have hp : execStmt 19 (balanceProgram .python) (pyAS b n 255 157 37 3 (.number .pyInt (b-n))) pyInvNumberLeftFrame (firstStmt pyNumberBody) =
   .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)),pyInvNumberLeftFrame,.normal⟩ := by
   simp only [pyAS,balanceStepPyAccepted,pyEffectsDone,pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal,
   pyEffects, pyEffectBody, pyEffectFor, pyPositiveTail, balanceStepProtected,
   balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source,
   pyWorldBody, pyParseBody, pyParseLoop, pyParseLoopBody]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hf : evalExpr 17 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) pyInvNumberLeftFrame pyFloatExpr =
   .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)),.ok (.number .pyFloat (b-n))⟩ := by
   have he : evalExpr 16 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) pyInvNumberLeftFrame (.local "float") =
     .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)),.ok (.builtin .float)⟩ := by with_unfolding_all rfl
   have ha : evalArgValues 16 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) pyInvNumberLeftFrame
     (.sequence (.local "value") .empty) = .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)),.ok [.number .pyInt (b-n)]⟩ := by
     with_unfolding_all rfl
   rw [pyFloatExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_float_exact_tag _ _ _ hx]
   with_unfolding_all rfl
 have ht : restStmt pyNumberBody = .sequence (.returnValue pyFloatExpr) .empty := by
   with_unfolding_all rfl
 rw [hshape,execSequence_eq 19,hp]
 dsimp only [Bind.bind,Except.bind]
 rw [ht,execSequence_eq 18,execStmt.eq_def]
 dsimp only
 rw [hf]
 with_unfolding_all rfl

private def pyInvNumberRightFrame : TargetFrame :=
 { closureFrame (pyClosure 2) with locals := [("value",255)] }
private theorem py_inv_number_right (b n : Int) (hx : (0 : Int).natAbs ≤ 9007199254740991) :
 evalExpr 21 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame pyNumberRight =
 .ok ⟨pyAS b n 256 159 37 3 (.number .pyInt (b-n)), .ok (.number .pyFloat 0)⟩ := by
 have he : evalExpr 20 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (.local "_number") =
   .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)), .ok (.closure 2)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 20 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame
   (.sequence (.local "right") .empty) = .ok ⟨pyAS b n 255 158 37 3 (.number .pyInt (b-n)),.ok [.number .pyFloat 0]⟩ := by
   with_unfolding_all rfl
 have hc : closureAt (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) 2 = .ok (pyClosure 2) := by with_unfolding_all rfl
 have hb : bindCallParams 20 (balanceProgram .python) (pyAS b n 255 158 37 3 (.number .pyInt (b-n))) (closureFrame (pyClosure 2))
   (pyClosure 2).params (pyClosure 2).pythonDefaults [.number .pyFloat 0] =
   .ok ⟨pyAS b n 256 158 37 3 (.number .pyInt (b-n)),pyInvNumberRightFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [pyNumberRight,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 2).body = pyNumberBody := by
   change balanceSourceBody (balanceProgram .python) "module._number" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]
 have hshape : pyNumberBody = .sequence (firstStmt pyNumberBody) (restStmt pyNumberBody) := by
   with_unfolding_all rfl
 have hp : execStmt 19 (balanceProgram .python) (pyAS b n 256 158 37 3 (.number .pyInt (b-n))) pyInvNumberRightFrame (firstStmt pyNumberBody) =
   .ok ⟨pyAS b n 256 159 37 3 (.number .pyInt (b-n)),pyInvNumberRightFrame,.normal⟩ := by
   simp only [pyAS,balanceStepPyAccepted,pyEffectsDone,pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
   balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
   balanceInvariantPyBound, balanceInvariantPyFinal,
   pyEffects, pyEffectBody, pyEffectFor, pyPositiveTail, balanceStepProtected,
   balanceStepSnapshots, balanceStepAfterBusy, balanceStep_stored_source,
   pyWorldBody, pyParseBody, pyParseLoop, pyParseLoopBody]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hf : evalExpr 17 (balanceProgram .python) (pyAS b n 256 159 37 3 (.number .pyInt (b-n))) pyInvNumberRightFrame pyFloatExpr =
   .ok ⟨pyAS b n 256 159 37 3 (.number .pyInt (b-n)),.ok (.number .pyFloat 0)⟩ := by
   have he : evalExpr 16 (balanceProgram .python) (pyAS b n 256 159 37 3 (.number .pyInt (b-n))) pyInvNumberRightFrame (.local "float") =
     .ok ⟨pyAS b n 256 159 37 3 (.number .pyInt (b-n)),.ok (.builtin .float)⟩ := by with_unfolding_all rfl
   have ha : evalArgValues 16 (balanceProgram .python) (pyAS b n 256 159 37 3 (.number .pyInt (b-n))) pyInvNumberRightFrame
     (.sequence (.local "value") .empty) = .ok ⟨pyAS b n 256 159 37 3 (.number .pyInt (b-n)),.ok [.number .pyFloat 0]⟩ := by
     with_unfolding_all rfl
   rw [pyFloatExpr,evalHost_call_eq he ha (by decide),balanceProgram_lang,host_float_exact_tag _ _ _ hx]
   with_unfolding_all rfl
 have ht : restStmt pyNumberBody = .sequence (.returnValue pyFloatExpr) .empty := by
   with_unfolding_all rfl
 rw [hshape,execSequence_eq 19,hp]
 dsimp only [Bind.bind,Except.bind]
 rw [ht,execSequence_eq 18,execStmt.eq_def]
 dsimp only
 rw [hf]
 with_unfolding_all rfl

private def pyInvArithmeticDone (b n : Int) := pyAS b n 256 159 37 3 (.bool true)

private theorem py_inv_comparison (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 evalExpr 22 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame
 (.binary .ge pyNumberLeft pyNumberRight) =
 .ok ⟨pyAS b n 256 159 37 3 (.number .pyInt (b-n)),.ok (.bool true)⟩ := by
 have hv : binaryValue .python (pyAS b n 256 159 37 3 (.number .pyInt (b-n))) .ge
   (.number .pyFloat (b-n)) (.number .pyFloat 0) = .ok (.ok (.bool true)) := by
   have h : 0 ≤ b-n := by omega
   with_unfolding_all change (Except.ok (Except.ok (.bool (decide (0≤b-n)))) : Except TargetError (Except TargetValue TargetValue)) = _
   rw [decide_eq_true h]
 exact evalBinary_eq (balanceProgram_lang .python) (by decide) (py_inv_number_left b n hs)
   (py_inv_number_right b n (by decide)) hv

private theorem py_inv_dispatch_conditions (b n : Int) (i : Nat) (hi : i≤3) :
 evalExpr (27-i) (balanceProgram .python) (pyAS b n 254 (155+min i 2) 37 3 (.number .pyInt (b-n)))
 pyInvArithmeticFrame (pyDispatchCond i) =
 .ok ⟨pyAS b n 254 (155+min (i+1) 2) 37 3 (.number .pyInt (b-n)),.ok (.bool (i==3))⟩ := by
 have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
 rcases hi with h|h|h|h <;> subst i <;>
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source] <;> with_unfolding_all rfl

private theorem py_inv_dispatch_skip (b n : Int) (i : Nat) (hi : i<3) :
 execStmt (28-i) (balanceProgram .python) (pyAS b n 254 (155+min i 2) 37 3 (.number .pyInt (b-n)))
 pyInvArithmeticFrame (pyDispatch i) =
 execStmt (27-i) (balanceProgram .python) (pyAS b n 254 (155+min (i+1) 2) 37 3 (.number .pyInt (b-n)))
 pyInvArithmeticFrame (pyDispatch (i+1)) := by
 have hf : 28-i=(27-i)+1 := by omega
 rw [hf,py_dispatch_shape i (by omega),execIf_bool_eq (balanceProgram_lang .python)
   (py_inv_dispatch_conditions b n i (by omega))]
 have h : (i==3)=false := by simp; omega
 rw [h]
 rfl

private theorem py_inv_compare_assign (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 23 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame
 (.assign (.local "left") (.binary .ge pyNumberLeft pyNumberRight)) =
 .ok ⟨pyInvArithmeticDone b n,pyInvArithmeticFrame,.normal⟩ :=
 execAssign_existing_eq (py_inv_comparison b n hs hle) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

private theorem py_inv_dispatch_run (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 29 (balanceProgram .python) (pyAS b n 254 155 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame
 (dropStmts 5 pyParseLoopBody) = .ok ⟨pyInvArithmeticDone b n,pyInvArithmeticFrame,.normal⟩ := by
 have he : evalExpr 24 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n)))
   pyInvArithmeticFrame (pyDispatchCond 3) =
   .ok ⟨pyAS b n 254 157 37 3 (.number .pyInt (b-n)),.ok (.bool true)⟩ := by
   simpa using py_inv_dispatch_conditions b n 3 (by decide)
 have hge : execStmt 25 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n)))
   pyInvArithmeticFrame (pyDispatch 3) = .ok ⟨pyInvArithmeticDone b n,pyInvArithmeticFrame,.normal⟩ := by
   rw [py_dispatch_shape 3 (by decide),execIf_bool_eq (balanceProgram_lang .python) he]
   have shape : pyDispatchYes 3 = .sequence (.assign (.local "left") (.binary .ge pyNumberLeft pyNumberRight)) .empty := by with_unfolding_all rfl
   change execStmt 24 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatchYes 3) = _
   rw [shape,seq_after_normal (py_inv_compare_assign b n hs hle)]
   with_unfolding_all rfl
 have h0 : execStmt 28 (balanceProgram .python) (pyAS b n 254 155 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatch 0) =
   execStmt 27 (balanceProgram .python) (pyAS b n 254 156 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatch 1) := by
   simpa using py_inv_dispatch_skip b n 0 (by decide)
 have h1 : execStmt 27 (balanceProgram .python) (pyAS b n 254 156 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatch 1) =
   execStmt 26 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatch 2) := by
   simpa using py_inv_dispatch_skip b n 1 (by decide)
 have h2 : execStmt 26 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatch 2) =
   execStmt 25 (balanceProgram .python) (pyAS b n 254 157 37 3 (.number .pyInt (b-n))) pyInvArithmeticFrame (pyDispatch 3) := by
   simpa using py_inv_dispatch_skip b n 2 (by decide)
 have shape : dropStmts 5 pyParseLoopBody = .sequence (pyDispatch 0) .empty := by with_unfolding_all rfl
 rw [shape,execSequence_eq 28,h0,h1,h2,hge]
 with_unfolding_all rfl

private theorem py_inv_loop_body_run (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 execStmt 34 (balanceProgram .python) (pyAS b n 248 153 37 1 (.number .pyInt (b-n)))
 pyInvParseReadyFrame pyParseLoopBody = .ok ⟨pyInvArithmeticDone b n,pyInvArithmeticFrame,.normal⟩ := by
 rw [execStepPrefix_normal 5 28 _ _ _ _ _ _ (by with_unfolding_all rfl)
   (py_inv_loop_prefix b n)]
 exact py_inv_dispatch_run b n hs hle

private theorem py_inv_parse_loop_run (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 execStmt 35 (balanceProgram .python) (pyAS b n 248 153 37 1 (.number .pyInt (b-n)))
 pyInvParseReadyFrame pyParseLoop = .ok ⟨pyInvArithmeticDone b n,pyInvArithmeticFrame,.normal⟩ := by
 let cond : TargetExpr := .binary .lt (.local "position") (.call (.local "len") (.sequence (.local "tokens") .empty))
 have shape : pyParseLoop = .whileDo cond pyParseLoopBody := by with_unfolding_all rfl
 have hc : evalExpr 34 (balanceProgram .python) (pyAS b n 248 153 37 1 (.number .pyInt (b-n)))
   pyInvParseReadyFrame cond = .ok ⟨pyAS b n 248 153 37 1 (.number .pyInt (b-n)),.ok (.bool true)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape,execWhile_normal_eq (balanceProgram_lang .python) hc (py_inv_loop_body_run b n hs hle)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_parse_body_run (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 execStmt 41 (balanceProgram .python) (pyAS b n 246 151 37) pyInvParseFrame pyParseBody =
 .ok ⟨pyInvArithmeticDone b n,pyInvArithmeticFrame,.returned (.bool true)⟩ := by
 rw [execStepPrefix_normal 5 35 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_inv_parse_prefix b n)]
 have shape : dropStmts 5 pyParseBody = .sequence pyParseLoop (restStmt (dropStmts 5 pyParseBody)) := by
   with_unfolding_all rfl
 rw [shape,seq_after_normal (py_inv_parse_loop_run b n hs hle)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_parse_open (b n : Int) :
 evalExpr 42 (balanceProgram .python) (pyAS b n 245 151 37) pyInvWorldReadyFrame (.call (.local "parse") .empty) =
 (do let out ← execStmt 41 (balanceProgram .python) (pyAS b n 246 151 37) pyInvParseFrame pyParseBody
     closureResult .python out) := by
 have he : evalExpr 41 (balanceProgram .python) (pyAS b n 245 151 37) pyInvWorldReadyFrame (.local "parse") =
   .ok ⟨pyAS b n 245 151 37,.ok (.closure 36)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 41 (balanceProgram .python) (pyAS b n 245 151 37) pyInvWorldReadyFrame .empty =
   .ok ⟨pyAS b n 245 151 37,.ok []⟩ := by with_unfolding_all rfl
 have hc : closureAt (pyAS b n 245 151 37) 36 = .ok (pyAClosure 36) := by with_unfolding_all rfl
 have hb : bindCallParams 41 (balanceProgram .python) (pyAS b n 245 151 37) (closureFrame (pyAClosure 36))
   (pyAClosure 36).params (pyAClosure 36).pythonDefaults [] = .ok ⟨pyAS b n 246 151 37,pyInvParseFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [evalCall_open_eq he ha hc hb]
 have hbody : (pyAClosure 36).body = pyParseBody := by
   change balanceSourceBody (balanceProgram .python) "module.evaluate_world.parse" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem py_inv_parse_run (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 evalExpr 42 (balanceProgram .python) (pyAS b n 245 151 37) pyInvWorldReadyFrame (.call (.local "parse") .empty) =
 .ok ⟨pyInvArithmeticDone b n,.ok (.bool true)⟩ := by
 rw [py_inv_parse_open,py_inv_parse_body_run b n hs hle]
 with_unfolding_all rfl

private def pyInvWorldCall : TargetExpr := .call (.local "evaluate_world")
 (.sequence (.index (.local "invariant") (.string "predicate")) (.sequence (.local "environment") .empty))
private def pyInvWorldResult (b n : Int) := pyAS b n 257 159 37 3 (.bool true)
private def pyInvWorldResultFrame : TargetFrame := {pyInvWorldReadyFrame with locals := ("result",256)::pyInvWorldReadyFrame.locals}

private theorem py_inv_world_result_assign (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 execStmt 43 (balanceProgram .python) (pyAS b n 245 151 37) pyInvWorldReadyFrame
 (.assign (.local "result") (.call (.local "parse") .empty)) =
 .ok ⟨pyInvWorldResult b n,pyInvWorldResultFrame,.normal⟩ :=
 (execAssign_fresh_eq (balanceProgram_lang .python) (py_inv_parse_run b n hs hle)
   (by with_unfolding_all rfl)).trans (by with_unfolding_all rfl)

private theorem py_inv_world_body_run (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 execStmt 51 (balanceProgram .python) (pyAS b n 240 150 36) pyInvWorldFrame pyWorldBody =
 .ok ⟨pyInvWorldResult b n,pyInvWorldResultFrame,.returned (.bool true)⟩ := by
 rw [execStepPrefix_normal 5 45 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_inv_tokenization b n)]
 rw [execStepPrefix_normal 2 43 _ _ _ _ _ _ (by with_unfolding_all rfl) (py_inv_parse_install b n)]
 have shape : dropStmts 2 (dropStmts 5 pyWorldBody) = .sequence
   (.assign (.local "result") (.call (.local "parse") .empty)) (restStmt (dropStmts 7 pyWorldBody)) := by
   with_unfolding_all rfl
 rw [shape,seq_after_normal (py_inv_world_result_assign b n hs hle)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_world_open (b n : Int) :
 evalExpr 52 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame pyInvWorldCall =
 (do let out ← execStmt 51 (balanceProgram .python) (pyAS b n 240 150 36) pyInvWorldFrame pyWorldBody
     closureResult .python out) := by
 let args : TargetExpr := match pyInvWorldCall with | .call _ a => a | _ => .empty
 have shape : pyInvWorldCall = .call (.local "evaluate_world") args := by with_unfolding_all rfl
 have he : evalExpr 51 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame (.local "evaluate_world") =
   .ok ⟨pyAS b n 238 150 36,.ok (.closure 5)⟩ := by with_unfolding_all rfl
 have ha : evalArgValues 51 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame args =
   .ok ⟨pyAS b n 238 150 36,.ok [.string "balance >= 0",.object 149]⟩ := by
   simp only [pyAS,balanceStepPyAccepted,pyEffectsDone,pyStage, balanceStepPyBoundsRejected, balanceStepPyPrefix,
     balanceCanonicalConstructed, balanceInvariantPyCopied, balanceInvariantPyReset,
     balanceInvariantPyBound, balanceInvariantPyFinal]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hc : closureAt (pyAS b n 238 150 36) 5 = .ok (pyClosure 5) := by with_unfolding_all rfl
 have hb : bindCallParams 51 (balanceProgram .python) (pyAS b n 238 150 36) (closureFrame (pyClosure 5))
   (pyClosure 5).params (pyClosure 5).pythonDefaults [.string "balance >= 0",.object 149] =
   .ok ⟨pyAS b n 240 150 36,pyInvWorldFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape,evalCall_open_eq he ha hc hb]
 have hbody : (pyClosure 5).body = pyWorldBody := by
   change balanceSourceBody (balanceProgram .python) "module.evaluate_world" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem py_inv_world_run (b n : Int)
 (hs : (b-n).natAbs ≤ 9007199254740991) (hle : n≤b) :
 evalExpr 52 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame pyInvWorldCall =
 .ok ⟨pyInvWorldResult b n,.ok (.bool true)⟩ := by
 rw [py_inv_world_open,py_inv_world_body_run b n hs hle]
 with_unfolding_all rfl

private def pyInvBody := balanceSourceBody BalancePrograms.balancePyProgram "WorldChecker._invariant"
private def pyInvFor := firstStmt (restStmt pyInvBody)
private def pyInvLoopBody := match pyInvFor with | .forDo _ _ s => s | _ => .empty
private def pyInvProtected := protectedSyntax (firstStmt pyInvLoopBody)

private theorem py_inv_check (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 evalExpr 53 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame
 (.binary .isNotIdentity pyInvWorldCall (.bool true)) =
 .ok ⟨pyInvWorldResult b n,.ok (.bool false)⟩ := by
 have hr : evalExpr 52 (balanceProgram .python) (pyInvWorldResult b n) pyInvLoopFrame (.bool true) =
   .ok ⟨pyInvWorldResult b n,.ok (.bool true)⟩ := by with_unfolding_all rfl
 exact evalBinary_eq (balanceProgram_lang .python) (by decide) (py_inv_world_run b n hs hle) hr
   (by with_unfolding_all rfl)

private theorem py_inv_try_body (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 55 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame pyInvProtected.body =
 .ok ⟨pyInvWorldResult b n,pyInvLoopFrame,.normal⟩ := by
 let yes : TargetStmt := match firstStmt pyInvProtected.body with | .ifThenElse _ s _ => s | _ => .empty
 have shape : pyInvProtected.body = .sequence
   (.ifThenElse (.binary .isNotIdentity pyInvWorldCall (.bool true)) yes .empty) .empty := by with_unfolding_all rfl
 rw [shape,execSequence_eq 54,execIf_bool_eq (balanceProgram_lang .python) (py_inv_check b n hs hle)]
 with_unfolding_all rfl

private theorem py_inv_loop (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 57 (balanceProgram .python) (pyAS b n 238 150 36) pyInvLoopFrame pyInvLoopBody =
 .ok ⟨pyInvWorldResult b n,pyInvLoopFrame,.normal⟩ := by
 have cleanup : pyInvProtected.cleanup = .empty := by with_unfolding_all rfl
 have hc : execStmt 55 (balanceProgram .python) (pyInvWorldResult b n) pyInvLoopFrame pyInvProtected.cleanup =
   .ok ⟨pyInvWorldResult b n,pyInvLoopFrame,.normal⟩ := by rw [cleanup]; with_unfolding_all rfl
 have hp := protected_normal (py_inv_try_body b n hs hle) hc
 have shape : pyInvLoopBody = .sequence pyInvProtected.stmt .empty := by with_unfolding_all rfl
 rw [shape,seq_after_normal hp]
 with_unfolding_all rfl

private def pyInvList : HeapObject := (objectAt (pyAS 0 0 237 150 36) 49).toOption.getD ⟨.pythonTuple,none,[],[],[],false,false⟩

private theorem py_inv_for (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 59 (balanceProgram .python) (pyAS b n 237 150 36) pyInvReadyFrame pyInvFor =
 .ok ⟨pyInvWorldResult b n,pyInvLoopFrame,.normal⟩ := by
 let iterable : TargetExpr := .index (.local "_WORLD") (.string "invariants")
 have shape : pyInvFor = .forDo ["invariant"] iterable pyInvLoopBody := by with_unfolding_all rfl
 have he : evalExpr 58 (balanceProgram .python) (pyAS b n 237 150 36) pyInvReadyFrame iterable =
   .ok ⟨pyAS b n 237 150 36,.ok (.object 49)⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 rw [shape]
 exact execFor_py_one (balanceProgram_lang .python) he
   (show objectAt (pyAS b n 237 150 36) 49 = .ok pyInvList from by with_unfolding_all rfl)
   (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
   (by exact py_inv_loop b n hs hle)

private theorem py_inv_environment (b n : Int) :
 execStmt 60 (balanceProgram .python) (pyAS b n 236 149 36) pyInvFrame (firstStmt pyInvBody) =
 .ok ⟨pyAS b n 237 150 36,pyInvReadyFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_inv_body (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 61 (balanceProgram .python) (pyAS b n 236 149 36) pyInvFrame pyInvBody =
 .ok ⟨pyInvWorldResult b n,pyInvLoopFrame,.returned .null⟩ := by
 have shape : pyInvBody = .sequence (firstStmt pyInvBody) (.sequence pyInvFor (dropStmts 2 pyInvBody)) := by with_unfolding_all rfl
 rw [shape,seq_after_normal (py_inv_environment b n),seq_after_normal (py_inv_for b n hs hle)]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private def pyInvCall : TargetExpr := .call (.property (.local "self") "_invariant")
 (.sequence (.index (.local "transition") (.string "to")) (.sequence (.local "candidate") (.sequence (.local "payload") .empty)))

private theorem py_inv_open (b n : Int) :
 evalExpr 62 (balanceProgram .python) (pyAS b n 233 149 35) pyPostBoundsFrame pyInvCall =
 (do let out ← execStmt 61 (balanceProgram .python) (pyAS b n 236 149 36) pyInvFrame pyInvBody
     closureResult .python out) := by
 let args : TargetExpr := match pyInvCall with | .call _ a => a | _ => .empty
 have he : evalExpr 61 (balanceProgram .python) (pyAS b n 233 149 35) pyPostBoundsFrame (.property (.local "self") "_invariant") =
   .ok ⟨pyAS b n 233 149 36,.ok (.closure 35)⟩ := by
   simp only [pyAS,balanceStepPyAccepted,pyEffectsDone,pyStage,balanceStepPyBoundsRejected,balanceStepPyPrefix,
     balanceCanonicalConstructed,balanceInvariantPyCopied,balanceInvariantPyReset,balanceInvariantPyBound,balanceInvariantPyFinal]
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 61 (balanceProgram .python) (pyAS b n 233 149 36) pyPostBoundsFrame args =
   .ok ⟨pyAS b n 233 149 36,.ok [.string "Ready",.object 134,.object 114]⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have hc : closureAt (pyAS b n 233 149 36) 35 = .ok (pyAClosure 35) := by with_unfolding_all rfl
 have hb : bindCallParams 61 (balanceProgram .python) (pyAS b n 233 149 36) (closureFrame (pyAClosure 35))
   (pyAClosure 35).params (pyAClosure 35).pythonDefaults [.string "Ready",.object 134,.object 114] =
   .ok ⟨pyAS b n 236 149 36,pyInvFrame,.ok ()⟩ := by
   simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   with_unfolding_all rfl
 have shape : pyInvCall = .call (.property (.local "self") "_invariant") args := by with_unfolding_all rfl
 rw [shape,evalCall_open_eq he ha hc hb]
 have hbody : (pyAClosure 35).body = pyInvBody := by
   change balanceSourceBody (balanceProgram .python) "WorldChecker._invariant" = _
   rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem py_inv_run (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 evalExpr 62 (balanceProgram .python) (pyAS b n 233 149 35) pyPostBoundsFrame pyInvCall =
 .ok ⟨pyInvWorldResult b n,.ok .null⟩ := by
 rw [py_inv_open,py_inv_body b n hs hle]
 with_unfolding_all rfl

private def pyPostProtected (b n : Int) : Except TargetError StmtOutcome := do
 let p := pyProtected
 let attempted ← execStmt 66 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame pyPostTail
 let handled ← match attempted.control with
   | .raised errorValue =>
       if controlCaught p.catchType (.raised errorValue) then do
         let bound := bindCatchFrame attempted.machine attempted.frame p.binder errorValue
         let caught ← execStmt 90 (balanceProgram .python) bound.1 bound.2 p.handler
         pure {caught with frame := {caught.frame with control := .normal}}
       else pure attempted
   | _ => pure attempted
 let finalized ← execStmt 90 (balanceProgram .python) handled.machine handled.frame p.cleanup
 match finalized.control with
 | .normal => pure ⟨finalized.machine,finalized.frame,handled.control⟩
 | _ => pure finalized

private def pyPostSequence (b n : Int) : Except TargetError StmtOutcome := do
 let head ← pyPostProtected b n
 match head.control with
 | .normal => execStmt 91 (balanceProgram .python) head.machine head.frame .empty
 | _ => pure head

private def pyPost (b n : Int) : Except TargetError ExprOutcome := do
 let out ← pyPostSequence b n
 closureResult .python out

private theorem py_positive_continuation (b n : Int) (hp : 0<n)
 (hb : b.natAbs≤9007199254740991) (hn : n.natAbs≤9007199254740991)
 (hs : (b-n).natAbs≤9007199254740991)
 (hns : -Harmonia.Applications.Kadmos.S≤n ∧ n≤Harmonia.Applications.Kadmos.S) :
 evalExpr 100 (balanceProgram .python)
   (debitCallEntry .python (balanceCanonicalConstructed .python b) n).1
   (debitCallEntry .python (balanceCanonicalConstructed .python b) n).2
   (debitCallExpression .python) = pyPost b n := by
 rw [balanceStep_canonical_prefix_continuation .python b n hns]
 unfold balanceStepPrefixContinuation balanceStepSequenceContinuation balanceStepProtectedContinuation
 simp only [show (TargetLang.python == TargetLang.ts) = false from rfl,
   Bool.false_eq_true,↓reduceIte,balanceStepCanonicalPrefix]
 have hcut := py_positive_tail_cut b n hp hb hn hs
 dsimp only [pyPositiveTail] at hcut
 rw [hcut]
 simp only [py_protected_source]
 rfl

private def pyPostRejectMachine (b n : Int) := (allocCell (pyBoundsSafeTyped b n) (.string "balance") true).1

private theorem py_post_reject_assign (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hlt : b<n) :
 execStmt 65 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame (.assign (.local "invalid") pyBoundsCall) =
 .ok ⟨pyPostRejectMachine b n,pyPostBoundsFrame,.normal⟩ :=
 (execAssign_fresh_eq (balanceProgram_lang .python) (py_bounds_reject b n hs hlt)
   (by with_unfolding_all rfl)).trans (by with_unfolding_all rfl)

private theorem py_post_valid_assign (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) (hmax : b-n≤9007199254740991) :
 execStmt 65 (balanceProgram .python) (pyEffectsDone b n) pyEffectFrame (.assign (.local "invalid") pyBoundsCall) =
 .ok ⟨pyAS b n 233 149 35,pyPostBoundsFrame,.normal⟩ :=
 (execAssign_fresh_eq (balanceProgram_lang .python) (py_bounds_valid b n hs hle hmax)
   (by with_unfolding_all rfl)).trans (by with_unfolding_all rfl)

private theorem py_post_invalid_skip (b n : Int) :
 execStmt 64 (balanceProgram .python) (pyAS b n 233 149 35) pyPostBoundsFrame (firstStmt (restStmt pyPostTail)) =
 .ok ⟨pyAS b n 233 149 35,pyPostBoundsFrame,.normal⟩ := by
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private def pyPostInvFrame : TargetFrame := {pyPostBoundsFrame with locals := ("violated",257)::pyPostBoundsFrame.locals}
private def pyPostInvMachine (b n : Int) := pyAS b n 258 159 37 3 (.bool true)

private theorem py_post_inv_assign (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) :
 execStmt 63 (balanceProgram .python) (pyAS b n 233 149 35) pyPostBoundsFrame (.assign (.local "violated") pyInvCall) =
 .ok ⟨pyPostInvMachine b n,pyPostInvFrame,.normal⟩ :=
 (execAssign_fresh_eq (balanceProgram_lang .python) (py_inv_run b n hs hle)
   (by with_unfolding_all rfl)).trans (by with_unfolding_all rfl)

private theorem py_post_shape : pyPostTail = .sequence (.assign (.local "invalid") pyBoundsCall) (restStmt pyPostTail) := by
 with_unfolding_all rfl

private theorem py_post_reject (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hlt : b<n) :
 pyPost b n = .ok ⟨balanceStepPyBoundsRejected b n,.ok (.object 157)⟩ := by
 unfold pyPost pyPostSequence pyPostProtected
 rw [py_post_shape,seq_after_normal (py_post_reject_assign b n hs hlt)]
 simp only [pyPostRejectMachine,pyBoundsSafeTyped,pyBS,pyEffectsDone,pyStage,balanceStepPyBoundsRejected,
   balanceStepPyPrefix,balanceCanonicalConstructed,balanceInvariantPyCopied,balanceInvariantPyReset,
   balanceInvariantPyBound,balanceInvariantPyFinal]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_post_accept (b n : Int) (hs : (b-n).natAbs≤9007199254740991) (hle : n≤b) (hmax : b-n≤9007199254740991) :
 pyPost b n = .ok ⟨balanceStepPyAccepted b n,.ok (.object 167)⟩ := by
 unfold pyPost pyPostSequence pyPostProtected
 rw [py_post_shape,seq_after_normal (py_post_valid_assign b n hs hle hmax)]
 have shape1 : restStmt pyPostTail = .sequence (firstStmt (restStmt pyPostTail)) (dropStmts 2 pyPostTail) := by with_unfolding_all rfl
 have shape2 : dropStmts 2 pyPostTail = .sequence (.assign (.local "violated") pyInvCall) (dropStmts 3 pyPostTail) := by with_unfolding_all rfl
 rw [shape1,seq_after_normal (py_post_invalid_skip b n),shape2,seq_after_normal (py_post_inv_assign b n hs hle)]
 simp only [pyPostInvMachine,pyAS,pyEffectsDone,pyStage,balanceStepPyAccepted,balanceStepPyBoundsRejected,
   balanceStepPyPrefix,balanceCanonicalConstructed,balanceInvariantPyCopied,balanceInvariantPyReset,
   balanceInvariantPyBound,balanceInvariantPyFinal]
 simp only [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]
 with_unfolding_all rfl

private theorem py_difference_safe (b n : Int)
 (hb0 : 0≤b) (hbS : b≤Harmonia.Applications.Kadmos.S)
 (hn0 : 0<n) (hnS : n≤Harmonia.Applications.Kadmos.S) :
 (b-n).natAbs≤9007199254740991 := by
 apply signed_natAbs
 constructor <;> omega

/-- Positive safe DEBIT rejects an overdraft and executes the stored finally. -/
theorem balanceStep_py_bounds_reject_execute (b n : Int)
 (hb0 : 0≤b) (hbS : b≤Harmonia.Applications.Kadmos.S)
 (hn0 : 0<n) (hnS : n≤Harmonia.Applications.Kadmos.S) (hbn : b<n) :
 evalExpr 100 (balanceProgram .python)
   (debitCallEntry .python (balanceCanonicalConstructed .python b) n).1
   (debitCallEntry .python (balanceCanonicalConstructed .python b) n).2
   (debitCallExpression .python) = .ok ⟨balanceStepPyBoundsRejected b n,.ok (.object 157)⟩ := by
 rw [py_positive_continuation b n hn0 (signed_natAbs (by constructor <;> omega))
   (signed_natAbs (by constructor <;> omega)) (py_difference_safe b n hb0 hbS hn0 hnS) (by constructor <;> omega)]
 exact py_post_reject b n (py_difference_safe b n hb0 hbS hn0 hnS) hbn

/-- Positive safe DEBIT checks the invariant, commits, and executes finally. -/
theorem balanceStep_py_accept_execute (b n : Int)
 (hb0 : 0≤b) (hbS : b≤Harmonia.Applications.Kadmos.S)
 (hn0 : 0<n) (hnS : n≤Harmonia.Applications.Kadmos.S) (hbn : n≤b) :
 evalExpr 100 (balanceProgram .python)
   (debitCallEntry .python (balanceCanonicalConstructed .python b) n).1
   (debitCallEntry .python (balanceCanonicalConstructed .python b) n).2
   (debitCallExpression .python) = .ok ⟨balanceStepPyAccepted b n,.ok (.object 167)⟩ := by
 rw [py_positive_continuation b n hn0 (signed_natAbs (by constructor <;> omega))
   (signed_natAbs (by constructor <;> omega)) (py_difference_safe b n hb0 hbS hn0 hnS) (by constructor <;> omega)]
 exact py_post_accept b n (py_difference_safe b n hb0 hbS hn0 hnS) hbn (by change b-n≤Harmonia.Applications.Kadmos.S; omega)

theorem targetStep_py_bounds_reject (b n : Int)
 (hb0 : 0≤b) (hbS : b≤Harmonia.Applications.Kadmos.S)
 (hn0 : 0<n) (hnS : n≤Harmonia.Applications.Kadmos.S) (hbn : b<n) :
 targetStep (balanceProgram .python) (balanceCanonicalConstructed .python b) (canonicalDebitRequest .python n) =
 .ok (balanceStepPyBoundsRejectedOutcome b n) := by
 rw [targetStep_balance_entry .python _ (by constructor <;> omega),balanceStep_py_bounds_reject_execute b n hb0 hbS hn0 hnS hbn]
 rfl

theorem targetStep_py_accept (b n : Int)
 (hb0 : 0≤b) (hbS : b≤Harmonia.Applications.Kadmos.S)
 (hn0 : 0<n) (hnS : n≤Harmonia.Applications.Kadmos.S) (hbn : n≤b) :
 targetStep (balanceProgram .python) (balanceCanonicalConstructed .python b) (canonicalDebitRequest .python n) =
 .ok (balanceStepPyAcceptedOutcome b n) := by
 rw [targetStep_balance_entry .python _ (by constructor <;> omega),balanceStep_py_accept_execute b n hb0 hbS hn0 hnS hbn]
 rfl

end Harmonia.Applications.Kadmos.Generated
