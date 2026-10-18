import Harmonia.Applications.Kadmos.Generated.BalanceStepPositiveModels

/-! Positive canonical TS DEBIT execution. Bounded balances and positive safe
amounts give a safe subtraction; exact interpreter post-states include bounds
rejection or invariant-checked commitment and the original finally cleanup. -/
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false
set_option smartUnfolding false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option pp.maxSteps 100

private def positiveTail := dropStmts 18 (balanceStepProtected .ts).body

private def positiveGuardMachine (b n : Int) : TargetMachine :=
 (allocCell (balanceStepTsGuard b n) (.bool true) false).1

private def positiveGuardFrame : TargetFrame :=
 { balanceStepTsPrefixFrame with locals := ("guardVal", 123) :: balanceStepTsPrefixFrame.locals }

/-- Exact effect boundary, retaining all allocations before checkBounds. -/
private def positiveEffectsMachine (b n : Int) : TargetMachine :=
 let m := balanceStepTsBoundsRejected b n
 { balanceStepTsPrefix b n with
   cells := m.cells.drop 21
   objects := m.objects.drop 14
   closures := m.closures.drop 3
   writableCells := m.writableCells.drop 21
   nextCell := 155
   nextObject := 82
   nextClosure := 29 }

private def positiveEffectsFrame : TargetFrame :=
 { positiveGuardFrame with locals := ("candidate", 124) :: positiveGuardFrame.locals }

private theorem positive_guard_execute (b n : Int) (hp : 0 < n) :
 execStmt 72 (balanceProgram .ts) (balanceStepTsPrefix b n) balanceStepTsPrefixFrame
   (firstStmt positiveTail) = .ok ⟨positiveGuardMachine b n, positiveGuardFrame, .normal⟩ := by
  let tail := dropStmts 18 (balanceStepProtected .ts).body
  let p := protectedSyntax (firstStmt tail)
  let guardName := match firstStmt p.body with
    | .letLocal name _ _ => name
    | _ => ""
  have hseq : tail = .sequence (firstStmt tail) (restStmt tail) := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    with_unfolding_all rfl
  have htry : firstStmt tail = p.stmt := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    with_unfolding_all rfl
  have hbody : p.body = .sequence (firstStmt p.body) (restStmt p.body) := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    with_unfolding_all rfl
  have hassign : firstStmt p.body = .letLocal guardName false (balanceStepGuardExpression .ts) := by
    dsimp only [tail, p, guardName]
    simp only [balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
      balanceStepAfterBusy, balanceStep_stored_source]
    rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
    with_unfolding_all rfl
  change execStmt 72 (balanceProgram .ts) (balanceStepTsPrefix b n)
    balanceStepTsPrefixFrame (firstStmt tail) = _
  rw [htry, execProtectedSyntax_eq 71, hbody, execSequence_eq 70, hassign, execStmt.eq_def]
  dsimp only
  have hg := balanceStep_ts_guard_execute b n
  change evalExpr 69 (balanceProgram .ts) (balanceStepTsPrefix b n)
    balanceStepTsPrefixFrame (balanceStepGuardExpression .ts) = _ at hg
  rw [hg, decide_eq_true hp]
  simp only [tail, p, guardName, positiveGuardMachine, positiveGuardFrame,
    balanceStepGuardExpression, balanceStepProtected, balanceStepSnapshots,
    balanceStepAfterBusy, balanceStep_stored_source, balanceStepTsGuard,
    balanceStepTsPrefix, balanceStepTsPrefixFrame, balanceCanonicalConstructed,
    balanceInvariantTsCopied, balanceInvariantTsReset, balanceInvariantTsBound,
    balanceInvariantTsFinal]
  simp only [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
  simp only [decide_eq_true hp]
  with_unfolding_all rfl

/-- The numeric-call boundary excludes the six later cells and their permissions. -/
private def positiveArithmeticMachine (b n : Int) : TargetMachine :=
 let m := positiveEffectsMachine b n
 { m with cells := (m.cells.drop 6).map (fun e => if e.1 == 139 then (139, .number .jsNumber b) else e)
          objects := m.objects.map (fun e => if e.1 == 69 then (69, balanceHeapObject .ts m b) else e)
          writableCells := m.writableCells.drop 6
          nextCell := 149 }

private def positiveArithmeticFrame (b n : Int) : TargetFrame :=
 let m := positiveArithmeticMachine b n
 let c := (closureAt m 28).toOption.getD ⟨"", [], [], .empty, [], none⟩
 ⟨"module.evaluateWorld.parse", [], [("right",148),("rank",141),("operator",140),
   ("left",139),("token",138),("minimum",137)], c.captures, none, .normal⟩

private def numericLeft : TargetExpr := .call (.local "numeric") (.sequence (.local "left") .empty)
private def numericRight : TargetExpr := .call (.local "numeric") (.sequence (.local "right") .empty)

private def positiveArithmeticLeft (b n : Int) :=
 (allocCell (positiveArithmeticMachine b n) (.number .jsNumber b) true).1

private def positiveArithmeticRight (b n : Int) :=
 (allocCell (positiveArithmeticLeft b n) (.number .jsNumber n) true).1

private theorem positive_numeric_left (b n : Int) :
 evalExpr 23 (balanceProgram .ts) (positiveArithmeticMachine b n)
   (positiveArithmeticFrame b n) numericLeft =
   .ok ⟨positiveArithmeticLeft b n, .ok (.number .jsNumber b)⟩ := by
 simp only [positiveArithmeticMachine, positiveArithmeticFrame, positiveArithmeticLeft,
   numericLeft, positiveEffectsMachine, balanceStepTsBoundsRejected,
   balanceStepTsPrefix, balanceCanonicalConstructed, balanceInvariantTsCopied,
   balanceInvariantTsReset, balanceInvariantTsBound, balanceInvariantTsFinal]
 simp only [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem positive_numeric_right (b n : Int) :
 evalExpr 23 (balanceProgram .ts) (positiveArithmeticLeft b n)
   (positiveArithmeticFrame b n) numericRight =
   .ok ⟨positiveArithmeticRight b n, .ok (.number .jsNumber n)⟩ := by
 simp only [positiveArithmeticMachine, positiveArithmeticFrame, positiveArithmeticLeft,
   positiveArithmeticRight, numericRight, positiveEffectsMachine, balanceStepTsBoundsRejected,
   balanceStepTsPrefix, balanceCanonicalConstructed, balanceInvariantTsCopied,
   balanceInvariantTsReset, balanceInvariantTsBound, balanceInvariantTsFinal]
 simp only [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

/-- The effect parser reaches subtraction at fuel 24 after skipping ten switch labels. -/
private theorem positive_arithmetic_execute (b n : Int)
 (hs : (b - n).natAbs ≤ 9007199254740991) :
 evalExpr 24 (balanceProgram .ts) (positiveArithmeticMachine b n)
   (positiveArithmeticFrame b n) (.binary .sub numericLeft numericRight) =
   .ok ⟨positiveArithmeticRight b n, .ok (.number .jsNumber (b - n))⟩ := by
 rw [evalExpr.eq_def]
 dsimp only
 rw [positive_numeric_left]
 dsimp only [Bind.bind, Except.bind]
 rw [positive_numeric_right]
 dsimp only [Bind.bind, Except.bind]
 simp only [balanceProgram_lang]
 rw [binary_sub_js_safe _ b n hs]
 rfl

private def positiveEffectsSyntax : TargetStmt :=
TargetStmt.sequence
  (TargetStmt.letLocal
    "candidate"
    false
    (TargetExpr.object
      (TargetExpr.objectSpread
        (TargetExpr.property
          (TargetExpr.local "this")
          "#context")
        (TargetExpr.empty))))
  (TargetStmt.sequence
    (TargetStmt.tryCatchFinally
      (TargetStmt.sequence
        (TargetStmt.forDo
          ["effect"]
          (TargetExpr.property
            (TargetExpr.local "transition")
            "effects")
          (TargetStmt.sequence
            (TargetStmt.letLocal
              "match"
              false
              (TargetExpr.call
                (TargetExpr.property
                  (TargetExpr.regexLiteral
                    "/^([A-Za-z_][A-Za-z_0-9]*)\\s*=\\s*(.+)$/")
                  "exec")
                (TargetExpr.sequence
                  (TargetExpr.local "effect")
                  (TargetExpr.empty))))
            (TargetStmt.sequence
              (TargetStmt.ifThenElse
                (TargetExpr.orElse
                  (TargetExpr.unary
                    (UnaryOp.not)
                    (TargetExpr.local "match"))
                  (TargetExpr.unary
                    (UnaryOp.not)
                    (TargetExpr.call
                      (TargetExpr.property
                        (TargetExpr.local "Object")
                        "hasOwn")
                      (TargetExpr.sequence
                        (TargetExpr.property
                          (TargetExpr.local "world")
                          "context")
                        (TargetExpr.sequence
                          (TargetExpr.nonNull
                            (TargetExpr.index
                              (TargetExpr.local "match")
                              (TargetExpr.integer 1)))
                          (TargetExpr.empty))))))
                (TargetStmt.returnValue
                  (TargetExpr.call
                    (TargetExpr.local "reject")
                    (TargetExpr.sequence
                      (TargetExpr.string "INVALID_EFFECT")
                      (TargetExpr.sequence
                        (TargetExpr.string "Invalid effect assignment target")
                        (TargetExpr.empty)))))
                (TargetStmt.empty))
              (TargetStmt.sequence
                (TargetStmt.letLocal
                  "value"
                  false
                  (TargetExpr.call
                    (TargetExpr.local "evaluateWorld")
                    (TargetExpr.sequence
                      (TargetExpr.nonNull
                        (TargetExpr.index
                          (TargetExpr.local "match")
                          (TargetExpr.integer 2)))
                      (TargetExpr.sequence
                        (TargetExpr.call
                          (TargetExpr.local "env")
                          (TargetExpr.sequence
                            (TargetExpr.property
                              (TargetExpr.local "transition")
                              "to")
                            (TargetExpr.sequence
                              (TargetExpr.local "candidate")
                              (TargetExpr.empty))))
                        (TargetExpr.empty)))))
                (TargetStmt.sequence
                  (TargetStmt.ifThenElse
                    (TargetExpr.conditional
                      (TargetExpr.binary
                        (BinaryOp.strictEq)
                        (TargetExpr.property
                          (TargetExpr.nonNull
                            (TargetExpr.index
                              (TargetExpr.local "contextDefinitions")
                              (TargetExpr.nonNull
                                (TargetExpr.index
                                  (TargetExpr.local "match")
                                  (TargetExpr.integer 1)))))
                          "type")
                        (TargetExpr.string "string"))
                      (TargetExpr.binary
                        (BinaryOp.strictNe)
                        (TargetExpr.unary
                          (UnaryOp.typeof)
                          (TargetExpr.local "value"))
                        (TargetExpr.string "string"))
                      (TargetExpr.orElse
                        (TargetExpr.binary
                          (BinaryOp.strictNe)
                          (TargetExpr.unary
                            (UnaryOp.typeof)
                            (TargetExpr.local "value"))
                          (TargetExpr.string "number"))
                        (TargetExpr.unary
                          (UnaryOp.not)
                          (TargetExpr.call
                            (TargetExpr.property
                              (TargetExpr.local "Number")
                              "isSafeInteger")
                            (TargetExpr.sequence
                              (TargetExpr.local "value")
                              (TargetExpr.empty))))))
                    (TargetStmt.returnValue
                      (TargetExpr.call
                        (TargetExpr.local "reject")
                        (TargetExpr.sequence
                          (TargetExpr.string "INVALID_EFFECT")
                          (TargetExpr.sequence
                            (TargetExpr.string
                              "Effect expression has wrong type")
                            (TargetExpr.empty)))))
                    (TargetStmt.empty))
                  (TargetStmt.sequence
                    (TargetStmt.assign
                      (AssignTarget.index
                        (TargetExpr.local "candidate")
                        (TargetExpr.nonNull
                          (TargetExpr.index
                            (TargetExpr.local "match")
                            (TargetExpr.integer 1))))
                      (TargetExpr.typeCast
                        (TargetExpr.local "value")
                        "string|number"))
                    (TargetStmt.empty)))))))
        (TargetStmt.empty))
      (some "any")
      (some "e")
      (TargetStmt.sequence
        (TargetStmt.ifThenElse
          (TargetExpr.andThen
            (TargetExpr.binary
              (BinaryOp.instanceOf)
              (TargetExpr.local "e")
              (TargetExpr.local "Error"))
            (TargetExpr.call
              (TargetExpr.property
                (TargetExpr.property
                  (TargetExpr.local "e")
                  "message")
                "includes")
              (TargetExpr.sequence
                (TargetExpr.string "REENTRANCY_DETECTED")
                (TargetExpr.empty))))
          (TargetStmt.throwValue
            (TargetExpr.local "e"))
          (TargetStmt.empty))
        (TargetStmt.sequence
          (TargetStmt.returnValue
            (TargetExpr.call
              (TargetExpr.local "reject")
              (TargetExpr.sequence
                (TargetExpr.string "INVALID_EFFECT")
                (TargetExpr.sequence
                  (TargetExpr.string "Effect evaluation failed")
                  (TargetExpr.empty)))))
          (TargetStmt.empty)))
      (TargetStmt.empty))
    (TargetStmt.empty))

private theorem positive_effects_source :
 takeStepStmts 2 (restStmt positiveTail) = positiveEffectsSyntax := by
 simp only [positiveTail, balanceStepProtected, balanceStepSnapshots,
   balanceStepAfterBusy, balanceStep_stored_source]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private def positiveStage (b n : Int) (nc no nk : Nat) (ix : Int := 0) : TargetMachine :=
 let m := positiveArithmeticMachine b n
 { m with cells := (m.cells.drop (149-nc)).map (fun e => if e.1 == 134 then (134,.number .jsNumber ix) else e)
          objects := m.objects.drop (82-no)
          closures := m.closures.drop (29-nk)
          writableCells := m.writableCells.drop (149-nc)
          nextCell := nc, nextObject := no, nextClosure := nk }
private def effectLoop : TargetStmt :=
 match firstStmt (protectedSyntax (firstStmt (restStmt positiveEffectsSyntax))).body with
 | .forDo _ _ body => body
 | _ => .empty
private def loopFrame : TargetFrame :=
 { positiveEffectsFrame with locals := ("effect",125)::positiveEffectsFrame.locals }
private def effectFrame : TargetFrame :=
 { loopFrame with locals := ("match",126)::loopFrame.locals }
private def worldCall : TargetExpr := match firstStmt (dropStmts 2 effectLoop) with
 | .letLocal _ _ e => e
 | _ => .undefined
private def worldFrame : TargetFrame :=
 { closureFrame ((closureAt (positiveStage 0 0 131 73 27) 1).toOption.getD ⟨"",[],[],.empty,[],none⟩) with
   locals := [("env",130),("expression",129)] }
private def worldReadyFrame : TargetFrame :=
 { worldFrame with locals := [("parse",136),("numeric",135),("index",134),("priority",133),
   ("tokens",132),("pattern",131)] ++ worldFrame.locals }
private def parseEntryFrame (b n : Int) : TargetFrame :=
 { closureFrame ((closureAt (positiveArithmeticMachine b n) 28).toOption.getD ⟨"",[],[],.empty,[],none⟩) with
   locals := [("minimum",137)] }
private def parseReadyFrame (b n : Int) : TargetFrame :=
 { parseEntryFrame b n with locals := [("left",139),("token",138),("minimum",137)] }
private def worldBody := balanceSourceBody BalancePrograms.balanceTsProgram "module.evaluateWorld"
private def parseBody := balanceSourceBody BalancePrograms.balanceTsProgram "module.evaluateWorld.parse"
private def parseLoop := firstStmt (dropStmts 4 parseBody)
private def parseLoopBody := match parseLoop with | .whileDo _ body => body | _ => .empty
private def arithmeticDone (b n : Int) :=
 (writeCell (positiveArithmeticRight b n) 139 (.number .jsNumber (b-n))).toOption.getD (positiveArithmeticRight b n)
private theorem arithmetic_assign (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 25 (balanceProgram .ts) (positiveArithmeticMachine b n) (positiveArithmeticFrame b n)
 (.assign (.local "left") (.binary .sub numericLeft numericRight)) =
 .ok ⟨arithmeticDone b n, positiveArithmeticFrame b n, .normal⟩ := by
 rw [execStmt.eq_def]
 dsimp only
 rw [positive_arithmetic_execute b n hs]
 with_unfolding_all rfl
private def arithmeticSwitch := firstStmt (dropStmts 5 parseLoopBody)
private def minusBody : TargetStmt := .sequence
 (.assign (.local "left") (.binary .sub numericLeft numericRight))
 (.sequence (.breakTarget "switch") .empty)
private theorem minus_body (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 26 (balanceProgram .ts) (positiveArithmeticMachine b n) (positiveArithmeticFrame b n)
 minusBody = .ok ⟨arithmeticDone b n, positiveArithmeticFrame b n, .broke "switch"⟩ := by
 rw [minusBody, execSequence_eq 25, arithmetic_assign b n hs]
 with_unfolding_all rfl
local macro "switchEval" : term => do
 let stem := (Lean.Name.num `_private.Harmonia.Applications.Kadmos.Generated.TargetSemantics 0) ++
   `Harmonia.Applications.Kadmos.Generated
 return Lean.mkIdent (stem ++ `evalSwitchCases)
local macro "unfold_switch" : tactic => do
 let stem := (Lean.Name.num `_private.Harmonia.Applications.Kadmos.Generated.TargetSemantics 0) ++
   `Harmonia.Applications.Kadmos.Generated
 let eqn := Lean.mkIdent ((stem ++ `evalSwitchCases) ++ `eq_def)
 `(tactic| conv => lhs; rw [$eqn:ident])
private def dropSwitchCases : Nat → TargetStmt → TargetStmt
 | 0, s => s
 | k+1, .switchCase _ _ next => dropSwitchCases k next
 | _, s => s
private def arithmeticCases := match arithmeticSwitch with | .switchOn _ cases => cases | _ => .empty
private theorem arithmetic_switch (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 38 (balanceProgram .ts) (positiveArithmeticMachine b n) (positiveArithmeticFrame b n)
 arithmeticSwitch = .ok ⟨arithmeticDone b n, positiveArithmeticFrame b n, .normal⟩ := by
 have hop : evalExpr 37 (balanceProgram .ts) (positiveArithmeticMachine b n)
   (positiveArithmeticFrame b n) (.local "operator") =
   .ok ⟨positiveArithmeticMachine b n, .ok (.string "-")⟩ := by
   simp only [positiveArithmeticMachine, positiveArithmeticFrame, positiveArithmeticRight,
    positiveArithmeticLeft, positiveEffectsMachine, balanceStepTsBoundsRejected,
    balanceStepTsPrefix, balanceCanonicalConstructed, balanceInvariantTsCopied,
    balanceInvariantTsReset, balanceInvariantTsBound, balanceInvariantTsFinal]
   simp only [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have shape : arithmeticSwitch = .switchOn (.local "operator")
   (match arithmeticSwitch with | .switchOn _ cases => cases | _ => .empty) := by
  with_unfolding_all rfl
 rw [shape]
 conv => lhs; rw [execStmt.eq_def]
 dsimp only
 rw [hop]
 dsimp only [Bind.bind, Except.bind]
 have hskip : switchEval 37 (balanceProgram .ts) (positiveArithmeticMachine b n)
     (positiveArithmeticFrame b n) (.string "-") false arithmeticCases =
   switchEval 27 (balanceProgram .ts) (positiveArithmeticMachine b n)
     (positiveArithmeticFrame b n) (.string "-") false (dropSwitchCases 10 arithmeticCases) := by
   with_unfolding_all rfl
 change switchEval 37 (balanceProgram .ts) (positiveArithmeticMachine b n)
   (positiveArithmeticFrame b n) (.string "-") false arithmeticCases = _
 rw [hskip]
 have hminus : dropSwitchCases 10 arithmeticCases =
   .switchCase "-" minusBody (dropSwitchCases 11 arithmeticCases) := by
   with_unfolding_all rfl
 rw [hminus]
 unfold_switch
 dsimp only
 simp only [show (false || ((.string "-" : TargetValue) == .string "-")) = true from rfl,
   ↓reduceIte]
 rw [minus_body b n hs]
 rfl

private def parseResultMachine (b n : Int) : TargetMachine :=
 let m := positiveEffectsMachine b n
 { m with cells := m.cells.drop 2
          objects := (positiveArithmeticMachine b n).objects
          writableCells := m.writableCells.drop 2
          nextCell := 153 }
private def parseResultFrame (b n : Int) : TargetFrame :=
 { positiveArithmeticFrame b n with locals := [("rank",152),("operator",151)] ++ (positiveArithmeticFrame b n).locals }

private theorem candidate_run (b n : Int) (hp : 0 < n) :
 execStmt 71 (balanceProgram .ts) (positiveGuardMachine b n) positiveGuardFrame
 (firstStmt positiveEffectsSyntax) = .ok ⟨positiveStage b n 125 70 27, positiveEffectsFrame, .normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 simp only [positiveGuardMachine, balanceStepTsGuard, decide_eq_true hp]
 with_unfolding_all rfl
private theorem effect_prefix_run (b n : Int) :
 execStmt 66 (balanceProgram .ts) (positiveStage b n 126 70 27) loopFrame
 (takeStepStmts 2 effectLoop) = .ok ⟨positiveStage b n 127 72 27, effectFrame, .normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl
private theorem world_prefix_run (b n : Int) :
 execStmt 61 (balanceProgram .ts) (positiveStage b n 131 73 27) worldFrame
 (takeStepStmts 8 worldBody) = .ok ⟨positiveStage b n 137 77 29, worldReadyFrame, .normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl
private theorem parse_prefix_run (b n : Int) :
 execStmt 50 (balanceProgram .ts) (positiveStage b n 138 77 29) (parseEntryFrame b n)
 (takeStepStmts 4 parseBody) = .ok ⟨positiveStage b n 140 79 29 1, parseReadyFrame b n, .normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl
private theorem loop_prefix_run (b n : Int) :
 execStmt 44 (balanceProgram .ts) (positiveStage b n 140 79 29 1) (parseReadyFrame b n)
 (takeStepStmts 5 parseLoopBody) = .ok ⟨positiveArithmeticMachine b n, positiveArithmeticFrame b n, .normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

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

private def worldArgs : TargetExpr := match worldCall with | .call _ args => args | _ => .empty
private def envExpression : TargetExpr := match worldArgs with
 | .sequence _ (.sequence e _) => e | _ => .undefined
private def envArgs : TargetExpr := match envExpression with | .call _ args => args | _ => .empty
private def envClosure : TargetClosure :=
 (closureAt (positiveStage 0 0 127 72 27) 24).toOption.getD ⟨"",[],[],.empty,[],none⟩
private def envFrame : TargetFrame :=
 { closureFrame envClosure with locals := [("values",128),("at",127)] }
private def worldClosure : TargetClosure :=
 (closureAt (positiveStage 0 0 131 73 27) 1).toOption.getD ⟨"",[],[],.empty,[],none⟩
private def parseClosure : TargetClosure :=
 (closureAt (positiveStage 0 0 137 77 29) 28).toOption.getD ⟨"",[],[],.empty,[],none⟩

private theorem env_execute (b n : Int) :
 evalExpr 59 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame envExpression =
 .ok ⟨positiveStage b n 129 73 27, .ok (.object 72)⟩ := by
 have shape : envExpression = .call (.local "env") envArgs := by with_unfolding_all rfl
 have he : evalExpr 58 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame
   (.local "env") = .ok ⟨positiveStage b n 127 72 27, .ok (.closure 24)⟩ := by
   with_unfolding_all rfl
 have ha : evalArgValues 58 (balanceProgram .ts) (positiveStage b n 127 72 27)
   effectFrame envArgs = .ok ⟨positiveStage b n 127 72 27, .ok [.string "Ready",.object 69]⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have hc : closureAt (positiveStage b n 127 72 27) 24 = .ok envClosure := by
   with_unfolding_all rfl
 have hb : bindCallParams 58 (balanceProgram .ts) (positiveStage b n 127 72 27)
   (closureFrame envClosure) envClosure.params envClosure.pythonDefaults [.string "Ready",.object 69] =
   .ok ⟨positiveStage b n 129 72 27, envFrame, .ok ()⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [shape, evalCall_open_eq he ha hc hb]
 rw [balanceProgram_lang]
 change (do
   let r ← execStmt 58 (balanceProgram .ts) (positiveStage b n 129 72 27) envFrame
     (balanceSourceBody (balanceProgram .ts) "WorldChecker.step.env")
   closureResult .ts r) = _
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem world_open (b n : Int) :
 evalExpr 62 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame worldCall =
 (do let r ← execStmt 61 (balanceProgram .ts) (positiveStage b n 131 73 27) worldFrame worldBody
     closureResult .ts r) := by
 have shape : worldCall = .call (.local "evaluateWorld") worldArgs := by with_unfolding_all rfl
 have he : evalExpr 61 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame
   (.local "evaluateWorld") = .ok ⟨positiveStage b n 127 72 27,.ok (.closure 1)⟩ := by
   with_unfolding_all rfl
 have hf : evalExpr 60 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame
   (.nonNull (.index (.local "match") (.integer 2))) =
   .ok ⟨positiveStage b n 127 72 27,.ok (.string "balance - event.amount")⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 61 (balanceProgram .ts) (positiveStage b n 127 72 27)
   effectFrame worldArgs = .ok ⟨positiveStage b n 129 73 27,
    .ok [.string "balance - event.amount",.object 72]⟩ := by
   have shape : worldArgs = .sequence (.nonNull (.index (.local "match") (.integer 2)))
     (.sequence envExpression .empty) := by with_unfolding_all rfl
   rw [shape, evalArgValues.eq_def]
   dsimp only
   rw [hf]
   dsimp only [Bind.bind, Except.bind]
   rw [evalArgValues.eq_def]
   dsimp only
   rw [env_execute b n]
   with_unfolding_all rfl
 have hc : closureAt (positiveStage b n 129 73 27) 1 = .ok worldClosure := by
   with_unfolding_all rfl
 have hb : bindCallParams 61 (balanceProgram .ts) (positiveStage b n 129 73 27)
   (closureFrame worldClosure) worldClosure.params worldClosure.pythonDefaults
   [.string "balance - event.amount",.object 72] =
   .ok ⟨positiveStage b n 131 73 27, worldFrame, .ok ()⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [shape, evalCall_open_eq he ha hc hb]
 have hbody : worldClosure.body = worldBody := by
   change balanceSourceBody (balanceProgram .ts) "module.evaluateWorld" = _
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   rfl
 rw [hbody, balanceProgram_lang]

private theorem parse_open (b n : Int) :
 evalExpr 51 (balanceProgram .ts) (positiveStage b n 137 77 29) worldReadyFrame
   (.call (.local "parse") .empty) =
 (do let r ← execStmt 50 (balanceProgram .ts) (positiveStage b n 138 77 29)
       (parseEntryFrame b n) parseBody
     closureResult .ts r) := by
 have he : evalExpr 50 (balanceProgram .ts) (positiveStage b n 137 77 29) worldReadyFrame
   (.local "parse") = .ok ⟨positiveStage b n 137 77 29,.ok (.closure 28)⟩ := by
   with_unfolding_all rfl
 have ha : evalArgValues 50 (balanceProgram .ts) (positiveStage b n 137 77 29)
   worldReadyFrame .empty = .ok ⟨positiveStage b n 137 77 29,.ok []⟩ := by with_unfolding_all rfl
 have hc : closureAt (positiveStage b n 137 77 29) 28 = .ok parseClosure := by
   with_unfolding_all rfl
 have hb : bindCallParams 50 (balanceProgram .ts) (positiveStage b n 137 77 29)
   (closureFrame parseClosure) parseClosure.params parseClosure.pythonDefaults [] =
   .ok ⟨positiveStage b n 138 77 29, parseEntryFrame b n, .ok ()⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [evalCall_open_eq he ha hc hb]
 have hbody : parseClosure.body = parseBody := by
   change balanceSourceBody (balanceProgram .ts) "module.evaluateWorld.parse" = _
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   rfl
 rw [hbody, balanceProgram_lang]

private theorem loop_body_run (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 44 (balanceProgram .ts) (positiveStage b n 140 79 29 1) (parseReadyFrame b n)
 parseLoopBody = .ok ⟨arithmeticDone b n,positiveArithmeticFrame b n,.normal⟩ := by
 have shape : stepPrefixShape 5 parseLoopBody = true := by with_unfolding_all rfl
 rw [execStepPrefix_normal 5 38 (balanceProgram .ts) (positiveStage b n 140 79 29 1)
   (parseReadyFrame b n) parseLoopBody (positiveArithmeticMachine b n) (positiveArithmeticFrame b n)
   shape (loop_prefix_run b n)]
 have tail : dropStmts 5 parseLoopBody = .sequence arithmeticSwitch .empty := by
   with_unfolding_all rfl
 rw [tail,execSequence_eq 38,arithmetic_switch b n hs]
 with_unfolding_all rfl

private theorem parse_loop_run (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 45 (balanceProgram .ts) (positiveStage b n 140 79 29 1) (parseReadyFrame b n)
 parseLoop = .ok ⟨parseResultMachine b n,parseResultFrame b n,.normal⟩ := by
 have shape : parseLoop = .whileDo (.bool true) parseLoopBody := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 have hc : evalExpr 44 (balanceProgram .ts) (positiveStage b n 140 79 29 1)
   (parseReadyFrame b n) (.bool true) = .ok ⟨positiveStage b n 140 79 29 1,.ok (.bool true)⟩ := by with_unfolding_all rfl
 dsimp only
 rw [hc]
 simp only [Bind.bind,Except.bind,sourceTruthy,balanceProgram_lang]
 rw [loop_body_run b n hs]
 simp only [Bind.bind,Except.bind]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem parse_body_run (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 50 (balanceProgram .ts) (positiveStage b n 138 77 29) (parseEntryFrame b n)
 parseBody = .ok ⟨parseResultMachine b n,parseResultFrame b n,.returned (.number .jsNumber (b-n))⟩ := by
 have shape : stepPrefixShape 4 parseBody = true := by with_unfolding_all rfl
 rw [execStepPrefix_normal 4 45 (balanceProgram .ts) (positiveStage b n 138 77 29)
   (parseEntryFrame b n) parseBody (positiveStage b n 140 79 29 1) (parseReadyFrame b n)
   shape (parse_prefix_run b n)]
 have tail : dropStmts 4 parseBody = .sequence parseLoop (restStmt (dropStmts 4 parseBody)) := by
   with_unfolding_all rfl
 rw [tail,execSequence_eq 45,parse_loop_run b n hs]
 simp only [Bind.bind,Except.bind]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem parse_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 51 (balanceProgram .ts) (positiveStage b n 137 77 29) worldReadyFrame
 (.call (.local "parse") .empty) = .ok ⟨parseResultMachine b n,.ok (.number .jsNumber (b-n))⟩ := by
 rw [parse_open b n,parse_body_run b n hs]
 with_unfolding_all rfl

private def worldResultMachine (b n : Int) : TargetMachine :=
 (allocCell (parseResultMachine b n) (.number .jsNumber (b-n)) false).1

private def worldResultFrame : TargetFrame :=
 { worldReadyFrame with locals := ("result",153)::worldReadyFrame.locals }

private theorem world_body_run (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 61 (balanceProgram .ts) (positiveStage b n 131 73 27) worldFrame worldBody =
 .ok ⟨worldResultMachine b n,worldResultFrame,.returned (.number .jsNumber (b-n))⟩ := by
 have shape : stepPrefixShape 8 worldBody = true := by with_unfolding_all rfl
 rw [execStepPrefix_normal 8 52 (balanceProgram .ts) (positiveStage b n 131 73 27)
   worldFrame worldBody (positiveStage b n 137 77 29) worldReadyFrame
   shape (world_prefix_run b n)]
 have tail : dropStmts 8 worldBody = .sequence
   (.letLocal "result" false (.call (.local "parse") .empty)) (restStmt (dropStmts 8 worldBody)) := by
   with_unfolding_all rfl
 rw [tail,execSequence_eq 52]
 conv => lhs; arg 1; rw [execStmt.eq_def]
 dsimp only
 rw [parse_execute b n hs]
 simp only [Bind.bind,Except.bind]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem world_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 62 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame worldCall =
 .ok ⟨worldResultMachine b n,.ok (.number .jsNumber (b-n))⟩ := by
 rw [world_open b n,world_body_run b n hs]
 with_unfolding_all rfl

private theorem host_safe_integer (m : TargetMachine) (x : Int) (hs : x.natAbs ≤ 9007199254740991) :
 hostCall .ts m .jsIsSafeInteger none [.number .jsNumber x] = .ok ⟨m,.ok (.bool true)⟩ := by
 change (Except.ok (⟨m,.ok (.bool (decide (x.natAbs ≤ 9007199254740991)))⟩ : ExprOutcome) : Except TargetError ExprOutcome) = _
 rw [decide_eq_true hs]

private def effectValueMachine (b n : Int) : TargetMachine :=
 (allocCell (worldResultMachine b n) (.number .jsNumber (b-n)) false).1

private def effectValueFrame : TargetFrame :=
 { effectFrame with locals := ("value",154)::effectFrame.locals }

private def safeIntegerExpression : TargetExpr := .call (.property (.local "Number") "isSafeInteger")
 (.sequence (.local "value") .empty)

private def effectCondition : TargetExpr := match firstStmt (dropStmts 3 effectLoop) with
 | .ifThenElse cond _ _ => cond | _ => .undefined

private def notResult (r : ExprOutcome) : Except TargetError ExprOutcome := do
 match r.result with
 | .error e => pure ⟨r.machine,.error e⟩
 | .ok v =>
   let t ← sourceTruthy .ts r.machine v
   pure ⟨r.machine,.ok (.bool (!t))⟩

private theorem effect_safe_call (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 58 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame safeIntegerExpression =
 .ok ⟨effectValueMachine b n,.ok (.bool true)⟩ := by
 have he : evalExpr 57 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame
   (.property (.local "Number") "isSafeInteger") =
   .ok ⟨effectValueMachine b n,.ok (.builtin .jsIsSafeInteger)⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 57 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame
   (.sequence (.local "value") .empty) =
   .ok ⟨effectValueMachine b n,.ok [.number .jsNumber (b-n)]⟩ := by
   with_unfolding_all rfl
 rw [safeIntegerExpression,evalExpr.eq_def]
 dsimp only
 rw [he]
 dsimp only [Bind.bind,Except.bind]
 rw [ha]
 dsimp only [Bind.bind,Except.bind]
 change hostCall (balanceProgram .ts).lang (effectValueMachine b n) .jsIsSafeInteger none
   [.number .jsNumber (b-n)] = _
 rw [balanceProgram_lang,host_safe_integer _ _ hs]

private theorem effect_condition_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 61 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame effectCondition =
 .ok ⟨effectValueMachine b n,.ok (.bool false)⟩ := by
 have cut : evalExpr 61 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame effectCondition =
   (do let r ← evalExpr 58 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame safeIntegerExpression
       notResult r) := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [cut,effect_safe_call b n hs]
 with_unfolding_all rfl

private theorem effect_tail_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 63 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame (dropStmts 3 effectLoop) =
 .ok ⟨positiveEffectsMachine b n,effectValueFrame,.normal⟩ := by
 have shape : dropStmts 3 effectLoop = .sequence (firstStmt (dropStmts 3 effectLoop))
   (restStmt (dropStmts 3 effectLoop)) := by with_unfolding_all rfl
 have hif : execStmt 62 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame
   (firstStmt (dropStmts 3 effectLoop)) = .ok ⟨effectValueMachine b n,effectValueFrame,.normal⟩ := by
   have hshape : firstStmt (dropStmts 3 effectLoop) = .ifThenElse effectCondition
     (match firstStmt (dropStmts 3 effectLoop) with | .ifThenElse _ yes _ => yes | _ => .empty) .empty := by
     with_unfolding_all rfl
   rw [hshape,execStmt.eq_def]
   dsimp only
   rw [effect_condition_execute b n ‹(b-n).natAbs ≤ 9007199254740991›]
   simp only [Bind.bind,Except.bind,balanceProgram_lang,sourceTruthy]
   with_unfolding_all rfl
 rw [shape,execSequence_eq 62,hif]
 simp only [Bind.bind,Except.bind]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem effect_value_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 63 (balanceProgram .ts) (positiveStage b n 127 72 27) effectFrame
   (firstStmt (dropStmts 2 effectLoop)) = .ok ⟨effectValueMachine b n,effectValueFrame,.normal⟩ := by
 have shape : firstStmt (dropStmts 2 effectLoop) = .letLocal "value" false worldCall := by
   with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [world_execute b n hs]
 with_unfolding_all rfl

private theorem effect_loop_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 66 (balanceProgram .ts) (positiveStage b n 126 70 27) loopFrame effectLoop =
 .ok ⟨positiveEffectsMachine b n,effectValueFrame,.normal⟩ := by
 have shape : stepPrefixShape 2 effectLoop = true := by with_unfolding_all rfl
 rw [execStepPrefix_normal 2 63 (balanceProgram .ts) (positiveStage b n 126 70 27) loopFrame
   effectLoop (positiveStage b n 127 72 27) effectFrame shape (effect_prefix_run b n)]
 have tail : dropStmts 2 effectLoop = .sequence (firstStmt (dropStmts 2 effectLoop))
   (dropStmts 3 effectLoop) := by with_unfolding_all rfl
 rw [tail,execSequence_eq 63,effect_value_execute b n hs]
 change execStmt 63 (balanceProgram .ts) (effectValueMachine b n) effectValueFrame
   (dropStmts 3 effectLoop) = _
 exact effect_tail_execute b n hs

private def tsForControl (m : TargetMachine) (outer inner : TargetFrame) (control : ControlResult) : Except TargetError StmtOutcome :=
 match control with
 | .normal | .continued "loop" | .broke "loop" => .ok ⟨m,outer,.normal⟩
 | _ => .ok ⟨m,inner,control⟩

private def tsForOneBound (m : TargetMachine) (f : TargetFrame) (name : String) (v : TargetValue) : TargetMachine × TargetFrame :=
 let a := allocCell m v false
 (a.1,{f with locals := (name,a.2)::f.locals})

local macro "simp_for_primitives" : tactic => do
 let stem := (Lean.Name.num `_private.Harmonia.Applications.Kadmos.Generated.TargetSemantics 0) ++
   `Harmonia.Applications.Kadmos.Generated
 let loop := Lean.mkIdent (stem ++ `execForItems)
 let bind := Lean.mkIdent (stem ++ `bindLoopValue)
 let one := Lean.mkIdent (stem ++ `bindOne)
 `(tactic| simp only [$loop:ident,$bind:ident,$one:ident])

private theorem execForDo_ts_one_control {program m source final f ff listRef list name item k iterable body control}
 (hlang : program.lang = .ts)
 (he : evalExpr (k+2) program m f iterable = .ok ⟨source,.ok (.object listRef)⟩)
 (hl : objectAt source listRef = .ok list) (hk : list.kind = .jsArray)
 (hi : list.items = [item])
 (hb : execStmt (k+1) program (tsForOneBound source f name item).1
   (tsForOneBound source f name item).2 body = .ok ⟨final,ff,control⟩) :
 execStmt (k+3) program m f (.forDo [name] iterable body) =
 tsForControl final f ff control := by
 rw [execStmt,he]
 simp only [Bind.bind,Except.bind,hl,hk,hlang,List.forIn_cons]
 rw [hi]
 simp_for_primitives
 simp only [hlang, show (TargetLang.ts == .python) = false from rfl,
   Bool.false_eq_true,if_false,Bind.bind,Except.bind,Pure.pure,Except.pure]
 change (do
   let result ← execStmt (k+1) program (tsForOneBound source f name item).1
     (tsForOneBound source f name item).2 body
   match result.control with
   | .normal | .continued "loop" => _
   | .broke "loop" => _
   | _ => _) = _
 rw [hb]
 with_unfolding_all rfl

local macro "simp_pair_bind" hp:ident hv:ident hlang:ident : tactic => do
 let stem := (Lean.Name.num `_private.Harmonia.Applications.Kadmos.Generated.TargetSemantics 0) ++
   `Harmonia.Applications.Kadmos.Generated
 let loop := Lean.mkIdent (stem ++ `execForItems)
 let bind := Lean.mkIdent (stem ++ `bindLoopValue)
 let one := Lean.mkIdent (stem ++ `bindOne)
 `(tactic| simp only [$loop:ident,$bind:ident,$one:ident,$hp:ident,$hv:ident,$hlang:ident,
    show (TargetLang.ts == .python) = false from rfl,
    Bool.false_eq_true,if_false,Bind.bind,Except.bind,Pure.pure,Except.pure])

private theorem execForDo_ts_one_pair_control {program m source final f ff listRef pairRef list pair
 leftName rightName left right k iterable body control}
 (hlang : program.lang = .ts)
 (he : evalExpr (k+2) program m f iterable = .ok ⟨source,.ok (.object listRef)⟩)
 (hl : objectAt source listRef = .ok list) (hk : list.kind = .jsArray)
 (hi : list.items = [.object pairRef]) (hp : objectAt source pairRef = .ok pair)
 (hv : pair.items = [left,right])
 (hb : execStmt (k+1) program (tsForPairBound source f leftName rightName left right).1
   (tsForPairBound source f leftName rightName left right).2 body = .ok ⟨final,ff,control⟩) :
 execStmt (k+3) program m f (.forDo [leftName,rightName] iterable body) =
 tsForControl final f ff control := by
 rw [execStmt,he]
 simp only [Bind.bind,Except.bind,hl,hk,hlang,List.forIn_cons]
 rw [hi]
 simp_pair_bind hp hv hlang
 change (do
   let result ← execStmt (k+1) program (tsForPairBound source f leftName rightName left right).1
     (tsForPairBound source f leftName rightName left right).2 body
   match result.control with
   | .normal | .continued "loop" => _
   | .broke "loop" => _
   | _ => _) = _
 rw [hb]
 with_unfolding_all rfl

private def effectForStmt : TargetStmt := firstStmt
 (protectedSyntax (firstStmt (restStmt positiveEffectsSyntax))).body

private def effectIterable : TargetExpr := .property (.local "transition") "effects"

private def effectList : HeapObject :=
 (objectAt (positiveStage 0 0 125 70 27) 15).toOption.getD ⟨.jsArray,none,[],[],[],false,false⟩

private theorem effect_for_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 68 (balanceProgram .ts) (positiveStage b n 125 70 27) positiveEffectsFrame effectForStmt =
 .ok ⟨positiveEffectsMachine b n,positiveEffectsFrame,.normal⟩ := by
 have shape : effectForStmt = .forDo ["effect"] effectIterable effectLoop := by with_unfolding_all rfl
 have he : evalExpr 67 (balanceProgram .ts) (positiveStage b n 125 70 27) positiveEffectsFrame
   effectIterable = .ok ⟨positiveStage b n 125 70 27,.ok (.object 15)⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have hl : objectAt (positiveStage b n 125 70 27) 15 = .ok effectList := by with_unfolding_all rfl
 have hk : effectList.kind = .jsArray := by with_unfolding_all rfl
 have hi : effectList.items = [.string "balance = balance - event.amount"] := by with_unfolding_all rfl
 have hb : execStmt 66 (balanceProgram .ts)
   (tsForOneBound (positiveStage b n 125 70 27) positiveEffectsFrame "effect"
     (.string "balance = balance - event.amount")).1
   (tsForOneBound (positiveStage b n 125 70 27) positiveEffectsFrame "effect"
     (.string "balance = balance - event.amount")).2 effectLoop =
   .ok ⟨positiveEffectsMachine b n,effectValueFrame,.normal⟩ := by
   change execStmt 66 (balanceProgram .ts) (positiveStage b n 126 70 27) loopFrame effectLoop = _
   exact effect_loop_execute b n hs
 rw [shape,execForDo_ts_one_control (balanceProgram_lang .ts) he hl hk hi hb]
 rfl

private theorem positive_effects_execute (b n : Int) (hp : 0<n)
 (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 72 (balanceProgram .ts) (positiveGuardMachine b n) positiveGuardFrame
   (takeStepStmts 2 (restStmt positiveTail)) =
 .ok ⟨positiveEffectsMachine b n,positiveEffectsFrame,.normal⟩ := by
 rw [positive_effects_source]
 have shape : positiveEffectsSyntax = .sequence (firstStmt positiveEffectsSyntax)
   (restStmt positiveEffectsSyntax) := by with_unfolding_all rfl
 rw [shape,execSequence_eq 71,candidate_run b n hp]
 simp only [Bind.bind,Except.bind]
 let p := protectedSyntax (firstStmt (restStmt positiveEffectsSyntax))
 have hrest : restStmt positiveEffectsSyntax = .sequence p.stmt .empty := by
   with_unfolding_all rfl
 have hbody : p.body = .sequence effectForStmt .empty := by with_unfolding_all rfl
 rw [hrest,execSequence_eq 70,execProtectedSyntax_eq 69,hbody,execSequence_eq 68,
   effect_for_execute b n hs]
 with_unfolding_all rfl

private def boundsStage (b n : Int) (nc no nk : Nat) : TargetMachine :=
 let base := positiveEffectsMachine b n
 let m := balanceStepTsBoundsRejected b n
 { base with cells := m.cells.drop (176-nc), objects := m.objects.drop (96-no)
             closures := m.closures.drop (32-nk), writableCells := m.writableCells.drop (176-nc)
             nextCell := nc, nextObject := no, nextClosure := nk }

private def boundsClosure : TargetClosure :=
 (closureAt (boundsStage 0 0 155 82 30) 29).toOption.getD ⟨"",[],[],.empty,[],none⟩
private def boundsFrame : TargetFrame := {closureFrame boundsClosure with locals := [("values",155)]}
private def boundsLoopFrame : TargetFrame :=
 {boundsFrame with locals := [("definition",157),("key",156)] ++ boundsFrame.locals}
private def boundsValueFrame : TargetFrame :=
 {boundsLoopFrame with locals := ("value",158)::boundsLoopFrame.locals}
private def boundsBody := balanceSourceBody BalancePrograms.balanceTsProgram "WorldChecker.checkBounds"
private def boundsForStmt := firstStmt boundsBody
private def boundsIterable : TargetExpr := match boundsForStmt with | .forDo _ e _ => e | _ => .empty
private def boundsLoopBody : TargetStmt := match boundsForStmt with | .forDo _ _ s => s | _ => .empty
private def boundsTypeCondition : TargetExpr := match firstStmt (dropStmts 1 boundsLoopBody) with
 | .ifThenElse e _ _ => e | _ => .undefined
private def boundsMinCondition : TargetExpr := match firstStmt (dropStmts 2 boundsLoopBody) with
 | .ifThenElse e _ _ => e | _ => .undefined
private def boundsMaxCondition : TargetExpr := match firstStmt (dropStmts 3 boundsLoopBody) with
 | .ifThenElse e _ _ => e | _ => .undefined
private def boundsCall : TargetExpr := .call (.property (.local "this") "checkBounds")
 (.sequence (.local "candidate") .empty)

private theorem bounds_open (b n : Int) :
 evalExpr 68 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame boundsCall =
 (do let r ← execStmt 67 (balanceProgram .ts) (boundsStage b n 156 82 30) boundsFrame boundsBody
     closureResult .ts r) := by
 have he : evalExpr 67 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame
   (.property (.local "this") "checkBounds") =
   .ok ⟨boundsStage b n 155 82 30,.ok (.closure 29)⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 67 (balanceProgram .ts) (boundsStage b n 155 82 30)
   positiveEffectsFrame (.sequence (.local "candidate") .empty) =
   .ok ⟨boundsStage b n 155 82 30,.ok [.object 69]⟩ := by with_unfolding_all rfl
 have hc : closureAt (boundsStage b n 155 82 30) 29 = .ok boundsClosure := by with_unfolding_all rfl
 have hb : bindCallParams 67 (balanceProgram .ts) (boundsStage b n 155 82 30)
   (closureFrame boundsClosure) boundsClosure.params boundsClosure.pythonDefaults [.object 69] =
   .ok ⟨boundsStage b n 156 82 30,boundsFrame,.ok ()⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [boundsCall,evalCall_open_eq he ha hc hb]
 have hbody : boundsClosure.body = boundsBody := by
   change balanceSourceBody (balanceProgram .ts) "WorldChecker.checkBounds" = _
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem bounds_value_execute (b n : Int) :
 execStmt 63 (balanceProgram .ts) (boundsStage b n 158 84 30) boundsLoopFrame
   (firstStmt boundsLoopBody) = .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem bounds_safe_call (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 58 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame safeIntegerExpression =
 .ok ⟨boundsStage b n 159 84 30,.ok (.bool true)⟩ := by
 have he : evalExpr 57 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame
   (.property (.local "Number") "isSafeInteger") =
   .ok ⟨boundsStage b n 159 84 30,.ok (.builtin .jsIsSafeInteger)⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 57 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame
   (.sequence (.local "value") .empty) =
   .ok ⟨boundsStage b n 159 84 30,.ok [.number .jsNumber (b-n)]⟩ := by with_unfolding_all rfl
 rw [safeIntegerExpression,evalExpr.eq_def]
 dsimp only
 rw [he]
 dsimp only [Bind.bind,Except.bind]
 rw [ha]
 dsimp only [Bind.bind,Except.bind]
 change hostCall (balanceProgram .ts).lang (boundsStage b n 159 84 30) .jsIsSafeInteger none
   [.number .jsNumber (b-n)] = _
 rw [balanceProgram_lang,host_safe_integer _ _ hs]

private theorem bounds_type_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 evalExpr 61 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame boundsTypeCondition =
 .ok ⟨boundsStage b n 159 84 30,.ok (.bool false)⟩ := by
 have cut : evalExpr 61 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame boundsTypeCondition =
   (do let r ← evalExpr 58 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame safeIntegerExpression
       notResult r) := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [cut,bounds_safe_call b n hs]
 with_unfolding_all rfl

private theorem bounds_min_execute (b n : Int) :
 evalExpr 60 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame boundsMinCondition =
 .ok ⟨boundsStage b n 159 84 30,.ok (.bool (decide (b-n<0)))⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem bounds_max_execute (b n : Int) :
 evalExpr 59 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame boundsMaxCondition =
 .ok ⟨boundsStage b n 159 84 30,.ok (.bool (decide (9007199254740991<b-n)))⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem bounds_type_skip (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) :
 execStmt 62 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame
 (firstStmt (dropStmts 1 boundsLoopBody)) = .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.normal⟩ := by
 have shape : firstStmt (dropStmts 1 boundsLoopBody) = .ifThenElse boundsTypeCondition
   (.returnValue (.local "key")) .empty := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [bounds_type_execute b n hs]
 simp only [Bind.bind,Except.bind,balanceProgram_lang,sourceTruthy]
 with_unfolding_all rfl

private theorem bounds_min_reject (b n : Int) (hlt : b<n) :
 execStmt 61 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame
 (firstStmt (dropStmts 2 boundsLoopBody)) =
 .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.returned (.string "balance")⟩ := by
 have shape : firstStmt (dropStmts 2 boundsLoopBody) = .ifThenElse boundsMinCondition
   (.returnValue (.local "key")) .empty := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [bounds_min_execute b n,decide_eq_true (by omega : b-n<0)]
 simp only [Bind.bind,Except.bind,balanceProgram_lang,sourceTruthy]
 with_unfolding_all rfl

private theorem bounds_min_skip (b n : Int) (hle : n≤b) :
 execStmt 61 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame
 (firstStmt (dropStmts 2 boundsLoopBody)) = .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.normal⟩ := by
 have shape : firstStmt (dropStmts 2 boundsLoopBody) = .ifThenElse boundsMinCondition
   (.returnValue (.local "key")) .empty := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [bounds_min_execute b n,decide_eq_false (by omega : ¬b-n<0)]
 simp only [Bind.bind,Except.bind,balanceProgram_lang,sourceTruthy]
 with_unfolding_all rfl

private theorem bounds_max_skip (b n : Int) (hmax : b-n≤9007199254740991) :
 execStmt 60 (balanceProgram .ts) (boundsStage b n 159 84 30) boundsValueFrame
 (firstStmt (dropStmts 3 boundsLoopBody)) = .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.normal⟩ := by
 have shape : firstStmt (dropStmts 3 boundsLoopBody) = .ifThenElse boundsMaxCondition
   (.returnValue (.local "key")) .empty := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [bounds_max_execute b n,decide_eq_false (by omega : ¬9007199254740991<b-n)]
 simp only [Bind.bind,Except.bind,balanceProgram_lang,sourceTruthy]
 with_unfolding_all rfl

private theorem bounds_loop_reject (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) (hlt : b<n) :
 execStmt 64 (balanceProgram .ts) (boundsStage b n 158 84 30) boundsLoopFrame boundsLoopBody =
 .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.returned (.string "balance")⟩ := by
 have h0 : boundsLoopBody = .sequence (firstStmt boundsLoopBody) (restStmt boundsLoopBody) := by with_unfolding_all rfl
 have h1 : restStmt boundsLoopBody = .sequence (firstStmt (dropStmts 1 boundsLoopBody))
   (dropStmts 2 boundsLoopBody) := by with_unfolding_all rfl
 have h2 : dropStmts 2 boundsLoopBody = .sequence (firstStmt (dropStmts 2 boundsLoopBody))
   (dropStmts 3 boundsLoopBody) := by with_unfolding_all rfl
 rw [h0,execSequence_eq 63,bounds_value_execute b n]
 simp only [Bind.bind,Except.bind]
 rw [h1,execSequence_eq 62,bounds_type_skip b n hs]
 simp only [Bind.bind,Except.bind]
 rw [h2,execSequence_eq 61,bounds_min_reject b n hlt]
 with_unfolding_all rfl

private theorem bounds_loop_valid (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991)
 (hle : n≤b) (hmax : b-n≤9007199254740991) :
 execStmt 64 (balanceProgram .ts) (boundsStage b n 158 84 30) boundsLoopFrame boundsLoopBody =
 .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,.normal⟩ := by
 have h0 : boundsLoopBody = .sequence (firstStmt boundsLoopBody) (restStmt boundsLoopBody) := by with_unfolding_all rfl
 have h1 : restStmt boundsLoopBody = .sequence (firstStmt (dropStmts 1 boundsLoopBody))
   (dropStmts 2 boundsLoopBody) := by with_unfolding_all rfl
 have h2 : dropStmts 2 boundsLoopBody = .sequence (firstStmt (dropStmts 2 boundsLoopBody))
   (dropStmts 3 boundsLoopBody) := by with_unfolding_all rfl
 have h3 : dropStmts 3 boundsLoopBody = .sequence (firstStmt (dropStmts 3 boundsLoopBody)) .empty := by with_unfolding_all rfl
 rw [h0,execSequence_eq 63,bounds_value_execute b n]
 simp only [Bind.bind,Except.bind]
 rw [h1,execSequence_eq 62,bounds_type_skip b n hs]
 simp only [Bind.bind,Except.bind]
 rw [h2,execSequence_eq 61,bounds_min_skip b n hle]
 simp only [Bind.bind,Except.bind]
 rw [h3,execSequence_eq 60,bounds_max_skip b n hmax]
 with_unfolding_all rfl
private def boundsEntryList : HeapObject :=
 (objectAt (boundsStage 0 0 156 84 30) 83).toOption.getD ⟨.jsArray,none,[],[],[],false,false⟩
private def boundsEntryPair : HeapObject :=
 (objectAt (boundsStage 0 0 156 84 30) 82).toOption.getD ⟨.jsArray,none,[],[],[],false,false⟩

private theorem bounds_for_run (b n : Int) (control : ControlResult)
 (hloop : execStmt 64 (balanceProgram .ts) (boundsStage b n 158 84 30) boundsLoopFrame boundsLoopBody =
   .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,control⟩) :
 execStmt 66 (balanceProgram .ts) (boundsStage b n 156 82 30) boundsFrame boundsForStmt =
 tsForControl (boundsStage b n 159 84 30) boundsFrame boundsValueFrame control := by
 have shape : boundsForStmt = .forDo ["key","definition"] boundsIterable boundsLoopBody := by with_unfolding_all rfl
 have he : evalExpr 65 (balanceProgram .ts) (boundsStage b n 156 82 30) boundsFrame boundsIterable =
   .ok ⟨boundsStage b n 156 84 30,.ok (.object 83)⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have hl : objectAt (boundsStage b n 156 84 30) 83 = .ok boundsEntryList := by with_unfolding_all rfl
 have hk : boundsEntryList.kind = .jsArray := by with_unfolding_all rfl
 have hi : boundsEntryList.items = [.object 82] := by with_unfolding_all rfl
 have hp : objectAt (boundsStage b n 156 84 30) 82 = .ok boundsEntryPair := by with_unfolding_all rfl
 have hv : boundsEntryPair.items = [.string "balance",.object 11] := by with_unfolding_all rfl
 have hb : execStmt 64 (balanceProgram .ts)
   (tsForPairBound (boundsStage b n 156 84 30) boundsFrame "key" "definition" (.string "balance") (.object 11)).1
   (tsForPairBound (boundsStage b n 156 84 30) boundsFrame "key" "definition" (.string "balance") (.object 11)).2
   boundsLoopBody = .ok ⟨boundsStage b n 159 84 30,boundsValueFrame,control⟩ := by
   change execStmt 64 (balanceProgram .ts) (boundsStage b n 158 84 30) boundsLoopFrame boundsLoopBody = _
   exact hloop
 rw [shape,execForDo_ts_one_pair_control (balanceProgram_lang .ts) he hl hk hi hp hv hb]

private theorem bounds_reject_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) (hlt : b<n) :
 evalExpr 68 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame boundsCall =
 .ok ⟨boundsStage b n 159 84 30,.ok (.string "balance")⟩ := by
 rw [bounds_open b n]
 have shape : boundsBody = .sequence boundsForStmt (restStmt boundsBody) := by with_unfolding_all rfl
 rw [shape,execSequence_eq 66,bounds_for_run b n _ (bounds_loop_reject b n hs hlt)]
 with_unfolding_all rfl

private theorem bounds_valid_execute (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991)
 (hle : n≤b) (hmax : b-n≤9007199254740991) :
 evalExpr 68 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame boundsCall =
 .ok ⟨boundsStage b n 159 84 30,.ok .undefined⟩ := by
 rw [bounds_open b n]
 have shape : boundsBody = .sequence boundsForStmt (restStmt boundsBody) := by with_unfolding_all rfl
 rw [shape,execSequence_eq 66,bounds_for_run b n _ (bounds_loop_valid b n hs hle hmax)]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private def invariantStage (b n : Int) (nc no nk : Nat) (q : Bool := true) : TargetMachine :=
 let base := positiveEffectsMachine b n
 let m := balanceStepTsAccepted b n
 { base with
   cells := (m.cells.drop (203-nc)).map (fun e =>
     if e.1 == 175 || e.1 == 188 then (e.1,.bool q) else e)
   objects := (m.objects.drop (97-no)).take (no-82) ++ base.objects
   closures := (m.closures.drop (34-nk)).take (nk-29) ++ base.closures
   writableCells := m.writableCells.drop (203-nc)
   nextCell := nc, nextObject := no, nextClosure := nk }

private def invariantClosure : TargetClosure :=
 (closureAt (invariantStage 0 0 160 84 31) 30).toOption.getD ⟨"",[],[],.empty,[],none⟩
private def invariantFrame : TargetFrame :=
 {closureFrame invariantClosure with locals := [("event",162),("values",161),("atState",160)]}
private def invariantEnvFrame : TargetFrame :=
 {invariantFrame with locals := ("env",163)::invariantFrame.locals}
private def invariantEvalFrame : TargetFrame :=
 {invariantEnvFrame with locals := ("invariant",164)::invariantEnvFrame.locals}
private def invariantResultFrame : TargetFrame :=
 {invariantEvalFrame with locals := ("res",189)::invariantEvalFrame.locals}
private def invariantBody := balanceSourceBody BalancePrograms.balanceTsProgram "WorldChecker.checkInvariants"
private def invariantForStmt := firstStmt (restStmt invariantBody)
private def invariantIterable : TargetExpr := match invariantForStmt with | .forDo _ e _ => e | _ => .empty
private def invariantLoopBody : TargetStmt := match invariantForStmt with | .forDo _ _ s => s | _ => .empty
private def invariantTry := protectedSyntax (firstStmt invariantLoopBody)
private def invariantEvalExpr : TargetExpr := match firstStmt invariantTry.body with
 | .letLocal _ _ e => e | _ => .undefined

private theorem invariant_world_execute (b n : Int) :
 evalExpr 57 (balanceProgram .ts) (invariantStage b n 165 85 31) invariantEvalFrame invariantEvalExpr =
 .ok ⟨invariantStage b n 189 92 33 (decide (0≤b-n)),.ok (.bool (decide (0≤b-n)))⟩ := by
 dsimp only [invariantStage,invariantClosure,invariantFrame,invariantEnvFrame,
   invariantEvalFrame,invariantEvalExpr,invariantTry,invariantLoopBody,invariantForStmt,
   invariantBody,balanceStepTsAccepted,positiveEffectsMachine,balanceStepTsBoundsRejected,
   balanceStepTsPrefix,balanceCanonicalConstructed,balanceInvariantTsCopied,
   balanceInvariantTsReset,balanceInvariantTsBound,balanceInvariantTsFinal]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private def postBoundsFrame : TargetFrame :=
 {positiveEffectsFrame with locals := ("boundError",159)::positiveEffectsFrame.locals}
private def invariantCall : TargetExpr := .call (.property (.local "this") "checkInvariants")
 (.sequence (.property (.local "transition") "to")
   (.sequence (.local "candidate") (.sequence (.local "safePayload") .empty)))

private theorem invariant_open (b n : Int) :
 evalExpr 66 (balanceProgram .ts) (invariantStage b n 160 84 30) postBoundsFrame invariantCall =
 (do let r ← execStmt 65 (balanceProgram .ts) (invariantStage b n 163 84 31) invariantFrame invariantBody
     closureResult .ts r) := by
 have he : evalExpr 65 (balanceProgram .ts) (invariantStage b n 160 84 30) postBoundsFrame
   (.property (.local "this") "checkInvariants") =
   .ok ⟨invariantStage b n 160 84 31,.ok (.closure 30)⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have ha : evalArgValues 65 (balanceProgram .ts) (invariantStage b n 160 84 31) postBoundsFrame
   (.sequence (.property (.local "transition") "to")
     (.sequence (.local "candidate") (.sequence (.local "safePayload") .empty))) =
   .ok ⟨invariantStage b n 160 84 31,.ok [.string "Ready",.object 69,.object 53]⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 have hc : closureAt (invariantStage b n 160 84 31) 30 = .ok invariantClosure := by with_unfolding_all rfl
 have hb : bindCallParams 65 (balanceProgram .ts) (invariantStage b n 160 84 31)
   (closureFrame invariantClosure) invariantClosure.params invariantClosure.pythonDefaults
   [.string "Ready",.object 69,.object 53] =
   .ok ⟨invariantStage b n 163 84 31,invariantFrame,.ok ()⟩ := by
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [invariantCall,evalCall_open_eq he ha hc hb]
 have hbody : invariantClosure.body = invariantBody := by
   change balanceSourceBody (balanceProgram .ts) "WorldChecker.checkInvariants" = _
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   rfl
 rw [hbody,balanceProgram_lang]

private theorem invariant_env_execute (b n : Int) :
 execStmt 64 (balanceProgram .ts) (invariantStage b n 163 84 31) invariantFrame
   (firstStmt invariantBody) = .ok ⟨invariantStage b n 164 85 31,invariantEnvFrame,.normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem invariant_value_execute (b n : Int) (hle : n≤b) :
 execStmt 58 (balanceProgram .ts) (invariantStage b n 165 85 31) invariantEvalFrame
   (firstStmt invariantTry.body) = .ok ⟨invariantStage b n 190 92 33,invariantResultFrame,.normal⟩ := by
 have hEval := invariant_world_execute b n
 rw [decide_eq_true (by omega : 0≤b-n)] at hEval
 have shape : firstStmt invariantTry.body = .letLocal "res" false invariantEvalExpr := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [hEval]
 with_unfolding_all rfl

private theorem invariant_try_body_execute (b n : Int) (hle : n≤b) :
 execStmt 59 (balanceProgram .ts) (invariantStage b n 165 85 31) invariantEvalFrame
   invariantTry.body = .ok ⟨invariantStage b n 190 92 33,invariantResultFrame,.normal⟩ := by
 have shape : invariantTry.body = .sequence (firstStmt invariantTry.body) (restStmt invariantTry.body) := by
   with_unfolding_all rfl
 rw [shape,execSequence_eq 58,invariant_value_execute b n hle]
 simp only [Bind.bind,Except.bind]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem invariant_loop_execute (b n : Int) (hle : n≤b) :
 execStmt 61 (balanceProgram .ts) (invariantStage b n 165 85 31) invariantEvalFrame
   invariantLoopBody = .ok ⟨invariantStage b n 190 92 33,invariantResultFrame,.normal⟩ := by
 have shape : invariantLoopBody = .sequence invariantTry.stmt .empty := by with_unfolding_all rfl
 rw [shape,execSequence_eq 60,execProtectedSyntax_eq 59,invariant_try_body_execute b n hle]
 with_unfolding_all rfl

private def invariantList : HeapObject :=
 (objectAt (invariantStage 0 0 164 85 31) 13).toOption.getD ⟨.jsArray,none,[],[],[],false,false⟩

private theorem invariant_for_execute (b n : Int) (hle : n≤b) :
 execStmt 63 (balanceProgram .ts) (invariantStage b n 164 85 31) invariantEnvFrame invariantForStmt =
 .ok ⟨invariantStage b n 190 92 33,invariantEnvFrame,.normal⟩ := by
 have shape : invariantForStmt = .forDo ["invariant"] invariantIterable invariantLoopBody := by with_unfolding_all rfl
 have he : evalExpr 62 (balanceProgram .ts) (invariantStage b n 164 85 31) invariantEnvFrame invariantIterable =
   .ok ⟨invariantStage b n 164 85 31,.ok (.object 13)⟩ := by with_unfolding_all rfl
 have hl : objectAt (invariantStage b n 164 85 31) 13 = .ok invariantList := by with_unfolding_all rfl
 have hk : invariantList.kind = .jsArray := by with_unfolding_all rfl
 have hi : invariantList.items = [.object 12] := by with_unfolding_all rfl
 have hb : execStmt 61 (balanceProgram .ts)
   (tsForOneBound (invariantStage b n 164 85 31) invariantEnvFrame "invariant" (.object 12)).1
   (tsForOneBound (invariantStage b n 164 85 31) invariantEnvFrame "invariant" (.object 12)).2
   invariantLoopBody = .ok ⟨invariantStage b n 190 92 33,invariantResultFrame,.normal⟩ := by
   change execStmt 61 (balanceProgram .ts) (invariantStage b n 165 85 31) invariantEvalFrame invariantLoopBody = _
   exact invariant_loop_execute b n hle
 rw [shape,execForDo_ts_one_control (balanceProgram_lang .ts) he hl hk hi hb]
 rfl

private theorem invariant_body_execute (b n : Int) (hle : n≤b) :
 execStmt 65 (balanceProgram .ts) (invariantStage b n 163 84 31) invariantFrame invariantBody =
 .ok ⟨invariantStage b n 190 92 33,invariantEnvFrame,.returned .undefined⟩ := by
 have h0 : invariantBody = .sequence (firstStmt invariantBody) (restStmt invariantBody) := by with_unfolding_all rfl
 have h1 : restStmt invariantBody = .sequence invariantForStmt (restStmt (restStmt invariantBody)) := by with_unfolding_all rfl
 rw [h0,execSequence_eq 64,invariant_env_execute b n]
 simp only [Bind.bind,Except.bind]
 rw [h1,execSequence_eq 63,invariant_for_execute b n hle]
 simp only [Bind.bind,Except.bind]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem invariant_execute (b n : Int) (hle : n≤b) :
 evalExpr 66 (balanceProgram .ts) (invariantStage b n 160 84 30) postBoundsFrame invariantCall =
 .ok ⟨invariantStage b n 190 92 33,.ok .undefined⟩ := by
 rw [invariant_open b n,invariant_body_execute b n hle]
 with_unfolding_all rfl

private def positiveTailSyntax : TargetStmt :=
TargetStmt.sequence
  (TargetStmt.letLocal
    "boundError"
    false
    (TargetExpr.call
      (TargetExpr.property
        (TargetExpr.local "this")
        "checkBounds")
      (TargetExpr.sequence
        (TargetExpr.local "candidate")
        (TargetExpr.empty))))
  (TargetStmt.sequence
    (TargetStmt.ifThenElse
      (TargetExpr.local "boundError")
      (TargetStmt.returnValue
        (TargetExpr.call
          (TargetExpr.local "reject")
          (TargetExpr.sequence
            (TargetExpr.string "INVALID_BOUNDS")
            (TargetExpr.sequence
              (TargetExpr.formatted
                (TargetExpr.formatPart
                  "Context bound failed on '"
                  (TargetExpr.local "boundError")
                  (TargetExpr.formatPart
                    "'"
                    (TargetExpr.empty)
                    (TargetExpr.empty))))
              (TargetExpr.empty)))))
      (TargetStmt.empty))
    (TargetStmt.sequence
      (TargetStmt.letLocal
        "violatedInv"
        false
        (TargetExpr.call
          (TargetExpr.property
            (TargetExpr.local "this")
            "checkInvariants")
          (TargetExpr.sequence
            (TargetExpr.property
              (TargetExpr.local "transition")
              "to")
            (TargetExpr.sequence
              (TargetExpr.local "candidate")
              (TargetExpr.sequence
                (TargetExpr.local "safePayload")
                (TargetExpr.empty))))))
      (TargetStmt.sequence
        (TargetStmt.ifThenElse
          (TargetExpr.local "violatedInv")
          (TargetStmt.returnValue
            (TargetExpr.call
              (TargetExpr.local "reject")
              (TargetExpr.sequence
                (TargetExpr.string "INVARIANT_FAILED")
                (TargetExpr.sequence
                  (TargetExpr.formatted
                    (TargetExpr.formatPart
                      "Invariant violation: '"
                      (TargetExpr.local "violatedInv")
                      (TargetExpr.formatPart
                        "'"
                        (TargetExpr.empty)
                        (TargetExpr.empty))))
                  (TargetExpr.sequence
                    (TargetExpr.local "violatedInv")
                    (TargetExpr.empty))))))
          (TargetStmt.empty))
        (TargetStmt.sequence
          (TargetStmt.assign
            (AssignTarget.property
              (TargetExpr.local "this")
              "#undo")
            (TargetExpr.object
              (TargetExpr.objectEntry
                "state"
                (TargetExpr.local "snapshotState")
                (TargetExpr.objectEntry
                  "context"
                  (TargetExpr.local "snapshotContext")
                  (TargetExpr.objectEntry
                    "history"
                    (TargetExpr.local "snapshotHistory")
                    (TargetExpr.empty))))))
          (TargetStmt.sequence
            (TargetStmt.assign
              (AssignTarget.property
                (TargetExpr.local "this")
                "#state")
              (TargetExpr.typeCast
                (TargetExpr.property
                  (TargetExpr.local "transition")
                  "to")
                "WorldState"))
            (TargetStmt.sequence
              (TargetStmt.assign
                (AssignTarget.property
                  (TargetExpr.local "this")
                  "#context")
                (TargetExpr.local "candidate"))
              (TargetStmt.sequence
                (TargetStmt.doExpr
                  (TargetExpr.call
                    (TargetExpr.property
                      (TargetExpr.property
                        (TargetExpr.local "this")
                        "#history")
                      "push")
                    (TargetExpr.sequence
                      (TargetExpr.call
                        (TargetExpr.local "deepFreezeWorld")
                        (TargetExpr.sequence
                          (TargetExpr.local "record")
                          (TargetExpr.empty)))
                      (TargetExpr.empty))))
                (TargetStmt.sequence
                  (TargetStmt.returnValue
                    (TargetExpr.object
                      (TargetExpr.objectEntry
                        "allowed"
                        (TargetExpr.bool true)
                        (TargetExpr.objectEntry
                          "previousState"
                          (TargetExpr.local "snapshotState")
                          (TargetExpr.objectEntry
                            "currentState"
                            (TargetExpr.property
                              (TargetExpr.local "this")
                              "#state")
                            (TargetExpr.objectEntry
                              "context"
                              (TargetExpr.call
                                (TargetExpr.property
                                  (TargetExpr.local "this")
                                  "getContext")
                                (TargetExpr.empty))
                              (TargetExpr.objectEntry
                                "directiveAllowed"
                                (TargetExpr.typeCast
                                  (TargetExpr.property
                                    (TargetExpr.local "transition")
                                    "directive")
                                  "StepVerdict[\"directiveAllowed\"]")
                                (TargetExpr.empty))))))))
                  (TargetStmt.empty)))))))))

private theorem positive_tail_source :
 dropStmts 3 positiveTail = positiveTailSyntax := by
 simp only [positiveTail, balanceStepProtected, balanceStepSnapshots,
   balanceStepAfterBusy, balanceStep_stored_source]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem positive_prefix_shape : stepPrefixShape 3 positiveTail = true := by
 simp only [positiveTail, balanceStepProtected, balanceStepSnapshots,
   balanceStepAfterBusy, balanceStep_stored_source]
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem positive_prefix_execute (b n : Int) (hp : 0 < n)
 (hs : (b - n).natAbs ≤ 9007199254740991) :
 execStmt 73 (balanceProgram .ts) (balanceStepTsPrefix b n) balanceStepTsPrefixFrame
   (takeStepStmts 3 positiveTail) =
   .ok ⟨positiveEffectsMachine b n, positiveEffectsFrame, .normal⟩ := by
 have shape : takeStepStmts 3 positiveTail =
     .sequence (firstStmt positiveTail) (takeStepStmts 2 (restStmt positiveTail)) := by
   simp only [positiveTail, balanceStepProtected, balanceStepSnapshots,
     balanceStepAfterBusy, balanceStep_stored_source]
   rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
   with_unfolding_all rfl
 rw [shape, execSequence_eq 72, positive_guard_execute b n hp]
 change execStmt 72 (balanceProgram .ts) (positiveGuardMachine b n) positiveGuardFrame
   (takeStepStmts 2 (restStmt positiveTail)) = _
 exact positive_effects_execute b n hp hs

private def positiveProtectedPost (b n : Int) : Except TargetError StmtOutcome := do
 let p := balanceStepProtected .ts
 let attempted ← execStmt 70 (balanceProgram .ts) (positiveEffectsMachine b n)
   positiveEffectsFrame (dropStmts 3 positiveTail)
 let handled ← match attempted.control with
   | .raised errorValue =>
       if controlCaught p.catchType (.raised errorValue) then do
         let bound := bindCatchFrame attempted.machine attempted.frame p.binder errorValue
         let caught ← execStmt 91 (balanceProgram .ts) bound.1 bound.2 p.handler
         pure { caught with frame := { caught.frame with control := .normal } }
       else pure attempted
   | _ => pure attempted
 let finalized ← execStmt 91 (balanceProgram .ts) handled.machine handled.frame p.cleanup
 match finalized.control with
 | .normal => pure ⟨finalized.machine,finalized.frame,handled.control⟩
 | _ => pure finalized

private def positiveSequencePost (b n : Int) : Except TargetError StmtOutcome := do
 let head ← positiveProtectedPost b n
 match head.control with
 | .normal => execStmt 92 (balanceProgram .ts) head.machine head.frame .empty
 | _ => pure head

private def positivePost (b n : Int) : Except TargetError ExprOutcome := do
 let body ← positiveSequencePost b n
 closureResult .ts body

private theorem positive_prefix_continuation (b n : Int) (hp : 0 < n)
 (hs : (b - n).natAbs ≤ 9007199254740991) :
 evalExpr 100 (balanceProgram .ts)
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).1
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).2
   (debitCallExpression .ts) = positivePost b n := by
 rw [balanceStep_ts_prefix_continuation b n]
 unfold balanceStepPrefixContinuation balanceStepSequenceContinuation balanceStepProtectedContinuation
 simp only [show (TargetLang.ts == TargetLang.ts) = true from rfl,
   ↓reduceIte, balanceStepCanonicalPrefix]
 have hcut := execStepPrefix_normal 3 69 (balanceProgram .ts) (balanceStepTsPrefix b n)
   balanceStepTsPrefixFrame positiveTail (positiveEffectsMachine b n) positiveEffectsFrame
   positive_prefix_shape (positive_prefix_execute b n hp hs)
 dsimp only [positiveTail] at hcut
 rw [hcut]
 with_unfolding_all rfl

private def postRejectMachine (b n : Int) : TargetMachine :=
 (allocCell (boundsStage b n 159 84 30) (.string "balance") false).1

private theorem post_bounds_reject_let (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) (hlt : b<n) :
 execStmt 69 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame
   (firstStmt positiveTailSyntax) = .ok ⟨postRejectMachine b n,postBoundsFrame,.normal⟩ := by
 have shape : firstStmt positiveTailSyntax = .letLocal "boundError" false boundsCall := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [bounds_reject_execute b n hs hlt]
 with_unfolding_all rfl

private theorem positive_post_reject (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991) (hlt : b<n) :
 positivePost b n = .ok ⟨balanceStepTsBoundsRejected b n,.ok (.object 86)⟩ := by
 unfold positivePost positiveSequencePost positiveProtectedPost
 rw [positive_tail_source]
 have shape : positiveTailSyntax = .sequence (firstStmt positiveTailSyntax) (restStmt positiveTailSyntax) := by
   with_unfolding_all rfl
 rw [shape,execSequence_eq 69,post_bounds_reject_let b n hs hlt]
 dsimp only [Bind.bind,Except.bind]
 dsimp only [postRejectMachine,positiveTailSyntax,boundsStage,positiveEffectsMachine,balanceStepTsBoundsRejected,
   balanceStepProtected,balanceStepSnapshots,balanceStepAfterBusy,balanceStepTsPrefix,
   balanceCanonicalConstructed,balanceInvariantTsCopied,balanceInvariantTsReset,
   balanceInvariantTsBound,balanceInvariantTsFinal]
 simp only [balanceStep_stored_source,balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem post_bounds_valid_let (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991)
 (hle : n≤b) (hmax : b-n≤9007199254740991) :
 execStmt 69 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame
   (firstStmt positiveTailSyntax) = .ok ⟨invariantStage b n 160 84 30,postBoundsFrame,.normal⟩ := by
 have shape : firstStmt positiveTailSyntax = .letLocal "boundError" false boundsCall := by with_unfolding_all rfl
 rw [shape,execStmt.eq_def]
 dsimp only
 rw [bounds_valid_execute b n hs hle hmax]
 with_unfolding_all rfl

private theorem post_bounds_valid_if (b n : Int) :
 execStmt 68 (balanceProgram .ts) (invariantStage b n 160 84 30) postBoundsFrame
   (firstStmt (restStmt positiveTailSyntax)) = .ok ⟨invariantStage b n 160 84 30,postBoundsFrame,.normal⟩ := by
 rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem post_bounds_valid_prefix (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991)
 (hle : n≤b) (hmax : b-n≤9007199254740991) :
 execStmt 70 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame
   (takeStepStmts 2 positiveTailSyntax) = .ok ⟨invariantStage b n 160 84 30,postBoundsFrame,.normal⟩ := by
 have shape : takeStepStmts 2 positiveTailSyntax = .sequence (firstStmt positiveTailSyntax)
   (.sequence (firstStmt (restStmt positiveTailSyntax)) .empty) := by with_unfolding_all rfl
 rw [shape,execSequence_eq 69,post_bounds_valid_let b n hs hle hmax]
 simp only [Bind.bind,Except.bind]
 rw [execSequence_eq 68,post_bounds_valid_if b n]
 with_unfolding_all rfl

private def postInvariantMachine (b n : Int) : TargetMachine :=
 (allocCell (invariantStage b n 190 92 33) .undefined false).1
private def postInvariantFrame : TargetFrame :=
 {postBoundsFrame with locals := ("violatedInv",190)::postBoundsFrame.locals}

private theorem post_invariant_let (b n : Int) (hle : n≤b) :
 execStmt 67 (balanceProgram .ts) (invariantStage b n 160 84 30) postBoundsFrame
   (.letLocal "violatedInv" false invariantCall) =
 .ok ⟨postInvariantMachine b n,postInvariantFrame,.normal⟩ := by
 rw [execStmt.eq_def]
 dsimp only
 rw [invariant_execute b n hle]
 with_unfolding_all rfl

private theorem positive_post_accept (b n : Int) (hs : (b-n).natAbs ≤ 9007199254740991)
 (hle : n≤b) (hmax : b-n≤9007199254740991) :
 positivePost b n = .ok ⟨balanceStepTsAccepted b n,.ok (.object 95)⟩ := by
 unfold positivePost positiveSequencePost positiveProtectedPost
 rw [positive_tail_source]
 have shape2 : stepPrefixShape 2 positiveTailSyntax = true := by with_unfolding_all rfl
 rw [execStepPrefix_normal 2 67 (balanceProgram .ts) (positiveEffectsMachine b n) positiveEffectsFrame
   positiveTailSyntax (invariantStage b n 160 84 30) postBoundsFrame shape2
   (post_bounds_valid_prefix b n hs hle hmax)]
 have shape : dropStmts 2 positiveTailSyntax = .sequence
   (.letLocal "violatedInv" false invariantCall) (restStmt (dropStmts 2 positiveTailSyntax)) := by
   with_unfolding_all rfl
 rw [shape,execSequence_eq 67,post_invariant_let b n hle]
 dsimp only [Bind.bind,Except.bind]
 dsimp only [postInvariantMachine,positiveTailSyntax,invariantStage,positiveEffectsMachine,balanceStepTsAccepted,
   balanceStepTsBoundsRejected,balanceStepProtected,balanceStepSnapshots,balanceStepAfterBusy,
   balanceStepTsPrefix,balanceCanonicalConstructed,balanceInvariantTsCopied,balanceInvariantTsReset,
   balanceInvariantTsBound,balanceInvariantTsFinal]
 simp only [balanceStep_stored_source,balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]
 with_unfolding_all rfl

private theorem positive_difference_safe (b n : Int)
 (hb : 0≤b ∧ b≤Harmonia.Applications.Kadmos.S)
 (hn : 0<n ∧ n≤Harmonia.Applications.Kadmos.S) :
 (b-n).natAbs≤9007199254740991 := by
 apply signed_natAbs
 constructor <;> omega

/-- The generated TS call takes the bounds rejection path and executes finally. -/
theorem balanceStep_ts_bounds_reject_execute (b n : Int)
 (hb : 0≤b ∧ b≤Harmonia.Applications.Kadmos.S)
 (hn : 0<n ∧ n≤Harmonia.Applications.Kadmos.S) (hlt : b<n) :
 evalExpr 100 (balanceProgram .ts)
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).1
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).2
   (debitCallExpression .ts) = .ok ⟨balanceStepTsBoundsRejected b n,.ok (.object 86)⟩ := by
 rw [positive_prefix_continuation b n hn.1 (positive_difference_safe b n hb hn)]
 exact positive_post_reject b n (positive_difference_safe b n hb hn) hlt

/-- The generated TS call checks the invariant, commits, and executes finally. -/
theorem balanceStep_ts_accept_execute (b n : Int)
 (hb : 0≤b ∧ b≤Harmonia.Applications.Kadmos.S)
 (hn : 0<n ∧ n≤Harmonia.Applications.Kadmos.S) (hle : n≤b) :
 evalExpr 100 (balanceProgram .ts)
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).1
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).2
   (debitCallExpression .ts) = .ok ⟨balanceStepTsAccepted b n,.ok (.object 95)⟩ := by
 rw [positive_prefix_continuation b n hn.1 (positive_difference_safe b n hb hn)]
 apply positive_post_accept b n (positive_difference_safe b n hb hn) hle
 change b-n≤Harmonia.Applications.Kadmos.S
 omega

theorem targetStep_ts_bounds_reject (b n : Int)
 (hb : 0≤b ∧ b≤Harmonia.Applications.Kadmos.S)
 (hn : 0<n ∧ n≤Harmonia.Applications.Kadmos.S) (hlt : b<n) :
 targetStep (balanceProgram .ts) (balanceCanonicalConstructed .ts b) (canonicalDebitRequest .ts n) =
 .ok (balanceStepTsBoundsRejectedOutcome b n) := by
 have hsign : -Harmonia.Applications.Kadmos.S≤n ∧ n≤Harmonia.Applications.Kadmos.S := by constructor <;> omega
 rw [targetStep_balance_entry .ts _ hsign,balanceStep_ts_bounds_reject_execute b n hb hn hlt]
 rfl

theorem targetStep_ts_accept (b n : Int)
 (hb : 0≤b ∧ b≤Harmonia.Applications.Kadmos.S)
 (hn : 0<n ∧ n≤Harmonia.Applications.Kadmos.S) (hle : n≤b) :
 targetStep (balanceProgram .ts) (balanceCanonicalConstructed .ts b) (canonicalDebitRequest .ts n) =
 .ok (balanceStepTsAcceptedOutcome b n) := by
 have hsign : -Harmonia.Applications.Kadmos.S≤n ∧ n≤Harmonia.Applications.Kadmos.S := by constructor <;> omega
 rw [targetStep_balance_entry .ts _ hsign,balanceStep_ts_accept_execute b n hb hn hle]
 rfl

end Harmonia.Applications.Kadmos.Generated
