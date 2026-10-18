import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonPrefix
import Harmonia.Applications.Kadmos.Generated.BalanceStepTSPrefix
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false
set_option smartUnfolding false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The original protected-body handling, with only its normal prefix consumed. -/
def balanceStepProtectedContinuation (lang : TargetLang) (b n : Int) :
    Except TargetError StmtOutcome := do
 let p := balanceStepProtected lang
 let prefixState := balanceStepCanonicalPrefix lang b n
 let attempted ← execStmt (if lang == .ts then 73 else 69) (balanceProgram lang)
   prefixState.1 prefixState.2 (dropStmts (if lang == .ts then 18 else 21) p.body)
 let handled ← match attempted.control with
   | .raised errorValue =>
       if controlCaught p.catchType (.raised errorValue) then do
         let bound := bindCatchFrame attempted.machine attempted.frame p.binder errorValue
         let caught ← execStmt (if lang == .ts then 91 else 90) (balanceProgram lang)
           bound.1 bound.2 p.handler
         pure { caught with frame := { caught.frame with control := .normal } }
       else pure attempted
   | _ => pure attempted
 let finalized ← execStmt (if lang == .ts then 91 else 90) (balanceProgram lang)
   handled.machine handled.frame p.cleanup
 match finalized.control with
 | .normal => pure ⟨finalized.machine, finalized.frame, handled.control⟩
 | _ => pure finalized

def balanceStepSequenceContinuation (lang : TargetLang) (b n : Int) :
    Except TargetError StmtOutcome := do
 let head ← balanceStepProtectedContinuation lang b n
 match head.control with
 | .normal =>
     execStmt (if lang == .ts then 92 else 91) (balanceProgram lang)
       head.machine head.frame .empty
 | _ => pure head

/-- Resume the actual protected source body after the checked normal prefix.
Handler/finally fuel and the final sequence sibling are unchanged. -/
def balanceStepPrefixContinuation (lang : TargetLang) (b n : Int) : Except TargetError ExprOutcome := do
 let body ← balanceStepSequenceContinuation lang b n
 closureResult lang body


private theorem balanceStep_prefix_call_of_execute (lang : TargetLang) (b n : Int)
 (hp : balanceStepPrefixRun lang b n = .ok
   ⟨(balanceStepCanonicalPrefix lang b n).1, (balanceStepCanonicalPrefix lang b n).2, .normal⟩) :
 evalExpr 100 (balanceProgram lang)
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).1
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).2
   (debitCallExpression lang) = balanceStepPrefixContinuation lang b n := by
 have hr : execStmt (if lang == .ts then 91 else 90) (balanceProgram lang)
     (balanceStepCanonicalSnapshots lang b n).1 (balanceStepCanonicalSnapshots lang b n).2
     (takeStepStmts (if lang == .ts then 18 else 21) (balanceStepProtected lang).body) =
     .ok ⟨(balanceStepCanonicalPrefix lang b n).1, (balanceStepCanonicalPrefix lang b n).2, .normal⟩ := by
   simpa only [balanceStepPrefixRun, balanceStep_canonical_snapshots_execute,
     Bind.bind, Except.bind] using hp
 have hb : execStmt (if lang == .ts then 91 else 90) (balanceProgram lang)
     (balanceStepCanonicalSnapshots lang b n).1 (balanceStepCanonicalSnapshots lang b n).2
     (balanceStepProtected lang).body =
   execStmt (if lang == .ts then 73 else 69) (balanceProgram lang)
     (balanceStepCanonicalPrefix lang b n).1 (balanceStepCanonicalPrefix lang b n).2
     (dropStmts (if lang == .ts then 18 else 21) (balanceStepProtected lang).body) := by
   cases lang
   · exact execStepPrefix_normal 18 72 _ _ _ _ _ _ (balanceStep_prefix_shape .ts) hr
   · exact execStepPrefix_normal 21 68 _ _ _ _ _ _ (balanceStep_prefix_shape .python) hr
 have shape : dropStmts (if lang == .ts then 4 else 5) (balanceStepSnapshots lang) =
     .sequence (balanceStepProtected lang).stmt .empty := balanceStep_protected_shape lang
 rw [balanceStep_canonical_snapshot_continuation, shape]
 have seq := execSequence_eq (if lang == .ts then 92 else 91) (balanceProgram lang)
   (balanceStepCanonicalSnapshots lang b n).1 (balanceStepCanonicalSnapshots lang b n).2
   (balanceStepProtected lang).stmt .empty
 have seqFuel : (if lang == .ts then 92 else 91) + 1 =
     (if lang == .ts then 93 else 92) := by cases lang <;> rfl
 rw [seqFuel] at seq
 rw [seq]
 have prot := execProtectedSyntax_eq (if lang == .ts then 91 else 90) (balanceProgram lang)
   (balanceStepCanonicalSnapshots lang b n).1 (balanceStepCanonicalSnapshots lang b n).2
   (balanceStepProtected lang)
 have protFuel : (if lang == .ts then 91 else 90) + 1 =
     (if lang == .ts then 92 else 91) := by cases lang <;> rfl
 rw [protFuel] at prot
 rw [prot, hb]
 with_unfolding_all rfl


theorem balanceStep_prefix_view (lang : TargetLang) (b n : Int) :
 balanceView lang (balanceStepCanonicalPrefix lang b n).1 =
   .ok ⟨"Ready", b, [], none, b, true⟩ := by
 cases lang <;> rfl

/-- The complete TS call continues from its exact normally executed prefix,
with the original catch, finally and return path retained. -/
theorem balanceStep_ts_prefix_continuation (b n : Int) :
 evalExpr 100 (balanceProgram .ts)
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).1
   (debitCallEntry .ts (balanceCanonicalConstructed .ts b) n).2
   (debitCallExpression .ts) = balanceStepPrefixContinuation .ts b n :=
 balanceStep_prefix_call_of_execute .ts b n (balanceStep_ts_prefix_execute b n)


/-- Actual shared prefix, including sanitization and all intermediate heap cells. -/
theorem balanceStep_canonical_prefix_execute (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
 balanceStepPrefixRun lang b n =
   .ok ⟨(balanceStepCanonicalPrefix lang b n).1,
        (balanceStepCanonicalPrefix lang b n).2, .normal⟩ := by
 cases lang
 · exact balanceStep_ts_prefix_execute b n
 · exact balanceStep_py_prefix_execute b n (signed_natAbs hn)

/-- The full canonical call reaches the proved prefix without discarding any
source continuation, catch handler, finally cleanup, or return translation. -/
theorem balanceStep_canonical_prefix_continuation (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
 evalExpr 100 (balanceProgram lang)
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).1
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).2
   (debitCallExpression lang) = balanceStepPrefixContinuation lang b n :=
 balanceStep_prefix_call_of_execute lang b n (balanceStep_canonical_prefix_execute lang b n hn)

/-- Execution and physical post-prefix payload/view contract for the canonical
safe request, before evaluating the stored guard. -/
theorem balanceStep_canonical_prefix_contract (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
 balanceStepPrefixRun lang b n =
   .ok ⟨(balanceStepCanonicalPrefix lang b n).1,
        (balanceStepCanonicalPrefix lang b n).2, .normal⟩ ∧
 balanceView lang (balanceStepCanonicalPrefix lang b n).1 =
   .ok ⟨"Ready", b, [], none, b, true⟩ ∧
 localValue (balanceStepCanonicalPrefix lang b n).1 (balanceStepCanonicalPrefix lang b n).2
     (if lang == .ts then "safePayload" else "payload") =
   .ok (.object (if lang == .ts then 53 else 114)) ∧
 readOwn (balanceStepCanonicalPrefix lang b n).1 (if lang == .ts then 53 else 114) "amount" =
   .ok (some ⟨some (.number (if lang == .ts then .jsNumber else .pyFloat) n),
              none, none, true, true, true⟩) :=
 ⟨balanceStep_canonical_prefix_execute lang b n hn, balanceStep_prefix_view lang b n,
  balanceStep_payload_local lang b n, balanceStep_payload_amount lang b n⟩

end Harmonia.Applications.Kadmos.Generated
