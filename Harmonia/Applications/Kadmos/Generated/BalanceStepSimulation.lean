import Harmonia.Applications.Kadmos.Generated.BalanceStepPositiveModels
import Harmonia.Applications.Kadmos.Generated.BalanceStepTSPositive
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonPositiveModels
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonPositive
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonReject
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonGuard
import Harmonia.Applications.Kadmos.Generated.BalanceStepLexemes
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonPrefixEntry
import Harmonia.Applications.Kadmos.Generated.BalanceStepContinuation
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonGuardStages
import Harmonia.Applications.Kadmos.Generated.BalanceStepSnapshots
import Harmonia.Applications.Kadmos.Generated.BalanceStepSource
import Harmonia.Applications.Kadmos.Generated.BalanceStepTSPrefix
import Harmonia.Applications.Kadmos.Generated.BalanceStepTSGuard
import Harmonia.Applications.Kadmos.Generated.BalanceStepTSReject
import Harmonia.Applications.Kadmos.Generated.BalanceStepPythonZero

/-! Canonical generated DEBIT execution contracts. -/
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

theorem targetStep_ts_guard_reject (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hle : n ≤ 0) :
 targetStep (balanceProgram .ts) (balanceCanonicalConstructed .ts b)
   (canonicalDebitRequest .ts n) = .ok (balanceStepGuardRejected .ts b n) := by
 rw [targetStep_balance_entry .ts _ hn, balanceStep_ts_guard_reject_execute b n hle]
 rfl

theorem targetStep_py_guard_zero (b : Int) :
 targetStep (balanceProgram .python) (balanceCanonicalConstructed .python b)
   (canonicalDebitRequest .python 0) = .ok (balanceStepGuardRejected .python b 0) := by
 rw [targetStep_balance_entry .python _ (by decide :
   -Harmonia.Applications.Kadmos.S ≤ (0 : Int) ∧ (0 : Int) ≤ Harmonia.Applications.Kadmos.S),
   balanceStep_py_guard_zero_execute b]
 rfl

/-- The physical final observation preserves every canonical initial view field,
including history, undo, constructor seed, and the released busy flag. -/
theorem balanceStep_guardRejected_preserves_view (lang : TargetLang) (b n : Int) :
 balanceView lang (balanceStepGuardRejected lang b n).machine =
   balanceView lang (balanceCanonicalConstructed lang b) :=
 (balanceStep_guardRejected_frame lang b n).trans
   (BalanceRep.view (balanceCanonicalConstructed_rep lang b)).symm


/-- Exact target-level rejection on every safe nonpositive amount. -/
theorem targetStep_guard_reject (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hle : n ≤ 0) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang b)
   (canonicalDebitRequest lang n) = .ok (balanceStepGuardRejected lang b n) := by
 cases lang
 · exact targetStep_ts_guard_reject b n hn hle
 · rw [targetStep_balance_entry .python _ hn,
       balanceStep_py_guard_reject_execute b n hn hle]
   rfl

/-- Canonical guard-rejection API: execution, logical projection, exact failure
code, physical well-formedness, and the complete initial/final view frame. -/
theorem step_guard_reject (lang : TargetLang) (b n : Int)
    (_hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hle : n ≤ 0) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang b)
   (canonicalDebitRequest lang n) = .ok (balanceStepGuardRejected lang b n) ∧
 targetProjection lang (balanceStepGuardRejected lang b n) =
   .ok ⟨false, "Ready", [("balance", b)], none⟩ ∧
 targetViolationCode (balanceStepGuardRejected lang b n) = .ok (some "GUARD_FAILED") ∧
 HeapWF lang (balanceStepGuardRejected lang b n).machine ∧
 balanceView lang (balanceStepGuardRejected lang b n).machine =
   .ok ⟨"Ready", b, [], none, b, false⟩ ∧
 balanceView lang (balanceStepGuardRejected lang b n).machine =
   balanceView lang (balanceCanonicalConstructed lang b) :=
 ⟨targetStep_guard_reject lang b n hn hle,
  balanceStep_guardRejected_projection lang b n,
  balanceStep_guardRejected_code lang b n,
  balanceStep_guardRejected_WF lang b n,
  balanceStep_guardRejected_frame lang b n,
  balanceStep_guardRejected_preserves_view lang b n⟩

/-- The actual stored guard computes the source predicate for every safe amount. -/
theorem balanceStep_canonical_guard_value (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
 (balanceStepGuardRun lang b n).toOption.map ExprOutcome.result =
   some (.ok (.bool (decide (0 < n)))) := by
 cases lang
 · exact balanceStep_ts_guard_value b n
 · exact balanceStep_py_guard_value b n (signed_natAbs hn)

/-- On the rejected branch the actual guard is false; no subtraction premise
or assumed evaluator success is required. -/
theorem balanceStep_canonical_guard_nonpositive (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hle : n ≤ 0) :
 (balanceStepGuardRun lang b n).toOption.map ExprOutcome.result =
   some (.ok (.bool false)) := by
 rw [balanceStep_canonical_guard_value lang b n hn, decide_eq_false (Int.not_lt.mpr hle)]


/-- Bounds rejection preserves the complete canonical initial observation. -/
theorem balanceStep_boundsRejected_preserves_view (lang : TargetLang) (b n : Int) :
 balanceView lang (balanceStepBoundsRejected lang b n).machine =
   balanceView lang (balanceCanonicalConstructed lang b) :=
 (balanceStep_boundsRejected_frame lang b n).trans
   (BalanceRep.view (balanceCanonicalConstructed_rep lang b)).symm

/-- Exact target execution of positive overdrafts in either language. -/
theorem targetStep_bounds_reject (lang : TargetLang) (b n : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : 0 < n ∧ n ≤ Harmonia.Applications.Kadmos.S) (hlt : b < n) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang b)
   (canonicalDebitRequest lang n) = .ok (balanceStepBoundsRejected lang b n) := by
 cases lang
 · exact targetStep_ts_bounds_reject b n hb hn hlt
 · exact targetStep_py_bounds_reject b n hb.1 hb.2 hn.1 hn.2 hlt

/-- Positive overdrafts reject with the exact violation and preserve the view. -/
theorem step_bounds_reject (lang : TargetLang) (b n : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : 0 < n ∧ n ≤ Harmonia.Applications.Kadmos.S) (hlt : b < n) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang b)
   (canonicalDebitRequest lang n) = .ok (balanceStepBoundsRejected lang b n) ∧
 targetProjection lang (balanceStepBoundsRejected lang b n) =
   .ok ⟨false, "Ready", [("balance", b)], none⟩ ∧
 targetViolationCode (balanceStepBoundsRejected lang b n) = .ok (some "INVALID_BOUNDS") ∧
 HeapWF lang (balanceStepBoundsRejected lang b n).machine ∧
 balanceView lang (balanceStepBoundsRejected lang b n).machine =
   .ok ⟨"Ready", b, [], none, b, false⟩ ∧
 balanceView lang (balanceStepBoundsRejected lang b n).machine =
   balanceView lang (balanceCanonicalConstructed lang b) :=
 ⟨targetStep_bounds_reject lang b n hb hn hlt,
  balanceStep_boundsRejected_projection lang b n,
  balanceStep_boundsRejected_code lang b n,
  balanceStep_boundsRejected_WF lang b n,
  balanceStep_boundsRejected_frame lang b n,
  balanceStep_boundsRejected_preserves_view lang b n⟩

/-- Exact target execution of accepted positive DEBIT in either language. -/
theorem targetStep_accept (lang : TargetLang) (b n : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : 0 < n ∧ n ≤ Harmonia.Applications.Kadmos.S) (hle : n ≤ b) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang b)
   (canonicalDebitRequest lang n) = .ok (balanceStepAccepted lang b n) := by
 cases lang
 · exact targetStep_ts_accept b n hb hn hle
 · exact targetStep_py_accept b n hb.1 hb.2 hn.1 hn.2 hle

/-- Accepted DEBIT commits the balance, history and undo, and releases busy. -/
theorem step_accept (lang : TargetLang) (b n : Int)
    (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : 0 < n ∧ n ≤ Harmonia.Applications.Kadmos.S) (hle : n ≤ b) :
 targetStep (balanceProgram lang) (balanceCanonicalConstructed lang b)
   (canonicalDebitRequest lang n) = .ok (balanceStepAccepted lang b n) ∧
 targetProjection lang (balanceStepAccepted lang b n) =
   .ok ⟨true, "Ready", [("balance", b - n)], none⟩ ∧
 targetViolationCode (balanceStepAccepted lang b n) = .ok none ∧
 HeapWF lang (balanceStepAccepted lang b n).machine ∧
 balanceView lang (balanceStepAccepted lang b n).machine =
   .ok ⟨"Ready", b - n, [expectedRecord lang n], some ⟨"Ready", b, []⟩, b, false⟩ :=
 ⟨targetStep_accept lang b n hb hn hle,
  balanceStep_accepted_projection lang b n,
  balanceStep_accepted_code lang b n,
  balanceStep_accepted_WF lang b n,
  balanceStep_accepted_frame lang b n⟩

/-- Every safe positive amount passes the actual stored guard. -/
theorem balanceStep_canonical_guard_positive (lang : TargetLang) (b n : Int)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hp : 0 < n) :
 (balanceStepGuardRun lang b n).toOption.map ExprOutcome.result =
   some (.ok (.bool true)) := by
 rw [balanceStep_canonical_guard_value lang b n hn, decide_eq_true hp]

end Harmonia.Applications.Kadmos.Generated
