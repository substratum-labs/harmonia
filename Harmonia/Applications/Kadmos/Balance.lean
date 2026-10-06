import Harmonia.Applications.Kadmos.System
namespace Harmonia.Applications.Kadmos

def balanceWorld : World 1 1 1 1 where
  phaseIds _ := "Ready"
  initialFlags _ := true
  terminalFlags _ := false
  contextIds _ := "balance"
  variables _ := ⟨0,S,some 100⟩
  fieldIds _ := "amount"
  actionIds _ := "DEBIT"
  transitions _ := ⟨0,0,.lt (.int 0) (.request 0),[⟨0,.sub (.context 0) (.request 0)⟩],none⟩
  invariants := [("nonnegative",.le (.int 0) (.context 0))]

def balanceState (n : Int) : State 1 1 := ⟨0,fun _ => n⟩
def debit (n : Int) : Request 1 := ⟨"DEBIT",fun _ => .int n,none⟩

theorem balance_initialized : «initialize» balanceWorld = .ok (balanceState 100) := rfl
theorem lookup_debit (n : Int) : lookupAction balanceWorld (debit n).actionId = some 0 := rfl

theorem finOne_context_eq (c : Fin 1 → Int) (n : Int) (h0 : c 0 = n) : c = fun _ => n := by
  funext y
  have hy : y = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ y.isLt))
  rw [hy]; exact h0

theorem balance_bounds (b : Int) (hb : 0 ≤ b) (hB : b ≤ S) :
    checkBounds balanceWorld (balanceState b) = none := by
  have safe : safeInt b := by unfold safeInt S at *; omega
  simp [checkBounds,inBounds,balanceWorld,balanceState,safe,hb,hB]

theorem balance_invariants (b : Int) (hb : 0 ≤ b) (hB : b ≤ S) :
    checkInvariants balanceWorld (balanceState b) = none := by
  have safe : safeInt b := by unfold safeInt S at *; omega
  simp [checkInvariants,checkInvariantList,balanceWorld,balanceState,eval,requireInt,
    checkedInt,safe,invariantPass,Bind.bind,Functor.map,Pure.pure,Except.bind,Except.map,Except.pure,show safeInt 0 by decide,hb]

/-- A computation lemma about the actual interpreter action, not a second Step. -/
theorem runAction_debit (b n : Int) (sb : safeInt b) (sn : safeInt n) (sd : safeInt (b-n)) (hn : 0 < n) :
    runAction balanceWorld 0 (balanceState b) (debit n) =
      publishCandidate balanceWorld (balanceState (b-n)) := by
  have hc : setContext (fun _ : Fin 1 => b) 0 (b-n) = (fun _ => b-n) :=
    finOne_context_eq _ _ (by simp)
  simp [runAction,debit,balanceWorld,balanceState,decode,inputValid,rawInt,sn,sb,sd,
    eval,requireInt,requireBool,checkedInt,show safeInt 0 by decide,hn,
    runTransitionEffects,runEffects,runEffect,Bind.bind,Functor.map,Pure.pure,
    Except.bind,Except.mapError,Except.map,Except.pure,hc]

theorem debit_accept (b n : Int) (hb : 0 ≤ b) (hB : b ≤ S) (hn : 0 < n) (hnb : n ≤ b) :
    interpret balanceWorld (balanceState b) (debit n) = ⟨balanceState (b-n),⟨.accepted,none⟩⟩ := by
  have sb : safeInt b := by unfold safeInt S at *; omega
  have sn : safeInt n := by unfold safeInt S at *; omega
  have sd : safeInt (b-n) := by unfold safeInt S at *; omega
  have hd : 0 ≤ b-n := by omega
  have hD : b-n ≤ S := by omega
  simp only [interpret,attempt,balance_initialized,lookup_debit]
  rw [runAction_debit b n sb sn sd hn]
  rw [publishCandidate_ok (balance_bounds (b-n) hd hD) (balance_invariants (b-n) hd hD)]
  rfl

theorem balance_negative_bounds (d : Int) (hd : d < 0) :
    checkBounds balanceWorld (balanceState d) = some 0 := by
  have hf : ¬ ∀ j, inBounds balanceWorld (balanceState d) j := by
    intro h
    have hz := (h 0).2.1
    change 0 ≤ d at hz
    omega
  rw [checkBounds,if_neg hf]
  change some (if inBounds balanceWorld (balanceState d) 0 then 0 else 0) = some 0
  simp

theorem debit_insufficient (b n : Int) (hb : 0 ≤ b) (hB : b ≤ S) (hbn : b < n) (hN : n ≤ S) :
    interpret balanceWorld (balanceState b) (debit n) = ⟨balanceState b,⟨.rejected (.bounds 0),none⟩⟩ := by
  have sb : safeInt b := by unfold safeInt S at *; omega
  have sn : safeInt n := by unfold safeInt S at *; omega
  have sd : safeInt (b-n) := by unfold safeInt S at *; omega
  have hn : 0 < n := by omega
  have hd : b-n < 0 := by omega
  have hpub : publishCandidate balanceWorld (balanceState (b-n)) = .error (.bounds 0) := by
    unfold publishCandidate
    split
    · rename_i j heq
      rw [balance_negative_bounds (b-n) hd] at heq
      cases Option.some.inj heq
      rfl
    · rename_i heq
      have hbad := balance_negative_bounds (b-n) hd
      rw [heq] at hbad
      cases hbad
  simp only [interpret,attempt,balance_initialized,lookup_debit]
  rw [runAction_debit b n sb sn sd hn,hpub]
  rfl

theorem balance_initial_reachable : Foundation.Reachable (system balanceWorld) (balanceState 100) :=
  .init balance_initialized

theorem balance_reachable_bounds (h : Foundation.Reachable (system balanceWorld) s) :
    0 ≤ s.context 0 ∧ s.context 0 ≤ S :=
  (good_bounds (reachable_good balance_initialized s h) 0).2

theorem balance_trace : Foundation.Execution (system balanceWorld) (balanceState 100)
    [(debit 30,⟨.accepted,none⟩),(debit 20,⟨.accepted,none⟩),
      (debit 130,⟨.rejected (.bounds 0),none⟩)] (balanceState 50) := by
  exact .cons (debit_accept 100 30 (by decide) (by decide) (by decide) (by decide))
    (.cons (debit_accept 70 20 (by decide) (by decide) (by decide) (by decide))
      (.cons (debit_insufficient 50 130 (by decide) (by decide) (by decide) (by decide)) .nil))
end Harmonia.Applications.Kadmos
