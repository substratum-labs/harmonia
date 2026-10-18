import Harmonia.Applications.Kadmos.Generated.BalanceStepSimulation
import Harmonia.Applications.Kadmos.Generated.BalanceModel
import Harmonia.Applications.Kadmos.Generated.TargetCertificate

/-! Source-bound, universal correspondence for one canonical BALANCE call.
The source certificate fixes the program; constructor and step execution,
physical well-formedness and dereferenced observations are conclusions. -/
namespace Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos (interpret)
open Harmonia.Applications.Kadmos.BridgeFixtures
set_option autoImplicit false
set_option Elab.async false

theorem k02_balance_one_call (lang : TargetLang) (source : String)
    (program : TargetProgram)
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed lang b) = .ok machine ∧
      HeapWF lang machine ∧
      BalanceRep lang b machine ∧ balanceView lang machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest lang n) = .ok out ∧
      HeapWF lang out.machine ∧
      balanceView lang out.machine = .ok after ∧
      targetProjection lang out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      (n ≤ 0 → targetViolationCode out = .ok (some "GUARD_FAILED") ∧
        after = before) ∧
      (0 < n ∧ n ≤ b → targetViolationCode out = .ok none ∧
        after.balance = b - n ∧ after.history = [expectedRecord lang n] ∧
        after.undo = some ⟨"Ready", b, []⟩ ∧
        after.constructorSeed = b) ∧
      (n > b → targetViolationCode out = .ok (some "INVALID_BOUNDS") ∧
        after = before) := by
  obtain ⟨_, rfl⟩ := checkGenerated_balanceProgram hc
  have rep := balanceCanonicalConstructed_rep lang b
  have construct := targetConstruct_sound lang b hb
  have view := rep.view
  by_cases hg : n ≤ 0
  · obtain ⟨hs, hp, hv, hw, ha, _⟩ := step_guard_reject lang b n hb hn hg
    refine ⟨_, _, ⟨"Ready", b, [], none, b, false⟩,
      ⟨"Ready", b, [], none, b, false⟩,
      construct, rep.heapWF, rep, view, hs, hw, ha, ?_, rfl, rfl,
      (fun _ => ⟨hv, rfl⟩), ?_, ?_⟩
    · rw [generated_balance_guard_reject b n hb.1 hb.2 hn.1 hg]
      exact hp
    · intro h; omega
    · intro h; omega
  · have hnpos : 0 < n := by omega
    by_cases hle : n ≤ b
    · obtain ⟨hs, hp, hv, hw, ha⟩ := step_accept lang b n hb ⟨hnpos, hn.2⟩ hle
      refine ⟨_, _, ⟨"Ready", b, [], none, b, false⟩,
        ⟨"Ready", b - n, [expectedRecord lang n], some ⟨"Ready", b, []⟩, b, false⟩,
        construct, rep.heapWF, rep, view, hs, hw, ha, ?_, rfl, rfl,
        ?_, (fun _ => ⟨hv, rfl, rfl, rfl, rfl⟩), ?_⟩
      · rw [generated_balance_accept b n hb.1 hb.2 hnpos hle]
        exact hp
      · intro h; omega
      · intro h; omega
    · have hlt : b < n := by omega
      obtain ⟨hs, hp, hv, hw, ha, _⟩ := step_bounds_reject lang b n hb ⟨hnpos, hn.2⟩ hlt
      refine ⟨_, _, ⟨"Ready", b, [], none, b, false⟩,
        ⟨"Ready", b, [], none, b, false⟩,
        construct, rep.heapWF, rep, view, hs, hw, ha, ?_, rfl, rfl,
        ?_, ?_, (fun _ => ⟨hv, rfl⟩)⟩
      · rw [generated_balance_bounds_reject b n hb.1 hb.2 hlt hn.2]
        exact hp
      · intro h; omega
      · intro h; omega

/-- Source-bound guard reject branch. -/
theorem k02_balance_one_call_guard_reject (lang : TargetLang) (source : String)
    (program : TargetProgram)
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hbranch : n ≤ 0) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed lang b) = .ok machine ∧
      HeapWF lang machine ∧
      BalanceRep lang b machine ∧ balanceView lang machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest lang n) = .ok out ∧
      HeapWF lang out.machine ∧
      balanceView lang out.machine = .ok after ∧
      targetProjection lang out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      targetViolationCode out = .ok (some "GUARD_FAILED") ∧
        after = before := by
  obtain ⟨m, out, before, after, hcst, hw, hr, hbefore, hs, hwout, hafter, hp, hready, hidle, hg, ha, hbnd⟩ :=
    k02_balance_one_call lang source program hc b n hb hn
  exact ⟨m, out, before, after, hcst, hw, hr, hbefore, hs, hwout, hafter, hp, hready, hidle, hg hbranch⟩

/-- Source-bound accept branch. -/
theorem k02_balance_one_call_accept (lang : TargetLang) (source : String)
    (program : TargetProgram)
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hbranch : 0 < n ∧ n ≤ b) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed lang b) = .ok machine ∧
      HeapWF lang machine ∧
      BalanceRep lang b machine ∧ balanceView lang machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest lang n) = .ok out ∧
      HeapWF lang out.machine ∧
      balanceView lang out.machine = .ok after ∧
      targetProjection lang out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      targetViolationCode out = .ok none ∧
        after.balance = b - n ∧ after.history = [expectedRecord lang n] ∧
        after.undo = some ⟨"Ready", b, []⟩ ∧
        after.constructorSeed = b := by
  obtain ⟨m, out, before, after, hcst, hw, hr, hbefore, hs, hwout, hafter, hp, hready, hidle, hg, ha, hbnd⟩ :=
    k02_balance_one_call lang source program hc b n hb hn
  exact ⟨m, out, before, after, hcst, hw, hr, hbefore, hs, hwout, hafter, hp, hready, hidle, ha hbranch⟩

/-- Source-bound bounds reject branch. -/
theorem k02_balance_one_call_bounds_reject (lang : TargetLang) (source : String)
    (program : TargetProgram)
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S)
    (hbranch : n > b) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed lang b) = .ok machine ∧
      HeapWF lang machine ∧
      BalanceRep lang b machine ∧ balanceView lang machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest lang n) = .ok out ∧
      HeapWF lang out.machine ∧
      balanceView lang out.machine = .ok after ∧
      targetProjection lang out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      targetViolationCode out = .ok (some "INVALID_BOUNDS") ∧
        after = before := by
  obtain ⟨m, out, before, after, hcst, hw, hr, hbefore, hs, hwout, hafter, hp, hready, hidle, hg, ha, hbnd⟩ :=
    k02_balance_one_call lang source program hc b n hb hn
  exact ⟨m, out, before, after, hcst, hw, hr, hbefore, hs, hwout, hafter, hp, hready, hidle, hbnd hbranch⟩

/-- Universal source-bound ts specialization. -/
theorem k02_balance_ts_one_call (source : String)
    (program : TargetProgram)
    (hc : checkGenerated .ts source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed .ts b) = .ok machine ∧
      HeapWF .ts machine ∧
      BalanceRep .ts b machine ∧ balanceView .ts machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest .ts n) = .ok out ∧
      HeapWF .ts out.machine ∧
      balanceView .ts out.machine = .ok after ∧
      targetProjection .ts out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      (n ≤ 0 → targetViolationCode out = .ok (some "GUARD_FAILED") ∧
        after = before) ∧
      (0 < n ∧ n ≤ b → targetViolationCode out = .ok none ∧
        after.balance = b - n ∧ after.history = [expectedRecord .ts n] ∧
        after.undo = some ⟨"Ready", b, []⟩ ∧
        after.constructorSeed = b) ∧
      (n > b → targetViolationCode out = .ok (some "INVALID_BOUNDS") ∧
        after = before) :=
  k02_balance_one_call .ts source program hc b n hb hn

/-- Universal source-bound python specialization. -/
theorem k02_balance_python_one_call (source : String)
    (program : TargetProgram)
    (hc : checkGenerated .python source balanceRaw balanceCandidate = .ok program)
    (b n : Int) (hb : 0 ≤ b ∧ b ≤ Harmonia.Applications.Kadmos.S)
    (hn : -Harmonia.Applications.Kadmos.S ≤ n ∧ n ≤ Harmonia.Applications.Kadmos.S) :
    ∃ machine out before after,
      targetConstruct program (canonicalBalanceSeed .python b) = .ok machine ∧
      HeapWF .python machine ∧
      BalanceRep .python b machine ∧ balanceView .python machine = .ok before ∧
      targetStep program machine (canonicalDebitRequest .python n) = .ok out ∧
      HeapWF .python out.machine ∧
      balanceView .python out.machine = .ok after ∧
      targetProjection .python out = .ok
        (balanceSourceProjection (interpret balanceCandidate
          (generatedBalanceState b) (generatedBalanceRequest n))) ∧
      after.state = "Ready" ∧ after.busy = false ∧
      (n ≤ 0 → targetViolationCode out = .ok (some "GUARD_FAILED") ∧
        after = before) ∧
      (0 < n ∧ n ≤ b → targetViolationCode out = .ok none ∧
        after.balance = b - n ∧ after.history = [expectedRecord .python n] ∧
        after.undo = some ⟨"Ready", b, []⟩ ∧
        after.constructorSeed = b) ∧
      (n > b → targetViolationCode out = .ok (some "INVALID_BOUNDS") ∧
        after = before) :=
  k02_balance_one_call .python source program hc b n hb hn

end Harmonia.Applications.Kadmos.Generated
