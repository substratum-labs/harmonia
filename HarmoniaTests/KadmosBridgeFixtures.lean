import Harmonia.Applications.Kadmos.Bridge.Fixtures
import Harmonia.Applications.Kadmos.System
open Harmonia.Applications.Kadmos
open Harmonia.Applications.Kadmos.Bridge
open Harmonia.Applications.Kadmos.BridgeFixtures
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Harmonia.Applications.Kadmos.BridgeFixtures.Tests

def balanceState (n : Int) : State 1 1 := ⟨0, fun _ => n⟩
def balanceRequest (n : Int) : Request 1 := ⟨"DEBIT",fun _ => .int n,none⟩
theorem balance_30 : interpret balanceCandidate (balanceState 100) (balanceRequest 30) =
  ⟨balanceState 70,⟨.accepted,none⟩⟩ := by
  have hp : (interpret balanceCandidate (balanceState 100) (balanceRequest 30)).state.phase = 0 := by decide +kernel
  have hc : (interpret balanceCandidate (balanceState 100) (balanceRequest 30)).state.context 0 = 70 := by decide +kernel
  have ho : (interpret balanceCandidate (balanceState 100) (balanceRequest 30)).observation = ⟨.accepted,none⟩ := by decide +kernel
  have hs : (interpret balanceCandidate (balanceState 100) (balanceRequest 30)).state = balanceState 70 := by
    cases h : (interpret balanceCandidate (balanceState 100) (balanceRequest 30)).state with
    | mk phase ctx =>
      have hphase : phase = 0 := by simpa [h] using hp
      have hcontext : ctx = (fun _ => (70 : Int)) := by
        funext j
        have hj : j = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
        rw [hj]
        simpa [h] using hc
      cases hphase
      cases hcontext
      rfl
  cases h : interpret balanceCandidate (balanceState 100) (balanceRequest 30) with
  | mk state obs =>
    have hst : state = balanceState 70 := by simpa [h] using hs
    have hob : obs = ⟨.accepted,none⟩ := by simpa [h] using ho
    cases hst
    cases hob
    rfl
theorem balance_20 : interpret balanceCandidate (balanceState 70) (balanceRequest 20) =
  ⟨balanceState 50,⟨.accepted,none⟩⟩ := by
  have hp : (interpret balanceCandidate (balanceState 70) (balanceRequest 20)).state.phase = 0 := by decide +kernel
  have hc : (interpret balanceCandidate (balanceState 70) (balanceRequest 20)).state.context 0 = 50 := by decide +kernel
  have ho : (interpret balanceCandidate (balanceState 70) (balanceRequest 20)).observation = ⟨.accepted,none⟩ := by decide +kernel
  have hs : (interpret balanceCandidate (balanceState 70) (balanceRequest 20)).state = balanceState 50 := by
    cases h : (interpret balanceCandidate (balanceState 70) (balanceRequest 20)).state with
    | mk phase ctx =>
      have hphase : phase = 0 := by simpa [h] using hp
      have hcontext : ctx = (fun _ => (50 : Int)) := by
        funext j
        have hj : j = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
        rw [hj]
        simpa [h] using hc
      cases hphase
      cases hcontext
      rfl
  cases h : interpret balanceCandidate (balanceState 70) (balanceRequest 20) with
  | mk state obs =>
    have hst : state = balanceState 50 := by simpa [h] using hs
    have hob : obs = ⟨.accepted,none⟩ := by simpa [h] using ho
    cases hst
    cases hob
    rfl
theorem balance_130 : interpret balanceCandidate (balanceState 100) (balanceRequest 130) =
  ⟨balanceState 100,⟨.rejected (.bounds 0),none⟩⟩ := by
  rfl
end Harmonia.Applications.Kadmos.BridgeFixtures.Tests

def orderInitial : State 2 2 := ⟨0,fun j => if j == 0 then 1 else 0⟩
def orderFinal : State 2 2 := ⟨1,fun _ => 2⟩
def orderRequest : Request 0 := ⟨"STEP",Fin.elim0,none⟩
theorem order_step : interpret orderCandidate orderInitial orderRequest =
  ⟨orderFinal,⟨.accepted,none⟩⟩ := by
  have hp : (interpret orderCandidate orderInitial orderRequest).state.phase = 1 := by decide +kernel
  have hx : (interpret orderCandidate orderInitial orderRequest).state.context 0 = 2 := by decide +kernel
  have hy : (interpret orderCandidate orderInitial orderRequest).state.context 1 = 2 := by decide +kernel
  have ho : (interpret orderCandidate orderInitial orderRequest).observation = ⟨.accepted,none⟩ := by decide +kernel
  have hs : (interpret orderCandidate orderInitial orderRequest).state = orderFinal := by
    cases h : (interpret orderCandidate orderInitial orderRequest).state with
    | mk phase ctx =>
      have hphase : phase = 1 := by simpa [h] using hp
      have hcontext : ctx = (fun _ => (2 : Int)) := by
        funext j
        by_cases hj : j = 0
        · simpa [h,hj] using hx
        · have hj1 : j = (1 : Fin 2) := by
            apply Fin.ext
            have hjlt := j.isLt
            have hj0 : j.val ≠ 0 := by intro hval; apply hj; exact Fin.ext hval
            omega
          simpa [h,hj1] using hy
      cases hphase
      cases hcontext
      rfl
  cases h : interpret orderCandidate orderInitial orderRequest with
  | mk state obs =>
    have hst : state = orderFinal := by simpa [h] using hs
    have hob : obs = ⟨.accepted,none⟩ := by simpa [h] using ho
    cases hst
    cases hob
    rfl

private def reversedRaw : RawWorld :=
  { orderRaw with transitions := [⟨"STEP","A","B",.bool true,["y = x","x = x + 1"],none⟩] }
private def reversedCandidate : World 2 2 0 1 :=
  { orderCandidate with transitions := fun _ =>
    ⟨0,1,.bool true,[⟨1,.context 0⟩,⟨0,.add (.context 0) (.int 1)⟩],none⟩ }
example : (checkBridge orderRaw reversedCandidate).toOption.isSome = false := by decide +kernel
example : (checkBridge reversedRaw reversedCandidate).toOption.isSome = true := by decide +kernel
theorem reversed_order_reject : interpret reversedCandidate orderInitial orderRequest =
  ⟨orderInitial,⟨.rejected (.invariant 0),none⟩⟩ := rfl
namespace Harmonia.Applications.Kadmos.BridgeFixtures.Tests
theorem balance_130_after50 : interpret balanceCandidate (balanceState 50) (balanceRequest 130) =
  ⟨balanceState 50,⟨.rejected (.bounds 0),none⟩⟩ := rfl

theorem balance_trace : Foundation.Execution (system balanceCandidate) (balanceState 100)
    [(balanceRequest 30,⟨.accepted,none⟩),(balanceRequest 20,⟨.accepted,none⟩),
      (balanceRequest 130,⟨.rejected (.bounds 0),none⟩)] (balanceState 50) := by
  exact .cons balance_30 (.cons balance_20 (.cons balance_130_after50 .nil))

end Harmonia.Applications.Kadmos.BridgeFixtures.Tests
namespace Harmonia.Applications.Kadmos.BridgeFixtures.Tests
private def rawRequest (r : RawPrimitive) : Request 1 := ⟨"DEBIT",fun _ => r,none⟩
example : (interpret balanceCandidate (balanceState 100) (rawRequest .missing)).observation.verdict = .rejected (.inputType 0) := by decide +kernel
example : (interpret balanceCandidate (balanceState 100) (rawRequest .null)).observation.verdict = .rejected (.inputType 0) := by decide +kernel
example : (interpret balanceCandidate (balanceState 100) (rawRequest (.bool true))).observation.verdict = .rejected (.inputType 0) := by decide +kernel
example : (interpret balanceCandidate (balanceState 100) (rawRequest (.string "30"))).observation.verdict = .rejected (.inputType 0) := by decide +kernel
example : (interpret balanceCandidate (balanceState 100) (rawRequest .invalidNumber)).observation.verdict = .rejected (.inputRange 0) := by decide +kernel
example : (interpret balanceCandidate (balanceState 100) (rawRequest (.int (S+1)))).observation.verdict = .rejected (.inputRange 0) := by decide +kernel
private def andOverflowRaw : RawWorld :=
  { balanceRaw with transitions := [⟨"DEBIT","Ready","Ready",
      .expr "false && (9007199254740991 + 1 < 0)",
      ["balance = balance - event.amount"],none⟩] }
private def andOverflowCandidate : World 1 1 1 1 :=
  { balanceCandidate with transitions := fun _ =>
      ⟨0,0,.and (.bool false) (.lt (.add (.int S) (.int 1)) (.int 0)),
        [⟨0,.sub (.context 0) (.request 0)⟩],none⟩ }
example : (checkBridge andOverflowRaw andOverflowCandidate).toOption.isSome = true := by decide +kernel
example : (interpret andOverflowCandidate (balanceState 100) (balanceRequest 30)).observation.verdict = .rejected (.guardError .overflow) := by decide +kernel
private def orOverflowRaw : RawWorld :=
  { balanceRaw with transitions := [⟨"DEBIT","Ready","Ready",
      .expr "true || (9007199254740991 + 1 < 0)",
      ["balance = balance - event.amount"],none⟩] }
private def orOverflowCandidate : World 1 1 1 1 :=
  { balanceCandidate with transitions := fun _ =>
      ⟨0,0,.or (.bool true) (.lt (.add (.int S) (.int 1)) (.int 0)),
        [⟨0,.sub (.context 0) (.request 0)⟩],none⟩ }
example : (checkBridge orOverflowRaw orOverflowCandidate).toOption.isSome = true := by decide +kernel
example : (interpret orOverflowCandidate (balanceState 100) (balanceRequest 30)).observation.verdict = .rejected (.guardError .overflow) := by decide +kernel
private def effectOverflowRaw : RawWorld :=
  { balanceRaw with transitions := [⟨"DEBIT","Ready","Ready",
      .expr "event.amount > 0",["balance = (9007199254740991 + 1) - 1"],none⟩] }
private def effectOverflowCandidate : World 1 1 1 1 :=
  { balanceCandidate with transitions := fun _ =>
      ⟨0,0,.not (.le (.request 0) (.int 0)),
        [⟨0,.sub (.add (.int S) (.int 1)) (.int 1)⟩],none⟩ }
example : (checkBridge effectOverflowRaw effectOverflowCandidate).toOption.isSome = true := by decide +kernel
example : (interpret effectOverflowCandidate (balanceState 100) (balanceRequest 30)).observation.verdict = .rejected (.effectError .overflow) := by decide +kernel
example : (lowerExpr balanceRaw balanceRaw.fields (.int (S+1))).toOption.isSome = false := by decide +kernel
end Harmonia.Applications.Kadmos.BridgeFixtures.Tests
