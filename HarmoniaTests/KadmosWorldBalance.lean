import Harmonia.Applications.Kadmos.Balance
import HarmoniaTests.KadmosWorldInterpreter
namespace Harmonia.Applications.Kadmos.Tests.Balance
example : «initialize» balanceWorld = .ok (balanceState 100) := by rfl
example : interpret balanceWorld (balanceState 100) (debit 30) =
  ⟨balanceState (100-30),⟨.accepted,none⟩⟩ := by
  exact debit_accept 100 30 (by decide) (by decide) (by decide) (by decide)
example : interpret balanceWorld (balanceState 100) (debit 130) =
  ⟨balanceState 100,⟨.rejected (.bounds 0),none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) (debit 100) =
  ⟨balanceState 0,⟨.accepted,none⟩⟩ := debit_accept 100 100 (by decide) (by decide) (by decide) (by decide)
example : interpret balanceWorld (balanceState 0) (debit 1) =
  ⟨balanceState 0,⟨.rejected (.bounds 0),none⟩⟩ := debit_insufficient 0 1 (by decide) (by decide) (by decide) (by decide)
end Harmonia.Applications.Kadmos.Tests.Balance
namespace Harmonia.Applications.Kadmos.Tests.Balance
open Harmonia.Applications.Kadmos.Tests.Interpreter
example : interpret balanceWorld (balanceState 100) (debit 0) =
  ⟨balanceState 100,⟨.rejected .guardFalse,none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) (debit (-1)) =
  ⟨balanceState 100,⟨.rejected .guardFalse,none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) {debit 30 with payload := fun _ => .bool true} =
  ⟨balanceState 100,⟨.rejected (.inputType 0),none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) {debit 30 with payload := fun _ => .string "30"} =
  ⟨balanceState 100,⟨.rejected (.inputType 0),none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) {debit 30 with payload := fun _ => .null} =
  ⟨balanceState 100,⟨.rejected (.inputType 0),none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) {debit 30 with payload := fun _ => .missing} =
  ⟨balanceState 100,⟨.rejected (.inputType 0),none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) (debit (S+1)) =
  ⟨balanceState 100,⟨.rejected (.inputRange 0),none⟩⟩ := by rfl
example : interpret balanceWorld (balanceState 100) {debit 30 with payload := fun _ => .invalidNumber} =
  ⟨balanceState 100,⟨.rejected (.inputRange 0),none⟩⟩ := by rfl
example : interpret {world [⟨0,.int 40⟩] with invariants := [("I",.le (.int 50) (.context 0))]} state request =
  ⟨state,⟨.rejected (.invariant 0),none⟩⟩ := by rfl
example : interpret {world [⟨0,.int S⟩] with invariants := [("I",.le (.add (.context 0) (.int 1)) (.int S))]} state request =
  ⟨state,⟨.rejected (.invariant 0),none⟩⟩ := by rfl

def phaseWorld : World 2 1 0 1 := {twoPhase with
  transitions := fun _ => ⟨0,1,.stateIs 0,[⟨0,.int 70⟩],none⟩
  invariants := [("A",.implies (.stateIs 0) (.eqInt (.context 0) (.int 100))),
    ("B",.implies (.stateIs 1) (.eqInt (.context 0) (.int 70)))]}
example : checkState phaseWorld ⟨1,fun _ => 70⟩ = true := by rfl
example : checkState phaseWorld ⟨0,fun _ => 70⟩ = false := by rfl
example : interpret phaseWorld phaseState request = ⟨⟨1,fun _ => 70⟩,⟨.accepted,none⟩⟩ := by
  have hc := finOne_context_eq (interpret phaseWorld phaseState request).state.context 70 (by rfl)
  change Result.mk (State.mk 1 (interpret phaseWorld phaseState request).state.context) ⟨.accepted,none⟩ = _
  rw [hc]
end Harmonia.Applications.Kadmos.Tests.Balance
