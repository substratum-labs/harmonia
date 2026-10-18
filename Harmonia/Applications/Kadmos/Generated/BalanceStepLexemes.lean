import Harmonia.Applications.Kadmos.Generated.TargetSemantics
namespace Harmonia.Applications.Kadmos.Generated
namespace BalanceStepLexemes
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
theorem token0 : tokenMatchAt "event.amount > 0" 0 = some ⟨"event", 0, 5, []⟩ := by decide +kernel
theorem token5 : tokenMatchAt "event.amount > 0" 5 = some ⟨".", 5, 6, []⟩ := by decide +kernel
theorem token6 : tokenMatchAt "event.amount > 0" 6 = some ⟨"amount", 6, 12, []⟩ := by decide +kernel
theorem token12 : tokenMatchAt "event.amount > 0" 12 = some ⟨" ", 12, 13, []⟩ := by decide +kernel
theorem token13 : tokenMatchAt "event.amount > 0" 13 = some ⟨">", 13, 14, []⟩ := by decide +kernel
theorem token14 : tokenMatchAt "event.amount > 0" 14 = some ⟨" ", 14, 15, []⟩ := by decide +kernel
theorem token15 : tokenMatchAt "event.amount > 0" 15 = some ⟨"0", 15, 16, []⟩ := by decide +kernel
theorem spaceEvent (m : TargetMachine) : hostCall .python m .stringIsSpace
 (some (.string "event")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem spaceDot (m : TargetMachine) : hostCall .python m .stringIsSpace
 (some (.string ".")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem spaceAmount (m : TargetMachine) : hostCall .python m .stringIsSpace
 (some (.string "amount")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem spaceOperator (m : TargetMachine) : hostCall .python m .stringIsSpace
 (some (.string ">")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem spaceZero (m : TargetMachine) : hostCall .python m .stringIsSpace
 (some (.string "0")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem spaceSpace (m : TargetMachine) : hostCall .python m .stringIsSpace
 (some (.string " ")) [] = .ok ⟨m, .ok (.bool true)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem startsEvent (m : TargetMachine) : hostCall .python m .stringStartsWith
 (some (.string "event")) [.string "'"] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem startsZero (m : TargetMachine) : hostCall .python m .stringStartsWith
 (some (.string "0")) [.string "'"] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem digitEvent (m : TargetMachine) : hostCall .python m .stringIsDigit
 (some (.string "e")) [] = .ok ⟨m, .ok (.bool false)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem digitZero (m : TargetMachine) : hostCall .python m .stringIsDigit
 (some (.string "0")) [] = .ok ⟨m, .ok (.bool true)⟩ := by
 rw [hostCall.eq_def]; with_unfolding_all rfl
theorem nameEvent : identifierFullMatch "event" = true := by decide +kernel
theorem nameAmount : identifierFullMatch "amount" = true := by decide +kernel
theorem nameZero : identifierFullMatch "0" = false := by decide +kernel
theorem floatZero (m : TargetMachine) : hostCall .python m .float none [.string "0"] =
 .ok ⟨m, .ok (.number .pyFloat 0)⟩ := by rw [hostCall.eq_def]; with_unfolding_all rfl
end BalanceStepLexemes
end Harmonia.Applications.Kadmos.Generated
