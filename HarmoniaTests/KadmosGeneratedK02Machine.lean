import Harmonia.Applications.Kadmos.Generated.TargetMachine

open Harmonia.Applications.Kadmos.Generated

private def emptyMachine : TargetMachine := TargetMachine.empty

example : sourceTruthy .ts emptyMachine .undefined = .ok false := by rfl
example : sourceTruthy .ts emptyMachine (.string "") = .ok false := by rfl
example : sourceTruthy .ts emptyMachine (.string "balance") = .ok true := by rfl
example : sourceTruthy .python emptyMachine (.number .pyInt 0) = .ok false := by rfl
example : sourceTruthy .python emptyMachine (.number .pyFloat 30) = .ok true := by rfl

private def emptyDict : HeapObject :=
  ⟨.pythonDict, none, [], [], [], false, false⟩
private def withDict : TargetMachine :=
  { emptyMachine with objects := [(1, emptyDict)] }
example : sourceTruthy .python withDict (.object 1) = .ok false := by rfl
example : sourceTruthy .ts withDict (.object 1) = .ok true := by rfl
example : sourceTruthy .python withDict (.object 2) = .error (.danglingObject 2) := by rfl

private def oneCell : TargetMachine :=
  { emptyMachine with cells := [(3, .number .pyInt 0)], nextCell := 4 }
example : readCell oneCell 3 = .ok (.number .pyInt 0) := by rfl
example : (writeCell oneCell 3 (.number .pyInt 1)).bind
    (fun m => readCell m 3) = .ok (.number .pyInt 1) := by rfl

private def balanceDescriptor : Descriptor :=
  ⟨some (.number .jsNumber 100), none, none, true, true, true⟩
private def balanceObject : HeapObject :=
  ⟨.jsOrdinary, some 0, [("balance", balanceDescriptor)], [], [], false, false⟩
private def balanceMachine : TargetMachine :=
  { emptyMachine with objects := [(1, balanceObject)] }
example : (readOwn balanceMachine 1 "balance").map (fun d => d.map Descriptor.value) =
    .ok (some (some (.number .jsNumber 100))) := by rfl
example : (writeOwn balanceMachine 1 "balance" (.number .jsNumber 70)).bind
    (fun m => (readOwn m 1 "balance").map (fun d => d.map Descriptor.value)) =
    .ok (some (some (.number .jsNumber 70))) := by rfl
