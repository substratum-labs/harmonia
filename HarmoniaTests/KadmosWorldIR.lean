import Harmonia.Applications.Kadmos.World
namespace Harmonia.Applications.Kadmos.Tests.IR
example : decode (fun _ : Fin 1 => .string "30") = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .bool true) = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .null) = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .missing) = .error (.inputType 0) := by rfl
example : decode (fun _ : Fin 1 => .invalidNumber) = .error (.inputRange 0) := by rfl
example : decode (fun _ : Fin 1 => .int (S+1)) = .error (.inputRange 0) := by rfl
example : decode (Fin.elim0 : Fin 0 → RawPrimitive) = .ok Fin.elim0 := by
  have h : ∀ j : Fin 0, inputValid (Fin.elim0 j) := fun j => Fin.elim0 j
  rw [decode, if_pos h]
  congr 1; funext j; exact Fin.elim0 j
example : decode (fun j : Fin 2 => if j = 0 then .int 30 else .missing) =
    .error (.inputType 1) := by rfl
example : decode (fun j : Fin 2 => if j = 0 then .int 30 else .int (S+1)) =
    .error (.inputRange 1) := by rfl

def bad : Expr 1 0 0 := .eqInt (.add (.int S) (.int 1)) (.int 0)
example : eval (0 : Fin 1) Fin.elim0 Fin.elim0 (.int (S+1)) = .error .overflow := by rfl
example : eval (0 : Fin 1) (fun _ : Fin 1 => S+1) Fin.elim0 (.context 0) = .error .overflow := by rfl
example : eval (0 : Fin 1) Fin.elim0 Fin.elim0
  (.sub (.add (.int S) (.int 1)) (.int 1)) = .error .overflow := by rfl
example : eval (0 : Fin 1) Fin.elim0 Fin.elim0 (.and (.bool false) bad) = .error .overflow := by rfl
example : eval (0 : Fin 1) Fin.elim0 Fin.elim0 (.or (.bool true) bad) = .error .overflow := by rfl
example : eval (0 : Fin 1) Fin.elim0 Fin.elim0 (.implies (.bool false) bad) = .error .overflow := by rfl
example : eval (0 : Fin 1) Fin.elim0 Fin.elim0 (.not bad) = .error .overflow := by rfl
end Harmonia.Applications.Kadmos.Tests.IR
namespace Harmonia.Applications.Kadmos.Tests.IR

def initWorld (flags : Bool) (lo hi : Int) (d : Option Int) : World 1 1 0 0 where
  phaseIds _ := "Ready"
  initialFlags _ := flags
  terminalFlags _ := false
  contextIds _ := "balance"
  variables _ := ⟨lo, hi, d⟩
  fieldIds := Fin.elim0
  actionIds := Fin.elim0
  transitions := Fin.elim0
  invariants := []
example : «initialize» (initWorld true 0 S (some 100)) = .ok ⟨0,fun _ => 100⟩ := by rfl
example : «initialize» (initWorld false 0 S (some 100)) = .error .initialCount := by rfl
example : «initialize» (initWorld true 2 1 (some 100)) = .error .invalidBounds := by rfl
example : «initialize» (initWorld true (-1) S (some 100)) = .error .invalidBounds := by rfl
example : «initialize» (initWorld true 0 (S+1) (some 100)) = .error .invalidBounds := by rfl
example : «initialize» (initWorld true 0 S (some (-1))) = .error .invalidDefault := by rfl
example : «initialize» (initWorld true 1 S none) = .error .invalidDefault := by rfl
example : «initialize» (initWorld true 0 S none) = .ok ⟨0,fun _ => 0⟩ := by rfl
example : «initialize» {initWorld true 0 S (some 100) with invariants := [("I",.bool false)]} =
  .error .initialInvariant := by rfl
example : «initialize» {initWorld true 0 S (some S) with
  invariants := [("I",.le (.add (.context 0) (.int 1)) (.int S))]} = .error .initialInvariant := by rfl

def empty : World 0 0 0 0 :=
  ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,[]⟩
example : «initialize» empty = .error .initialCount := by rfl

def inert : World 1 0 0 0 :=
  ⟨fun _ => "Ready",fun _ => true,fun _ => false,Fin.elim0,Fin.elim0,
    Fin.elim0,Fin.elim0,Fin.elim0,[]⟩
example : («initialize» inert).isOk = true := by rfl

def twoInitial : World 2 0 0 0 :=
  ⟨fun j => if j=0 then "A" else "B",fun _ => true,fun _ => false,Fin.elim0,
    Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,[]⟩
example : «initialize» twoInitial = .error .initialCount := by rfl
example : «initialize» {twoInitial with phaseIds := fun _ => "A"} = .error .phaseIds := by rfl
end Harmonia.Applications.Kadmos.Tests.IR

namespace KadmosNamespaceEscape
theorem marker : True := True.intro
end KadmosNamespaceEscape
