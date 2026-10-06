import Harmonia.Applications.Kadmos.Interpreter
import HarmoniaTests.KadmosWorldIR
namespace Harmonia.Applications.Kadmos.Tests.Interpreter

def increment : Effect 1 2 0 := ⟨0,.add (.context 0) (.int 1)⟩
def copy : Effect 1 2 0 := ⟨1,.context 0⟩
def start : Fin 2 → Int := fun x => if x=0 then 1 else 0
example : (runEffects (0 : Fin 1) Fin.elim0 [increment,copy] start).map
  (fun c => (c 0,c 1)) = .ok (2,2) := by rfl
example : (runEffects (0 : Fin 1) Fin.elim0 [copy,increment] start).map
  (fun c => (c 0,c 1)) = .ok (2,1) := by rfl
example : (runEffects (0 : Fin 1) Fin.elim0 [increment,increment] start).map
  (fun c => (c 0,c 1)) = .ok (3,0) := by rfl
example : runEffects (0 : Fin 1) Fin.elim0 [] start = .ok start := by rfl

def world (effects : List (Effect 1 1 0)) : World 1 1 0 1 where
  phaseIds _ := "Ready"
  initialFlags _ := true
  terminalFlags _ := false
  contextIds _ := "balance"
  variables _ := ⟨0,S,some 100⟩
  fieldIds := Fin.elim0
  actionIds _ := "DO"
  transitions _ := ⟨0,0,.bool true,effects,none⟩
  invariants := []
def state : State 1 1 := ⟨0,fun _ => 100⟩
def request : Request 0 := ⟨"DO",Fin.elim0,none⟩
def subtract : Effect 1 1 0 := ⟨0,.sub (.context 0) (.int 150)⟩
def add : Effect 1 1 0 := ⟨0,.add (.context 0) (.int 150)⟩
example : (interpret (world [subtract,add]) state request).observation = ⟨.accepted,none⟩ := by rfl
example : (interpret (world [subtract,add]) state request).state.context 0 = 100 := by rfl
example : (interpret (world [add,subtract]) state request).observation = ⟨.accepted,none⟩ := by rfl
example : (interpret (world [add,subtract]) state request).state.context 0 = 100 := by rfl
example : interpret (world [subtract]) state request =
  ⟨state,⟨.rejected (.bounds 0),none⟩⟩ := by rfl
example : interpret (world [⟨0,.int 101⟩,⟨0,.add (.int S) (.int 1)⟩]) state request =
  ⟨state,⟨.rejected (.effectError .overflow),none⟩⟩ := by rfl
example : interpret (world []) state {request with actionId := "UNKNOWN"} =
  ⟨state,⟨.rejected .unknownAction,none⟩⟩ := by rfl
end Harmonia.Applications.Kadmos.Tests.Interpreter
namespace Harmonia.Applications.Kadmos.Tests.Interpreter

theorem singleton_context (c : Fin 1 → Int) (n : Int) (h : c 0 = n) : c = fun _ => n := by
  funext y
  have hy : y = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ y.isLt))
  rw [hy]; exact h

example : interpret (world [subtract,add]) state request = ⟨state,⟨.accepted,none⟩⟩ := by
  have hc := singleton_context (interpret (world [subtract,add]) state request).state.context 100 (by rfl)
  change Result.mk (State.mk 0 (interpret (world [subtract,add]) state request).state.context) ⟨.accepted,none⟩ = _
  rw [hc]; rfl
example : interpret (world [add,subtract]) state request = ⟨state,⟨.accepted,none⟩⟩ := by
  have hc := singleton_context (interpret (world [add,subtract]) state request).state.context 100 (by rfl)
  change Result.mk (State.mk 0 (interpret (world [add,subtract]) state request).state.context) ⟨.accepted,none⟩ = _
  rw [hc]; rfl
example : interpret (world []) state request = ⟨state,⟨.accepted,none⟩⟩ := by rfl

def inputWorld {f : Nat} (guard : Expr 1 1 f) (directive : Option String := none) : World 1 1 f 1 :=
  ⟨fun _ => "Ready",fun _ => true,fun _ => false,fun _ => "balance",fun _ => ⟨0,S,some 100⟩,
    fun j => if j.val=0 then "amount" else "unused",fun _ => "DO",
    fun _ => ⟨0,0,guard,[],directive⟩,[]⟩
def inputRequest (raw : RawPrimitive) (proposal : Option String := none) : Request 1 :=
  ⟨"DO",fun _ => raw,proposal⟩
example : interpret (inputWorld (.bool false)) state (inputRequest (.string "30")) =
  ⟨state,⟨.rejected (.inputType 0),none⟩⟩ := by rfl
example : interpret (inputWorld (.bool false)) state (inputRequest (.int (S+1))) =
  ⟨state,⟨.rejected (.inputRange 0),none⟩⟩ := by rfl
example : interpret (inputWorld (.bool false)) state (inputRequest .invalidNumber) =
  ⟨state,⟨.rejected (.inputRange 0),none⟩⟩ := by rfl
example : interpret (inputWorld (.bool false)) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected .guardFalse,none⟩⟩ := by rfl
example : interpret (inputWorld (.int 1)) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected (.guardError .expectedBool),none⟩⟩ := by rfl
example : interpret (inputWorld (.bool true) (some "SEND")) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected .unauthorizedDirective,none⟩⟩ := by rfl
example : interpret (inputWorld (.bool true) (some "SEND")) state (inputRequest (.int 30) (some "NO")) =
  ⟨state,⟨.rejected .unauthorizedDirective,none⟩⟩ := by rfl
example : interpret (inputWorld (.bool true) (some "SEND")) state (inputRequest (.int 30) (some "")) =
  ⟨state,⟨.rejected .unauthorizedDirective,none⟩⟩ := by rfl
example : interpret (inputWorld (.bool true) (some "SEND")) state (inputRequest (.int 30) (some "SEND")) =
  ⟨state,⟨.accepted,some "SEND"⟩⟩ := by rfl
example : interpret (inputWorld (.bool true)) state (inputRequest (.int 30)) =
  ⟨state,⟨.accepted,none⟩⟩ := by rfl
example : interpret (inputWorld (.bool false)) state
    (⟨"DO",fun j : Fin 2 => if j=0 then .int 30 else .missing,none⟩) =
  ⟨state,⟨.rejected (.inputType 1),none⟩⟩ := by rfl
example : interpret (inputWorld (.bool false)) state
    (⟨"DO",fun j : Fin 2 => if j=0 then .int 30 else .int (S+1),none⟩) =
  ⟨state,⟨.rejected (.inputRange 1),none⟩⟩ := by rfl

def badGuard : Expr 1 1 1 := .eqInt (.add (.int S) (.int 1)) (.int 0)
example : interpret (inputWorld (.and (.bool false) badGuard)) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected (.guardError .overflow),none⟩⟩ := by rfl
example : interpret (inputWorld (.or (.bool true) badGuard)) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected (.guardError .overflow),none⟩⟩ := by rfl
example : interpret (inputWorld (.implies (.bool false) badGuard)) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected (.guardError .overflow),none⟩⟩ := by rfl
example : interpret (inputWorld (.not badGuard)) state (inputRequest (.int 30)) =
  ⟨state,⟨.rejected (.guardError .overflow),none⟩⟩ := by rfl

def twoPhase : World 2 1 0 1 :=
  ⟨fun j => if j=0 then "A" else "B",fun j => j==0,fun _ => false,fun _ => "balance",
    fun _ => ⟨0,S,some 100⟩,Fin.elim0,fun _ => "DO",fun _ => ⟨1,1,.bool true,[],some "SEND"⟩,[]⟩
def phaseState : State 2 1 := ⟨0,fun _ => 100⟩
example : interpret twoPhase phaseState {request with proposedDirective := some "NO"} =
  ⟨phaseState,⟨.rejected .wrongPhase,none⟩⟩ := by rfl
example : interpret twoPhase phaseState {request with actionId := "UNKNOWN"} =
  ⟨phaseState,⟨.rejected .unknownAction,none⟩⟩ := by rfl
example : eval (1 : Fin 2) (fun _ : Fin 1 => 100) Fin.elim0 (.stateIs 1) = .ok (.bool true) := by rfl
example : runTransitionEffects (⟨0,1,.bool true,[⟨0,.stateIs 1⟩],none⟩ : Transition 2 1 0)
  Fin.elim0 phaseState = .error .expectedInt := by rfl

example : interpret {world [] with variables := fun _ => ⟨2,1,some 100⟩} state request =
  ⟨state,⟨.rejected (.malformedSpec .invalidBounds),none⟩⟩ := by rfl
example : interpret {world [] with variables := fun _ => ⟨(-1),S,some 100⟩} state request =
  ⟨state,⟨.rejected (.malformedSpec .invalidBounds),none⟩⟩ := by rfl
example : interpret {world [] with variables := fun _ => ⟨0,S+1,some 100⟩} state request =
  ⟨state,⟨.rejected (.malformedSpec .invalidBounds),none⟩⟩ := by rfl
example : interpret {world [] with actionIds := fun _ => ""} state request =
  ⟨state,⟨.rejected (.malformedSpec .actionIds),none⟩⟩ := by rfl
example : interpret {world [] with terminalFlags := fun _ => true} state request =
  ⟨state,⟨.rejected (.malformedSpec .terminalSource),none⟩⟩ := by rfl
example : interpret {world [] with variables := fun _ => ⟨0,S,some (-1)⟩} state request =
  ⟨state,⟨.rejected (.malformedSpec .invalidDefault),none⟩⟩ := by rfl
example : interpret {twoPhase with initialFlags := fun _ => true} phaseState request =
  ⟨phaseState,⟨.rejected (.malformedSpec .initialCount),none⟩⟩ := by rfl

def duplicateActions : World 1 1 0 2 :=
  ⟨fun _ => "Ready",fun _ => true,fun _ => false,fun _ => "balance",fun _ => ⟨0,S,some 100⟩,
    Fin.elim0,fun _ => "DO",fun _ => ⟨0,0,.bool true,[],none⟩,[]⟩
example : interpret duplicateActions state request =
  ⟨state,⟨.rejected (.malformedSpec .actionIds),none⟩⟩ := by rfl
example : interpret {world [] with invariants := [("I",.bool false)]} state request =
  ⟨state,⟨.rejected (.malformedSpec .initialInvariant),none⟩⟩ := by rfl
example : interpret {world [] with
    variables := fun _ => ⟨0,S,some S⟩
    invariants := [("I",.le (.add (.context 0) (.int 1)) (.int S))]} state request =
  ⟨state,⟨.rejected (.malformedSpec .initialInvariant),none⟩⟩ := by rfl
example : interpret IR.inert (⟨0,Fin.elim0⟩ : State 1 0) request =
  ⟨⟨0,Fin.elim0⟩,⟨.rejected .unknownAction,none⟩⟩ := by rfl
end Harmonia.Applications.Kadmos.Tests.Interpreter
namespace Harmonia.Applications.Kadmos.Tests.Interpreter
example {w : World p v f a} (s : State p v) (r : Request f) {j : Fin f}
    (h : ¬ inputValid (r.payload j)) :
    ∃ e, interpret w s r = ⟨s,⟨.rejected e,none⟩⟩ := interpret_invalid_input h
end Harmonia.Applications.Kadmos.Tests.Interpreter
