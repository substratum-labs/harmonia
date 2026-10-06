import Harmonia.Applications.Kadmos.Bridge.Syntax
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open Harmonia.Applications.Kadmos.Bridge
open Harmonia.Applications.Kadmos

example : (parseSourceExpr "event.amount > 0").toOption = some (.gt (.field .event "amount") (.int 0)) := by decide
example : (parseSourceExpr "state == 'B' => y == x").toOption = some (.implies (.stateEq "B") (.eqInt (.context "y") (.context "x"))) := by decide
example : (parseSourceExpr "a => b => c").toOption = some (.implies (.context "a") (.implies (.context "b") (.context "c"))) := by decide
example : (parseSourceExpr "-1").toOption = none := by decide
example : (parseSourceExpr "1 != 2").toOption = none := by decide
example : (parseSourceExpr "null").toOption = none := by decide
example : (parseSourceExpr "event.a.b").toOption = none := by decide
example : (parseSourceExpr "1 2").toOption = none := by decide
example : (parseSourceExpr "(1+2)*3").toOption = none := by decide
private def zeroEnv : SourceEnv := ⟨"A",fun _ => 0,fun _ => 0⟩
example : sourceEval zeroEnv (.and (.bool false) (.lt (.add (.int S) (.int 1)) (.int 0))) = .ok (.bool false) := rfl
example : ¬ sourceSafe zeroEnv (.and (.bool false) (.lt (.add (.int S) (.int 1)) (.int 0))) := by
  intro h
  cases h with
  | and _ _ _ hright =>
    cases hright with
    | lt _ _ hleft _ =>
      cases hleft with
      | add _ _ _ _ hsum =>
        have hs := hsum S 1 (by rfl) (by rfl)
        dsimp [safeInt,S] at hs
        omega
example : sourceEval zeroEnv (.or (.bool true) (.lt (.add (.int S) (.int 1)) (.int 0))) = .ok (.bool true) := rfl
example : ¬ sourceSafe zeroEnv (.or (.bool true) (.lt (.add (.int S) (.int 1)) (.int 0))) := by
  intro h
  cases h with
  | or _ _ _ hright =>
    cases hright with
    | lt _ _ hleft _ =>
      cases hleft with
      | add _ _ _ _ hsum =>
        have hs := hsum S 1 (by rfl) (by rfl)
        dsimp [safeInt,S] at hs
        omega
example : sourceEval zeroEnv (.sub (.add (.int S) (.int 1)) (.int 1)) = .ok (.int S) := rfl
example : ¬ sourceSafe zeroEnv (.sub (.add (.int S) (.int 1)) (.int 1)) := by
  intro h
  cases h with
  | sub _ _ hleft _ _ =>
    cases hleft with
    | add _ _ _ _ hsum =>
      have hs := hsum S 1 (by rfl) (by rfl)
      dsimp [safeInt,S] at hs
      omega
example : (parseSourceExpr "state == 'B\\C'").toOption = none := by decide +kernel
