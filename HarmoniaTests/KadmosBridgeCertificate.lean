import Harmonia.Applications.Kadmos.Bridge.Certificate
open Harmonia.Applications.Kadmos.Bridge
#check checkBridge
#check lowerExpr_sound
#check checkBridge_exact
open Harmonia.Applications.Kadmos
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
private def smallRaw : RawWorld :=
  { version := "kadmos.world.v0", name := "Small", description := none,
    states := [{ id := "A", initial := true, terminal := false, description := none }],
    context := [("x", ⟨"integer",some 0,some 100,some 1,none,none⟩)],
    invariants := [{ id := "nonnegative", predicate := "x >= 0", description := none }],
    transitions := [⟨"STEP","A","A",.expr "event.amount > 0",
      ["x = x - event.amount"],none⟩],
    fields := ["amount"], extras := [] }
private def smallCandidate : World 1 1 1 1 :=
  ⟨(fun _ => "A"),(fun _ => true),(fun _ => false),(fun _ => "x"),
    (fun _ => ⟨0,100,some 1⟩),(fun _ => "amount"),(fun _ => "STEP"),
    (fun _ => ⟨0,0,.not (.le (.request 0) (.int 0)),
      [⟨0,.sub (.context 0) (.request 0)⟩],none⟩),
    [("nonnegative",.not (.lt (.context 0) (.int 0)))]⟩
example : (checkBridge smallRaw smallCandidate).toOption.isSome = true := by decide +kernel
example : (projectWorld { smallRaw with extras := ["bad"] }).toOption.isSome = false := by decide +kernel
example : (projectWorld { smallRaw with fields := ["unused"] }).toOption.isSome = false := by decide +kernel
example : decide (NamesWF smallRaw smallRaw.fields) = true := by decide +kernel
private def twoRaw : RawWorld :=
  { smallRaw with fields := ["amount","fee"], transitions :=
    [⟨"STEP","A","A",.expr "event.amount > 0 && event.fee >= 0",
      ["x = x - event.amount"],none⟩] }
private def twoCandidate : World 1 1 2 1 :=
  ⟨(fun _ => "A"),(fun _ => true),(fun _ => false),(fun _ => "x"),
    (fun _ => ⟨0,100,some 1⟩),(fun j => if j == 0 then "amount" else "fee"),
    (fun _ => "STEP"),
    (fun _ => ⟨0,0,.and (.not (.le (.request 0) (.int 0)))
      (.not (.lt (.request 1) (.int 0))),[⟨0,.sub (.context 0) (.request 0)⟩],none⟩),
    [("nonnegative",.not (.lt (.context 0) (.int 0)))]⟩
private def swappedCandidate : World 1 1 2 1 :=
  { twoCandidate with fieldIds := fun j => if j == 0 then "fee" else "amount" }
example : (checkBridge twoRaw twoCandidate).toOption.isSome = true := by decide +kernel
example : (checkBridge twoRaw swappedCandidate).toOption.isSome = false := by decide +kernel
private def dupPhase : RawWorld :=
  { smallRaw with states := [{id := "A", initial := true, terminal := false, description := none},
    {id := "A", initial := false, terminal := false, description := none}] }
example : (projectWorld dupPhase).toOption.isSome = false := by decide +kernel
example : (lowerExpr dupPhase [] (.stateEq "A")).toOption.isSome = true := by decide +kernel
example : (projectWorld { smallRaw with context := [("state",⟨"integer",some 0,some 1,some 0,none,none⟩)] }).toOption.isSome = false := by decide +kernel
example : (projectWorld { smallRaw with invariants :=
  [{id := "bad", predicate := "event.amount > 0", description := none}] }).toOption.isSome = false := by decide +kernel
example : (projectWorld { smallRaw with context :=
  [("x",⟨"integer",none,some 100,some 1,none,none⟩)] }).toOption.isSome = false := by decide +kernel
example : (projectWorld { smallRaw with context :=
  [("x",⟨"string",some 0,some 100,some 1,none,none⟩)] }).toOption.isSome = false := by decide +kernel
example : (projectWorld { smallRaw with transitions :=
  [⟨"STEP","A","A",.expr "event.amount > 0",["x = state == 'A'"],none⟩] }).toOption.isSome = false := by decide +kernel
private def directiveCandidate : World 1 1 1 1 :=
  { smallCandidate with transitions := fun _ =>
    ⟨0,0,.not (.le (.request 0) (.int 0)),[⟨0,.sub (.context 0) (.request 0)⟩],some "SEND"⟩ }
example : (checkBridge smallRaw directiveCandidate).toOption.isSome = false := by decide +kernel
