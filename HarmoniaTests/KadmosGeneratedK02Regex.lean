import Harmonia.Applications.Kadmos.Generated.TargetRegex

open Harmonia.Applications.Kadmos.Generated

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

example : (tokenMatchAt "balance >= 0" 0).map
    (fun m => (m.full, m.start, m.stop)) = some ("balance", 0, 7) := by decide +kernel
example : (tokenMatchAt "balance >= 0" 8).map
    (fun m => (m.full, m.start, m.stop)) = some (">=", 8, 10) := by decide +kernel
example : tokenizeWorldExpr "event.amount > 0" =
    some ["event", ".", "amount", ">", "0"] := by decide +kernel
example : tokenizeWorldExpr "balance - event.amount" =
    some ["balance", "-", "event", ".", "amount"] := by decide +kernel
example : tokenizeWorldExpr "balance >= 0" =
    some ["balance", ">=", "0"] := by decide +kernel
example : tokenizeWorldExpr "state == 'B' => y == x" =
    some ["state", "==", "'B'", "=>", "y", "==", "x"] := by decide +kernel
example : identifierFullMatch "balance" = true := by decide +kernel
example : identifierFullMatch "1bad" = false := by decide +kernel
example : (effectFullMatch "balance = balance - event.amount").map MatchValue.groups =
    some [some "balance", some "balance - event.amount"] := by decide +kernel
