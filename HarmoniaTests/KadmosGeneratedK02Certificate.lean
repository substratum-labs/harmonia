import Harmonia.Applications.Kadmos.Generated.TargetCertificate

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.BridgeFixtures
open Harmonia.Applications.Kadmos.GeneratedFixtures

example : checkGenerated .ts "edited generated source" balanceRaw balanceCandidate =
    .error .sourceMismatch := by
  apply checkGenerated_rejects_changed_source .ts
    "edited generated source" balanceTsSource balanceRaw balanceCandidate
  · exact balance_certificate
  · rfl
  · decide

example : emittedDefaultsData balanceRaw =
    .object (.keyVal "balance" (.integer 100) .empty) := by decide +kernel

-- The admitted source and AST are fixed even when supplied abstractly.
-- Changing the certificate's byte or parser gates invalidates this result.
theorem kadmos_generated_balance_certificate_binding {lang source program}
    (hc : checkGenerated lang source balanceRaw balanceCandidate = .ok program) :
    source = balanceSource lang ∧ program = balanceProgram lang :=
  checkGenerated_balanceProgram hc

#print axioms checkGenerated_source
#print axioms checkGenerated_balanceProgram
#print axioms kadmos_generated_balance_certificate_binding
