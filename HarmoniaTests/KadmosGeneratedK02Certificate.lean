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
