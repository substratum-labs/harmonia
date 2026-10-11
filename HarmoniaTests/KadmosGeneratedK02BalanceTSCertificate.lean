import Harmonia.Applications.Kadmos.Generated.TargetCertificate
import HarmoniaTests.KadmosGeneratedK02BalanceTSParse

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.BridgeFixtures
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

theorem kadmos_k02_balance_ts_world_data :
    (parseGenerated .ts balanceTsSource).toOption.bind embeddedWorldJSON =
      some (emittedWorldData balanceRaw) := by decide +kernel

theorem kadmos_k02_balance_ts_defaults_data :
    (parseGenerated .ts balanceTsSource).toOption.bind embeddedDefaultsJSON =
      some (emittedDefaultsData balanceRaw) := by decide +kernel

theorem kadmos_k02_balance_ts_certificate_nonvacuous :
    ∃ program, checkGenerated .ts balanceTsSource balanceRaw balanceCandidate =
      .ok program := by
  cases h : parseGenerated .ts balanceTsSource with
  | error error =>
      have hp := kadmos_k02_balance_ts_parses
      simp [h] at hp
      cases hp
  | ok program =>
      have hw : embeddedWorldJSON program = some (emittedWorldData balanceRaw) := by
        simpa [h] using kadmos_k02_balance_ts_world_data
      have hd : embeddedDefaultsJSON program = some (emittedDefaultsData balanceRaw) := by
        simpa [h] using kadmos_k02_balance_ts_defaults_data
      exact ⟨program, checkGenerated_accept_if .ts balanceTsSource balanceRaw
        balanceCandidate program balance_certificate (by rfl) h hw (fun _ => hd)⟩
