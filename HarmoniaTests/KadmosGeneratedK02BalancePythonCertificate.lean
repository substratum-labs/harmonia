import Harmonia.Applications.Kadmos.Generated.TargetCertificate
import HarmoniaTests.KadmosGeneratedK02BalancePythonParse

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.BridgeFixtures
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

theorem kadmos_k02_balance_python_world_data :
    (parseGenerated .python balancePySource).toOption.bind embeddedWorldJSON =
      some (emittedWorldData balanceRaw) := by decide +kernel

theorem kadmos_k02_balance_python_certificate_nonvacuous :
    ∃ program, checkGenerated .python balancePySource balanceRaw balanceCandidate =
      .ok program := by
  cases h : parseGenerated .python balancePySource with
  | error error =>
      have hp := kadmos_k02_balance_python_parses
      simp [h] at hp
      cases hp
  | ok program =>
      have hw : embeddedWorldJSON program = some (emittedWorldData balanceRaw) := by
        simpa [h] using kadmos_k02_balance_python_world_data
      exact ⟨program, checkGenerated_accept_if .python balancePySource balanceRaw
        balanceCandidate program balance_certificate (by rfl) h hw (by intro h; cases h)⟩
