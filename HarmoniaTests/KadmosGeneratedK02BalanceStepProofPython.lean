import HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures
open HarmoniaTests.KadmosGeneratedK02Closed
open HarmoniaTests.KadmosGeneratedK02ClosedPrograms

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

theorem kadmos_k02_step_python_guard_zero_closed :
    checkOneDebit .python balancePySource ⟨100, 0, false, some "GUARD_FAILED"⟩ = some true := by
  unfold checkOneDebit
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_step_python_guard_negative_closed :
    checkOneDebit .python balancePySource ⟨100, -1, false, some "GUARD_FAILED"⟩ = some true := by
  unfold checkOneDebit
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_step_python_accept_closed :
    checkOneDebit .python balancePySource ⟨100, 30, true, none⟩ = some true := by
  unfold checkOneDebit
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_step_python_bounds_closed :
    checkOneDebit .python balancePySource ⟨100, 130, false, some "INVALID_BOUNDS"⟩ = some true := by
  unfold checkOneDebit
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_step_python_maximum_accept_closed :
    checkOneDebit .python balancePySource ⟨9007199254740991, 9007199254740991, true, none⟩ = some true := by
  unfold checkOneDebit
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_step_python_maximum_guard_closed :
    checkOneDebit .python balancePySource ⟨9007199254740991, -9007199254740991, false, some "GUARD_FAILED"⟩ = some true := by
  unfold checkOneDebit
  rw [balancePyProgram_source]
  decide +kernel
