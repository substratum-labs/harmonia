import Harmonia.Applications.Kadmos.Generated.BalancePrograms

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

namespace HarmoniaTests.KadmosGeneratedK02ClosedPrograms

-- Preserve the test interface; production uses the same kernel-bound ASTs.
abbrev balanceTsProgram := BalancePrograms.balanceTsProgram
abbrev balancePyProgram := BalancePrograms.balancePyProgram

theorem balanceTsProgram_source : parseGenerated .ts balanceTsSource = .ok balanceTsProgram :=
  BalancePrograms.balanceTsProgram_source

theorem balancePyProgram_source : parseGenerated .python balancePySource = .ok balancePyProgram :=
  BalancePrograms.balancePyProgram_source

end HarmoniaTests.KadmosGeneratedK02ClosedPrograms
