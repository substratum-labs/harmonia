import HarmoniaTests.KadmosGeneratedK02ClosedPrograms
import Harmonia.Applications.Kadmos.Generated.BalanceSimulation
import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.TargetObservation
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

open HarmoniaTests.KadmosGeneratedK02ClosedPrograms

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000


-- Individual closed constructor checks; no universal totality claim.

theorem kadmos_k02_constructor_ts_zero :
    (parseGenerated .ts balanceTsSource).toOption.bind
      (fun p => (targetConstruct p (canonicalBalanceSeed .ts 0)).toOption.map
        (balanceRepCheck .ts 0)) = some true := by
  rw [balanceTsProgram_source]
  decide +kernel

theorem kadmos_k02_constructor_ts_hundred :
    (parseGenerated .ts balanceTsSource).toOption.bind
      (fun p => (targetConstruct p (canonicalBalanceSeed .ts 100)).toOption.map
        (balanceRepCheck .ts 100)) = some true := by
  rw [balanceTsProgram_source]
  decide +kernel

theorem kadmos_k02_constructor_ts_maximum :
    (parseGenerated .ts balanceTsSource).toOption.bind
      (fun p => (targetConstruct p (canonicalBalanceSeed .ts 9007199254740991)).toOption.map
        (balanceRepCheck .ts 9007199254740991)) = some true := by
  rw [balanceTsProgram_source]
  decide +kernel

