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


theorem kadmos_k02_constructor_python_zero :
    (parseGenerated .python balancePySource).toOption.bind
      (fun p => (targetConstruct p (canonicalBalanceSeed .python 0)).toOption.map
        (balanceRepCheck .python 0)) = some true := by
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_constructor_python_hundred :
    (parseGenerated .python balancePySource).toOption.bind
      (fun p => (targetConstruct p (canonicalBalanceSeed .python 100)).toOption.map
        (balanceRepCheck .python 100)) = some true := by
  rw [balancePyProgram_source]
  decide +kernel

theorem kadmos_k02_constructor_python_maximum :
    (parseGenerated .python balancePySource).toOption.bind
      (fun p => (targetConstruct p (canonicalBalanceSeed .python 9007199254740991)).toOption.map
        (balanceRepCheck .python 9007199254740991)) = some true := by
  rw [balancePyProgram_source]
  decide +kernel

