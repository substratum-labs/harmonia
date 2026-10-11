import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

example : (parseGenerated .ts orderTsSource).toOption.isSome = true := by decide +kernel
