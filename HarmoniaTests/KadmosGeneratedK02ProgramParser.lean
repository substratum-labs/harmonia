import Harmonia.Applications.Kadmos.Generated.TargetProgramParser

open Harmonia.Applications.Kadmos.Generated

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

example : (parseGenerated .python
    "import json\ndef f(x: int = 0) -> int:\n    return x\n").toOption.isSome = true := by decide +kernel
example : (parseGenerated .ts
    "const contextDefaults = { balance: 100 };\n").toOption.isSome = true := by decide +kernel
example : (parseGenerated .ts
    "const world = JSON.parse(\"{\\\"balance\\\":100}\");\n").toOption.bind
      embeddedWorldJSON = some (.object (.keyVal "balance" (.integer 100) .empty)) := by decide +kernel
