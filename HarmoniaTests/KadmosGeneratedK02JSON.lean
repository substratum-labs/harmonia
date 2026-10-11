import Harmonia.Applications.Kadmos.Generated.TargetJSON

open Harmonia.Applications.Kadmos.Generated

example : (parseTargetJSON "{\"balance\":100}").toOption =
    some (.object (.keyVal "balance" (.integer 100) .empty)) := by decide +kernel
example : (parseTargetJSON
    "{\"states\":[{\"id\":\"Ready\",\"initial\":true}],\"directive\":null}").toOption =
    some (.object (.keyVal "states"
      (.array (.valueItem (.object
        (.keyVal "id" (.string "Ready")
          (.keyVal "initial" (.bool true) .empty))) .empty))
      (.keyVal "directive" .null .empty))) := by decide +kernel
example : (parseTargetJSON "{\"x\":1,\"x\":2}").toOption = none := by decide +kernel
