import Harmonia.Applications.Kadmos.Generated.TargetObservation
import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- A concrete, source-bound kernel execution witness. The universal `b,n`
    target-step theorem remains a separate open obligation. -/
theorem kadmos_k02_balance_ts_debit30_closed :
    (parseGenerated .ts balanceTsSource).toOption.bind
      (fun program => (targetConstruct program (canonicalBalanceSeed .ts 100)).toOption.bind
        (fun machine => (targetStep program machine (canonicalDebitRequest .ts 30)).toOption.bind
          (fun outcome => (targetProjection .ts outcome).toOption))) =
        some ⟨true, "Ready", [("balance", 70)], none⟩ := by decide +kernel
