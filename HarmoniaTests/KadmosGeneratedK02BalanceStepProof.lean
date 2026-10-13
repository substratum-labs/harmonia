import HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS
import HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython

-- These twelve boundary facts check actual executor output and heap contents.
-- Universal helper/branch simulation is not inferred from finite checks.

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos

-- Conditional arithmetic covers every bounded b/n; effects need n > 0.
theorem kadmos_generated_accept_numeric_domain {b n : Int}
    (hb : 0 ≤ b ∧ b ≤ S) (hn : 0 < n ∧ n ≤ b) :
    (b - n).natAbs ≤ 9007199254740991 :=
  signed_natAbs (balance_accept_difference_bounds hb hn)

theorem kadmos_generated_bounds_numeric_domain {b n : Int}
    (hb : 0 ≤ b ∧ b ≤ S) (hn : b < n ∧ n ≤ S) :
    (b - n).natAbs ≤ 9007199254740991 :=
  signed_natAbs (balance_reject_difference_bounds hb hn)
