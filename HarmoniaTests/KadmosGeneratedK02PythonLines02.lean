import HarmoniaTests.KadmosGeneratedK02PythonLines01

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

def balanceChunk02 : String :=
  (⟨2169, 3124⟩ : SourceSpan).text balancePySource
def balanceLines02 : List LocatedSourceLine :=
  shiftSourceLines 2169 (locateSourceLines balanceChunk02).dropLast
theorem kadmos_balance_python_lines_chunk_02 :
    validatePrefixLinesAt balanceChunk02 2169 balanceLines02 = true := by
  decide +kernel
def balanceAccum02 : List LocatedSourceLine :=
  balanceAccum01 ++ balanceLines02
