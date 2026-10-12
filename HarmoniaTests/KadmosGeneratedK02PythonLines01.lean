import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- Untrusted chunk slicing proposes absolute line records. Each chunk is
    kernel checked, and the independent prefix relation composes them. -/

def balanceChunk00 : String :=
  (⟨0, 1468⟩ : SourceSpan).text balancePySource
def balanceLines00 : List LocatedSourceLine :=
  shiftSourceLines 0 (locateSourceLines balanceChunk00).dropLast
theorem kadmos_balance_python_lines_chunk_00 :
    validatePrefixLinesAt balanceChunk00 0 balanceLines00 = true := by
  decide +kernel

theorem kadmos_balance_python_line_offset_mutation_rejected :
    validatePrefixLinesAt balanceChunk00 1 balanceLines00 = false := by
  decide +kernel
def balanceAccum00 : List LocatedSourceLine :=
  balanceLines00
theorem kadmos_balance_python_lines_prefix_00 :
    PrefixLinesAt ((⟨0, 1468⟩ : SourceSpan).text balancePySource) 0
      balanceAccum00 := by
  exact validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_00

def balanceChunk01 : String :=
  (⟨1468, 2169⟩ : SourceSpan).text balancePySource
def balanceLines01 : List LocatedSourceLine :=
  shiftSourceLines 1468 (locateSourceLines balanceChunk01).dropLast
theorem kadmos_balance_python_lines_chunk_01 :
    validatePrefixLinesAt balanceChunk01 1468 balanceLines01 = true := by
  decide +kernel
def balanceAccum01 : List LocatedSourceLine :=
  balanceAccum00 ++ balanceLines01
theorem kadmos_balance_python_lines_prefix_01 :
    PrefixLinesAt ((⟨0, 2169⟩ : SourceSpan).text balancePySource) 0
      balanceAccum01 := by
  have hWithin : 1468 ≤ balancePySource.length := by decide +kernel
  have hChunk : PrefixLinesAt balanceChunk01
      (0 + ((⟨0, 1468⟩ : SourceSpan).text balancePySource).length)
      balanceLines01 := by
    simpa [SourceSpan.prefix_length balancePySource 1468 hWithin] using
      (validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_01)
  have hApp := PrefixLinesAt.append
    kadmos_balance_python_lines_prefix_00 hChunk
  simpa only [balanceAccum01,
    SourceSpan.prefix_then_slice balancePySource 1468 2169 (by decide)] using hApp
