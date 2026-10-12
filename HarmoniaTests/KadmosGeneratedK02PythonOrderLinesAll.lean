import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 131072
set_option maxHeartbeats 10000000

/-- Every physical line of the pinned order Python source is independently
    checked in absolute source intervals; offsets are untrusted candidates. -/

def orderChunk00 : String :=
  (⟨0, 1524⟩ : SourceSpan).text orderPySource
def orderLines00 : List LocatedSourceLine :=
  shiftSourceLines 0 (locateSourceLines orderChunk00).dropLast
theorem kadmos_order_python_lines_chunk_00 :
    validatePrefixLinesAt orderChunk00 0 orderLines00 = true := by
  decide +kernel

def orderChunk01 : String :=
  (⟨1524, 2225⟩ : SourceSpan).text orderPySource
def orderLines01 : List LocatedSourceLine :=
  shiftSourceLines 1524 (locateSourceLines orderChunk01).dropLast
theorem kadmos_order_python_lines_chunk_01 :
    validatePrefixLinesAt orderChunk01 1524 orderLines01 = true := by
  decide +kernel

def orderChunk02 : String :=
  (⟨2225, 3180⟩ : SourceSpan).text orderPySource
def orderLines02 : List LocatedSourceLine :=
  shiftSourceLines 2225 (locateSourceLines orderChunk02).dropLast
theorem kadmos_order_python_lines_chunk_02 :
    validatePrefixLinesAt orderChunk02 2225 orderLines02 = true := by
  decide +kernel

def orderChunk03 : String :=
  (⟨3180, 4264⟩ : SourceSpan).text orderPySource
def orderLines03 : List LocatedSourceLine :=
  shiftSourceLines 3180 (locateSourceLines orderChunk03).dropLast
theorem kadmos_order_python_lines_chunk_03 :
    validatePrefixLinesAt orderChunk03 3180 orderLines03 = true := by
  decide +kernel

def orderChunk04 : String :=
  (⟨4264, 5364⟩ : SourceSpan).text orderPySource
def orderLines04 : List LocatedSourceLine :=
  shiftSourceLines 4264 (locateSourceLines orderChunk04).dropLast
theorem kadmos_order_python_lines_chunk_04 :
    validatePrefixLinesAt orderChunk04 4264 orderLines04 = true := by
  decide +kernel

def orderChunk05 : String :=
  (⟨5364, 6353⟩ : SourceSpan).text orderPySource
def orderLines05 : List LocatedSourceLine :=
  shiftSourceLines 5364 (locateSourceLines orderChunk05).dropLast
theorem kadmos_order_python_lines_chunk_05 :
    validatePrefixLinesAt orderChunk05 5364 orderLines05 = true := by
  decide +kernel

def orderChunk06 : String :=
  (⟨6353, 7401⟩ : SourceSpan).text orderPySource
def orderLines06 : List LocatedSourceLine :=
  shiftSourceLines 6353 (locateSourceLines orderChunk06).dropLast
theorem kadmos_order_python_lines_chunk_06 :
    validatePrefixLinesAt orderChunk06 6353 orderLines06 = true := by
  decide +kernel

def orderChunk07 : String :=
  (⟨7401, 8550⟩ : SourceSpan).text orderPySource
def orderLines07 : List LocatedSourceLine :=
  shiftSourceLines 7401 (locateSourceLines orderChunk07).dropLast
theorem kadmos_order_python_lines_chunk_07 :
    validatePrefixLinesAt orderChunk07 7401 orderLines07 = true := by
  decide +kernel

def orderChunk08 : String :=
  (⟨8550, 9328⟩ : SourceSpan).text orderPySource
def orderLines08 : List LocatedSourceLine :=
  shiftSourceLines 8550 (locateSourceLines orderChunk08).dropLast
theorem kadmos_order_python_lines_chunk_08 :
    validatePrefixLinesAt orderChunk08 8550 orderLines08 = true := by
  decide +kernel

def orderChunk09 : String :=
  (⟨9328, 10426⟩ : SourceSpan).text orderPySource
def orderLines09 : List LocatedSourceLine :=
  shiftSourceLines 9328 (locateSourceLines orderChunk09).dropLast
theorem kadmos_order_python_lines_chunk_09 :
    validatePrefixLinesAt orderChunk09 9328 orderLines09 = true := by
  decide +kernel

def orderChunk10 : String :=
  (⟨10426, 11590⟩ : SourceSpan).text orderPySource
def orderLines10 : List LocatedSourceLine :=
  shiftSourceLines 10426 (locateSourceLines orderChunk10).dropLast
theorem kadmos_order_python_lines_chunk_10 :
    validatePrefixLinesAt orderChunk10 10426 orderLines10 = true := by
  decide +kernel

def orderChunk11 : String :=
  (⟨11590, 12825⟩ : SourceSpan).text orderPySource
def orderLines11 : List LocatedSourceLine :=
  shiftSourceLines 11590 (locateSourceLines orderChunk11).dropLast
theorem kadmos_order_python_lines_chunk_11 :
    validatePrefixLinesAt orderChunk11 11590 orderLines11 = true := by
  decide +kernel

def orderChunk12 : String :=
  (⟨12825, 14248⟩ : SourceSpan).text orderPySource
def orderLines12 : List LocatedSourceLine :=
  shiftSourceLines 12825 (locateSourceLines orderChunk12).dropLast
theorem kadmos_order_python_lines_chunk_12 :
    validatePrefixLinesAt orderChunk12 12825 orderLines12 = true := by
  decide +kernel

def orderChunk13 : String :=
  (⟨14248, 15635⟩ : SourceSpan).text orderPySource
def orderLines13 : List LocatedSourceLine :=
  shiftSourceLines 14248 (locateSourceLines orderChunk13).dropLast
theorem kadmos_order_python_lines_chunk_13 :
    validatePrefixLinesAt orderChunk13 14248 orderLines13 = true := by
  decide +kernel

def orderChunk14 : String :=
  (⟨15635, 17485⟩ : SourceSpan).text orderPySource
def orderLines14 : List LocatedSourceLine :=
  shiftSourceLines 15635 (locateSourceLines orderChunk14).dropLast
theorem kadmos_order_python_lines_chunk_14 :
    validatePrefixLinesAt orderChunk14 15635 orderLines14 = true := by
  decide +kernel

def orderChunk15 : String :=
  (⟨17485, 19022⟩ : SourceSpan).text orderPySource
def orderLines15 : List LocatedSourceLine :=
  shiftSourceLines 17485 (locateSourceLines orderChunk15).dropLast
theorem kadmos_order_python_lines_chunk_15 :
    validatePrefixLinesAt orderChunk15 17485 orderLines15 = true := by
  decide +kernel

theorem kadmos_order_python_lines_chunked_15 :
    ChunkedLines (SourceSpan.suffix orderPySource 17485) 17485
      [⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 17485 19022 (by decide)
  have hChunk : PrefixLinesAt orderChunk15 17485 orderLines15 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_15
  have hTail : ChunkedLines (SourceSpan.suffix orderPySource 19022)
      19022 [] := by
    have hEnd : SourceSpan.suffix orderPySource 19022 = "" := by
      simpa only [show orderPySource.length = 19022 by decide +kernel] using
        SourceSpan.suffix_end orderPySource
    rw [hEnd]
    exact .empty _
  have hLen : 17485 + orderChunk15.length = 19022 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk15 ++ SourceSpan.suffix orderPySource 19022) 17485
      [⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_14 :
    ChunkedLines (SourceSpan.suffix orderPySource 15635) 15635
      [⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 15635 17485 (by decide)
  have hChunk : PrefixLinesAt orderChunk14 15635 orderLines14 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_14
  have hTail := kadmos_order_python_lines_chunked_15
  have hLen : 15635 + orderChunk14.length = 17485 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk14 ++ SourceSpan.suffix orderPySource 17485) 15635
      [⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_13 :
    ChunkedLines (SourceSpan.suffix orderPySource 14248) 14248
      [⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 14248 15635 (by decide)
  have hChunk : PrefixLinesAt orderChunk13 14248 orderLines13 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_13
  have hTail := kadmos_order_python_lines_chunked_14
  have hLen : 14248 + orderChunk13.length = 15635 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk13 ++ SourceSpan.suffix orderPySource 15635) 14248
      [⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_12 :
    ChunkedLines (SourceSpan.suffix orderPySource 12825) 12825
      [⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 12825 14248 (by decide)
  have hChunk : PrefixLinesAt orderChunk12 12825 orderLines12 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_12
  have hTail := kadmos_order_python_lines_chunked_13
  have hLen : 12825 + orderChunk12.length = 14248 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk12 ++ SourceSpan.suffix orderPySource 14248) 12825
      [⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_11 :
    ChunkedLines (SourceSpan.suffix orderPySource 11590) 11590
      [⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 11590 12825 (by decide)
  have hChunk : PrefixLinesAt orderChunk11 11590 orderLines11 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_11
  have hTail := kadmos_order_python_lines_chunked_12
  have hLen : 11590 + orderChunk11.length = 12825 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk11 ++ SourceSpan.suffix orderPySource 12825) 11590
      [⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_10 :
    ChunkedLines (SourceSpan.suffix orderPySource 10426) 10426
      [⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 10426 11590 (by decide)
  have hChunk : PrefixLinesAt orderChunk10 10426 orderLines10 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_10
  have hTail := kadmos_order_python_lines_chunked_11
  have hLen : 10426 + orderChunk10.length = 11590 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk10 ++ SourceSpan.suffix orderPySource 11590) 10426
      [⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_09 :
    ChunkedLines (SourceSpan.suffix orderPySource 9328) 9328
      [⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 9328 10426 (by decide)
  have hChunk : PrefixLinesAt orderChunk09 9328 orderLines09 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_09
  have hTail := kadmos_order_python_lines_chunked_10
  have hLen : 9328 + orderChunk09.length = 10426 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk09 ++ SourceSpan.suffix orderPySource 10426) 9328
      [⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_08 :
    ChunkedLines (SourceSpan.suffix orderPySource 8550) 8550
      [⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 8550 9328 (by decide)
  have hChunk : PrefixLinesAt orderChunk08 8550 orderLines08 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_08
  have hTail := kadmos_order_python_lines_chunked_09
  have hLen : 8550 + orderChunk08.length = 9328 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk08 ++ SourceSpan.suffix orderPySource 9328) 8550
      [⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_07 :
    ChunkedLines (SourceSpan.suffix orderPySource 7401) 7401
      [⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 7401 8550 (by decide)
  have hChunk : PrefixLinesAt orderChunk07 7401 orderLines07 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_07
  have hTail := kadmos_order_python_lines_chunked_08
  have hLen : 7401 + orderChunk07.length = 8550 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk07 ++ SourceSpan.suffix orderPySource 8550) 7401
      [⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_06 :
    ChunkedLines (SourceSpan.suffix orderPySource 6353) 6353
      [⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 6353 7401 (by decide)
  have hChunk : PrefixLinesAt orderChunk06 6353 orderLines06 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_06
  have hTail := kadmos_order_python_lines_chunked_07
  have hLen : 6353 + orderChunk06.length = 7401 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk06 ++ SourceSpan.suffix orderPySource 7401) 6353
      [⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_05 :
    ChunkedLines (SourceSpan.suffix orderPySource 5364) 5364
      [⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 5364 6353 (by decide)
  have hChunk : PrefixLinesAt orderChunk05 5364 orderLines05 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_05
  have hTail := kadmos_order_python_lines_chunked_06
  have hLen : 5364 + orderChunk05.length = 6353 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk05 ++ SourceSpan.suffix orderPySource 6353) 5364
      [⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_04 :
    ChunkedLines (SourceSpan.suffix orderPySource 4264) 4264
      [⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 4264 5364 (by decide)
  have hChunk : PrefixLinesAt orderChunk04 4264 orderLines04 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_04
  have hTail := kadmos_order_python_lines_chunked_05
  have hLen : 4264 + orderChunk04.length = 5364 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk04 ++ SourceSpan.suffix orderPySource 5364) 4264
      [⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_03 :
    ChunkedLines (SourceSpan.suffix orderPySource 3180) 3180
      [⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 3180 4264 (by decide)
  have hChunk : PrefixLinesAt orderChunk03 3180 orderLines03 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_03
  have hTail := kadmos_order_python_lines_chunked_04
  have hLen : 3180 + orderChunk03.length = 4264 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk03 ++ SourceSpan.suffix orderPySource 4264) 3180
      [⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_02 :
    ChunkedLines (SourceSpan.suffix orderPySource 2225) 2225
      [⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 2225 3180 (by decide)
  have hChunk : PrefixLinesAt orderChunk02 2225 orderLines02 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_02
  have hTail := kadmos_order_python_lines_chunked_03
  have hLen : 2225 + orderChunk02.length = 3180 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk02 ++ SourceSpan.suffix orderPySource 3180) 2225
      [⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_01 :
    ChunkedLines (SourceSpan.suffix orderPySource 1524) 1524
      [⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 1524 2225 (by decide)
  have hChunk : PrefixLinesAt orderChunk01 1524 orderLines01 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_01
  have hTail := kadmos_order_python_lines_chunked_02
  have hLen : 1524 + orderChunk01.length = 2225 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk01 ++ SourceSpan.suffix orderPySource 2225) 1524
      [⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_lines_chunked_00 :
    ChunkedLines (SourceSpan.suffix orderPySource 0) 0
      [⟨orderChunk00, orderLines00⟩, ⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  have hSplit := SourceSpan.suffix_split orderPySource 0 1524 (by decide)
  have hChunk : PrefixLinesAt orderChunk00 0 orderLines00 :=
    validatePrefixLinesAt_sound kadmos_order_python_lines_chunk_00
  have hTail := kadmos_order_python_lines_chunked_01
  have hLen : 0 + orderChunk00.length = 1524 := by decide +kernel
  have hCons : ChunkedLines
      (orderChunk00 ++ SourceSpan.suffix orderPySource 1524) 0
      [⟨orderChunk00, orderLines00⟩, ⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_order_python_all_lines_chunked :
    ChunkedLines orderPySource 0
      [⟨orderChunk00, orderLines00⟩, ⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] := by
  simpa only [SourceSpan.suffix_zero] using
    kadmos_order_python_lines_chunked_00

/-- Chunk partition erased: the full source has one contiguous physical-line
    derivation with absolute offsets. -/
theorem kadmos_order_python_all_lines_prefix :
    PrefixLinesAt orderPySource 0 (flattenedChunkLines
      [⟨orderChunk00, orderLines00⟩, ⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩]) :=
  ChunkedLines.toPrefixLinesAt kadmos_order_python_all_lines_chunked

/-- Includes the final zero-length physical line after the emitted trailing
    newline. The line relation owns the complete original source. -/
theorem kadmos_order_python_all_lines_at :
    LinesAt orderPySource 0
      (flattenedChunkLines [⟨orderChunk00, orderLines00⟩, ⟨orderChunk01, orderLines01⟩, ⟨orderChunk02, orderLines02⟩, ⟨orderChunk03, orderLines03⟩, ⟨orderChunk04, orderLines04⟩, ⟨orderChunk05, orderLines05⟩, ⟨orderChunk06, orderLines06⟩, ⟨orderChunk07, orderLines07⟩, ⟨orderChunk08, orderLines08⟩, ⟨orderChunk09, orderLines09⟩, ⟨orderChunk10, orderLines10⟩, ⟨orderChunk11, orderLines11⟩, ⟨orderChunk12, orderLines12⟩, ⟨orderChunk13, orderLines13⟩, ⟨orderChunk14, orderLines14⟩, ⟨orderChunk15, orderLines15⟩] ++
        [⟨orderPySource.length, orderPySource.length, "", false⟩]) := by
  simpa only [Nat.zero_add] using
    PrefixLinesAt.toLinesAt kadmos_order_python_all_lines_prefix
