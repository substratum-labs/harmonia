import HarmoniaTests.KadmosGeneratedK02PythonLines02

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 131072
set_option maxHeartbeats 10000000

/-- The candidate offsets are untrusted; each interval and its physical lines
    are checked by the kernel before the independent chunk relation composes. -/

def balanceChunk03 : String :=
  (⟨3124, 4208⟩ : SourceSpan).text balancePySource
def balanceLines03 : List LocatedSourceLine :=
  shiftSourceLines 3124 (locateSourceLines balanceChunk03).dropLast
theorem kadmos_balance_python_lines_chunk_03 :
    validatePrefixLinesAt balanceChunk03 3124 balanceLines03 = true := by
  decide +kernel

def balanceChunk04 : String :=
  (⟨4208, 5308⟩ : SourceSpan).text balancePySource
def balanceLines04 : List LocatedSourceLine :=
  shiftSourceLines 4208 (locateSourceLines balanceChunk04).dropLast
theorem kadmos_balance_python_lines_chunk_04 :
    validatePrefixLinesAt balanceChunk04 4208 balanceLines04 = true := by
  decide +kernel

def balanceChunk05 : String :=
  (⟨5308, 6297⟩ : SourceSpan).text balancePySource
def balanceLines05 : List LocatedSourceLine :=
  shiftSourceLines 5308 (locateSourceLines balanceChunk05).dropLast
theorem kadmos_balance_python_lines_chunk_05 :
    validatePrefixLinesAt balanceChunk05 5308 balanceLines05 = true := by
  decide +kernel

def balanceChunk06 : String :=
  (⟨6297, 7345⟩ : SourceSpan).text balancePySource
def balanceLines06 : List LocatedSourceLine :=
  shiftSourceLines 6297 (locateSourceLines balanceChunk06).dropLast
theorem kadmos_balance_python_lines_chunk_06 :
    validatePrefixLinesAt balanceChunk06 6297 balanceLines06 = true := by
  decide +kernel

def balanceChunk07 : String :=
  (⟨7345, 8494⟩ : SourceSpan).text balancePySource
def balanceLines07 : List LocatedSourceLine :=
  shiftSourceLines 7345 (locateSourceLines balanceChunk07).dropLast
theorem kadmos_balance_python_lines_chunk_07 :
    validatePrefixLinesAt balanceChunk07 7345 balanceLines07 = true := by
  decide +kernel

def balanceChunk08 : String :=
  (⟨8494, 9272⟩ : SourceSpan).text balancePySource
def balanceLines08 : List LocatedSourceLine :=
  shiftSourceLines 8494 (locateSourceLines balanceChunk08).dropLast
theorem kadmos_balance_python_lines_chunk_08 :
    validatePrefixLinesAt balanceChunk08 8494 balanceLines08 = true := by
  decide +kernel

def balanceChunk09 : String :=
  (⟨9272, 10370⟩ : SourceSpan).text balancePySource
def balanceLines09 : List LocatedSourceLine :=
  shiftSourceLines 9272 (locateSourceLines balanceChunk09).dropLast
theorem kadmos_balance_python_lines_chunk_09 :
    validatePrefixLinesAt balanceChunk09 9272 balanceLines09 = true := by
  decide +kernel

def balanceChunk10 : String :=
  (⟨10370, 11534⟩ : SourceSpan).text balancePySource
def balanceLines10 : List LocatedSourceLine :=
  shiftSourceLines 10370 (locateSourceLines balanceChunk10).dropLast
theorem kadmos_balance_python_lines_chunk_10 :
    validatePrefixLinesAt balanceChunk10 10370 balanceLines10 = true := by
  decide +kernel

def balanceChunk11 : String :=
  (⟨11534, 12769⟩ : SourceSpan).text balancePySource
def balanceLines11 : List LocatedSourceLine :=
  shiftSourceLines 11534 (locateSourceLines balanceChunk11).dropLast
theorem kadmos_balance_python_lines_chunk_11 :
    validatePrefixLinesAt balanceChunk11 11534 balanceLines11 = true := by
  decide +kernel

def balanceChunk12 : String :=
  (⟨12769, 14192⟩ : SourceSpan).text balancePySource
def balanceLines12 : List LocatedSourceLine :=
  shiftSourceLines 12769 (locateSourceLines balanceChunk12).dropLast
theorem kadmos_balance_python_lines_chunk_12 :
    validatePrefixLinesAt balanceChunk12 12769 balanceLines12 = true := by
  decide +kernel

def balanceChunk13 : String :=
  (⟨14192, 15579⟩ : SourceSpan).text balancePySource
def balanceLines13 : List LocatedSourceLine :=
  shiftSourceLines 14192 (locateSourceLines balanceChunk13).dropLast
theorem kadmos_balance_python_lines_chunk_13 :
    validatePrefixLinesAt balanceChunk13 14192 balanceLines13 = true := by
  decide +kernel

def balanceChunk14 : String :=
  (⟨15579, 17429⟩ : SourceSpan).text balancePySource
def balanceLines14 : List LocatedSourceLine :=
  shiftSourceLines 15579 (locateSourceLines balanceChunk14).dropLast
theorem kadmos_balance_python_lines_chunk_14 :
    validatePrefixLinesAt balanceChunk14 15579 balanceLines14 = true := by
  decide +kernel

def balanceChunk15 : String :=
  (⟨17429, 18966⟩ : SourceSpan).text balancePySource
def balanceLines15 : List LocatedSourceLine :=
  shiftSourceLines 17429 (locateSourceLines balanceChunk15).dropLast
theorem kadmos_balance_python_lines_chunk_15 :
    validatePrefixLinesAt balanceChunk15 17429 balanceLines15 = true := by
  decide +kernel

theorem kadmos_balance_python_lines_chunked_15 :
    ChunkedLines (SourceSpan.suffix balancePySource 17429) 17429
      [⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 17429 18966 (by decide)
  have hChunk : PrefixLinesAt balanceChunk15 17429 balanceLines15 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_15
  have hTail : ChunkedLines (SourceSpan.suffix balancePySource 18966)
      18966 [] := by
    have hEnd : SourceSpan.suffix balancePySource 18966 = "" := by
      simpa only [show balancePySource.length = 18966 by decide +kernel] using
        SourceSpan.suffix_end balancePySource
    rw [hEnd]
    exact .empty _
  have hLen : 17429 + balanceChunk15.length = 18966 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk15 ++ SourceSpan.suffix balancePySource 18966) 17429
      [⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_14 :
    ChunkedLines (SourceSpan.suffix balancePySource 15579) 15579
      [⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 15579 17429 (by decide)
  have hChunk : PrefixLinesAt balanceChunk14 15579 balanceLines14 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_14
  have hTail := kadmos_balance_python_lines_chunked_15
  have hLen : 15579 + balanceChunk14.length = 17429 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk14 ++ SourceSpan.suffix balancePySource 17429) 15579
      [⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_13 :
    ChunkedLines (SourceSpan.suffix balancePySource 14192) 14192
      [⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 14192 15579 (by decide)
  have hChunk : PrefixLinesAt balanceChunk13 14192 balanceLines13 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_13
  have hTail := kadmos_balance_python_lines_chunked_14
  have hLen : 14192 + balanceChunk13.length = 15579 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk13 ++ SourceSpan.suffix balancePySource 15579) 14192
      [⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_12 :
    ChunkedLines (SourceSpan.suffix balancePySource 12769) 12769
      [⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 12769 14192 (by decide)
  have hChunk : PrefixLinesAt balanceChunk12 12769 balanceLines12 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_12
  have hTail := kadmos_balance_python_lines_chunked_13
  have hLen : 12769 + balanceChunk12.length = 14192 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk12 ++ SourceSpan.suffix balancePySource 14192) 12769
      [⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_11 :
    ChunkedLines (SourceSpan.suffix balancePySource 11534) 11534
      [⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 11534 12769 (by decide)
  have hChunk : PrefixLinesAt balanceChunk11 11534 balanceLines11 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_11
  have hTail := kadmos_balance_python_lines_chunked_12
  have hLen : 11534 + balanceChunk11.length = 12769 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk11 ++ SourceSpan.suffix balancePySource 12769) 11534
      [⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_10 :
    ChunkedLines (SourceSpan.suffix balancePySource 10370) 10370
      [⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 10370 11534 (by decide)
  have hChunk : PrefixLinesAt balanceChunk10 10370 balanceLines10 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_10
  have hTail := kadmos_balance_python_lines_chunked_11
  have hLen : 10370 + balanceChunk10.length = 11534 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk10 ++ SourceSpan.suffix balancePySource 11534) 10370
      [⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_09 :
    ChunkedLines (SourceSpan.suffix balancePySource 9272) 9272
      [⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 9272 10370 (by decide)
  have hChunk : PrefixLinesAt balanceChunk09 9272 balanceLines09 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_09
  have hTail := kadmos_balance_python_lines_chunked_10
  have hLen : 9272 + balanceChunk09.length = 10370 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk09 ++ SourceSpan.suffix balancePySource 10370) 9272
      [⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_08 :
    ChunkedLines (SourceSpan.suffix balancePySource 8494) 8494
      [⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 8494 9272 (by decide)
  have hChunk : PrefixLinesAt balanceChunk08 8494 balanceLines08 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_08
  have hTail := kadmos_balance_python_lines_chunked_09
  have hLen : 8494 + balanceChunk08.length = 9272 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk08 ++ SourceSpan.suffix balancePySource 9272) 8494
      [⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_07 :
    ChunkedLines (SourceSpan.suffix balancePySource 7345) 7345
      [⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 7345 8494 (by decide)
  have hChunk : PrefixLinesAt balanceChunk07 7345 balanceLines07 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_07
  have hTail := kadmos_balance_python_lines_chunked_08
  have hLen : 7345 + balanceChunk07.length = 8494 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk07 ++ SourceSpan.suffix balancePySource 8494) 7345
      [⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_06 :
    ChunkedLines (SourceSpan.suffix balancePySource 6297) 6297
      [⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 6297 7345 (by decide)
  have hChunk : PrefixLinesAt balanceChunk06 6297 balanceLines06 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_06
  have hTail := kadmos_balance_python_lines_chunked_07
  have hLen : 6297 + balanceChunk06.length = 7345 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk06 ++ SourceSpan.suffix balancePySource 7345) 6297
      [⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_05 :
    ChunkedLines (SourceSpan.suffix balancePySource 5308) 5308
      [⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 5308 6297 (by decide)
  have hChunk : PrefixLinesAt balanceChunk05 5308 balanceLines05 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_05
  have hTail := kadmos_balance_python_lines_chunked_06
  have hLen : 5308 + balanceChunk05.length = 6297 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk05 ++ SourceSpan.suffix balancePySource 6297) 5308
      [⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_04 :
    ChunkedLines (SourceSpan.suffix balancePySource 4208) 4208
      [⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 4208 5308 (by decide)
  have hChunk : PrefixLinesAt balanceChunk04 4208 balanceLines04 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_04
  have hTail := kadmos_balance_python_lines_chunked_05
  have hLen : 4208 + balanceChunk04.length = 5308 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk04 ++ SourceSpan.suffix balancePySource 5308) 4208
      [⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_03 :
    ChunkedLines (SourceSpan.suffix balancePySource 3124) 3124
      [⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 3124 4208 (by decide)
  have hChunk : PrefixLinesAt balanceChunk03 3124 balanceLines03 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_03
  have hTail := kadmos_balance_python_lines_chunked_04
  have hLen : 3124 + balanceChunk03.length = 4208 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk03 ++ SourceSpan.suffix balancePySource 4208) 3124
      [⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_02 :
    ChunkedLines (SourceSpan.suffix balancePySource 2169) 2169
      [⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 2169 3124 (by decide)
  have hChunk : PrefixLinesAt balanceChunk02 2169 balanceLines02 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_02
  have hTail := kadmos_balance_python_lines_chunked_03
  have hLen : 2169 + balanceChunk02.length = 3124 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk02 ++ SourceSpan.suffix balancePySource 3124) 2169
      [⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_01 :
    ChunkedLines (SourceSpan.suffix balancePySource 1468) 1468
      [⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 1468 2169 (by decide)
  have hChunk : PrefixLinesAt balanceChunk01 1468 balanceLines01 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_01
  have hTail := kadmos_balance_python_lines_chunked_02
  have hLen : 1468 + balanceChunk01.length = 2169 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk01 ++ SourceSpan.suffix balancePySource 2169) 1468
      [⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_lines_chunked_00 :
    ChunkedLines (SourceSpan.suffix balancePySource 0) 0
      [⟨balanceChunk00, balanceLines00⟩, ⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  have hSplit := SourceSpan.suffix_split balancePySource 0 1468 (by decide)
  have hChunk : PrefixLinesAt balanceChunk00 0 balanceLines00 :=
    validatePrefixLinesAt_sound kadmos_balance_python_lines_chunk_00
  have hTail := kadmos_balance_python_lines_chunked_01
  have hLen : 0 + balanceChunk00.length = 1468 := by decide +kernel
  have hCons : ChunkedLines
      (balanceChunk00 ++ SourceSpan.suffix balancePySource 1468) 0
      [⟨balanceChunk00, balanceLines00⟩, ⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
    exact .cons hChunk (by simpa only [hLen] using hTail)
  rw [hSplit]
  exact hCons

theorem kadmos_balance_python_all_lines_chunked :
    ChunkedLines balancePySource 0
      [⟨balanceChunk00, balanceLines00⟩, ⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] := by
  simpa only [SourceSpan.suffix_zero] using
    kadmos_balance_python_lines_chunked_00

/-- Chunk partition erased: the full source has one contiguous physical-line
    derivation with absolute offsets. -/
theorem kadmos_balance_python_all_lines_prefix :
    PrefixLinesAt balancePySource 0 (flattenedChunkLines
      [⟨balanceChunk00, balanceLines00⟩, ⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩]) :=
  ChunkedLines.toPrefixLinesAt kadmos_balance_python_all_lines_chunked

/-- Includes the final zero-length physical line after the emitted trailing
    newline. The line relation owns the complete original source. -/
theorem kadmos_balance_python_all_lines_at :
    LinesAt balancePySource 0
      (flattenedChunkLines [⟨balanceChunk00, balanceLines00⟩, ⟨balanceChunk01, balanceLines01⟩, ⟨balanceChunk02, balanceLines02⟩, ⟨balanceChunk03, balanceLines03⟩, ⟨balanceChunk04, balanceLines04⟩, ⟨balanceChunk05, balanceLines05⟩, ⟨balanceChunk06, balanceLines06⟩, ⟨balanceChunk07, balanceLines07⟩, ⟨balanceChunk08, balanceLines08⟩, ⟨balanceChunk09, balanceLines09⟩, ⟨balanceChunk10, balanceLines10⟩, ⟨balanceChunk11, balanceLines11⟩, ⟨balanceChunk12, balanceLines12⟩, ⟨balanceChunk13, balanceLines13⟩, ⟨balanceChunk14, balanceLines14⟩, ⟨balanceChunk15, balanceLines15⟩] ++
        [⟨balancePySource.length, balancePySource.length, "", false⟩]) := by
  simpa only [Nat.zero_add] using
    PrefixLinesAt.toLinesAt kadmos_balance_python_all_lines_prefix
