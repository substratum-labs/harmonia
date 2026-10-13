import HarmoniaTests.KadmosGeneratedK02ConstructorProofTS
import HarmoniaTests.KadmosGeneratedK02ConstructorProofPython

open Harmonia.Applications.Kadmos.Generated

-- Boundary facts are split by language to bound physical kernel memory.
-- Universal targetConstruct_sound remains a separate open proof obligation.
#print axioms balanceRepCheck_sound
#print axioms checkedConstructor_witness
