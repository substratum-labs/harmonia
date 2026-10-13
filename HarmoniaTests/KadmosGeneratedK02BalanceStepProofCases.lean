import HarmoniaTests.KadmosGeneratedK02ClosedPrograms
import Harmonia.Applications.Kadmos.Generated.BalanceSimulation
import Harmonia.Applications.Kadmos.Generated.TargetObservation
import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

-- Content checks dereference records and savepoints, including Python float tags.
theorem kadmos_k02_step_expected_python_record :
    (expectedRecord .python 30).amount = .number .pyFloat 30 := by rfl

theorem kadmos_k02_view_rejects_missing_seed :
    balanceView .ts TargetMachine.empty = .error .invalidTag := by decide +kernel

private def contextProbe (descriptor : Descriptor) : TargetMachine × ObjRef :=
  allocObject TargetMachine.empty
    ⟨.jsOrdinary, some 0, [("balance", descriptor)], [], [], false, false⟩

theorem kadmos_k02_view_rejects_accessor :
    let pair := contextProbe ⟨some (.number .jsNumber 100), some 0, none, true, true, true⟩
    balanceContextValue .ts pair.1 pair.2 = .error .badDescriptor := by decide +kernel

theorem kadmos_k02_view_rejects_non_enumerable :
    let pair := contextProbe ⟨some (.number .jsNumber 100), none, none, false, true, true⟩
    balanceContextValue .ts pair.1 pair.2 = .error .badDescriptor := by decide +kernel

theorem kadmos_k02_view_rejects_context_float_tag :
    let pair := allocObject TargetMachine.empty
      ⟨.pythonDict, none, [("balance", ⟨some (.number .pyFloat 100), none, none, true, true, true⟩)], [], [], false, false⟩
    balanceContextValue .python pair.1 pair.2 = .error .invalidTag := by decide +kernel

private def historyProbe (amount : TargetValue) : TargetMachine × ObjRef :=
  let data (v : TargetValue) : Descriptor := ⟨some v, none, none, true, true, true⟩
  let (m, payload) := allocObject TargetMachine.empty
    ⟨.pythonDict, none, [("amount", data amount)], [], [], false, false⟩
  let (m, record) := allocObject m
    ⟨.pythonDict, none,
      [("step", data (.number .pyInt 1)), ("state", data (.string "Ready")),
        ("action", data (.string "DEBIT")), ("eventPayload", data (.object payload))],
      [], [], false, false⟩
  allocObject m ⟨.pythonList, none, [], [.object record], [], false, false⟩

theorem kadmos_k02_view_rejects_unsanitized_python_tag :
    let pair := historyProbe (.number .pyInt 30)
    decodeBalanceHistory .python pair.1 pair.2 = .error .invalidTag := by decide +kernel

theorem kadmos_k02_view_reads_sanitized_python_record :
    let pair := historyProbe (.number .pyFloat 30)
    decodeBalanceHistory .python pair.1 pair.2 = .ok [expectedRecord .python 30] := by decide +kernel


private def verdictProbe (allowed : Descriptor) (code : Option Descriptor) : TargetOutcome :=
  let data (v : TargetValue) : Descriptor := ⟨some v, none, none, true, true, true⟩
  let (m, fields) := match code with
    | none => (TargetMachine.empty, [("allowed", allowed)])
    | some codeDescriptor =>
        let (m, violation) := allocObject TargetMachine.empty
          ⟨.jsOrdinary, some 0, [("code", codeDescriptor)], [], [], false, false⟩
        (m, [("allowed", allowed), ("violation", data (.object violation))])
  let (m, verdict) := allocObject m ⟨.jsOrdinary, some 0, fields, [], [], false, false⟩
  ⟨m, .object verdict⟩

theorem kadmos_k02_violation_rejects_hidden_allowed :
    targetViolationCode (verdictProbe
      ⟨some (.bool true), none, none, false, true, true⟩ none) =
      .error .badDescriptor := by decide +kernel

theorem kadmos_k02_violation_rejects_allowed_accessor :
    targetViolationCode (verdictProbe
      ⟨some (.bool true), some 0, none, true, true, true⟩ none) =
      .error .badDescriptor := by decide +kernel

theorem kadmos_k02_violation_rejects_hidden_code :
    targetViolationCode (verdictProbe
      ⟨some (.bool false), none, none, true, true, true⟩
      (some ⟨some (.string "GUARD_FAILED"), none, none, false, true, true⟩)) =
      .error .badDescriptor := by decide +kernel

theorem kadmos_k02_violation_rejects_code_accessor :
    targetViolationCode (verdictProbe
      ⟨some (.bool false), none, none, true, true, true⟩
      (some ⟨some (.string "GUARD_FAILED"), none, some 0, true, true, true⟩)) =
      .error .badDescriptor := by decide +kernel


namespace HarmoniaTests.KadmosGeneratedK02Closed

structure DebitCase where
  balance : Int
  amount : Int
  allowed : Bool
  violation : Option String

-- This helper observes actual executor results. Expected logical data is only
-- a comparison operand; it never supplies a heap, verdict, or helper result.
def checkDebitCase (lang : TargetLang) (program : TargetProgram)
    (sample : DebitCase) : Except TargetError Bool := do
  let m ← targetConstruct program (canonicalBalanceSeed lang sample.balance)
  let before ← balanceView lang m
  let out ← targetStep program m (canonicalDebitRequest lang sample.amount)
  let after ← balanceView lang out.machine
  let projection ← targetProjection lang out
  let code ← targetViolationCode out
  let expectedAfter : BalanceView := if sample.allowed then
      ⟨"Ready", sample.balance - sample.amount, [expectedRecord lang sample.amount],
        some ⟨"Ready", sample.balance, []⟩, sample.balance, false⟩
    else before
  let expectedProjection : Normalized :=
    ⟨sample.allowed, "Ready", [("balance", expectedAfter.balance)], none⟩
  return balanceRepCheck lang sample.balance m && heapWFCheck lang out.machine &&
    decide (before = ⟨"Ready", sample.balance, [], none, sample.balance, false⟩) &&
    decide (after = expectedAfter) && decide (projection = expectedProjection) &&
    decide (code = sample.violation) && decide (out.machine.checker.busy = false)

def checkOneDebit (lang : TargetLang) (source : String) (sample : DebitCase) : Option Bool :=
  (parseGenerated lang source).toOption.bind fun program =>
    (checkDebitCase lang program sample).toOption


end HarmoniaTests.KadmosGeneratedK02Closed
