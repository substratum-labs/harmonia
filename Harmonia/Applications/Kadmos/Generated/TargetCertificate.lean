import Harmonia.Applications.Kadmos.Generated.TargetProgramParser
import Harmonia.Applications.Kadmos.Generated.Fixtures
import Harmonia.Applications.Kadmos.Bridge.Fixtures

namespace Harmonia.Applications.Kadmos.Generated

open Harmonia.Applications.Kadmos.Bridge
open Harmonia.Applications.Kadmos.BridgeFixtures
open Harmonia.Applications.Kadmos.GeneratedFixtures
open Harmonia.Applications.Kadmos

inductive CertError where
  | bridge (error : BridgeError)
  | unsupportedFixture | sourceMismatch | parser (error : ParseError)
  | worldMismatch | defaultsMismatch
  deriving DecidableEq

private def jsonFields : List (String × TargetJSON) → TargetJSON
  | [] => .empty
  | (key, value) :: rest => .keyVal key value (jsonFields rest)

private def jsonItems : List TargetJSON → TargetJSON
  | [] => .empty
  | value :: rest => .valueItem value (jsonItems rest)

private def jsonObject (fields : List (String × TargetJSON)) : TargetJSON :=
  .object (jsonFields fields)

private def jsonArray (values : List TargetJSON) : TargetJSON :=
  .array (jsonItems values)

private def optionalField (name : String) (value : Option α)
    (encode : α → TargetJSON) : List (String × TargetJSON) :=
  match value with
  | none => []
  | some v => [(name, encode v)]

private def stateJSON (state : RawState) : TargetJSON :=
  jsonObject ([ ("id", .string state.id) ] ++
    (if state.initial then [("initial", .bool true)] else []) ++
    (if state.terminal then [("terminal", .bool true)] else []))

private def variableJSON (definition : RawVariable) : TargetJSON :=
  jsonObject ([("type", .string definition.type)] ++
    optionalField "min" definition.min .integer ++
    optionalField "max" definition.max .integer ++
    optionalField "default" definition.default .integer)

private def invariantJSON (invariant : RawInvariant) : TargetJSON :=
  jsonObject [("id", .string invariant.id),
    ("predicate", .string invariant.predicate)]

private def guardJSON : RawGuard → TargetJSON
  | .bool value => .bool value
  | .expr source => .string source

private def transitionJSON (transition : RawTransition) : TargetJSON :=
  jsonObject [("id", .string transition.id),
    ("from", .string transition.from), ("to", .string transition.to),
    ("guard", guardJSON transition.guard),
    ("directive", transition.directive.map TargetJSON.string |>.getD .null),
    ("effects", jsonArray (transition.effects.map TargetJSON.string))]

/-- K-02's first-profile emission normalization. It intentionally erases
    descriptions, units, fields and explicit-false presence: `RawWorld` does
    not retain the latter. Source equality below confines this normal form to
    the two reviewed fixtures, and no arbitrary WorldSpec reconstruction is
    claimed. -/
def emittedWorldData (raw : RawWorld) : TargetJSON :=
  jsonObject [("version", .string raw.version), ("name", .string raw.name),
    ("states", jsonArray (raw.states.map stateJSON)),
    ("context", jsonObject (raw.context.map fun entry =>
      (entry.1, variableJSON entry.2))),
    ("invariants", jsonArray (raw.invariants.map invariantJSON)),
    ("transitions", jsonArray (raw.transitions.map transitionJSON))]

def emittedDefaultsData (raw : RawWorld) : TargetJSON :=
  jsonObject (raw.context.map fun entry =>
    (entry.1, .integer (entry.2.default.getD 0)))

private def pinnedSource (lang : TargetLang) (name : String) :
    Option String :=
  match lang, name with
  | .ts, "BalanceWorld" => some balanceTsSource
  | .python, "BalanceWorld" => some balancePySource
  | .ts, "OrderPhaseWorld" => some orderTsSource
  | .python, "OrderPhaseWorld" => some orderPySource
  | _, _ => none

private def checkGeneratedSource (lang : TargetLang) (source : String)
    (raw : RawWorld) : Except CertError TargetProgram :=
  match pinnedSource lang raw.name with
  | none => .error .unsupportedFixture
  | some expected =>
      if source != expected then .error .sourceMismatch
      else
        match parseGenerated lang source with
        | .error error => .error (.parser error)
        | .ok program =>
            if embeddedWorldJSON program != some (emittedWorldData raw) then
              .error .worldMismatch
            else if lang == .ts && embeddedDefaultsJSON program !=
                some (emittedDefaultsData raw) then .error .defaultsMismatch
            else .ok program

/-- The byte gate narrows the first certified subset. It is not a claim that
    bytes or JSON alone preserve semantics: the returned low-level program
    must separately satisfy `SourceParses` and the execution theorem. -/
def checkGenerated (lang : TargetLang) (source : String) (raw : RawWorld)
    (candidate : World raw.states.length raw.context.length raw.fields.length
      raw.transitions.length) : Except CertError TargetProgram := do
  match checkBridge raw candidate with
  | .error error => throw (.bridge error)
  | .ok _ => checkGeneratedSource lang source raw

theorem checkGenerated_when_bridge_ok (lang : TargetLang) (source : String)
    (raw : RawWorld)
    (candidate : World raw.states.length raw.context.length raw.fields.length
      raw.transitions.length) (h : checkBridge raw candidate = .ok candidate) :
    checkGenerated lang source raw candidate =
      checkGeneratedSource lang source raw := by
  simp [checkGenerated, h]

theorem checkGenerated_rejects_changed_source (lang : TargetLang)
    (source expected : String) (raw : RawWorld)
    (candidate : World raw.states.length raw.context.length raw.fields.length
      raw.transitions.length)
    (hBridge : checkBridge raw candidate = .ok candidate)
    (hPinned : pinnedSource lang raw.name = some expected)
    (hChanged : source ≠ expected) :
    checkGenerated lang source raw candidate = .error .sourceMismatch := by
  rw [checkGenerated_when_bridge_ok lang source raw candidate hBridge]
  simp [checkGeneratedSource, hPinned, hChanged]

theorem checkGenerated_accept_if (lang : TargetLang) (source : String)
    (raw : RawWorld)
    (candidate : World raw.states.length raw.context.length raw.fields.length
      raw.transitions.length) (program : TargetProgram)
    (hBridge : checkBridge raw candidate = .ok candidate)
    (hSource : pinnedSource lang raw.name = some source)
    (hParser : parseGenerated lang source = .ok program)
    (hWorld : embeddedWorldJSON program = some (emittedWorldData raw))
    (hDefaults : lang = .ts → embeddedDefaultsJSON program =
      some (emittedDefaultsData raw)) :
    checkGenerated lang source raw candidate = .ok program := by
  rw [checkGenerated_when_bridge_ok lang source raw candidate hBridge]
  by_cases hTS : lang = .ts
  · subst lang
    simp [checkGeneratedSource, hSource, hParser, hWorld, hDefaults rfl]
  · simp [checkGeneratedSource, hSource, hParser, hWorld, hTS]

end Harmonia.Applications.Kadmos.Generated
