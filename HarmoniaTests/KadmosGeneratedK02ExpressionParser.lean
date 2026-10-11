import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser

open Harmonia.Applications.Kadmos.Generated

example : (parseTargetExpr .ts "this.#busy").toOption =
    some (.property (.local "this") "#busy") := by decide +kernel
example : (parseTargetExpr .python "self._busy").toOption =
    some (.property (.local "self") "_busy") := by decide +kernel
example : (parseTargetExpr .python "position + 1").toOption =
    some (.binary .add (.local "position") (.integer 1)) := by decide +kernel
example : (parseTargetExpr .ts "!transition").toOption =
    some (.unary .not (.local "transition")) := by decide +kernel
example : (parseTargetExpr .ts "Object.hasOwn(left, property)").toOption =
    some (.call (.property (.local "Object") "hasOwn")
      (.sequence (.local "left") (.sequence (.local "property") .empty))) := by decide +kernel
example : (parseTargetExpr .python "_TOKEN.match(expression, offset)").toOption =
    some (.call (.property (.local "_TOKEN") "match")
      (.sequence (.local "expression") (.sequence (.local "offset") .empty))) := by decide +kernel
example : (parseTargetExpr .python "tokens[position]").toOption =
    some (.index (.local "tokens") (.local "position")) := by decide +kernel
example : (parseTargetExpr .python "r\"\\s+\"").toOption =
    some (.string "\\s+") := by decide +kernel
example : (parseTargetExpr .ts "/^\\d/.test(token)").toOption =
    some (.call (.property (.regexLiteral "/^\\d/") "test")
      (.sequence (.local "token") .empty)) := by decide +kernel
example : (parseTargetExpr .ts "\"{\\\"balance\\\":100}\"").toOption =
    some (.string "{\"balance\":100}") := by decide +kernel
example : (parseTargetExpr .ts "{ ...contextDefaults }").toOption =
    some (.object (.objectSpread (.local "contextDefaults") .empty)) := by decide +kernel
example : (parseTargetExpr .python "{\"balance\": 100}").toOption =
    some (.object (.objectEntry "balance" (.integer 100) .empty)) := by decide +kernel
example : (parseTargetExpr .python "[]").toOption =
    some (.array .empty) := by decide +kernel
example : (parseTargetExpr .ts "ready ? yes : no").toOption =
    some (.conditional (.local "ready") (.local "yes") (.local "no")) := by decide +kernel
example : (parseTargetExpr .python "yes if ready else no").toOption =
    some (.conditional (.local "ready") (.local "yes") (.local "no")) := by decide +kernel
example : (parseTargetExpr .ts "typeof nodeTypes?.isProxy === \"function\"").toOption =
    some (.binary .strictEq (.unary .typeof
      (.optionalProperty (.local "nodeTypes") "isProxy")) (.string "function")) := by decide +kernel
example : (parseTargetExpr .python "type(value) is not str").toOption =
    some (.binary .isNotIdentity (.call (.local "type")
      (.sequence (.local "value") .empty)) (.local "str")) := by decide +kernel
example : (parseTargetExpr .python "(int, float)").toOption =
    some (.tuple (.sequence (.local "int")
      (.sequence (.local "float") .empty))) := by decide +kernel
example : (parseTargetExpr .python "{k: _freeze(v) for k, v in value.items()}").toOption =
    some (.dictComprehension (.local "k")
      (.call (.local "_freeze") (.sequence (.local "v") .empty))
      ["k", "v"] (.call (.property (.local "value") "items") .empty) .empty) := by decide +kernel
example : (parseTargetExpr .python "[copy.deepcopy(r) for r in original_history]").toOption =
    some (.listComprehension
      (.call (.property (.local "copy") "deepcopy") (.sequence (.local "r") .empty))
      ["r"] (.local "original_history") .empty) := by decide +kernel
example : (parseTargetExpr .python
    "next(state[\"id\"] for state in _WORLD[\"states\"] if state.get(\"initial\"))").toOption =
    some (.call (.local "next") (.sequence
      (.generator (.index (.local "state") (.string "id")) ["state"]
        (.index (.local "_WORLD") (.string "states"))
        (.call (.property (.local "state") "get") (.sequence (.string "initial") .empty)))
      .empty)) := by decide +kernel
example : (parseTargetExpr .python "f\"INVALID_BOUNDS: {invalid}\"").toOption =
    some (.formatted (.formatPart "INVALID_BOUNDS: " (.local "invalid") .empty)) := by decide +kernel
example : (parseTargetExpr .ts "`Context bound failed on '${boundError}'`").toOption =
    some (.formatted (.formatPart "Context bound failed on '" (.local "boundError")
      (.formatPart "'" .empty .empty))) := by decide +kernel
example : (parseTargetExpr .ts "`broken ${`").toOption = none := by decide +kernel
example : (parseTargetExpr .python "lambda state, values: {**values, \"state\": state}").toOption =
    some (.lambdaExpr ["state", "values"]
      (.object (.objectSpread (.local "values")
        (.objectEntry "state" (.local "state") .empty)))) := by decide +kernel
example : (parseTargetExpr .python "0.0").toOption =
    some (.decimal "0.0") := by decide +kernel
example : (parseTargetExpr .python "token[1:-1]").toOption =
    some (.slice (.local "token") (.integer 1) (.unary .neg (.integer 1))) := by decide +kernel
