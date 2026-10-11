import Harmonia.Applications.Kadmos.Generated.TargetTSStatementParser

open Harmonia.Applications.Kadmos.Generated

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def constructorBody :=
  "this.reset(initialContext);\n" ++
  "this.#constructorSeed = { ...this.#context };"

example : (parseTSBlock constructorBody).toOption =
    some (.sequence
      (.doExpr (.call (.property (.local "this") "reset")
        (.sequence (.local "initialContext") .empty)))
      (.sequence
        (.assign (.property (.local "this") "#constructorSeed")
          (.object (.objectSpread (.property (.local "this") "#context") .empty)))
        .empty)) := by decide +kernel

private def booleanBody :=
  "if (typeof value !== \"boolean\") throw new Error(\"INVALID_EXPRESSION: expected boolean\");\n" ++
  "return value;"
example : (parseTSBlock booleanBody).toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "const value = values[key]; let index = 0; return undefined;").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "const result: Record<string, unknown> = Object.create(null);").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    ("for (const [key, definition] of Object.entries(contextDefinitions)) {" ++
     " const value = values[key]; if (value > 0) return key; }")).toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "try { const res = evaluateWorld(expr, env); return res; } catch { return undefined; }").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "const rollback = () => { this.#state = snapshotState; this.#context = { ...snapshotContext }; };").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "const f = (env: Record<string, unknown>) => { return env; };").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "const f = (env: Record<string, unknown>) => { return env; };").toOption =
    some (.sequence (.defineFunction "f" [⟨"env", none⟩]
      (.sequence (.returnValue (.local "env")) .empty)) .empty) := by decide +kernel
example : (parseTSBlock "let overrides: Record<string, unknown>;").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "while (tokens[index] === \".\") { index++; break; }").toOption.isSome = true := by decide +kernel
example : (parseTSBlock
    "switch (operator) { case \"+\": left = 1; break; }").toOption =
    some (.sequence (.switchOn (.local "operator")
      (.switchCase "+"
        (.sequence (.assign (.local "left") (.integer 1))
        (.sequence (.breakTarget "switch") .empty)) .empty)) .empty) := by decide +kernel
private def smallModule :=
  "import { types as nodeTypes } from \"node:util\";\n" ++
  "type WorldData = { value: number };\n" ++
  "const contextDefaults = { balance: 100 };\n" ++
  "function helper(x: number): number { return x; }\n" ++
  "export class WorldChecker {\n" ++
  "  #busy: boolean = false;\n" ++
  "  constructor(initialContext: unknown = null) { this.#busy = false; }\n" ++
  "}\n"
example : (parseTSProgram smallModule).toOption.isSome = true := by decide +kernel
