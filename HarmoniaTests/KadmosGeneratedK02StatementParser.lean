import Harmonia.Applications.Kadmos.Generated.TargetStatementParser

open Harmonia.Applications.Kadmos.Generated

private def booleanBody :=
  "    if type(value) is not bool:\n" ++
  "        raise ValueError(\"INVALID_EXPRESSION: expected boolean operand\")\n" ++
  "    return value\n"

example : (parsePythonBlock booleanBody 4).toOption =
    some (.sequence
      (.ifThenElse
        (.binary .isNotIdentity
          (.call (.local "type") (.sequence (.local "value") .empty))
          (.local "bool"))
        (.sequence (.throwValue
          (.call (.local "ValueError")
            (.sequence (.string "INVALID_EXPRESSION: expected boolean operand") .empty))) .empty)
        .empty)
      (.sequence (.returnValue (.local "value")) .empty)) := by decide +kernel

private def freezeBody :=
  "    if type(value) is dict:\n" ++
  "        return types.MappingProxyType({k: _freeze(v) for k, v in value.items()})\n" ++
  "    if type(value) is list:\n" ++
  "        return tuple(_freeze(v) for v in value)\n" ++
  "    return value\n"
example : (parsePythonBlock freezeBody 4).toOption.isSome = true := by decide +kernel

private def initSlice :=
  "        self.__state = _INITIAL\n" ++
  "        self._busy = False\n" ++
  "        self.reset(initial_context)\n" ++
  "        self.__constructor_seed = dict(self.__context)\n"
example : (parsePythonBlock initSlice 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    "        self.__context: dict[str, int | str] = {}\n" 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("        for name, definition in _WORLD[\"context\"].items():\n" ++
     "            value = values.get(name)\n") 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("    if value is None:\n" ++
     "        return None\n" ++
     "    elif type(value) is dict:\n" ++
     "        return value\n" ++
     "    else:\n" ++
     "        return False\n") 4).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("        try:\n" ++
     "            candidate = dict(_DEFAULTS)\n" ++
     "        except Exception:\n" ++
     "            rollback()\n" ++
     "            raise\n" ++
     "        finally:\n" ++
     "            self._busy = False\n") 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("        def rollback() -> None:\n" ++
     "            self.__state = snapshot_state\n" ++
     "            self.__context = dict(snapshot_context)\n") 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    "        saved_state, saved_context, saved_history = self.__undo\n" 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("        nonlocal position\n" ++
     "        position += 1\n" ++
     "        break\n") 8).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("import json\nfrom __future__ import annotations\n" ++
     "class WorldChecker(IWorldChecker):\n" ++
     "    @property\n" ++
     "    def state(self) -> str:\n" ++
     "        return self.__state\n") 0).toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    ("def f(environment: dict[str, Any], minimum: int = 0) -> Any:\n" ++
     "    return minimum\n") 0).toOption.isSome = true := by decide +kernel
example : (parsePythonProgram
    "import json\ndef f(x: int = 0) -> int:\n    return x\n").toOption.isSome = true := by decide +kernel
example : (parsePythonBlock
    "class WorldChecker(IWorldChecker):\n    def get_state(self):\n        return self.__state\n" 0).toOption =
    some (.sequence (.defineClass "WorldChecker" (.local "IWorldChecker")
      (.sequence (.defineFunction "get_state" []
        (.sequence (.returnValue (.property (.local "self") "__state")) .empty)) .empty))
      .empty) := by decide +kernel
