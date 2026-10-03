/-
  Harmonia.SMT.AST
  Abstract syntax tree and serialization for SMT-LIB2 standard formats.
-/

namespace Harmonia.SMT

/-- SMT-LIB2 Sorts (Types). Renamed to SMTSort to avoid collision with Lean's Sort keyword. -/
inductive SMTSort where
  | bool
  | int
  | string
  | custom (name : String)
deriving DecidableEq, Repr

namespace SMTSort

def toString : SMTSort → String
  | bool => "Bool"
  | int => "Int"
  | string => "String"
  | custom name => name

instance : ToString SMTSort where
  toString := toString

end SMTSort

/-- SMT-LIB2 Terms and Formulas. -/
inductive Term where
  | boolConst (b : Bool)
  | intConst (n : Int)
  | var (name : String)
  | app (fn : String) (args : List Term)
  | not (t : Term)
  | and (ts : List Term)
  | or (ts : List Term)
  | implies (t1 t2 : Term)
  | eq (t1 t2 : Term)
  | distinct (ts : List Term)
  | ite (c t e : Term)

namespace Term

partial def toString : Term → String
  | boolConst b => if b then "true" else "false"
  | intConst n => s!"{n}"
  | var name => name
  | app fn args => s!"({fn} {" ".intercalate (args.map toString)})"
  | not t => s!"(not {t.toString})"
  | and [] => "true"
  | and [t] => t.toString
  | and ts => s!"(and {" ".intercalate (ts.map toString)})"
  | or [] => "false"
  | or [t] => t.toString
  | or ts => s!"(or {" ".intercalate (ts.map toString)})"
  | implies t1 t2 => s!"(=> {t1.toString} {t2.toString})"
  | eq t1 t2 => s!"(= {t1.toString} {t2.toString})"
  | distinct ts => s!"(distinct {" ".intercalate (ts.map toString)})"
  | ite c t e => s!"(ite {c.toString} {t.toString} {e.toString})"

instance : ToString Term where
  toString := toString

end Term

/-- SMT-LIB2 Top-Level Commands. -/
inductive Command where
  | setLogic (logic : String)
  | setOption (opt : String) (val : String)
  | declareDatatype (name : String) (constructors : List String)
  | declareConst (name : String) (sort : SMTSort)
  | declareFun (name : String) (argSorts : List SMTSort) (retSort : SMTSort)
  | assert (t : Term)
  | checkSat
  | getModel
  | comment (text : String)

namespace Command

def toString : Command → String
  | setLogic logic => s!"(set-logic {logic})"
  | setOption opt val => s!"(set-option :{opt} {val})"
  | declareDatatype name ctors =>
      let ctorDefs := ctors.map (fun c => s!"({c})")
      s!"(declare-datatype {name} ({" ".intercalate ctorDefs}))"
  | declareConst name s => s!"(declare-const {name} {s})"
  | declareFun name args ret =>
      let argStrs := " ".intercalate (args.map SMTSort.toString)
      s!"(declare-fun {name} ({argStrs}) {ret})"
  | assert t => s!"(assert {t})"
  | checkSat => "(check-sat)"
  | getModel => "(get-model)"
  | comment text => s!";; {text}"

instance : ToString Command where
  toString := toString

end Command

/-- Render a sequence of commands into a complete SMT-LIB2 script. -/
def renderScript (cmds : List Command) : String :=
  String.intercalate "\n" (cmds.map Command.toString) ++ "\n"

end Harmonia.SMT
