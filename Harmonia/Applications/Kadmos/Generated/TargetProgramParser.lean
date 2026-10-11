import Harmonia.Applications.Kadmos.Generated.TargetStatementParser
import Harmonia.Applications.Kadmos.Generated.TargetTSStatementParser
import Harmonia.Applications.Kadmos.Generated.TargetJSON

namespace Harmonia.Applications.Kadmos.Generated

def parseGenerated (lang : TargetLang) (source : String) :
    Except ParseError TargetProgram :=
  match lang with
  | .ts => parseTSProgram source
  | .python => parsePythonProgram source

private def findBinding (name : String) : TargetStmt → Option TargetExpr
  | .sequence first rest =>
      (findBinding name first).orElse fun _ => findBinding name rest
  | .letLocal localName _ value => if name == localName then some value else none
  | .assign (.local localName) value => if name == localName then some value else none
  | _ => none

private def tsJSONArgument : TargetExpr → Option String
  | .call (.property (.local "JSON") "parse") (.sequence (.string source) .empty) =>
      some source
  | _ => none

private def pyJSONArgument : TargetExpr → Option String
  | .call (.local "_freeze")
      (.sequence (.call (.property (.local "json") "loads")
        (.sequence (.string source) .empty)) .empty) => some source
  | _ => none

def embeddedWorldJSON (program : TargetProgram) : Option TargetJSON := do
  let literal ← match program.lang with
    | .ts => (findBinding "world" program.moduleInit).bind tsJSONArgument
    | .python => (findBinding "_WORLD" program.moduleInit).bind pyJSONArgument
  (parseTargetJSON literal).toOption

def embeddedDefaultsJSON (program : TargetProgram) : Option TargetJSON := do
  if program.lang != .ts then none
  else
    let literal ← (findBinding "contextDefaults" program.moduleInit).bind tsJSONArgument
    (parseTargetJSON literal).toOption

end Harmonia.Applications.Kadmos.Generated
