import Harmonia.Applications.Kadmos.Generated.TargetStatementParser
import Harmonia.Applications.Kadmos.Generated.TargetTSStatementParser

namespace Harmonia.Applications.Kadmos.Generated

def parseGenerated (lang : TargetLang) (source : String) :
    Except ParseError TargetProgram :=
  match lang with
  | .ts => parseTSProgram source
  | .python => parsePythonProgram source

end Harmonia.Applications.Kadmos.Generated
