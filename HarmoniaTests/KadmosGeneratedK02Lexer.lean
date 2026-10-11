import Harmonia.Applications.Kadmos.Generated.TargetSyntax
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

-- Lexical coverage alone is not a parsed program or behavior certificate.
example : (tokenizeSource .ts balanceTsSource).toOption.isSome = true := by decide +kernel
example : (tokenizeSource .python balancePySource).toOption.isSome = true := by decide +kernel
example : (tokenizeSource .ts orderTsSource).toOption.isSome = true := by decide +kernel
example : (tokenizeSource .python orderPySource).toOption.isSome = true := by decide +kernel

example : (tokenizeSource .ts "const x = /a[b/]c/g; // tail\n").toOption.map
    (fun xs => String.join (xs.map SourceToken.text)) =
    some "const x = /a[b/]c/g; // tail\n" := by decide +kernel
example : (tokenizeSource .python "_TOKEN = re.compile(r'\\s+')\n").toOption.map
    (fun xs => String.join (xs.map SourceToken.text)) =
    some "_TOKEN = re.compile(r'\\s+')\n" := by decide +kernel
