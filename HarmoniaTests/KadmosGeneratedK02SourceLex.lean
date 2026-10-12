import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.Fixtures

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

theorem kadmos_generated_balance_ts_token_coverage :
    (tokenizeSource .ts balanceTsSource).toOption.map
      (validateLexes .ts balanceTsSource) = some true := by
  decide +kernel

theorem kadmos_generated_order_ts_token_coverage :
    (tokenizeSource .ts orderTsSource).toOption.map
      (validateLexes .ts orderTsSource) = some true := by
  decide +kernel

theorem kadmos_generated_balance_python_token_coverage :
    (tokenizeSource .python balancePySource).toOption.map
      (validateLexes .python balancePySource) = some true := by
  decide +kernel

theorem kadmos_generated_order_python_token_coverage :
    (tokenizeSource .python orderPySource).toOption.map
      (validateLexes .python orderPySource) = some true := by
  decide +kernel

theorem kadmos_generated_nonmaximal_identifier_rejected :
    validateLexes .ts "ab"
      [⟨.identifier, "a", 0, 1⟩, ⟨.identifier, "b", 1, 2⟩] = false := by
  decide +kernel

theorem kadmos_generated_identifier_as_punctuation_rejected :
    validateLexes .ts "a" [⟨.punctuation, "a", 0, 1⟩] = false := by
  decide +kernel

theorem kadmos_generated_regex_punctuation_split_rejected :
    validateLexes .ts "/x/"
      [⟨.punctuation, "/", 0, 1⟩, ⟨.identifier, "x", 1, 2⟩,
       ⟨.punctuation, "/", 2, 3⟩] = false := by
  decide +kernel

theorem kadmos_generated_comment_punctuation_split_rejected :
    validateLexes .ts "//x"
      [⟨.punctuation, "/", 0, 1⟩, ⟨.punctuation, "/", 1, 2⟩,
       ⟨.identifier, "x", 2, 3⟩] = false := by
  decide +kernel

theorem kadmos_generated_regex_first_close_owned :
    validateLexes .ts "/x/" [⟨.regex, "/x/", 0, 3⟩] = true := by
  decide +kernel

theorem kadmos_generated_regex_early_close_rejected :
    validateLexes .ts "/x/y/" [⟨.regex, "/x/y/", 0, 5⟩] = false := by
  decide +kernel
