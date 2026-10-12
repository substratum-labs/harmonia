import Harmonia.Applications.Kadmos.Generated.SourceValidator
import Harmonia.Applications.Kadmos.Generated.TargetExpressionParser
import Harmonia.Applications.Kadmos.Generated.Fixtures
import HarmoniaTests.KadmosGeneratedK02SourceLex

open Harmonia.Applications.Kadmos.Generated
open Harmonia.Applications.Kadmos.GeneratedFixtures

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

private def rhs (span : SourceSpan) : Option TargetExpr :=
  (parseTargetExpr .ts (span.text balanceTsSource)).toOption

/-- The candidate producer is deliberately untrusted. The independent
    validator checks the individual source rules and nontrivia ownership. -/
private def balanceTSModulePrefix : Option (List SourceItem) := do
  let world ← rhs ⟨797, 1266⟩
  let defaults ← rhs ⟨1335, 1366⟩
  let context ← rhs ⟨1498, 1511⟩
  let states ← rhs ⟨1603, 1615⟩
  let invariants ← rhs ⟨1710, 1726⟩
  let transitions ← rhs ⟨1944, 1961⟩
  return [
    .runtime .module ⟨74, 121⟩
      (.fromImport "node:util" "types" "nodeTypes"),
    .tsTypeImport ⟨122, 244⟩
      ["IWorldChecker", "WorldContext", "WorldState", "TransitionStepRequest",
       "StepVerdict", "StepRecord"] "./ports.js",
    .tsWorldDataType ⟨245, 771⟩,
    .runtime .module ⟨772, 1267⟩ (.letLocal "world" false world),
    .runtime .module ⟨1268, 1367⟩
      (.letLocal "contextDefaults" false defaults),
    .runtime .module ⟨1368, 1512⟩
      (.letLocal "contextDefinitions" false context),
    .runtime .module ⟨1513, 1616⟩
      (.letLocal "stateDefinitions" false states),
    .runtime .module ⟨1617, 1727⟩
      (.letLocal "invariantDefinitions" false invariants),
    .runtime .module ⟨1728, 1962⟩
      (.letLocal "transitionDefinitions" false transitions)]

private def tokenCandidate : Option (List SourceToken) :=
  (tokenizeSource .ts balanceTsSource).toOption

theorem kadmos_generated_balance_ts_module_prefix_owned :
    (do
      let items ← balanceTSModulePrefix
      let tokens ← tokenCandidate
      pure (validateSourceItems .ts balanceTsSource items &&
        validateOrderedItems items &&
        validateNontriviaOwned tokens items 1962)) = some true := by
  decide +kernel

theorem kadmos_generated_balance_ts_prefix_derives :
    PrefixDerives .ts balanceTsSource 1962 := by
  have hPrefix := kadmos_generated_balance_ts_module_prefix_owned
  have hLex := kadmos_generated_balance_ts_token_coverage
  cases ht : tokenCandidate with
  | none =>
      have hNoTokens : (tokenizeSource .ts balanceTsSource).toOption = none := by
        simpa [tokenCandidate] using ht
      simp [hNoTokens] at hLex
  | some tokens =>
      cases hi : balanceTSModulePrefix with
      | none => simp [hi, ht] at hPrefix
      | some items =>
          simp [hi, ht] at hPrefix
          have hTokens : (tokenizeSource .ts balanceTsSource).toOption =
              some tokens := by simpa [tokenCandidate] using ht
          have hLexBool : validateLexes .ts balanceTsSource tokens = true := by
            simpa [hTokens] using hLex
          exact .ofItems (validateLexes_sound hLexBool)
            (validateSourceItems_sound hPrefix.1.1)
            (validateOrderedItems_sound hPrefix.1.2)
            (validateNontriviaOwned_sound hPrefix.2)

private def orderRhs (span : SourceSpan) : Option TargetExpr :=
  (parseTargetExpr .ts (span.text orderTsSource)).toOption

private def orderTSModulePrefix : Option (List SourceItem) := do
  let world ← orderRhs ⟨797, 1322⟩
  let defaults ← orderRhs ⟨1391, 1422⟩
  let context ← orderRhs ⟨1554, 1567⟩
  let states ← orderRhs ⟨1659, 1671⟩
  let invariants ← orderRhs ⟨1766, 1782⟩
  let transitions ← orderRhs ⟨2000, 2017⟩
  return [
    .runtime .module ⟨74, 121⟩
      (.fromImport "node:util" "types" "nodeTypes"),
    .tsTypeImport ⟨122, 244⟩
      ["IWorldChecker", "WorldContext", "WorldState", "TransitionStepRequest",
       "StepVerdict", "StepRecord"] "./ports.js",
    .tsWorldDataType ⟨245, 771⟩,
    .runtime .module ⟨772, 1323⟩ (.letLocal "world" false world),
    .runtime .module ⟨1324, 1423⟩
      (.letLocal "contextDefaults" false defaults),
    .runtime .module ⟨1424, 1568⟩
      (.letLocal "contextDefinitions" false context),
    .runtime .module ⟨1569, 1672⟩
      (.letLocal "stateDefinitions" false states),
    .runtime .module ⟨1673, 1783⟩
      (.letLocal "invariantDefinitions" false invariants),
    .runtime .module ⟨1784, 2018⟩
      (.letLocal "transitionDefinitions" false transitions)]

theorem kadmos_generated_order_ts_module_prefix_owned :
    (do
      let items ← orderTSModulePrefix
      let tokens ← (tokenizeSource .ts orderTsSource).toOption
      pure (validateSourceItems .ts orderTsSource items &&
        validateOrderedItems items &&
        validateNontriviaOwned tokens items 2018)) = some true := by
  decide +kernel

theorem kadmos_generated_order_ts_prefix_derives :
    PrefixDerives .ts orderTsSource 2018 := by
  have hPrefix := kadmos_generated_order_ts_module_prefix_owned
  have hLex := kadmos_generated_order_ts_token_coverage
  cases ht : (tokenizeSource .ts orderTsSource).toOption with
  | none => simp [ht] at hLex
  | some tokens =>
      cases hi : orderTSModulePrefix with
      | none => simp [hi] at hPrefix
      | some items =>
          simp [hi, ht] at hPrefix
          have hLexBool : validateLexes .ts orderTsSource tokens = true := by
            simpa [ht] using hLex
          exact .ofItems (validateLexes_sound hLexBool)
            (validateSourceItems_sound hPrefix.1.1)
            (validateOrderedItems_sound hPrefix.1.2)
            (validateNontriviaOwned_sound hPrefix.2)

private def dropTypeAlias : List SourceItem → List SourceItem
  | first :: second :: _alias :: rest => first :: second :: rest
  | items => items

theorem kadmos_generated_balance_ts_missing_alias_unowned :
    (do
      let items ← balanceTSModulePrefix
      let tokens ← tokenCandidate
      pure (validateNontriviaOwned tokens (dropTypeAlias items) 1962)) =
        some false := by
  decide +kernel

private def swapFirstTwo : List SourceItem → List SourceItem
  | first :: second :: rest => second :: first :: rest
  | items => items

theorem kadmos_generated_balance_ts_reordered_prefix_rejected :
    balanceTSModulePrefix.map
      (fun items => validateOrderedItems (swapFirstTwo items)) = some false := by
  decide +kernel

#check validateSourceItems_sound
#check validateOrderedItems_sound
#check validateNontriviaOwned_sound
