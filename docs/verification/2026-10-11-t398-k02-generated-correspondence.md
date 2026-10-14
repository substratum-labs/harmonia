# T-398 K-02 generated correspondence: implementation and proof-strategy receipt

Status: **T-398 IN_PROGRESS; physical proof-strategy R3 ACCEPT admits Task 2A implementation, which is underway.** Parent archived the valid independent R3 report for clean source `e3996929ff34c89574a9753f4f02b511405f8008`, session `01a12d29-3253-7851-ac84-6630f0f3e887`, structured success/is_error=false, exit0/291.8s. R1/R2 review findings are closed at the **plan** level; R3 is not source-code correspondence acceptance. This task now implements the independent full-source `SourceParses` grammar/validator, checked parser, uniqueness and four actual-source kernel acceptance facts under the [corrected design](../superpowers/specs/2026-10-11-t398-k02-checked-syntax-and-simulation-design.md) and [plan](../superpowers/plans/2026-10-11-t398-k02-generated-correspondence.md). No independent `SourceParses` theorem, universal TS/Python b/n target-step correspondence, constructor-totality theorem, new CI gate or merge existed at task start. Parent owns Grok, later review and integration; owner thread `01a11179-2107-7842-8ea3-adaac2c2993a` uses only isolated source/coordinator workspaces.

**Latest owner continuation from `8f2578f` — 2026-10-12:** This continuation repairs grammar prerequisites and span ownership. Task 2A and Task 2B remain **incomplete**. Postfix/callee/unary binding-power premises exclude lower-precedence receivers; statement lists use a separate `.body` grammar sort; Python suites require significant statements, deeper children for suite headers, enclosing function layout and the actual source column at each statement span. Integral member receivers require an explicit delimiter before the dot. Function-item body intervals must start after the admitted header and end before the language's trailer, rather than merely contain matching text somewhere inside the declaration. Formatted literals require delimiter ownership, language-sensitive brace checks and nonreserved local names, with an explicit TS `this` exception. Validator soundness and existing source witnesses are updated for these premises.

Escaped formatted literals and Python comparison chains fail closed until explicit decoding/chain productions exist. These restrictions do not establish full expression or program uniqueness. The live theorem probe still reports `ProgramDerives`, `validateSource_sound`, `parseGenerated_sound` and `SourceParses.unique` as unknown. `parseGenerated` still dispatches to the raw decoders. `TargetSimulation.lean`, `BalanceSimulation.lean`, the two simulation/constructor proof targets, and universal constructor totality remain absent. Existing parse/certificate successes certify the previous raw-decoder interface; they do not close independent checked-source admission. The command receipts and independent review for this continuation are recorded at the end of this document. Earlier checkpoints below remain historical evidence.

**2026-10-12 physical resumption:** The inherited `SingleStatement`/`suiteLinesWithin` change was reproduced RED in the Python Boolean syntax target and repaired by supplying the new proof premises. Generated auditing now rejects `Classical.choice`; explicit `safeInt` conjunction proofs and a constructive source-span list proof remove the observed Generated dependencies. Verification of the final diff is recorded below. **Stage 3c is still incomplete:** the independent reviewer reproduced four remaining source-grammar defects, and complete checked-source admission and Tasks 2B–4 remain absent. No parser-success or audit-success result below is a correspondence theorem.

**Current checkpoint (owner continuation after parent steer):** Task 2A remains **IN_PROGRESS and incomplete**. The partial grammar now excludes language literal/control words from expression-local names, has a separate inductive argument-list sort, and constrains subtraction's right operand so the outer subtraction is left-associated in this fragment. Joint structural induction proves both expression and argument validator soundness; closed kernel tests reject the reported `true`-as-local and `f(x)`-as-bare-argument trees. This does **not** establish full expression precedence or `SourceParses.unique`. Both actual 400-line Python sources now have complete, absolute-offset `ChunkedLines` derivations from 16 independently checked bounded chunks. The generic `ChunkedLines.toPrefixLinesAt` and `PrefixLinesAt.toLinesAt` proofs erase the partition to one contiguous full-source physical-line derivation, including the final empty line after the emitted trailing newline. `lake build kadmosGeneratedK02PythonLinesTest` exited 0 using `--tstack=131072` solely for that test target. The exact Generated inventory passed with 15 product modules, 27 test/audit modules, 48 certified closure modules and 23 test targets; nine disposable-tree checks passed, including rejection of changed or commented-out proof-resource options. Full runtime AST mapping and the four checked-program admissions are still absent. `ProgramDerives`, all four complete source validators, `SourceParses.unique`, checked `parseGenerated_sound`, and source-bound certificate integration remain the open Task 2A gate. None of these line or fragment facts is a generated-step correspondence claim or admission to Task 2B/3.

**Next constituent slice after checkpoint `24eaa324faeaaef689565895cea478e83f975662`:** The separate argument grammar now admits multiple arguments through a validated lexical token stream and a deterministic first comma at delimiter depth zero. Its soundness remains in the joint structural proof. RED `lake build kadmosGeneratedK02SourceGrammarTest` failed the intended `f(a, b)` and nested `f(g(a, b), c)` facts; GREEN passed after the rule. The actual pinned Python source span `⟨6105,6140⟩` for `_div(_number(left), _number(right))` now derives its nested call AST from source, and an `ideal_div` call-target mutation is rejected. Actual Python constructor span `⟨12175,12211⟩` for `self._invariant(_INITIAL, candidate)` likewise derives with argument order checked. The TS parser represents the source keyword `this` as `.local "this"`; a separate `ExprSyntax.tsThis` production owns that spelling while ordinary expression identifiers still exclude reserved words. Actual TS constructor span `⟨11893,11933⟩` for `this.checkInvariants("Ready", candidate)` derives and a changed call target is rejected. Separate kernel facts confirm the raw expression decoder proposes these same three ASTs; those facts are candidate equality, while the independent grammar supplies the source derivation. `#print axioms` on argument validator soundness and both constructor-call derivations showed `[propext, Quot.sound]`. These are reached source-expression constituents, **not** complete helper bodies or program admission. Serial Lake builds for SourceGrammar, SourceValidator, PythonBooleanSyntax, SourceModule, SourceLex, PythonLines, normal Generated audit, normal World audit, and `lake build` all exited 0. Generated audit: 7,382 theorems / 9,813 declarations; World audit: 9,015 / 12,063; each observed only `[propext, Quot.sound, Classical.choice]`. Live exact inventory and nine disposable-tree checks exited 0. The full Task 2A source-program gate remains open.

**Further constituent slice after `22f446f6c34eaab87b01a3774f1ea725d19648ef`:** The original property rule could parse only one dot and could not map TS private `#` fields. RED actual-source facts for `this.#context` and `Object.prototype.toString.call` failed; the independent grammar now has separate TS public/private and Python dotted-name categories, while the AST-guided validator uses the last source dot and checks each nested property. The exact pinned TS spans `⟨8234,8247⟩` and `⟨6469,6499⟩` now validate and derive; separate closed facts match the raw decoder candidate ASTs. A changed `#history` field candidate fails against the `#context` source. A TS keyword property is accepted and a Python reserved keyword property rejected under their separate categories. `#print axioms` on the property-name soundness and both source derivations showed only `[propext]` or `[propext, Quot.sound]`. Serial affected SourceGrammar/SourceValidator/PythonBooleanSyntax/SourceModule/SourceLex/PythonLines targets, normal Generated audit, normal World audit and `lake build` exited 0. Generated audit: 7,401 theorems / 9,845 declarations; World audit: 9,018 / 12,078; each observed only `[propext, Quot.sound, Classical.choice]`. Exact inventory and nine disposable-tree checks passed. This still does **not** validate every emitted expression or any full helper; the full Task 2A gate remains open.

**Further constituent slice after `c534a359aaaa3f9e5709af65d632b2db183aeb16`:** The actual TS sanitizer source span `⟨6115,6133⟩` is `nodeTypes?.isProxy`, which the target parser maps to `.optionalProperty` and the earlier grammar rejected. A new TS-only optional-property production and source check now own the `?.` spelling and the independently checked receiver/name. The actual source derivation and separate raw-decoder AST equality are kernel facts; changing the AST property name or changing source `?.` to `.` fails. `#print axioms` on the derivation and generic expression validator soundness showed `[propext, Quot.sound]`. This is a sanitizer-expression constituent, not a sanitizer body or a full-source certificate. The focused grammar target passed after an intended RED failure; serial affected SourceValidator/PythonBooleanSyntax/SourceModule/SourceLex/PythonLines, normal Generated audit, normal World audit and `lake build` all exited 0. Generated audit: 7,412 theorems / 9,862 declarations; World audit: 9,020 / 12,086; each observed only `[propext, Quot.sound, Classical.choice]`. Exact inventory and nine disposable-tree checks passed. The full Task 2A gate remains open.

**Current batched postfix work after `0de0d954ea892323e39154814295d96ce9ed9533`:** Following the parent's coherent-proof-batch ruling, focused RED/GREEN checked two related source forms before a heavyweight suite. Actual TS `env[token]` span `⟨3608,3618⟩`, Python `_WORLD["context"]` span `⟨1146,1163⟩`, and Python nested `_WORLD["context"][name]` span `⟨11959,11982⟩` now derive through a recursive index grammar rule; separate kernel facts match their raw expression-decoder ASTs, and a changed context key is rejected. Actual TS `contextDefinitions[name]!` span `⟨11516,11541⟩` now derives through a TS-only non-null postfix rule, with raw candidate equality and a missing-`!` source mutation rejection. `#print axioms` on the actual TS/Python index and TS non-null derivations showed `[propext, Quot.sound]`. Serial affected SourceGrammar/SourceValidator/PythonBooleanSyntax/SourceModule/SourceLex/PythonLines targets, normal Generated audit, normal World audit and `lake build` exited 0. Generated audit: 7,439 theorems / 9,901 declarations; World audit: 9,024 / 12,101; observed only `[propext, Quot.sound, Classical.choice]`. Exact inventory and nine disposable-tree checks passed. These are expression constituents only; full program grammar/uniqueness/checked parser/four admissions remain open.

**Proof-module organization after `d6bbc56a31400bf69d815c8897b7e9e2faef5cd5`:** Following the parent's resource ruling, stable token/span/physical-line grammar and validator declarations were moved without renaming public definitions to `SourceLexical.lean` and `SourceLexicalValidator.lean`. `SourceGrammar.lean` now imports the stable grammar and contains the changing expression/statement grammar; `SourceValidator.lean` imports both and contains the changing checks. The full-source lexical and Python line test roots import the stable validator directly. Product modules, focused grammar, full TS/Python lexical coverage, both full Python line targets, SourceValidator, PythonBooleanSyntax, SourceModule, normal Generated audit, normal World audit and `lake build` passed serially. The exact inventory passed with 17 product modules, 27 test/audit modules, 50 certified closure modules and 23 targets; nine disposable-tree checks passed. Generated audit: 7,442 theorems / 9,908 declarations; World audit: 9,027 / 12,108; each observed only `[propext, Quot.sound, Classical.choice]`. This changes proof-build dependency shape only; no source-language semantics or certificate gate changed. Full Task 2A remains open.

**Current grammar-canonicality batch after `bc8cfbb79f1d18a26becd5b010a2015330859e70`:** A private constructor witness showed that empty argument text derived both no arguments and one empty argument; the grammar now requires nonempty text for a one-argument spine and kernel-proves `ArgumentSyntax.empty_only`. Focused RED/GREEN also removed empty call callee, leading comma argument, and empty property/optional/index receiver trees from the grammar and validator; declarative negative lemmas prevent those trees, rather than relying only on biased validator output. For call chains, source checking no longer splits at the first `(`. `finalCallOpen` counts nested parentheses backwards from the final `)` in independently validated tokens; `finalCallOpen.unique_on_source` derives a unique boundary from `Lexes.unique`. Actual pinned Python `match.group().isspace()` span `⟨2837,2860⟩` and `float(value).is_integer()` span `⟨2276,2301⟩` now validate; the first has an independent `ExprDerives` fact, separate raw decoder AST equality and a wrong-call-target rejection, while the second has separate raw AST equality. `#print axioms` on boundary uniqueness/empty-form lemmas showed `[propext]`; the actual chained-call derivation showed `[propext, Quot.sound]`. The focused grammar/product targets, serial SourceValidator/PythonBooleanSyntax/SourceModule, normal Generated audit, normal World audit and `lake build` all exited 0. Generated audit: 7,478 theorems / 9,953 declarations; World audit: 9,034 / 12,122; each observed only `[propext, Quot.sound, Classical.choice]`. Full lexical and both Python line targets returned immediately from unchanged cached proof modules after this expression-only batch. Exact inventory (17 product / 27 test / 50 closure / 23 targets) and nine mutations passed. Complete operator precedence, full program mapping and program-wide uniqueness are **still open**.

**Current function-item work after `9a90c8075865fd100a5e576eadaa8d033998f372`:** `SourceItem.functionDecl` carries a full function span and an inner body span. The independent checker verifies the TS/Python Boolean helper header, exact parameters, body containment and each low-level `if`/throw or raise/return/sequence statement through `StmtSyntax`; it never assigns ideal Boolean-helper behavior. Generic soundness produces `FunctionDerives` and `StmtDerives`. RED actual `validateFunctionItem` probes returned false before the function-statement rules; executable probes then returned true, and dedicated **kernel** tests passed for TS `booleanWorld` and Python `_boolean` items. Wrong function name/body and shifted Python body span are rejected. For both balance and order TS, a candidate generated by parsing the bounded body is checked as a tenth ordered source item; `PrefixDerives` now covers every nontrivia token through the complete function (balance stop 2121, order stop 2177), and dropping the balance function item leaves tokens unowned. Separate kernel facts show that checked function equals the `booleanWorld` field in each **actual full parsed program**. Python has an individual `_boolean` item derivation, while its preceding module functions remain outside the current whole-prefix certificate. `#print axioms` on selected generic/item/prefix derivations showed `[propext, Quot.sound]`. Serial SourceValidator, PythonBooleanSyntax, SourceModule, normal Generated audit, normal World audit and `lake build` all exited 0. Generated audit: 7,545 theorems / 10,038 declarations; World audit: 9,075 / 12,178; each observed only `[propext, Quot.sound, Classical.choice]`. Exact inventory (17 product / 27 test / 50 closure / 23 targets) and nine mutation checks passed. These are **source-syntax and AST-field facts**, not helper execution or full-program correspondence; Task 2A remains open.

**Current span-certificate work after `a8e2982000f8d1558a74b7a5c9ab5e759d518334`:** `SourceStatementCertificate.lean` introduces an untrusted child-span tree for low-level empty/final/sequence/return/throw/if statements. Its checker requires child containment, order, exact source punctuation and recursive AST/source validation. The generic Lean theorem derives `StmtDerives` from checker success by induction on the certificate; it does not call the raw program decoder or assign helper behavior. Actual parsed TS `booleanWorld` and Python `_boolean` statement trees accepted executable probes and then passed **kernel** certificate-success and `StmtDerives` theorems. Shifting the inner throw/raise expression span is kernel rejected in both languages. `#print axioms` on generic soundness and both actual body derivations showed `[propext, Quot.sound]`. The exact inventory passed with 18 product modules, 27 test/audit modules, 51 certified closure modules and 23 targets, and nine mutations passed. Serial dedicated TS/Python certificate targets, normal Generated audit, normal World audit and `lake build` exited 0. Generated audit: 7,594 theorems / 10,123 declarations; World audit: 9,114 / 12,251; each observed only `[propext, Quot.sound, Classical.choice]`. This certificate is a reusable source-span carrier for additional statement forms; the two Boolean bodies do **not** complete all generated helpers. Full Task 2A remains open.

**Current cursor/statement batch after `7dc8a1fb7bdbcabffe4ade34780ce7b321ddb6b7`:** The same independent statement grammar/certificate now checks source-owned TS/Python expression statements and local bindings, plus TS postincrement and Python `+=` on captured parse cursors. Actual pinned spans include TS `seen.add(raw);` `⟨6448,6462⟩`, Python `seen.add(identity)` `⟨7353,7371⟩`, TS `let index = 0;` `⟨2695,2709⟩`, Python `position = 0` `⟨2907,2919⟩`, TS `index++;` `⟨3658,3666⟩` and Python `position += 1` `⟨3132,3145⟩`. Every positive statement has a separate kernel raw statement-parser AST match and a checked `StmtDerives` fact; changed call target/argument, binder name, mutability or update operator is rejected. Focused RED was confirmed on a small `index++`/missing-augment rule probe; a whole-file RED attempt overflowed the default Lean stack before reaching the intended false fact, so the small probe is the semantic RED evidence. The dedicated statement certificate target passes, and selected derivations depend only on `[propext, Quot.sound]`. Serial SourceValidator, PythonBooleanSyntax, SourceModule, normal Generated audit, normal World audit and `lake build` all exited 0. Generated audit: 7,660 theorems / 10,206 declarations; World audit: 9,134 / 12,286; each observed only `[propext, Quot.sound, Classical.choice]`. Exact inventory passes with 18 product modules, 28 test/audit modules, 52 closure modules and 24 targets; nine disposable-tree checks pass. This remains fragment syntax certification, not whole helper execution or program correspondence.

**Current comparison/depth-branch batch after `834e4edc4d82b2a89fd31a5c016f76317806b54d`:** Focused RED `/private/tmp/t398-comparison-red.lean` showed both TS and Python `depth > 128` missing from the source grammar. Independent `ExprSyntax` now owns actual TS/Python `depth > 128` and TS `seen.size >= 128`, with separate kernel raw expression-decoder matches. `exprBindingPower` checks operator nesting; the declarative grammar theorem rejects a comparison as an unparenthesized subtraction operand, and a wrong operator AST fails the validator. Actual TS `if (depth > 128) throw new Error(...)` has a complete `StmtDerives` certificate and raw block-parser match. Actual Python nested `if depth > 128:` uses 12 source spaces; the new certificate form checks exact indentation, its final-sequence body wrapper, and the raw suite parser candidate under the emitted nesting level. A changed indentation is rejected. Selected derivations print only `[propext, Quot.sound]`. After an interrupted audit attempted to rebuild two heavy witnesses concurrently, the owned process was stopped, its children checked gone, and the affected dependencies were rebuilt one at a time. Serial SourceGrammar, SourceValidator, StatementCertificate, focused tests, closed SourceValidator, PythonBooleanSyntax, SourceModule, normal Generated audit, normal World audit and `lake build` exited 0. Generated audit: 7,753 theorems / 10,320 declarations; World audit: 9,193 / 12,359; each observed only `[propext, Quot.sound, Classical.choice]`. Exact inventory 18 product / 28 test / 52 closure / 24 targets and nine disposable-tree checks pass. These are bounded source fragments; complete sanitizer and full program mapping are still open.

**Current statement-boundary batch (verification in progress):** `/private/tmp/t398-stmt-sequence-ambiguity.lean` produced two different `StmtSyntax` ASTs for the same TS `a;\n  b;\n  c;` source, each with only `propext`. An independent `SingleStatement` grammar premise now requires the first child of a sibling sequence or final wrapper to be one statement; a kernel theorem rejects the former left-nested tree while retaining the right-nested tree. TS unbraced `if` likewise cannot swallow a sequence of following siblings; a separate braced-body grammar rule remains necessary for actual multi-statement blocks. `/private/tmp/t398-python-dedent-ambiguity.lean` then exhibited an invalid Python `if` tree that swallowed a line dedented from 8 to 4 spaces. `suiteLinesWithin` is now a source-text premise of Python suite derivations and checked certificates; the exact dedented source fails a kernel Boolean fact, while the actual pinned 12-space depth refusal still derives. These constraints remove concrete ambiguities but do **not** yet prove all statement or program uniqueness.

The parent interruption of the previous owner process was intentional coordination, not a technical failure. The parent independently compiled four ambiguity witnesses in `/private/tmp/t398-parent-expr-ambiguity.lean` and found that three Python line chunks pass at `--tstack=65536` while the old monolithic 16-chunk proof fails even at larger stack/recursion settings. I reproduced the ambiguity witness (exit 0), preserved checkpoint `3be57ae36f9df19693f3d11c9fe402b12fdb1c19` and existing WIP, and used bounded compositional line derivations instead. `--tstack` changes Lean's physical thread stack, not kernel trust or proof reduction. The larger expression/statement/program syntax derivations remain to be designed and checked; no source-string-to-program theorem is inferred from line coverage.

**Verification of this slice:** `lake build Harmonia.Applications.Kadmos.Generated.SourceValidator`, `lake build kadmosGeneratedK02SourceGrammarTest`, `lake build kadmosGeneratedK02SourceValidatorTest`, `lake build kadmosGeneratedK02PythonBooleanSyntaxTest`, `lake build kadmosGeneratedK02PythonLinesTest`, `lake build kadmosGeneratedK02SourceLexTest`, `lake build kadmosGeneratedK02SourceModuleTest`, and `lake build` each exited 0 after the signature repair. The larger constituent syntax/lexical targets each took several minutes of CPU for existing closed actual-source facts; an accidental first lost shell session left one owned build running, which I stopped by exact PID before repeating verification. `#print axioms` on joint expression/argument soundness showed `[propext, Quot.sound]`; declarative negative grammar tests showed `[propext]`; both full Python `LinesAt` facts showed `[propext, Quot.sound]`. A cached `lake --old build kadmosGeneratedK02Audit` first passed; after rebuilding affected source, lexical, Boolean and module test roots individually, a **normal** `lake build kadmosGeneratedK02Audit` also exited 0: 7,348 theorems / 9,755 declarations, observed `[propext, Quot.sound, Classical.choice]`. `lake build kadmosWorldAudit` exited 0: 9,008 theorems / 12,037 declarations with the same observed axioms. No custom axiom, sorry, admit or native decision was introduced.

## Task 2A execution ledger (2026-10-11)

- **task-start / BASE:** Clean source `e3996929ff34c89574a9753f4f02b511405f8008`, branch `feat/t396-generated-correspondence`, isolated worktree `/Users/yong/.codex/worktrees/5b89/harmonia`; coordinator clean `68f11d5e2f93bffc70bf335b65c50f0ef3ad6534` with R3 ACCEPT archived. Pinned Kadmos main `1ac9422a12ab743a9bbb8b8ad508d37c582637df` stays read-only. Task 2A acceptance requires independent source-derived constituent AST/span grammar for all four complete checkers, validator soundness and uniqueness, checked parser integration, actual-source nonvacuity, hostile mutations and affected audits. Existing four raw parse-success facts and two balance certificates are partial baseline only.
- **Ruling:** Retain the existing decoder as an untrusted candidate producer; make a separate AST-guided validation pass own original source spans and check source syntax against every returned `TargetProgram` field. Its declarative grammar and soundness theorem must be independent of decoder success and exact fixture equality. This avoids reusing the decoder as its own checker; cost is a full restricted source grammar across both languages. No runtime-domain/backend change.
- **RED/GREEN syntax slices:** `lake build kadmosGeneratedK02SourceGrammarTest kadmosGeneratedK02SourceValidatorTest` first failed because both new modules were absent. New `SourceGrammar.lean` states token/line span and expression/format derivation rules independent of raw parser success; `SourceValidator.lean` checks source spans against candidate AST nodes and proves `validateExprSpan_sound`, `validateLexes_sound`, `validateLinesAt_sound`, and format-fragment soundness. `kadmosGeneratedK02SourceValidatorTest` is GREEN for the actual `balance - event.amount` mapping in TS/Python, rejects `.add` in its place, checks TS `${invalid}` and Python `{invalid}` holes, rejects a changed hole, and checks two-hole TS/Python message order. It kernel-checks complete balance TS token character coverage. The separate `SourceGrammarTest` intentionally remains RED at the missing `SourceParses.unique`/`parseGenerated_sound` gate. These slices do not validate complete checker ASTs.
- **Ruling: closed Python line checks:** An executable probe confirms `validateLinesAt pySource 0 (locateSourceLines pySource)` for both 400-line current Python checkers. A monolithic full-balance `by decide +kernel` line proof stack-overflowed (private `/private/tmp/t398-line-kernel-py.lean`), so closed line evidence must be split into bounded chunks and composed under the inductive `LinesAt` relation. A small line-offset/mutation kernel test is GREEN; no full Python line certificate is claimed yet. The stack limit is a proof decomposition issue, not a reason to weaken span ownership.
- **Ruling: first format grammar:** The actual pinned TS `${...}` and Python f-string interpolations use identifier holes (`name`, `invalid`, `snapshotAction`, etc.). The checked `FormatSyntax` first admits only identifier holes, including multiple holes in source order; arbitrary expression holes are rejected until a separate structural expression rule is proved. This still covers the reached current artifacts and prevents a template span from becoming an opaque string. The cost is an intentionally restricted accepted language, not a changed emitted artifact. TS/Python one- and two-hole kernel tests and a changed-hole rejection test are GREEN.
- **RED/GREEN control slices:** A second RED cycle added Python `nonlocal position` and TS `break;` in a switch with wrong-local/wrong-loop mutations. `validateStmtSpan_sound` now derives these from separate `StmtSyntax` productions; the focused `kadmosGeneratedK02SourceValidatorTest` is GREEN. This proves spelling and control-context ownership for those fragments, not yet the outer lexical-cell binding or whole program.
- **Four-source lexical ownership:** Separate `decide +kernel` facts now show the independent `validateLexes` accepts the full raw token candidate stream for balance/order TS and Python. This covers character intervals and token forms in all four emitted files; it does not map any complete function body to AST. The first added Python facts were RED because I used nonexistent `balancePythonSource`/`orderPythonSource` names; the actual fixture names are `balancePySource`/`orderPySource`. Corrected serial `lake build kadmosGeneratedK02SourceValidatorTest` exited 0.
- **Lexical ambiguity RED/GREEN:** A private probe found that the first `Lexes` relation admitted both a regex and slash/identifier/slash split for `/x/`, and both a comment and punct/punct/identifier split for `//x`. That would falsify `SourceParses.unique`. The declarative relation now includes an independently checked `PriorityAt` trace, with comment precedence, regex-start context, first unescaped regex close and maximal flags. The four full-source lexical facts still pass. Kernel hostile facts reject the former split witnesses and an early-close regex. This is necessary groundwork, not yet a proof that all lexical traces are unique.
- **Lexical uniqueness GREEN:** An independently written `canonicalLexicalHead` reconstructs only the next token from source characters and prior lexical context; it does not parse an expression, statement or program. `CanonicalAt` is a separate inductive per-token relation and `Lexes.unique` proves that two complete accepted token traces of the same source are equal. `validateCanonicalAt_sound` constructs that derivation from a candidate trace. All four actual full-source kernel lexical facts still pass after adding this stronger condition; `lake build kadmosGeneratedK02SourceValidatorTest` exited 0. Private `#print axioms` reports `Lexes.unique [propext]`, `validateLexes_sound [propext, Quot.sound]` and `validateExprSpan_sound [propext, Quot.sound]`. This does **not** establish `SourceParses.unique`: expression/statement/program productions remain incomplete.
- **Literal rules:** `ExprSyntax` and its separately implemented validator now cover TS/Python booleans, null/None, TS undefined, nonnegative integer tokens and decimal tokens in addition to the prior string/property/subtraction/template fragment. `validateExprText_sound` constructs the corresponding grammar derivation. The complete expression, statement and program grammars remain open; `SourceGrammarTest` stays RED by design at the missing `SourceParses.unique` and checked `parseGenerated_sound` declarations.
- **Actual nested module calls:** The expression grammar/validator now derives empty and one-argument call spines. Closed kernel facts accept the full actual TS balance `JSON.parse(<normal JSON string>)` source span `⟨797,1266⟩` and Python `_freeze(json.loads(<normal JSON string>))` span `⟨489,967⟩`, with each property/local call target and the owned string argument checked recursively. Mutating TS `.parse` to `.stringify` or Python `_freeze` to `idealFreeze` in the candidate AST is rejected. `lake build kadmosGeneratedK02SourceValidatorTest` exited 0 after these additions. This is syntax mapping only: `_freeze` remains a user-defined body that full Task 2A must separately derive and later simulation must execute.
- **Module binding slices and test cycle:** `StmtSyntax` now includes declarative TS named value import and Python `import`/`from … import …` forms. Closed actual-source facts own TS `node:util`/`types as nodeTypes`, Python `__future__.annotations` and `copy` import spans; alias and module-name AST mutations fail. The four expensive whole-file lexical facts were moved into `kadmosGeneratedK02SourceLexTest`; its first serial build exited 0, and the remaining focused `kadmosGeneratedK02SourceValidatorTest` exited 0 in roughly 12 seconds. This split changes proof build cost only; it does not supply missing full-program derivations.
- **Hostile source edits:** The focused kernel target rejects source edits to the TS JSON call target (`JSON.parse`→`JSON.xarse` at the actual world-expression span, keeping the candidate AST), TS interpolation hole, TS switch `break`, and Python `nonlocal` spelling. These complement AST-only mutations and demonstrate actual source-slice checking. They remain fragment probes until `validateSource` checks every returned field and every source span.
- **Erased TS import ownership:** `ErasedSyntax`/`ErasedDerives` now distinguish type-only imports from runtime statements. `validateErasedTypeImport_sound` checks each imported identifier and the quoted module literal against a source span. A closed fact accepts actual `import type { … } from "./ports.js";` at `⟨122,244⟩`; changed module and reordered names fail. In-statement type annotations still need separate source rules.
- **Pinned erased type alias:** The 526-character `type WorldData = …;` declaration is now an explicit runtime-erased grammar terminal, separate from any executable statement. Kernel facts own exactly `⟨245,771⟩` in both TS artifacts and reject a local `readonly context` source edit. This narrow fixed terminal is valid because the alias is erased and contributes no `TargetProgram` AST node; it is **not** a replacement rule for reached helper bodies or typed runtime declarations. A first negative test tried to reduce `String.replace` over the entire 18 KB source and `decide +kernel` did not close; shrinking the mutation to the owned 526-character alias made the hostile fact kernel-check. Both positive facts and the bounded hostile fact built in `kadmosGeneratedK02SourceValidatorTest`.
- **Six TS module bindings:** `StmtSyntax.tsModuleConst` fixes each of the six K-02 erased module type annotations by its binding name and derives the runtime RHS through `ExprSyntax`. Its validator separately checks the full declaration span, the candidate RHS AST and exact source spelling. Kernel facts accept the actual balance TS `world`, `contextDefaults`, `contextDefinitions`, `stateDefinitions`, `invariantDefinitions` and `transitionDefinitions` declarations at their original spans; `lake build kadmosGeneratedK02SourceValidatorTest` exited 0. These facts do not yet assert that their ordered `TargetStmt.sequence` equals the raw `moduleInit`, nor that the TS functions/class fields or Python module are derived.
- **Partial ordered source ownership:** `SourceItem` distinguishes a runtime statement, a TS type-only import and the runtime-erased WorldData alias. `ItemsDerive`, `OrderedItems` and `NontriviaOwned` are independent propositions; the candidate checks have kernel soundness theorems. A new closed balance TS prefix fact validates the nine ordered items through character offset 1962 and accounts for every nontrivia token there. Dropping the type-alias item makes coverage false; swapping the first two items fails ordering. `lake build kadmosGeneratedK02SourceModuleTest` exited 0. This is a **prefix**, not a complete `ProgramDerives`: tokens after 1962, functions, class fields and all Python declarations remain unowned at this gate.
- **Propositional prefix witness:** `PrefixDerives .ts balanceTsSource 1962` is now kernel-proved from the closed full-source `Lexes` fact, checked nine-item syntax, order, and nontrivia ownership. This is stronger than a Boolean probe: it constructs the independent derivations for the actual prefix. The theorem intentionally has no constructor for a whole `TargetProgram`, so it cannot be used as a vacuous `SourceParses` certificate. `lake build kadmosGeneratedK02SourceModuleTest` exited 0 after its proof.
- **Proof granularity RED/GREEN:** Extending the recursive expression validator at once with TS `typeof`, strict inequality and `new` caused its monolithic `validateExprText_sound` proof to exhaust one million Lean heartbeats even at the `.empty` branch. A private declaration-only probe showed the same timeout; a targeted definitional `change` closed that branch, confirming an elaboration/unfolding cost. I retained the independent grammar constructors for those forms, removed the unfinished generic validator cases from the checked path, and restored the previously compiling soundness theorem. The next slice must use separate form lemmas or a proof-producing syntax certificate; no unsupported form is accepted by the current validator. This is a proof decomposition issue, not a claim that those source forms cannot be formalized.
- **First reached TS helper body, constituent syntax only:** Form-specific `validateTSTypeofValue_sound`, `validateTSStrictNeTypeofValue_sound` and `validateTSNewValue_sound` avoid the monolithic reduction. Closed facts derive the actual `booleanWorld` condition (`typeof value !== "boolean"`), `new Error(...)`, `throw`, `if`, `return`, and their ordered body source slices through `StmtSyntax` constructors. A separate `decide +kernel` fact confirms the raw full-file parser's `functions` entry named `booleanWorld` contains exactly that derived low-level body AST. Mutating the condition operator is rejected. `lake build kadmosGeneratedK02SourceValidatorTest` exited 0. This is **one helper's syntax mapping**; its header/parameter binding, execution meaning, other reached helpers, and complete source-program certification remain open.
- **Python module assignment slice:** `StmtSyntax.pythonModuleAssign` checks an identifier left-hand binding and recursively derives its right-hand expression. A closed fact owns the actual balance `_WORLD = _freeze(json.loads(<normal JSON string>))` span `⟨480,967⟩`; changing the candidate assignment target to `_MODEL` fails. The focused test target exited 0. This does not derive the preceding `_freeze` function, the `_INITIAL` generator, `_DEFAULTS` comprehension, later globals or the checker class.
- **Complete `booleanWorld` source function:** `FunctionSyntax.tsUnknownToBool` owns the emitted header, parameter name, erased `unknown`/`boolean` annotations and a body derived statement by statement. `kadmos_generated_boolean_world_function_derives` proves the original span `⟨1964,2121⟩` derives the explicit `TargetFunction`; a separate `decide +kernel` fact proves the full raw TS parser returns that exact named function entry. `lake build kadmosGeneratedK02SourceValidatorTest` exited 0. This is the first complete function syntax certificate, **not** a generic whole-program validator or an execution theorem.
- **Both TS module prefixes:** The same nine-item source certificate now derives the order TS prefix through offset 2018, with its actual longer world JSON and all six module bindings. `kadmos_generated_order_ts_prefix_derives : PrefixDerives .ts orderTsSource 2018` is a kernel theorem; `lake build kadmosGeneratedK02SourceModuleTest` exited 0. Both TS certificates own whole-file lexical streams but only their stated prefixes of nontrivia tokens.
- **Complete Python `_boolean` source function:** Independent Python `is not`, `raise`, `return`, indented `if`, sequence, and `Any`→`bool` header rules derive actual balance source span `⟨1593,1748⟩` down to its `type(value)` and `ValueError(...)` calls. Closed facts show raw `parseGenerated .python balancePySource` contains exactly the derived `_boolean` definition in `moduleInit`. `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` exited 0; selected axiom checks for the function theorem and `validatePythonIsNotValues_sound` are `[propext, Quot.sound]`, raw function equality `[propext]`. The Python helper's execution and other bodies remain unproved.
- **Expanded Generated root audit:** After adding `KadmosGeneratedK02PythonBooleanSyntax` to its exact root, live inventory exited 0 with 15 product modules, 23 tests, 44-module certified closure and 22 test targets. The serial `lake build kadmosGeneratedK02Audit` exited 0 after an unusually long full root scan: **7,139 theorems / 9,400 declarations**, observed `[propext, Quot.sound, Classical.choice]` within the same whitelist. The log is private `/private/tmp/t398-task2a-generated-audit2.log`; no policy rule was weakened. This supersedes the earlier 7,117/9,354 audit count for the previous root without the new Python test.
- **Final affected old World root:** After the latest source-grammar additions, serial `lake build kadmosWorldAudit` exited 0 with **8,958 theorems / 11,908 declarations**, observed `[propext, Quot.sound, Classical.choice]` within the same whitelist. Its inventory closure remains 27 application modules; the prior 8,957/11,892 number was from before the Python syntax additions. The Generated inventory self-test again passed 7/7.
- **Selected axiom audit:** Private `lake env lean /private/tmp/t398-task2a-progress-axioms.lean` exited 0. `#print axioms` reports `Lexes.unique [propext]`; `validateSourceItems_sound`, both TS prefix theorems and the complete `booleanWorld` function syntax theorem `[propext, Quot.sound]`; the raw-parser named-function equality `[propext]`. No new axiom, `sorry`, `admit` or `native_decide` is used in these facts. The broader current-source root audit results follow below.
- **Affected inventories and audits:** The exact Generated manifest now includes 15 product modules and 22 tests; the World application manifest grows to 27 product/application modules because its scan covers all `Harmonia/Applications`. The Generated axiom root imports the four new test modules; the World root imports the new source validator through genuine source closure. No old semantics or policy whitelist changed. `python3 -B scripts/check_kadmos_generated_k02_audit.py --self-test` passed 7/7 after replacing historical fixed-count smoke assertions with positive counts while preserving the script's exact manifest/closure comparison. Live Generated inventory exited 0 (15 product, 22 tests, 43 closure, 21 targets); live World inventory exited 0 (27 application, 31 closure). `lake build kadmosGeneratedK02Audit` exited 0: 7,117 theorems / 9,354 declarations, observed `[propext, Quot.sound, Classical.choice]`; `lake build kadmosWorldAudit` exited 0: 8,957 / 11,892 with the same whitelist. Both Generated and World rejection audit targets exited 0. `lake build` exited 0. K-02 artifact self-test passed 8/8, live artifact check passed 10 files with fixtures Lean SHA-256 `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`.
- **Open acceptance gate, still RED:** The private `/private/tmp/t398-task2a-open-gate.lean` checks for `SourceParses.unique`, `validateSource_sound` and `parseGenerated_sound` exit 1 with three unknown-identifier errors. The tracked `SourceGrammarTest` now checks only established declarations and builds; it does not pretend the missing full-source gate is green. `ProgramDerives`, a generic full-source validator, every returned TS/Python function/method/class-field derivation, four complete checked-source facts and checked `parseGenerated` integration are absent. The source syntax facts above are independently valuable slices, not Task 2A completion or generated-step correspondence.

## Current proof-strategy R2 corrections and evidence (2026-10-11)

- **Actual catch/finally bug, not merely a planned rule:** Before the fix, `execStmt` returned from the caught handler before cleanup. `lake build kadmosGeneratedK02SemanticsTest` with six new TS/Python kernel facts was RED (six intended `decide` failures). Direct current-code `#eval` showed catch-return/cleanup-return produced `returned 1` rather than `returned 2`, and catch-rethrow/cleanup-busy-clear produced `raised "boom", busy=true` in **both** languages. The earlier R1 design's claim that this catch path already saved the outcome through cleanup was false. The only executor edit changes that catch-arm `return` to `pure`, binding the handler outcome and reaching the existing cleanup join; `ResumeFrame.finally` continues to save `StmtOutcome.control` rather than the cleared frame field.
- **GREEN retained facts:** `lake build kadmosGeneratedK02SemanticsTest` exits 0 after the one-line fix. `kadmos_generated_caught_return_finally_{ts,python}` prove exiting cleanup return2 overrides caught return1; `kadmos_generated_caught_rethrow_finally_{ts,python}` prove rethrow propagates while cleanup sets busy=false; `kadmos_generated_caught_return_normal_finally_{ts,python}` prove normal cleanup preserves caught return1 and clears busy. New `kadmos_generated_normal_return_finally_python` complements the existing TS normal-return fact. `#print axioms` for the six catch theorems reports `[propext, Quot.sound]`, no custom/sorry axiom. Parent's `/private/tmp/t398-catch-finally-parent.lean` remains an intentionally failing scratch RED fixture with `rfl` assertions; it was **not** staged or treated as a passing gate.
- **Exact rank inventory:** The only 15 functions in `TargetSemantics.lean` that match on entrypoint `fuel` are `evalExpr`, `execStmt`, `bindCallParams`, `evalDefaults`, `evalArgValues`, `evalObjectFields`, `evalArrayElems`, `evalSwitchCases`, `execForItems`, `evalDictCompItems`, `evalListCompItems`, `evalArrayMethodItems`, `evalFormattedParts`, `resumeGenerator`, `consumeGenerator`. `evalCompFilter` does **not** match fuel; nor do `callClosure`, `resumeNext`, `evalArrayMethod`, `evalOneDefault`, `consumeIterable`. Their calls pass the same k into the listed functions without an extra edge. Sequence, parameter/default, format, object/array, switch and iteration cons tails remain nested rank edges. Module init, TS class fields and constructor call each receive the same k from the wrapper and need separate `<k` bounds; step call has its own. Host `cloneValue 2048` and JSON conversion `source.length*4+1` use **separate** fuel recursion, with separate supported-domain adequacy bounds. The design now states those exact obligations.
- **Selected-step regression:** `lake env lean /private/tmp/t398-k02-step-boundaries.lean` exits0 and physically executes six boundary cases in each language: n0/negative guard reject, n>b bounds reject, 100/30 and S/S accept, preserving expected logical balance/history/undo/busy. `lake env lean /private/tmp/t398-k02-step-extreme.lean` exits0 for `b=S,n=-S` guard refusal in both languages. These are finite executable regressions; the full universal one-call theorem remains unproved.
- **Serial verification after the fix:** `lake build` exit0. A single serial Lake process building `foundationsTest foundationsAudit kadmosGeneratedK02SemanticsTest kadmosGeneratedK02BalanceTSStepTest kadmosGeneratedK02Audit kadmosGeneratedK02AuditRejection kadmosWorldAudit` exit0, including the old closed TS 100/30 theorem and rejection root. Foundation audit: 52 theorems, `[propext, Quot.sound]`; Generated audit: **6,745 theorems / 8,452 declarations**, `[propext, Quot.sound, Classical.choice]`; old World audit: 8,736/11,171, same whitelist. `python3 -B scripts/check_kadmos_generated_k02_artifacts.py --self-test` 8/8, live check 10 files; Generated inventory self-test 7/7, live check 13 product/18 tests/37 closure/17 targets; World inventory self-test 21/21 and live check pass. Private `lake env lean /private/tmp/t398-r2-axioms.lean` reports `[propext, Quot.sound]` for all seven new regression theorems. The pre-fix RED log is `/private/tmp/t398-r2-catch-red.txt`; post-fix GREEN log is `/private/tmp/t398-r2-catch-green2.txt`. Logs and scratch are not staged.

## Historical proof-strategy R1 corrections (2026-10-11)

- **Meter and proof direction:** `TargetConfig`/`Runs` are unfueled. The existing executable fuel counts the deepest mutually recursive call, because siblings reuse the predecessor; it does not count global small steps. The corrected plan requires evaluator→relation soundness **and** reached-path relation→evaluator adequacy, plus a branch-specific `1+max` mutual-depth rank `<100` or one consistently raised proved entrypoint constant. Trace length cannot justify `targetConstruct`/`targetStep = .ok`.
- **Negative amount branch:** The guard-return proof for `n≤0` never evaluates the effect or invokes a `safeIntermediate (b-n)` lemma. At `b=S,n=-S`, subtraction would be `2S`, outside the safe range, yet the actual source rejects at guard. Conditional subtraction bounds are used only when `n>0`, separately for accept and bounds refusal.
- **Source ownership and control:** TS backtick template literals and ordered `${}` holes are explicit grammar/validator cases alongside Python f-strings. `ResumeFrame.finally` saves `StmtOutcome.control`, not the `frame.control` field cleared before cleanup. A normal cleanup propagates that saved return/exception; an exiting cleanup overrides it.
- **Logical frame:** `after = before` refers solely to checked dereferenced `BalanceView` contents after derived `HeapWF` for both heaps. Rollback may clone context/history, so raw object refs, frozen flags, shallow `logicalChecker.history` values and undo `ObjRef`s are not compared as equal.
- **Small probe:** Updated private `/private/tmp/t398-option1-tiny.lean` compiled with `lake env lean` exit 0. It retains the independent expression/captured-cell facts, elaborates the unfueled `TargetConfig`/`Runs` schema, and kernel-checks that current `execStmt` propagates a returned value through normal `finally` cleanup. Closed checks also show `.empty` succeeds at fuel1 and fails at fuel0, fixing the rank convention to leaf0 and strict `rank<fuel`. This does not prove full source grammar, adequacy, constructor or dynamic correspondence.
- **Revision verification:** `git diff --check`, cached `lake build`, existing `kadmosGeneratedK02BalanceTSStepTest`, `kadmosGeneratedK02Audit` (6,731 theorems / 8,435 declarations; only `[propext, Quot.sound, Classical.choice]`), K-02 artifact live check (10 files), Generated inventory live check (13 product / 18 test / 37 closure / 17 targets / World inventory 25), and `lake env lean /private/tmp/t398-option1-tiny.lean` all exited 0. These validate unchanged product code and the tiny schema probe, not the still-open proof obligations.

## Current option 1 evidence and next gates (2026-10-11)

- Source is immutable Kadmos K-02 `1ac9422a12ab743a9bbb8b8ad508d37c582637df`. Tracked full TS/Python balance/order files, pinned SHA-256 and physical vectors below remain the exact artifact evidence; no generator or fixture was edited in this planning invocation. T-395's older `fda8c6e` Bridge pin remains separate.
- Existing kernel results are four complete-source parse-success facts, two balance `checkGenerated` nonvacuity facts, symbolic `interpret balanceCandidate` branch theorems and scalar target arithmetic lemmas, plus one actual-source TS b=100/n=30 closed target execution. Generated/World axiom audits and artifact/inventory tests have passed as recorded below. These do not establish source-to-AST soundness or universal dynamic target execution.
- Private `/private/tmp/t398-option1-tiny.lean` ran `lake env lean` exit 0. It proves `tinyValidate_sound` for an independent five-token subtraction/property fragment, closed TS/Python `parseTargetExpr "balance - event.amount"` agreement with that AST, and a shared mutable `CellRef` update/read fact. Its `TargetFocus`/continuation/configuration and one integer `SmallStep`/inductive `Runs`/Hoare schema elaborate. A first schema attempt using `Relation.ReflTransGen` failed because Lean 4.16/Init lacks that name; the design now defines `Runs` inductively, and the corrected probe passes. The probe is **not staged** and is not a full-source validator, heap simulation or correspondence theorem.
- Current plan-only verification: `lake build` exit 0; `lake build kadmosGeneratedK02BalanceTSStepTest` exit 0 (only the existing Bridge `simpa` lint warning); `lake build kadmosGeneratedK02Audit` exit 0 with 6,731 theorems / 8,435 declarations and observed axioms `[propext, Quot.sound, Classical.choice]`; `python3 -B scripts/check_kadmos_generated_k02_artifacts.py --root .` exit 0 (10 files, fixture literal SHA-256 `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`); `python3 -B scripts/check_kadmos_generated_k02_audit.py --root .` exit 0 (13 product modules, 18 tests, closure 37, 17 test targets, World inventory 25). These are unchanged-code baseline checks, not new proof gates.
- Next gates, in order: validated source spans/AST and parser soundness/uniqueness; unfueled generic small-step/Hoare relation plus **both** evaluator soundness and reached-path adequacy; constructor-derived canonical prestate for every b; parsed-helper/branch simulations for every safe n with guard-first early return; universal source-bound theorem for both languages; fresh exact root audits and hosted Linux. `targetConstruct`/`targetStep` currently use recursive-depth fuel 100, so a strict uniform mutual-depth rank or a consistently raised proved constant is required. `logicalChecker` currently exposes pointer-level history/undo; the checked `BalanceView` content decoder must establish frame/savepoint conclusions after `HeapWF`. Source PR #5 and coordinator PR #92 remain draft/unmergeable.

The remaining sections are a **chronological evidence log**. Older statements that described no implementation or requested an architecture ruling were true at their dated checkpoints, not current task status.

## Workspaces, pins and source-history relationship

### Post-preflight Task 1 (2026-10-11)

Parent's physical current-source R1 preflight returned **ACCEPT** on `2948ffc23c6d381f3cbb46fb66a8dddf12342687`: session `01a12b88-df86-7c13-b755-4d4da0b3be60`, exit0/1176.7s, structured success/is_error=false. Exact report is archived in isolated coordination PR #92 as `design/harmonia/reviews/2026-10-11_t398_k02_preflight_grok_r1_accept.md` at coordinator `3b5977f0c547ddedb11aea580a2c271a7bed5309`, source-copy SHA-256 `0c4ecd2fdf51aa6707a53765b1294bdde3348c157421eaf14599c7f008b2ef89`. Yong authorized the reviewed evidence disclosure. This is a design admission, not a proof result.

The pinned compiler was recompiled into `/private/tmp/t398-k02-task1/kadmos-js` and `tools/export_kadmos_generated_k02.mjs` regenerated all ten complete emitted files into private scratch, plus four full-source Lean literals. The tracked files in `conformance/kadmos-generated-k02` match the exact hashes in the table below; the full-source Lean literal module hash is `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`. The external checker pins reviewed hashes independently of the editable manifest, checks fixture YAML, ordered admitted-record equality with unchanged old-pin T-395 records, TS/Python embedded-world JSON and TS defaults, and a source inventory. It does **not** prove source semantics. `python3 scripts/check_kadmos_generated_k02_artifacts.py --self-test` passed 8 tests, including a changed effect with a recomputed manifest hash, TS world/default changes, Python world order and old Bridge mismatch. `python3 scripts/check_kadmos_generated_k02_artifacts.py --root . --kadmos /Users/yong/projects/substratum/kadmos` and `lake env lean Harmonia/Applications/Kadmos/Generated/Fixtures.lean` both exited 0. The earlier physical probe was rerun: both languages matched on seven BALANCE boundary vectors and order STEP; finite agreement is not a theorem.

### Task 2 intermediate source-grammar work (2026-10-11)

`Harmonia/Applications/Kadmos/Generated/TargetSyntax.lean` introduces explicit TS/Python lexical tokens with exact spans, preserved whitespace/comments/quoted strings and JS regex literals, plus a proposed low-level expression/statement/function AST whose user functions are separate from host `BuiltinId`. `HarmoniaTests/KadmosGeneratedK02Lexer.lean` kernel-checks that all four complete checkers tokenize; `lake build kadmosGeneratedK02LexerTest` passed. Small source round-trip examples for TS regex/comment and Python raw-string spelling passed by `decide +kernel`; a private executable probe returned true for full-source token text reconstruction, but a closed full-source kernel equality proof was too costly and is not claimed. The `parseGenerated` statement parser, independent `SourceParses`, desugaring theorem, module/helper execution and constructor totality are **not implemented**. Task 2 and T-398 as a whole remain IN_PROGRESS; lexical success is not source execution or correspondence.

`TargetMachine.lean` now has separate tagged exact integer values, reference/object/cell/closure heaps, own descriptors and frozen/prototype metadata, explicit checker fields including Python instance attributes, frames with control tags, erroring cell/object reads and writes, and executable JS/Python truthiness that errors on dangling references. `lake build kadmosGeneratedK02MachineTest` passes scalar/container truthiness, dangling reference, shared-cell update and own-descriptor read/write examples. These are source-language machine primitives; no generated helper is assumed correct. The source parser and generic statement executor remain the open Task 2 gate.

An additional restricted expression parser in `TargetExpressionParser.lean` parses representative reached TS/Python property, optional property, call, index, unary, arithmetic, comparison, ternary, raw/normal string, regex, object/array spread, tuple and Python comprehension/generator forms. `lake build kadmosGeneratedK02ExpressionParserTest` passed kernel-checked source-expression examples including `_freeze`'s dict comprehension and `_INITIAL`'s `next` generator. The following paragraph records its later expansion; neither stage gives a whole-file parser or source-code correspondence theorem.

The Python source subset now also includes exact numeric decimal tokens, Python/TS formatted strings, lambda, slices, nonlocal declarations, shared-cell augmented assignments, tuple destructuring, nested functions, conditional/for/while/try/except/finally, and annotated assignment erasure. A private executable coverage probe extracted each function body from the **actual tracked** `balance/world_checker.py` with CPython `ast` only as an inventory aid, then passed those exact strings to the Lean `parsePythonBlock` function: **26/26 returned `.ok`**. This is not a kernel whole-file certificate: the private extraction and `#eval` probe remain external, headers/imports/class/module binding and independent inductive `SourceParses` are open, and no parsed body has been executed. `lake build kadmosGeneratedK02StatementParserTest` passed small kernel examples; the full `__init__` closed `by decide +kernel` proof was interrupted after roughly 90 seconds of elaboration, so full-source kernel reflection needs a scalable compositional proof rather than a single monolithic `decide`.

`TargetTSStatementParser.lean` now parses representative actual TS constructor, checkBounds, checkInvariants, reset, evaluator and step bodies into low-level statements, including type annotation erasure, declared closures, `if`/`for`/`while`/`try`/`switch`, targeted switch breaks, optional properties, spreads and callback lambdas. A private physical inventory delimited the ten reached function/method bodies in the tracked `balance/world_checker.ts` and `#eval (parseTSBlock body).toOption.isSome` returned **true for 10/10**; the four one-line public getters are included in the source inventory but await whole-class parsing/binding. The inventory delimiters are external evidence only, and the parser still lacks independent `SourceParses`, whole-module/class parsing, checked type/switch desugaring preservation and execution. Its acceptance is not a source-correspondence certificate. Generic host expression parsing currently accepts a broader union than either individual language; language-specific rejection/soundness is an explicit Task 2 obligation before any certificate theorem.

`TargetSemantics.lean` begins an independent executable target semantics over the parsed AST: tagged exact-domain arithmetic and comparison, lexical cell lookup, lazy JS/Python `and`/`or`, nullish choice and conditionals, unary truthiness and explicit target-versus-formal errors. `lake build kadmosGeneratedK02SemanticsTest` passes scalar and lazy examples; out-of-safe-range arithmetic returns a **formal unsupported-domain error**, not a false target exception or an invented IEEE result. It imports neither Bridge nor the reference interpreter. The next paragraph records later machine coverage; this intermediate evaluator proves no complete generated-helper behavior.

Further generic target-semantics work covers fresh ordinary objects/lists/tuples, own data descriptors, enumerable spreads, dynamic indexed reads/writes, Python negative indices and string slices, bound primitive methods, frame cells with const mutability, source-level return/raise and `finally`, function-level return from a `for`, ordered two-binder entry destructuring, and separate switch-vs-loop breaks. Component `decide +kernel` tests pass for captured `index++`, candidate balance assignment, finalizer busy clearing, `Object.entries` and Python `.items()`. `TargetMachine.empty` now gives one shared `Object.prototype` reference and a distinct checker receiver reference; `this.#busy` and `self._busy` dispatch to the same `TargetStore.busy`. These pieces remain a partial interpreter: actual emitted module/constructor/helper calls and host JSON/regex/sanitizer operations do not yet execute. Language-specific parser soundness, closure call/default semantics, source strings to program certificate, and all correspondence obligations stay open.

The next intermediate parser pass consumes the **entire** pinned balance and order TS/Python checker strings, including TS import/type/class/function structure and six ordered class field initializers, and Python imports/class/method/property declarations. Private `#eval` probes of `parseGenerated` returned `.ok` for all four exact source strings. The TS result lists `booleanWorld`, `evaluateWorld`, `deepFreezeWorld`, `sanitizeWorldPayload` and eight `WorldChecker` methods, with six field initializers. The parser consumes to end of source; this is still an executable check, not a kernel certificate or a proof of independent grammar soundness. A private whole-source TS `by decide +kernel` attempt was terminated after 45 seconds without a result, after an earlier closed Python `__init__` attempt exceeded roughly 90 seconds. The planned certificate must use compositional kernel evidence over exact source spans, then prove those spans partition the emitted source and preserve their AST/control meaning. No `native_decide` was used.

The generic semantics now stores lexical closures with shared **cell locations**, runs their parsed bodies through `execStmt`, binds explicit arguments with JS omitted/`undefined` call-time defaults or Python definition-time defaults, and preserves recursive self bindings. Kernel examples prove a user function call and the 5→9 captured-seed default distinction across languages. Target object/array heap and ordered `Object.entries`/Python `.items()` are modeled as primitive contracts; selected target numerics remain exact tagged integers only. Actual K-02 constructor/module initialization, JSON/regex host contracts, frozen/copied history and one-call step remain unexecuted, so Task 2 and T-398 are not complete. The preceding paragraph's earlier open closure/default item is superseded by this limited component implementation; no generated-helper correctness is assumed.

The latest independent semantic slice adds an Init-only ordered JSON parser (rejecting duplicate keys, fractions, negative zero and unsafe integer tokens outside the first profile), heap conversion for `JSON.parse`/`json.loads`, explicit host module imports, class-base evaluation/method closure binding, Python `type`, `dict.get`, `MappingProxyType`, lazy generators with `next`/tuple consumption, dictionary comprehensions and regex **compilation**. Small kernel tests cover malformed JSON, captured generator laziness, ordered defaults and module-host call resolution. Private executable probes then ran **the actual parsed complete module initialization** for balance and order in both TS and Python with `execStmt`: all four returned `ControlResult.normal`. The K-02 user-defined `_freeze` body was parsed and executed generically; no ideal `_freeze` macro exists. The Python mapping-proxy abstraction records the backing reference and a canonical immutable snapshot; a future proof must justify no backing mutation on the supported path. Regex match/test/fullmatch behavior, constructor/reset/evaluator execution, independent grammar soundness and universal correspondence remain open. The earlier “module initialization unexecuted” statement describes its checkpoint before this slice and is superseded here. These four `#eval` runs are not kernel theorems.

The next Task 2 checkpoint implements the restricted token regex contracts, Python anchored match/fullmatch and group shape, actual TS regex literal/test/match, whitespace/quote replace, `Object.getOwnPropertyDescriptors`/`defineProperty`/`hasOwn`, `Array.isArray`, `nodeTypes.isProxy`, `Object.getPrototypeOf`, JS `typeof`, safe-integer and array-join primitives. These operations are independently specified host primitives; the emitted evaluator, reset, bounds and invariant functions remain parsed user bodies. A TS constructor probe first returned the default 100 for every supplied b; inspection of Lean's elaborated `targetConstruct` showed a branch-local `return` exiting before seed allocation and constructor call. Replacing it with `pure` exposed the actual source path and its missing primitives. After those additions, private `lake env lean /private/tmp/t398-k02-construct-boundaries.lean` returned Ready/b for b=0,100,S in **both** TS (`.jsNumber`) and Python (`.pyInt`), busy=false. This is physical `#eval` evidence, not a kernel constructor theorem or a proof that arbitrary b is handled. Nine new component Lake targets passed serially. `tinyConstructor` whole-run `by decide +kernel` did not reduce (despite physical `#eval` success); the test was removed rather than retained as a false certificate. A compositional kernel proof of actual full-source parsing and constructor execution remains a hard Task 2 gate. Step execution and all T-398 acceptance claims remain open.

The current Task 2/3 execution checkpoint adds an explicit canonical `TargetRequest` allocation and `targetStep` which calls the parsed generated method on the live heap. It does not synthesize a verdict. Additional reached primitive contracts and generic callback/comprehension execution include `Object.prototype.toString.call`, `Object.getOwnPropertyDescriptor`/own names/create, JS sets, Python `isinstance`/list concatenation and list comprehensions, JS `.find/.some/.map` callbacks through `callClosure`, anchored effect regex `.exec`, `Object.freeze/isFrozen`, source formatted strings and string slices. The emitted `deepFreezeWorld`, sanitizer, evaluator, bounds, invariant, constructor/reset and step remain parsed low-level user statements. Private `lake env lean /private/tmp/t398-k02-step-boundaries.lean` physically produced the expected **six** balance vectors in each language: guard reject for n=0 and -1, bounds reject for n>b, accept with b-n for n=30 and n=S at b=S; every observed run was Ready/b-or-b-n, busy=false, rejected history empty/undo absent and accepted history length1/undo present. `/private/tmp/t398-k02-step-extreme.lean` additionally observed guard rejection at n=-S. Order default constructor `#eval` returned A/(x=1,y=0), busy=false for both languages using the parsed order code. Nine component Lake targets passed serially after these changes. **These are finite executable probes, not kernel correspondence proofs.** The symbolic b/n theorem, exact whole-source kernel certificate, independent inductive grammar soundness, desugaring proof, hostile source mutation gate and audits remain open. No Task 2/3 completion claim is made.

The parser's Python line splitter initially called Init's irreducible `String.splitOnAux`: `#eval` succeeded while closed `by decide +kernel` got stuck even on the length of 362 lines. The restricted parser now uses a structurally recursive `splitSourceOn`; `by decide +kernel` checks that `pythonLines balancePySource` has length 362, and a private 19,698-byte literal line-list certificate proved exact equality in 10.95s. The monolithic 362-line Python suite proof remained impractical after more than four minutes, so `parsePythonProgram` now parses independently delimited top-level chunks; the 195-line class chunk alone proved in about 31s. Four separate tracked Lake targets subsequently proved **whole-source parser success by `decide +kernel`** for balance TS (41s), balance Python (about 197s), order TS (41s), and order Python (about 245s), all exit0. The combined four-proof target was deliberately interrupted after more than ten minutes and replaced with serial isolated targets. These success facts show each exact source parses to *some* AST; they do not establish independent `SourceParses` soundness, uniqueness or that a future certificate compares the right AST.

`Generated/BalanceModel.lean` now proves the three universal `interpret balanceCandidate` cases directly: guard rejection for `n≤0`, acceptance of `b-n` for `0<n≤b`, and bounds rejection for `n>b`, with b in [0,S] and safe n. `lake build Harmonia.Applications.Kadmos.Generated.BalanceModel` passed; `#print axioms` on all three returned only `[propext, Classical.choice, Quot.sound]`, no custom or sorry axiom. `TargetObservation.lean` independently reads actual target verdict/context object descriptors and checker history/undo/busy into a four-field normalized observation and logical checker snapshot. Private `#eval` gave TS accept 100/30 → Ready/70, one history record and undo present, and Python reject 100/130 → Ready/100, empty history and undo absent, both busy=false. These are model-side symbolic cases plus finite target probes; there is **no** theorem joining them yet.

The first symbolic target arithmetic lemmas now prove JS subtraction and Python tagged `.pyInt→.pyFloat`, float subtraction and `.pyFloat→.pyInt` primitive conversion on the exact safe integer range. These are about independent `TargetSemantics` operations, not a copied model evaluator. A broad one-shot `simp` over Python's nested `hostCall` hit Lean's 5,000,000-heartbeat limit; explicit primitive lemmas plus small `evalExpr` lemmas compiled. `TargetCertificate.lean` adds a fixture-restricted `emittedWorldData`/defaults normal form, dependent `checkGenerated`, and generic kernel lemmas for changed-source rejection and compositional certificate acceptance. Private `#eval` checked all four actual source/Bridge fixture pairs; these executable checks alone are not certificates.

Separate **kernel** balance certificate tests now establish `∃ program, checkGenerated .ts balanceTsSource balanceRaw balanceCandidate = .ok program` and the analogous Python fact, using independent closed parse, embedded-world/default JSON facts and the existing `balance_certificate`. TS target `lake build kadmosGeneratedK02BalanceTSCertificateTest` passed after splitting one-shot reduction to avoid stack overflow. Python target `lake build kadmosGeneratedK02BalancePythonCertificateTest` passed after a long serial build (roughly 14 minutes); `#print axioms` for both nonvacuity theorems returned `[propext, Quot.sound]`. `kadmosGeneratedK02CertificateTest` also kernel-checks changed-source rejection and balance defaults. These facts bind reviewed bytes/normalized emitted data to an executable low-level AST, but **do not prove** independent `SourceParses` syntax soundness or any target-step correspondence. The source-to-program relation and all dynamic b/n target path lemmas remain the central open gates; no code-correctness claim is made.

Audit integration has reached the genuine source closure only. `check_kadmos_world_audit.py` initially rejected all 13 new `Generated` product modules, then passed after their exact addition to `kadmosWorldSourceModules` and imports in the old World audit root. The shared scrubber needed one precise Lean `Char` literal case for `\'"\'`; its 21 mutation tests include a new test showing this case cannot hide a following axiom. `lake build kadmosWorldAudit` passed with 8,736 theorems / 11,169 declarations and only `[propext, Quot.sound, Classical.choice]`. A separate exact-source Generated selector and `KadmosGeneratedK02AxiomAudit` passed with **6,729 theorems / 8,431 declarations**, only `[propext, Quot.sound, Classical.choice]`; its own rejection target passed unused/unsafe/indirect axiom traps. `scripts/check_kadmos_generated_k02_audit.py --self-test` passed seven disposable-tree mutations and its live check passed with 13 product modules, 17 test/audit modules, 36 imported modules and 16 dedicated test targets. None of these audits upgrades the still-missing dynamic target-step theorem. The existing unrelated current-main Quorum/CAP source-inventory incompatibility remains unchanged; hosted CI integration is deferred until the accepted T-398 proof gate exists.

After that checkpoint, the formal evaluator's initial 20,000 fuel prevented closed kernel reduction even for a one-line artificial constructor: `#eval` returned Ready but `by decide +kernel` stuck, and `#reduce` overflowed Lean's stack. Parameterizing the two entry points and using fuel **100** made the artificial constructor provable by `decide +kernel`; separate `#eval` runs of all six balance vectors in both languages still produced the same outcomes. This is a chosen formal execution bound, not a proof yet that every safe b/n path finishes under it. A private closed kernel proof of the **actual parsed TS** constructor at balance100 passed; another closed kernel proof of the actual parsed TS constructor followed by DEBIT30 passed and is tracked as `kadmos_k02_balance_ts_debit30_closed` (`#print axioms`: `[propext, Quot.sound]`). It proves one normalized Ready/70 acceptance from the actual source AST and independent evaluator, not universal b/n or Python. The analogous Python closed step `by decide +kernel` was interrupted after more than ten minutes; its physical `#eval` witness remains only executable evidence. The current dedicated inventory passes with 13 product modules, 18 test/audit modules, 37-module closure and 17 test targets; its seven disposable-tree tests pass. Fresh `kadmosGeneratedK02Audit` passes with 6,731 theorems / 8,435 declarations and `[propext, Quot.sound, Classical.choice]`; the refreshed old World audit passes with 8,736 theorems / 11,171 declarations and the same allowed axioms. The **proof gap remains** as stated in the separate feasibility report.

- Source: `/Users/yong/.codex/worktrees/5b89/harmonia`, clean historical branch name `feat/t396-generated-correspondence`, open draft source [PR #5](https://github.com/substratum-labs/harmonia/pull/5). It began at `bcf44916b5cedf351a78e715470c351ddc84a2ad`; this invocation fetched and cleanly rebased its four documentation commits onto `origin/main@bac00db43cdfff8ba44779fa537a1560958a6154`, which already contains T-399 Quorum and T-400 CAP. The independent T-401 FLP worktrees and primary Harmonia checkout were not edited. The source branch has no product modifications; this invocation adds only the new three T-398 documents.
- Kadmos: read-only `/Users/yong/projects/substratum/kadmos`, clean main `1ac9422a12ab743a9bbb8b8ad508d37c582637df`, manifest `0.1.2`, `kadmos.compiler.k02.v1`. Installed Kadmos `tsc` wrote solely to `/private/tmp/t398-k02/kadmos-js`; its actual `parseWorldSpec`, `compileWorldSpec`, `compileWorldSpecPython` then wrote generated files and runtime probes solely under `/private/tmp/t398-k02/`.
- Stage3b Bridge: unchanged tracked YAML and certificate; exporter/artifact checker still pin `fda8c6e42825b35afe5484a4af9d84d9d206ba9a`. New K-02 admitted JSON for both fixture IDs is value- and ordered-serialization-equal to each old `parsed.json` entry (Python `json.dumps(...,separators=(',',':'))` comparison true). This is an **external compatibility observation**, not a proof of the new parser/admission/serializer or a silent rewrite of T-395's pin.
- Coordination: dirty primary `/Users/yong/projects/substratum/substratum-internal` was inspected and not edited. Isolated worktree `/Users/yong/projects/substratum/substratum-internal/.worktrees/t398-correspondence-coordination` started from fetched `origin/main@c254da370fd5fabc56aef2034af8933970ac82dd`. It registered **T-398 `[IN_PROGRESS]`** in `ledger/TASKS.md` and `ledger/projects/harmonia.md`, with an explicit historical Harmonia T-396 alias and human-resumption handoff. Castor T-396 remains DONE; T-401 remains separately owned. Initial coordination commit `0364c74` was pushed and [draft PR #92](https://github.com/substratum-labs/substratum-internal/pull/92) opened. `bash scripts/check_ledger.sh` passed after correcting the active board's dependency to published K-02; accepted T-395 remains in project history rather than a duplicate active board row.

## Actual K-02 emitted artifacts in private scratch

Commands:

```text
/Users/yong/projects/substratum/kadmos/node_modules/.bin/tsc \
  -p /Users/yong/projects/substratum/kadmos/tsconfig.json \
  --outDir /private/tmp/t398-k02/kadmos-js
node --experimental-strip-types /private/tmp/t398-k02/probe.mjs
```

Both exited 0. The probe imported **fresh compiled K-02 code**, parsed the unchanged Stage3b balance/order YAML, called both actual compiler functions, wrote complete TS/Python source and ports to private tmp, imported emitted TS with Node 26 type stripping, and imported emitted Python with Python 3. Exact current fingerprints are SHA-256 of UTF-8 bytes (size in bytes):

| Fixture | admitted.json | world_checker.ts | ports.d.ts | world_checker.py | ports.py |
| --- | --- | --- | --- | --- | --- |
| balance | `23e1e9a9a047a0497a6fe9ef35673d188fabb60e3833674ce3c5008ab320150d` (392) | `08aa10110b3a36450c2bd2552ac0bb89cc0f4216784f0f30df462abeef6b4e0a` (18,428) | `debb1ab3db463e8691615a929b98ccf627c552820e2bf728203ec4cdf2d7cf80` (1,221) | `50b4da8809d42e72bedc2287bf6fde09291988213e781f4fea173f8163f15437` (18,966) | `56809a0466af05bf94a1a3968cf8d1f4de9a7c919acb0dfa0560b40b021447b3` (1,399) |
| order_phase | `a70d58c266b1b225d01db73f01a8b507b8edc7149b6e6c72ef56377982c921fa` (432) | `161631c389776c7fee161d4a6a8d7037147c435a66f650125649e7d5c400b402` (18,472) | `a60a83d94e37d7ecacefe99e5a2152034de0eeaf33e31340cf9f7993fe5b0cbf` (1,241) | `f3dc44d14365e9349b1dc5d13f9d9935e7d7a9aeb84a49ed211453b241e82da0` (19,022) | `da9cab2af85c26fa460d93b446e71b71d82e3951fb3782d5c2474a160dcbf830` (1,404) |

The balance and order YAML hashes remain `1357baa55f5cc0453a491df264ca75adacad1db580e4bc952dc4adffc900258b` and `53bd1b2a133ff562c01a9b7b10066ed7f78fc45c10a1a821390de6164038db60`. These values bind the **observed** current output, not its semantics. K-02 TS now has a contract header, `world = JSON.parse(<quoted JSON>)`, separate `contextDefaults = JSON.parse(<quoted JSON>)`, class `#constructorSeed` and constructor→reset. Python has `__constructor_seed`, `__state/__context/__history/__undo`, plain `_busy`, read-only public properties and constructor→reset. These are material changes from the old fda8c6e artifacts; prior source-level syntax plans cannot be reused verbatim.

## Physical execution and adversarial witness

From freshly emitted programs, each language constructed a checker with explicit balance seed b and ran exactly one ordinary/exact-dict `DEBIT` request, absent directive, amount n:

| b | n | TS result | Python result |
| ---: | ---: | --- | --- |
| 0 | 0 | `GUARD_FAILED`, Ready/0, null directive | same |
| 0 | 1 | `INVALID_BOUNDS`, Ready/0, null directive | same |
| 100 | -1 | `GUARD_FAILED`, Ready/100, null directive | same |
| 100 | 30 | accepted, Ready/70, null directive | same |
| 100 | 130 | `INVALID_BOUNDS`, Ready/100, null directive | same |
| S | S | accepted, Ready/0, null directive | same |
| S | -S | `GUARD_FAILED`, Ready/S, null directive | same |

For order default construction, both returned A/(x=1,y=0); actual emitted STEP accepted and returned B/(2,2). Rejected balance verdicts carried a one-record trace with step1, Ready, DEBIT and the original payload; their getters showed unchanged logical context. Separately, both languages raised `NO_CHECKER_SAVEPOINT` before any accepted step, accepted DEBIT30, rolled it back to Ready/100, raised the same error on a second rollback, and raised it after a rejected DEBIT130. This confirms current finite behavior of the new private savepoint contract only; rollback is not part of the first theorem. Source mutation in private tmp changed the sole embedded `balance - event.amount` to `balance + event.amount`; both emitted checkers accepted DEBIT30 and returned Ready/130 instead of Ready/70. The later Lean checker must reject or diagnose this source mutation even if a digest is recomputed; **no such checker exists yet**.

## Baseline and old-review evidence

On the rebased branch over Harmonia `origin/main@bac00db`, `lake build` exited 0 (`Build completed successfully`), then **all 20 existing dedicated Lake targets** ran serially and each exited 0: Foundation test/audit/rejection; Distributed test/audit/rejection; Kadmos World test/audit/rejection; Bridge syntax/certificate/fixture test, audit/rejection; Quorum test/audit/rejection; CAP test/audit/rejection. Logs are separate `/private/tmp/t398-k02/<target>.log` files; no new target exists. `lake env lean --version` was not reached in the original `set -e` shell because a later inventory failed; a separate subsequent `lake env lean --version` exited 0 and reported Lean 4.16.0 on arm64 macOS; the pinned `lean-toolchain` file remains `leanprover/lean4:v4.16.0`. Five existing inventory/artifact checks exited 0: Distributed, Kadmos World, old-pin Bridge artifact, Bridge source/root, and CAP. **Existing baseline exception:** `python3 scripts/check_quorum_audit.py` exited 1 with `QUORUM CHECK REJECTED: nonstandard theorem import in Harmonia.Theorems.CAP: ['Harmonia.Core.Execution']`. It is a current-main policy/import interaction, unrelated to this docs-only T-398 branch. `python3 scripts/check_quorum_audit.py --self-test` independently passed five tests; `python3 scripts/check_cap_audit.py` passed with 63 theorems/157 declarations and observed `[propext]` within `[propext, Quot.sound]`. No T-398 policy/code change is proposed to mask the failure. Old accepted T-395 artifact checker remains an old-pin gate, not a K-02 source check.

Prior physical R1/R2/R3 reports read from the isolated internal harmonia-registration worktree: `design/harmonia/reviews/2026-10-06_generated_preflight_grok_{r1,r2,r3}.md`. Their cumulative retained findings cover mutable lexical cells, targeted loop/switch exits, defaults, TS/Python module and constructor initialization, exact emitted JSON, primitive and Python numeric tags, heap descriptors/frozen identity, independent SourceParses, truthiness, Python `_busy` alias and anchored regex match-at-offset/`.end()`. R3 was the third consecutive historical REVISE; it stopped old-pin work without product code. Yong's explicit 2026-10-11 intervention resets the review counter **for redesigned K-02 T-398 only**. None of R1/R2/R3 is a current-source ACCEPT, and the parent will run the new independent preflight.

## Self-review and limits

The new spec/plan are source-bound to K-02, not a mechanical old-name replacement. The theorem target is an explicit constructor followed by exactly one DEBIT for all bounded b and safe n, with total constructor execution in the conclusion. It has a separate target store/request/observation relation, exact Bridge-dependent dimensions, and a required parser/operational semantics of every reached generated helper body. An unexecuted source span may be version-locked by exact syntax but cannot justify runtime behavior. The accepted prior model cases are from `balanceCandidate`, not `Balance.balanceWorld`. New generated files, theorem, tests, CI, host-language conformance and Linux checks are future implementation gates. Source exact-byte serialization, pinned Kadmos admission and basic Node/CPython primitive behavior remain explicitly trusted; solver UNSAT, hashes and finite traces are not kernel proofs. If the full reached fragment is too large to model without an ideal helper macro, the parent must decide on more formalization or an explicitly authorized alternative backend. No product code was started in this invocation.

## 2026-10-12 physical resumption: compile repair and strict audit

The existing isolated source branch is `feat/t396-generated-correspondence`; the toolchain remains `leanprover/lean4:v4.16.0`. The six inherited modified files were preserved and incorporated into this continuation. The initial `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` exited 1 with the expected missing suite and `SingleStatement` premises at the `pythonIfThen`, `pythonSequence` and two `pythonFinal` calls. The corrected proof uses `(by decide +kernel)` for the suite, `(by simp [SingleStatement, pythonBooleanIf])` for the first sequence item, and `(by simp [SingleStatement])` for each final item. The same target then exited 0.

The first ordinary Generated audit exited 0 under its historical choice-permitting policy (7,781 theorems / 10,358 declarations). Its log exposed `Classical.choice` in `SourceSpan.prefix_then_slice` and the symbolic balance bounds/invariant/branch proofs. This was **not** a strict audit success. Separate RED strict dependency probes rejected the balance guard theorem and span theorem before their proof changes.

The balance proofs now construct both `safeInt` inequalities explicitly before calling `omega`. Their statement types and reference semantics are unchanged. Lean 4.16's `List.take_add` itself depends on `Classical.choice`; the new private `sourceTake_add` proves the required take/drop equation by structural induction instead. `SourceSpan.prefix_then_slice` now depends only on `[propext]`, and `generated_balance_guard_reject`, `generated_balance_accept` and `generated_balance_bounds_reject` each depend only on `[propext, Quot.sound]`. These three theorems concern `interpret balanceCandidate`, not target execution.

The Generated audit selects its existing exact source/test manifest and passes `allowChoice := false` through every declaration and unused-axiom check. Its printed whitelist is `[propext, Quot.sound]`. Other legacy audit commands retain their existing policy; no Quorum/CAP policy was weakened. `KadmosGeneratedK02AuditRejection.choice_dependency` deliberately depends on `Classical.choice` and the new strict declaration command rejects it under `#guard_msgs`; it is confined to the existing rejection root. The inventory suite gained two strict-policy mutations. Changing the Generated command to allow choice initially passed the old inventory check (RED); it is now rejected. An independent reviewer found that a commented strict command could mask a weakened live command. The reproduced mutation initially failed the rejection assertion (RED); comparing the matched region against the comment/string-scrubbed live source fixes it (GREEN, all 11 mutation tests).

Independent review was read-only and used actual `lake env lean --stdin` processes. It found no further Critical/Important defect in this continuation's witness repair, constructive proof changes, or strict policy changes. Its audit-policy finding was fixed and tested. It **did not accept Stage 3c**. The remaining source-grammar findings are:

1. `balance - event.amount` derives both `sub balance (property event amount)` and `property (sub balance event) amount`. Postfix receiver and unary/callee precedence restrictions are still missing.
2. `return true;` derives both a bare return and `sequence (return true) empty`. `SingleStatement` forbids a nested sequence head but does not distinguish a single statement from a canonical statement-list body.
3. The current suite rule and function grammar accept `def f(x: Any) -> bool:\n    if True:\n        if True:\n        return True`. CPython `compile` rejects it: `IndentationError: expected an indented block after 'if' statement on line 3`. `suiteLinesWithin` checks a minimum prefix without the enclosing indentation context.
4. The formatted-wrapper grammar accepts TS `` `a` + `b` `` and Python `f"a" + f"b"` as one formatted literal containing the internal closing quotes and operator text. Delimiter ownership and escape decoding remain open.

Kernel probes independently confirmed the expression/statement ambiguities and formatted-wrapper admissions. The initial combined reproducer's function application needed explicit string/name parameters; the corrected focused function-layout probe exited 0. These are counterexamples to the adequacy/canonicality of the current grammar, not failures of its validator-to-grammar soundness proof. They must be corrected before a whole-program uniqueness theorem can be established.

A live interface probe imported `SourceValidator` and `TargetProgramParser`, then checked `validateSource_sound`, `parseGenerated_sound` and `SourceParses.unique`. It exited 1 with all three identifiers unknown. `parseGenerated` still dispatches directly to the raw TS/Python decoders. `TargetSimulation.lean`, `BalanceSimulation.lean`, `BalanceCorrespondence.lean` and their four requested test targets are absent. Therefore the constructor-for-all-b, helper/branch simulation, reached-path adequacy and universal `k02_balance_one_call` deliverables are not proved. No Stage 3c completion, checked parser admission, CI acceptance, push, merge or integration is claimed by this receipt.

Final serial verification results are recorded below. One earlier aggregate rebuild was interrupted (exit 130) because Lake launched several expensive closed-source roots concurrently; its result is not counted as verification. The affected roots are rebuilt individually before the final ordinary audit.

### Final serial command receipt

Every command below ran as an actual CLI process, in this order. Exit codes are observed process results.

| Command | Exit | Seconds |
| --- | ---: | ---: |
| `lake build kadmosGeneratedK02SourceLexTest` | 0 | 97.54 |
| `lake build kadmosGeneratedK02SourceValidatorTest` | 0 | 144.34 |
| `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` | 0 | 126.86 |
| `lake build kadmosGeneratedK02SourceModuleTest` | 0 | 103.53 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 | 59.95 |
| `lake build kadmosGeneratedK02SourceGrammarTest` | 0 | 0.27 |
| `lake build kadmosGeneratedK02BalanceTSParseTest` | 0 | 0.25 |
| `lake build kadmosGeneratedK02BalancePythonParseTest` | 0 | 0.26 |
| `lake build kadmosGeneratedK02BalanceTSCertificateTest` | 0 | 0.27 |
| `lake build kadmosGeneratedK02BalancePythonCertificateTest` | 0 | 0.26 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 | 0.26 |
| `lake build kadmosGeneratedK02Audit` | 0 | 54.89 |
| `lake build kadmosWorldAudit` | 0 | 39.06 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | 12.84 |
| `lake build distributedTest distributedAudit distributedAuditRejection` | 0 | 47.15 |
| `lake build kadmosWorldTest kadmosWorldAuditRejection` | 0 | 47.48 |
| `lake build kadmosBridgeSyntaxTest kadmosBridgeCertificateTest kadmosBridgeFixturesTest kadmosBridgeAudit kadmosBridgeAuditRejection` | 0 | 23.82 |
| `lake build` | 0 | 0.27 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 | 0.07 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 | 0.09 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 | 1.07 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 | 5.47 |

Portable output excerpts (all audit counts are observed, not fixed acceptance constants):

```text
$ lake build kadmosGeneratedK02SourceLexTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02SourceValidatorTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02PythonBooleanSyntaxTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02SourceModuleTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02BalanceTSStepTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02SourceGrammarTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02BalanceTSParseTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02BalancePythonParseTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02BalanceTSCertificateTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02BalancePythonCertificateTest
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02AuditRejection
Build completed successfully.
exit 0

$ lake build kadmosGeneratedK02Audit
KADMOS GENERATED K-02 AUDIT PASS: 7782 theorems; 10359 declarations; observed axioms [propext,
 Quot.sound]; whitelist [propext, Quot.sound]
exit 0

$ lake build kadmosWorldAudit
KADMOS WORLD AUDIT PASS: 9205 theorems; 12378 declarations; observed axioms [propext,
 Quot.sound,
 Classical.choice]; whitelist [propext, Quot.sound, Classical.choice]
exit 0

$ lake build foundationsTest foundationsAudit foundationsAuditRejection
AUDIT PASS: 52 theorems; observed axioms [propext, Quot.sound]; whitelist [propext, Quot.sound, Classical.choice]
exit 0

$ lake build distributedTest distributedAudit distributedAuditRejection
DISTRIBUTED AUDIT PASS: 336 theorems; 594 declarations; observed axioms [propext,
 Quot.sound,
 Classical.choice]; whitelist [propext, Quot.sound, Classical.choice]
exit 0

$ lake build kadmosWorldTest kadmosWorldAuditRejection
Build completed successfully.
exit 0

$ lake build kadmosBridgeSyntaxTest kadmosBridgeCertificateTest kadmosBridgeFixturesTest kadmosBridgeAudit kadmosBridgeAuditRejection
KADMOS BRIDGE AUDIT PASS: 1691 theorems; 2163 declarations; observed axioms [propext,
 Quot.sound]; whitelist [propext, Quot.sound, Classical.choice]
exit 0

$ lake build
Build completed successfully.
exit 0

$ python3 scripts/check_kadmos_generated_k02_artifacts.py
K-02 ARTIFACT PASS: {'files': 10, 'fixturesLeanSha256': '3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3'}
exit 0

$ python3 scripts/test_kadmos_generated_k02_artifacts.py
Ran 8 tests in 0.042s
OK
exit 0

$ python3 scripts/check_kadmos_generated_k02_audit.py
KADMOS GENERATED K-02 INVENTORY PASS: {'generated_modules': 18, 'generated_tests': 28, 'certified_closure': 52, 'test_targets': 24, 'world_inventory': 30}
exit 0

$ python3 scripts/test_kadmos_generated_k02_audit.py
Ran 11 tests in 5.431s
OK
exit 0

```

Observed build warnings, deduplicated (not hidden or counted as errors):

```text
warning: ././././Harmonia/Applications/Kadmos/Bridge/Certificate.lean:185:54: try 'simp' instead of 'simpa'
```

The [portable Generated theorem dependency listing](2026-10-12-t398-generated-axioms.txt) records every theorem axiom list printed by the final strict audit. The audit also checks every selected safe declaration and declared source axiom, including unused axioms. The old World audit retains its historical policy and any observed choice dependencies there are reported in its output above; strict Generated acceptance is separate.

Additional compatibility command, after the serial receipt: `lake build quorumTest quorumAudit quorumAuditRejection capTest capAudit capAuditRejection` exited 0. Quorum audit: 15 theorems / 17 declarations, observed `[propext, Quot.sound]`; CAP audit: 63 theorems / 157 declarations, observed `[propext]`. Their existing policies are unchanged.


## 2026-10-12 owner continuation: grammar roles and absolute span ownership

Base: `8f2578f`, branch `feat/t396-generated-correspondence`. The seven changed Lean files repair prerequisites; they do not complete Task 2A or introduce Task 2B. No emitted artifact, target executor, toolchain, Core module or audit policy was changed.

RED kernel probes admitted lower-precedence member/call receivers, adjacent formatted literals, unmatched Python closing braces, reserved interpolation names, a same-indent nested Python suite and a same-indent statement certificate at actual source offsets. The repaired declarative productions require binding power, literal delimiters and braces, legal local names, distinct statement/body sorts, enclosing suite layout and absolute indentation prefixes. Exact function header/body/trailer locations now replace mere containment of a repeated body text. Further probes reject postincrement receivers, undelimited integral member dots and Python comparisons assigned JS nesting. Product soundness and all retained witnesses passed after these changes. The fresh serial run below was repeated after the last source edit; its successful commands are cached replays of the preceding observed compilations.

| Command | Exit | Observation |
| --- | ---: | --- |
| `lake build` | 0 | Pass |
| `lake build foundationsTest` | 0 | Pass |
| `lake build foundationsAudit` | 0 | Pass |
| `lake build foundationsAuditRejection` | 0 | Pass |
| `lake build kadmosGeneratedK02SourceGrammarTest` | 0 | Pass |
| `lake build kadmosGeneratedK02SourceValidatorTest` | 0 | Pass |
| `lake build kadmosGeneratedK02SourceModuleTest` | 0 | Pass |
| `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` | 0 | Pass |
| `lake build kadmosGeneratedK02StatementCertificateTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalanceTSParseTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalancePythonParseTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalanceTSCertificateTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalancePythonCertificateTest` | 0 | Pass |
| `lake build kadmosGeneratedK02SimulationTest` | 1 | Unknown target; Task 2B is not implemented |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 1 | Unknown target; Task 2B is not implemented |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 | Pass |
| `lake build kadmosGeneratedK02Audit` | 0 | Pass |
| `lake build kadmosGeneratedK02AuditRejection` | 0 | Pass |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 | Pass |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 | Pass |

The Generated audit reports **7,868 theorems / 10,474 declarations**, observed axioms **`[propext, Quot.sound]`**, with that same strict whitelist. This is 86 additional audited theorems and 115 additional declarations relative to `8f2578f`. The [portable dependency listing](2026-10-12-t398-generated-axioms.txt) contains exactly 7,868 theorem entries from this run. Foundation audit: 52 theorems, observed `[propext, Quot.sound]`; its historical whitelist remains unchanged. Inventory: 18 Generated product modules, 28 test/audit modules, 52 certified closure modules, 24 test targets and 30 World inventory modules. All 11 inventory/policy mutation tests passed. The unchanged Bridge certificate linter suggestion at line 185 was observed in replayed builds; it is not an error.

A separate actual `lake env lean --stdin` probe imported both `SourceStatementCertificate` and `TargetProgramParser`. It exited 1: `ProgramDerives`, `validateSource_sound`, `parseGenerated_sound` and `SourceParses.unique` are still unknown. Axiom probes for `validateExprSpan_sound`, `validateStmtSpan_sound`, `validateStmtCertificate_sound`, `validateFunctionItem_sound` and `functionBodyLocatedCheck_sound` each reported `[propext, Quot.sound]`. The two unknown build targets above are genuine missing deliverables, not expected rejection fixtures. The corresponding simulation modules, heap invariants, reached-path adequacy and universal constructor theorem remain absent. The accepted plan's full-source and constructor gates remain open; T-398 stays IN_PROGRESS and draft PR #5 stays unmergeable.

Rulings for this continuation: escaped formatted literals fail closed until a decoding production exists, and Python comparison chains fail closed until a chain production exists. The cost is that this fragment cannot certify these otherwise valid forms yet. No general formatting, expression determinism or program uniqueness theorem is inferred from the passing fragment tests.

## 2026-10-12 continuation from d436bbd: empty expressions and initial scalar simulation

This continuation is **partial Task 2A and partial Task 2B**, not Stage 3c completion. Runtime `ExprSyntax.empty` is removed; `TargetExpr.empty`, `ArgumentSyntax.empty` and `FormatSyntax.empty` remain list/format sentinels. RED kernel checks reproduced acceptance of an empty runtime expression and a missing TS subtraction operand; both now reject, while empty argument lists and `f()` remain accepted. A direct grammar theorem rules out Python empty-expression ghost statements. The two validator ghost-statement probes already rejected on the baseline (expression statements are not supported by that validator); they are retained negative controls, not claimed RED regressions.

`TargetSimulation.lean` adds an unfueled scalar/binary `SmallStep`, explicit reflexive-transitive `Runs`, ordered binary continuations and ranked `DepthDerivesExpr` constructors. `evalScalar_sound` covers only `ScalarSyntax`: undefined/null/bool/integer/string and non-addition binary nodes, including source exceptions from either child. `evalExpr_adequate` proves the reverse direction for those semantic derivations with strict `rank < k`; leaves have rank zero and siblings use `1 + max`, not a trace-step sum. Python allocation-sensitive list addition is excluded. No rule assumes a generated helper body's result or an executable success equation. The initial relation preserves the whole heap because this slice performs no writes or allocations; that preservation theorem does not cover future mutation rules. An axiom probe caught `omega` introducing classical contradiction for an impossible equality goal. Explicit `False` elimination repaired it: soundness/adequacy depend only on `[propext, Quot.sound]`, and `expr_path_runs` has no axioms.

The finite `HeapWF` check requires distinct/bounded object, cell and closure addresses, matching live permission cells, live descriptors and object contents, live local/capture/global cells, live closure/default/receiver values, live checker references, a live modeled Object.prototype, and generator object/state correspondence in both directions. It accepts both actual initial host machines. Negative kernel probes reject duplicate object addresses, invalid fresh counters, dangling context references and invalid generator tables. `BalanceSimulation.lean` adds a relational `BalanceRep`: Ready, exact one-key own-data context, unfrozen empty history, no undo, busy false and a live distinct copied constructor seed. Its consequences are physical context/seed descriptor reads. No fabricated constructor execution or universal constructor witness is introduced.

Independent review used an actual read-only Codex CLI process against a frozen source snapshot. It found one Important defect: live Python generator objects were not required to have generator-state entries. An actual pinned Lean RED probe reproduced the orphan-object acceptance; the reverse liveness guard and two-direction kernel regressions repaired it. No Critical or Minor findings were reported. The reviewer checked the source inventory but did not run kernel builds; the serial verification receipt below is the implementation agent's evidence.

Still absent: `ProgramDerives`, the four complete declarative source certificates, `SourceParses`, `validateSource_sound`, `parseGenerated_sound`, `SourceParses.unique`, `CanonicalGlobals`, statement/call depth derivations, full evaluator/path adequacy, clone/JSON budget proofs, constructor totality, shared cursor/helper simulation, decoded history/savepoint frame correspondence, branch simulation and `k02_balance_one_call`. The constructor proof target remains missing. A pinned Lean interface probe reports the named program/global/correspondence identifiers as unknown. Current raw fixture parse/certificate tests remain decoder evidence. T-398 is IN_PROGRESS and draft PR #5 remains unmergeable.

The strict inventory registers 20 Generated product modules, 29 test/audit modules, 55 certified-closure modules, 25 test targets and 32 World product modules. The World audit imports the new product closure; no historical policy is weakened. CI now invokes the Generated inventory/mutation checks, scalar simulation target and strict audit/rejection targets.

| Command | Exit | Observation |
| --- | ---: | --- |
| `lake build kadmosGeneratedK02SourceModuleTest` | 0 | Pass |
| `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 | Pass |
| `lake build kadmosGeneratedK02SimulationTest` | 0 | Pass |
| `lake build` | 0 | Pass |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 | Pass |
| `lake build kadmosGeneratedK02SourceGrammarTest kadmosGeneratedK02SourceValidatorTest` | 0 | Pass |
| `lake build kadmosGeneratedK02BalanceTSParseTest kadmosGeneratedK02BalancePythonParseTest kadmosGeneratedK02BalanceTSCertificateTest kadmosGeneratedK02BalancePythonCertificateTest` | 0 | Pass |
| `lake build kadmosGeneratedK02Audit` | 0 | Pass |
| `lake build kadmosGeneratedK02AuditRejection` | 0 | Pass |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | 0 | Pass |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 | Pass |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 | Pass |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 | Pass |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 | Pass |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 1 | Missing target; constructor gate remains open |

The final strict Generated audit reports **7,950 theorems / 10,706 declarations**, observed axioms and whitelist **`[propext, Quot.sound]`** (+82 theorems / +232 declarations from `d436bbd`). The [portable dependency listing](2026-10-12-t398-generated-axioms.txt) contains exactly 7,950 theorem entries. Foundation audit: 52 theorems, observed `[propext, Quot.sound]`; its historical whitelist is unchanged. World audit: 9,265 theorems / 12,611 declarations; its historical `[propext, Quot.sound, Classical.choice]` observations/policy remain reported separately and are not strict Generated acceptance. Eight artifact and eleven inventory/policy mutation tests pass. The unchanged Bridge.Certificate line 185 unnecessarySimpa warning was observed in replayed builds.

The preliminary aggregate rebuild was interrupted (exit 130) after concurrent heavy kernel roots stalled, matching earlier ledger evidence. Rebuilding SourceModule, PythonBooleanSyntax and BalanceTSStep individually resolved that scheduling issue; the final aggregate audit completed on the repaired source. The missing constructor target above is an unmet deliverable, not an adversarial rejection fixture or a passing gate. The independent review's one Important generator defect is repaired RED→GREEN; there are no deferred Minor findings. The global gates it set aside remain explicitly open, as enumerated above.


## 2026-10-12 constructor/branch continuation from 32a1120

This is partial Task 2B and Task 3 groundwork. **Universal constructor totality and the three universal branch simulation theorems are not established.** The new proof-root names register the plan's closed sanity checks; a green root is not completion of its universal gate.

`TargetSimulation` now gives elementary statement/control rules and ranked derivations for empty statements, source-ordered sequences, return/throw/rethrow, break/continue, checker-field writes and caught/uncaught try/finally. `stmt_path_runs` turns these derivations into unfueled traces, and `execStmt_adequate` proves reverse adequacy with strict `rank < k`. These are supported-rule theorems, not coverage of all statements or calls. Every sequence tail contributes a predecessor-depth edge. Body, handler and cleanup ranks combine by maximum; normal cleanup restores the saved **outcome** control, while exiting cleanup overrides it. Exception binding allocates a fresh cell and sets the active frame control; the handler frame is cleared before cleanup, separately from its saved outcome.

Pure `controlCaught` and `bindCatchFrame` helpers extract the existing low-level catch tag and lexical-binding operations from the generic executor. The generated source, its helpers and behavior are unchanged. The relation uses primitive heap/field operations and actual expression derivations; no rule assumes constructor, reset, tokenizer, sanitizer or step helper correctness. General `Runs.machine_eq` is removed because statement traces can now write the busy slot. Scalar expression derivations retain their machine-equality/HeapWF preservation lemma. No general mutation-preservation theorem is inferred.

`CountedRuns` has a separate natural-number trace index. This replaces the design's optional function from Prop-valued Runs proofs to Nat, which Lean cannot eliminate in that way. A kernel regression proves a 253-step scalar expression trace with rank 6 executes at depth 7. Trace count is never used as entrypoint fuel and never changes the machine's unused fuel field.

The checked content decoder dereferences exact one-key contexts and seeds, history records and payloads, TS object savepoints and Python tuple savepoints. Python context/step numbers require `.pyInt`; sanitized record amounts require `.pyFloat`. It rejects extra/missing keys, duplicate canonical keys, accessors, non-enumerable data, wrong container/numeric tags and malformed savepoint layouts. Freeze metadata and heap identity remain separate source-execution obligations. `BalanceRep.view` derives the constructed logical view from physical heap reads; `balanceRepCheck_sound` turns a decidable check of an actual heap into the existing relational representation. `checkedConstructor_witness` only lifts an already checked executable result; its success premise is explicit and it is not `targetConstruct_sound`.

Test-only `KadmosGeneratedK02ClosedPrograms` contains fixed full AST literals, including every module/class/function field. Candidate literals were dumped by the raw decoder; that generator is untrusted. Two `decide +kernel` facts prove the entire candidates equal to parsing the pinned TS/Python fixture strings. Boundary facts rewrite by those equalities and then kernel-check the same actual executor computations, avoiding repeated normalization of source parsing during method lookup. This is raw-decoder equality evidence, not independent source grammar or validator soundness. There are no native verdict premises or generated helper macros. The exact `--tstack=131072` option is limited to this certificate target and the existing Python-line target. The inventory linter requires those exact options and thirteen inventory/policy tests now pass, including altered trust flags and commented-out options for both targets. Language-specific boundary modules are built serially before their aggregate roots.

The constructor root checks actual raw-decoder/executor results at b=0,100,S for TS and Python. The step root checks 100/0,100/-1,100/30,100/130,S/S,S/-S for both languages, including post-construction, pre-step representation, both logical views, postheap HeapWF, violation code, normalized projection, accepted one-record history/precall savepoint and busy=false. Rejections compare dereferenced complete views, allowing rollback allocations to differ. S/-S succeeds as guard rejection even though its unused subtraction would be outside the safe domain. These finite kernel facts do not establish a generated helper body theorem, uniform rank, universal termination, independent full-source grammar or correspondence.

An independent actual read-only Codex CLI reviewer (gpt-6.1-sol) reviewed a frozen snapshot. It found one Important decoder defect: `targetViolationCode` consumed allowed/code via the legacy weak value reader. Four small kernel probes reproduced admission of non-enumerable or mixed accessor/data descriptors. Strict own-data reads for both fields repair this RED-to-GREEN. The reviewer found no new catch-control or depth issue. Its minor float-tag-test mismatch was corrected to explicitly test `.pyFloat`. The reviewer ran no builds and did not certify native runtimes, Linux CI, provenance regeneration or the snapshot's base independently; the local physical verification below is the implementation agent's evidence.

Open gates remain: CanonicalGlobals derived from execution, declarations/collections/call/closure/helper simulation, statement soundness and full rule coverage, execution-derived mutation HeapWF preservation, canonical clone/JSON host-budget adequacy, uniform module/field/constructor and step-call depth bounds, targetConstruct_sound, step_guard_reject, step_accept, step_bounds_reject, full-source ProgramDerives/SourceParses soundness/uniqueness and k02_balance_one_call. T-398 remains IN_PROGRESS; draft PR #5 remains unmergeable. No push or merge was performed.

All twenty final serial commands below exited 0. The strict Generated audit reports **8,341 theorems / 11,341 declarations**, observed axioms and whitelist **`[propext, Quot.sound]`** (+391 theorems / +635 declarations from 32a1120). The portable dependency listing contains exactly 8,341 entries. Foundation audit: 52 theorems, observed `[propext, Quot.sound]`; its historical policy is unchanged. World audit: 9,551 theorems / 13,105 declarations with its separately reported historical `[propext, Quot.sound, Classical.choice]` policy/observations. Inventory: 20 product modules, 37 test/audit modules, 63 certified closure modules, 28 test targets and 32 World inventory modules. Eight artifact tests and thirteen inventory/policy tests pass. Lean remains pinned to `leanprover/lean4:v4.16.0`.

| Command | Exit |
| --- | ---: |
| `lake build kadmosGeneratedK02ClosedProgramsTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02BalanceTSParseTest kadmosGeneratedK02BalancePythonParseTest kadmosGeneratedK02BalanceTSCertificateTest kadmosGeneratedK02BalancePythonCertificateTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |

Preliminary combined/unpartitioned constructor runs were interrupted with child exit 130 during slow/high-memory kernel reduction. The first combined monadic check also had an elaboration/stack error (134), repaired by explicit typed helpers and then individual facts. Cached whole-AST equality first exceeded default thread stack (134); exact capacity and generic Option-to-Except result lifting repaired subsequent recursion-depth errors. These unsuccessful attempts are not passing gates. The final receipt above is from the repaired source and all twenty commands passed. The unchanged Bridge.Certificate line 185 unnecessarySimpa suggestion is the only replayed linter warning.

A post-verification pinned Lean interface probe exits 1: `balanceRepCheck` exists, but `targetConstruct_sound`, `step_guard_reject`, `step_accept` and `step_bounds_reject` are still unknown identifiers. This is an unmet universal deliverable, separately recorded from the passing closed proof roots.

Final independent physical read-only Codex review (gpt-6.1-sol, high effort) accepts this partial slice with no Critical or Important findings. It verified the whole-AST equality binding, original-executor boundary rewriting, saved-control/rank rules, strict verdict reads, exact registrations/resource options and the 8,341-entry dependency listing. Two documentation findings are corrected: total test counts distinguish clean smoke tests from hostile mutations, and representation checking is post-construction and pre-step. The reviewer did not independently run the receipt, native runtimes, Linux CI or provenance regeneration; those limits remain explicit. This review is not universal-task acceptance or merge authorization.


## 2026-10-12 universal-prerequisite continuation from 70c4969

This continuation is **partial Task 2B/3 progress; the requested universal constructor, branch simulation and source correspondence mission is incomplete**. A final pinned Lean interface probe still exits 1 for `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject` and `k02_balance_one_call`. `lake build kadmosGeneratedK02CorrespondenceTest` exits 1 because that target is absent. These are unmet deliverables, not negative-test acceptance gates. No placeholder correspondence module or passing target is introduced.

The unfueled relation and ranked expression derivations now cover actual local/global/checker-field reads. Lexical lookup uses the existing receiver/local/capture/global-cell operation; soundness includes successful outer evaluator results and does not hide dangling-cell errors. Kernel regressions check current captured-cell reads, local shadowing and failure without capture fallback when a local cell is dangling. Conditional statement rules evaluate the condition and only the selected arm, or propagate its raised source value without entering either arm. Their rank is `1 + max conditionRank selectedArmRank`; the unselected arm needs no derivation or fuel bound. Reverse adequacy and unfueled trace projection are extended to those paths. An adequate common depth proves deterministic outcomes for any two supported expression or statement derivations, even if their ranks differ. None of these rules assumes a generated helper or executable result.

`allocateSeed_balance` proves physical input allocation for every safe canonical balance, both languages and every starting machine. Its bounded-balance regression derives the host absolute-value check symbolically. This is seed allocation only: actual module initialization, class fields and constructor/reset calls still need derivations and separate rank obligations. Existing `localValue`, `cloneValue` and `allocateSeed` bodies are unchanged; only their visibility and documentation change. No host primitive or generated-helper macro is added.

`replaceObject_allocObject` proves that replacing a fresh allocation preserves all older objects. `HeapWF.object_fresh` derives the needed absence of the next object address from the structural invariant. `cloneValue_balance` proves the existing host clone succeeds at every budget `k + 2` for a canonical one-key numeric context, uniformly in balance and language; its conclusion preserves the complete prior machine apart from prepending the copied object and incrementing the object counter. The actual fixed host budget 2048 therefore suffices for this shape. A separate kernel regression proves host depth one exhausts before copying the numeric child. This obligation is independent of entrypoint depth and trace count. It does not cover history/savepoints, frozen containers, nested objects, cycles, JSON initialization, generated rollback, or post-mutation HeapWF preservation.

The signed interval-to-absolute-value and accept/bounds-reject subtraction lemmas are symbolic, not enumerated. They discharge the safe intermediate obligation under the respective positive-amount branch hypotheses; no subtraction obligation is imposed on guard rejection. These arithmetic lemmas do not execute sanitizer/tokenizer/evaluator helper bodies or prove target branch outcomes.

Still open: full-source `ProgramDerives`/`SourceParses` soundness and uniqueness; `CanonicalGlobals`; declaration/property/call/closure/collection/helper coverage and statement soundness; execution-derived mutation HeapWF preservation; canonical JSON and remaining clone host budgets; uniform module/fields/constructor and step-call ranks; `targetConstruct_sound`; all three universal target branch lemmas; and `k02_balance_one_call`. The source target executor remains independent of the reference interpreter, generic Core/Distributed/legacy semantics are unchanged, and no behaviorally connected legacy claim is made. T-398 remains IN_PROGRESS; draft PR #5 remains unmergeable.

Independent review used an actual read-only Codex CLI process against a frozen base-70c4969 diff. It exited 0 with **no Critical, Important or Minor findings** for this prerequisite slice and explicitly **did not accept the full mission**. It verified read/control/rank behavior, unchanged primitive bodies, clone freshness/frame and shape limitations. The reviewer ran no Lean/Lake, native TS/Python, hosted Linux CI or provenance regeneration, and did not independently authenticate upstream/base provenance. The local verification below is the implementation agent's evidence. No deferred minors, review fixes, push or merge occurred.

All twenty serial commands below exited 0. The strict Generated audit reports **8,398 theorems / 11,429 declarations**, observed axioms and whitelist **`[propext, Quot.sound]`** (+57 theorems / +88 declarations from 70c4969). The refreshed [portable dependency listing](2026-10-12-t398-generated-axioms.txt) has exactly 8,398 theorem entries. Foundation audit: 52 theorems with observed `[propext, Quot.sound]`; its historical whitelist is unchanged. World audit: 9,585 theorems / 13,169 declarations with its separately reported historical `[propext, Quot.sound, Classical.choice]` observations/policy. Inventory is unchanged at 20 product modules, 37 test/audit modules, 63 certified-closure modules, 28 test targets and 32 World inventory modules. Eight artifact and thirteen inventory/policy tests pass. Lean remains `leanprover/lean4:v4.16.0`; fixture literal SHA-256 remains `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`.

| Command | Exit |
| --- | ---: |
| `lake build kadmosGeneratedK02ClosedProgramsTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02BalanceTSParseTest kadmosGeneratedK02BalancePythonParseTest kadmosGeneratedK02BalanceTSCertificateTest kadmosGeneratedK02BalancePythonCertificateTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |

Observed RED-to-GREEN cycles covered missing read/conditional semantic rules, seed allocation/clone proofs, read soundness/freshness and ranked-path determinism. Intermediate elaboration failures included a reserved constructor case label, private result-wrapper definitional equality, allocation-reference simplification, Boolean-versus-propositional map tests, unavailable loop names and adjacent declaration comments; they were corrected before the final receipt. One short RED `lake env lean` probe accidentally overlapped an earlier product rebuild; all final twenty commands ran serially. The unchanged Bridge.Certificate line 185 unnecessarySimpa suggestion was replayed. The missing universal-interface and correspondence-target failures remain open after these passing checks.


## 2026-10-12 lexical statement continuation from `61f03df` — universal mission incomplete

**T-398 remains IN_PROGRESS. Tasks 2B, 3 and 4 are not complete.** This continuation implements constructor/helper prerequisites in the generic relation; it does not prove `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject` or `k02_balance_one_call`. A final actual pinned Lean interface probe exited 1 with all five names unknown, together with `CanonicalGlobals`, `ProgramDerives` and `parseGenerated_sound`. `lake build kadmosGeneratedK02CorrespondenceTest` exited 1 with unknown target. No placeholder correspondence module/target, semantic success assumption or task-completion line was introduced. Full-source admission, module/class/function/call and collection/helper derivations, preservation and uniform entrypoint ranks remain open.

`TargetSimulation` now derives actual `letLocal`, existing lexical assignment, Python fresh-local assignment, `doExpr` and positive `nonlocalNames` execution. A declaration allocates at the RHS outcome machine's next cell; existing assignment keeps the resolved cell address. Local/capture/global precedence is explicit, and assignment continuations snapshot **original-machine globals**, matching `execStmt`, while writes affect the RHS outcome machine. Source-raised RHS outcomes propagate without allocation or assignment. Unbound TS assignments and immutable/dangling writes remain outer target errors. `nonlocalNames` checks captured names without allocation; it has rank 0 because the executor performs no recursive evaluator call.

All these ranked derivations project to unfueled traces preserving arbitrary outer continuations, and reverse adequacy establishes actual executor results for strict depth bounds. New `execLexical_sound` covers only declaration, local assignment and expression statements with **ScalarSyntax** children; it does not cover generated calls or arbitrary statement syntax. Positive nonlocal adequacy is separate. No generated helper is introduced as a primitive and `TargetSemantics` is unchanged. Heap preservation and canonical globals are not inferred from these statement proofs.

Observed RED→GREEN cycles: SimulationTest initially failed on four missing lexical derivation constructors; then on missing `execLexical_sound`, then on missing `nonlocalNames`. New symbolic tests check actual allocation, captured cursor writes and declaration shadowing, missing TS bindings, immutable cells, missing nonlocal captures, insufficient depth and all three RHS source-error paths. Private evaluator result wrappers, List.lookup and Option.orElse required explicit proof rewrites during elaboration; those proof failures were corrected before the final receipt. Retained catch/finally, trace-versus-depth, closed constructor and one-step boundary tests pass. The boundary tests still establish six/twelve finite checks, not universal entrypoint execution.

Actual independent read-only Codex CLI review exited 0, model gpt-6.1-sol, session `01a13354-f939-7bc1-8994-de89a75db677`, against a frozen `git archive 61f03df145838d7aaa743b03add21ddb2ca010c8` snapshot plus the two-file diff. It reported **no Critical, Important or Minor correctness findings for this prerequisite slice**, explicitly declining full-mission acceptance. Both reviewed source postimages match the final source byte-for-byte. The reviewer verified diff preimage/postimage consistency but did not independently authenticate upstream/base association, run Lean/Lake, native runtimes, a fresh axiom audit or hosted Linux CI. Owner serial CLI results below supply current local kernel/inventory evidence; prior native-runtime and Linux limits remain unchanged. No deferred review findings or merge/push.

All nineteen serial prerequisite/compatibility commands below exited 0. Strict Generated audit: **8,446 theorems / 11,522 declarations**, observed axioms and whitelist **[propext, Quot.sound]** (+48/+93 from `61f03df`). The portable dependency listing contains exactly 8,446 unique theorem entries. Foundation audit: 52 theorems, observed [propext, Quot.sound], historical policy unchanged. World compatibility: 9,597 theorems / 13,219 declarations, historical [propext, Quot.sound, Classical.choice] observations/policy reported separately. Artifact tests: 8 total (7 mutations + 1 smoke). Inventory/policy tests: 13 total (12 mutations + 1 smoke). Inventory unchanged: 20 product modules, 37 test/audit modules, 63 certified closure modules, 28 test targets, 32 World inventory modules. Lean remains `leanprover/lean4:v4.16.0`; unchanged fixture literal SHA-256 `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`. No new imports, proof-resource options, compiler/runtime changes or legacy protocol edits. The existing Bridge.Certificate unnecessarySimpa warning remains.

| Command | Exit |
| --- | ---: |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02BalanceTSParseTest kadmosGeneratedK02BalancePythonParseTest kadmosGeneratedK02BalanceTSCertificateTest kadmosGeneratedK02BalancePythonCertificateTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |

The passing constructor/step targets above retain their boundary assertions. Separate required open-gate checks:

| Gate | Observed result |
| --- | --- |
| Pinned Lean interface probe | Exit1; all five requested universal names and three prerequisite names unknown |
| `lake build kadmosGeneratedK02CorrespondenceTest` | Exit1; unknown target |

This commit is a verified prerequisite checkpoint, **not completion of the requested universal constructor/branch/correspondence mission**. The plan workspace is retained for resumption.


## Property/object/call prerequisite continuation — 2026-10-12

Resumed from clean `f66a9581428240ff920343bce24b45762e9afb2a` in the specified isolated `feat/t396-generated-correspondence` worktree. This checkpoint advances generic simulation infrastructure; **Tasks 2B, 3 and 4 remain incomplete**.

`TargetSimulation.lean` now derives receiver-property evaluation (including method-binding closure allocation), fresh TS object/Python dict allocation with ordered field writes, ordered argument spines, supplied-parameter binding with fresh mutable cells, calls through the actual stored closure body, caller-frame restoration and body/argument exception propagation. Direct basic host calls cover unbound builtins excluding `next/tuple/list`, and bound builtins excluding callback `find/some/map`; those exclusions are also enforced by the unfueled host-finish transition. Default selection and excess-argument paths are outside the provided-parameter binding relation. No generated constructor, sanitizer, evaluator, bounds or step helper becomes a primitive.

Expression/field/argument/statement derivations are mutually indexed, and their arbitrary-continuation trace projections and reverse adequacy proofs recurse on strictly smaller ranks. Calls use `1 + max` over callee, argument spine, binding spine and body; `callClosure` adds no depth match. Fields and parameter/argument tails each retain their actual predecessor edge. The proof preserves executed machines, including bound-closure allocation; scalar machine/heap preservation now explicitly requires `ScalarSyntax`. HeapWF preservation for allocating expressions/calls, canonical globals and generated helper execution are still open. The mutual adequacy declaration exceeded the default 200,000-heartbeat limit during development and now has a scoped 1,000,000-heartbeat limit; no trust option, Lake target or stack setting changed.

`TargetSemantics.lean` exposes six previously private definitions (`readPropertyValue`, `hostCall`, `evalObjectFields`, `evalArgValues`, `bindCallParams`, `callClosure`). The owner compared final text against the base after exactly those six visibility replacements; every interpreter body is identical. No Core, Distributed, legacy protocol, compiler/runtime or fixture changes.

Observed RED→GREEN tests cover the missing property/object/field/argument/closure/host derivation interfaces and scalar-receiver property soundness. Symbolic regressions cover `this` and `self`, physical method-closure allocation, one/two-field order, provided arguments despite defaults, TS undefined-default exclusion, actual parameter-cell reads, sibling depth maxima, body/argument exceptions, caller restoration and insufficient depth. These tests establish generic model rules, not execution of all generated bodies.

Independent actual read-only Codex CLI review used **gpt-6.1-sol/high**, session `01a13374-a5af-75c2-89e1-a52d4a796f6c`, against a frozen `git archive f66a958` snapshot plus the three-file diff, and exited 0. It found no static semantic mismatch in the covered derivations, but **did not accept the full mission**. Its Important vacuous host test finding was repaired in one fix pass: the original theorem assumed success for zero-argument `isSafeInteger`, which the executor rejects. A valid one-argument regression first failed (serial SimulationTest exit 1), then passed after deriving the primitive result without any host-success premise. A concrete satisfiable callee binding now has both unfueled trace and executable-adequacy witnesses, and invalid zero-argument arity has a separate rejection fact.

The subsequent strict audit exposed `Classical.choice` in the method-allocation test's `simp` proof of `counter + 1 ≠ counter`. Printed proof dependencies and a minimal Init-only probe localized it to a Nat simplifier auxiliary. The final proof uses `Nat.ne_of_lt (Nat.lt_succ_self _)` directly; its permanent axiom print reports `[propext, Quot.sound]`. No whitelist relaxation. The owner reran the entire serial suite after both fixes. Both reviewed product postimages match final source byte-for-byte; post-review changes are test repairs validated RED→GREEN and by the final strict audit. No second review was substituted for verification.

Deferred review minor: composed call tests should further exercise captured-cell mutation, receiver reads inside the body, repeated calls with distinct parameter cells and caller restoration after an exception. Default/generator/callback/collection/declaration coverage remains required proof work, not an optional completion claim. Full-language JS/Python/runtime/compiler/serialization correctness and order/repeated-call semantics remain outside the spec's first-call theorem. The reviewer verified patch pre/post blob hashes but did not independently authenticate upstream/base association, run Lean/Lake, kernel/native/CI checks or edit files; owner archive/rev-parse and serial checks provide local evidence. Native runtime and hosted Linux evidence were not rerun or inferred.

Final strict Generated audit: **8,573 theorems / 11,768 declarations**, observed axioms and whitelist **`[propext, Quot.sound]`** (+127/+246 from `f66a958`). The refreshed portable dependency listing contains exactly 8,573 unique entries. Foundation audit: 52 theorems with observed `[propext, Quot.sound]`, historical policy unchanged. World compatibility: 9,661 theorems / 13,398 declarations, with historical `[propext, Quot.sound, Classical.choice]` observations/policy reported separately. Artifact tests: 8 (7 mutations + 1 smoke); inventory tests: 13 (12 mutations + 1 smoke). Inventory unchanged at 20 product modules, 37 test/audit modules, 63 certified closure modules, 28 test targets and 32 World inventory modules. Lean remains `leanprover/lean4:v4.16.0`; fixture SHA-256 remains `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`. Existing Bridge.Certificate unnecessarySimpa warning persists.

All twenty final serial commands exited 0:

| Command | Exit |
| --- | --- |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02BalanceTSParseTest kadmosGeneratedK02BalancePythonParseTest kadmosGeneratedK02BalanceTSCertificateTest kadmosGeneratedK02BalancePythonCertificateTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |

Separate universal acceptance probes retain their failures:

| Gate | Observed result |
| --- | --- |
| Lean interface probe | Exit 1: all five requested universal names and `CanonicalGlobals`, `ProgramDerives`, `parseGenerated_sound`, `balanceProgram` unknown |
| `lake build kadmosGeneratedK02CorrespondenceTest` | Exit 1: unknown target |

Universal constructor composition, the three branch lemmas, checked whole-source admission and one-call correspondence have not been proved. Existing constructor/step roots still establish boundary facts. No correspondence stub or weakened theorem was added, no task-complete ledger line, push or merge; retain the incomplete plan workspace for resumption.


## Canonical BALANCE program and admission binding — 2026-10-12

Resumed from clean `d26ee6e61180862d17fb6bf83f236efa4c853d60` in the specified isolated `feat/t396-generated-correspondence` worktree. **Stage 3c and Tasks 2B, 3 and 4 remain incomplete.** This change defines the requested canonical program and proves certificate inversion; it does not prove universal constructor totality, branch simulation or one-call correspondence.

`TargetCertificate.lean` now defines `balanceSource` from the two actual pinned fixtures and `balanceProgram` from their parser output. Both unconditional closed kernel equalities in ConstructorProof bind it to the existing actual-source TS/Python ASTs. The fallback empty AST is excluded by those equalities for both pinned sources and by admission inversion for accepted certificates. `checkGenerated_source` extracts exact pinned-source equality and parser `.ok` from admission; `checkGenerated_balanceProgram` then proves that an arbitrary accepted BALANCE source/program pair equals the canonical source/program. These lemmas assume no target execution result, ideal generated helper or heap representation. They establish byte/decoder ownership, **not** independent source-language grammar soundness.

Observed RED→GREEN: ConstructorProofTest first exited 1 for missing `balanceProgram`/`balanceProgram_of_parse`, then exited 0 after implementation. Both canonical AST equalities and the generic admission/balance-binding lemmas print `[propext]`. The Generated strict audit observes only `[propext, Quot.sound]`. `BalanceSimulation` imports the application certificate definitions; the target executor and generic relation retain their independent import boundaries. No interpreter body, Core/Distributed/legacy semantics, fixture literal, toolchain pin or audit policy changed.

Actual independent read-only Codex CLI review used **gpt-6.1-sol/high**, session `01a1338d-f270-7821-9e3c-c35bc4c0d79c`, and exited 0. It reviewed a frozen `git archive d26ee6e` snapshot plus the four-file patch and accepted the canonical binding slice. **It rejected whole-mission completion**, reporting two Important unresolved requirements: the five universal constructor/branch/correspondence proofs, and checked whole-program source syntax. No Critical or Minor patch correctness findings were reported. All four reviewed source postimages match the final source byte-for-byte. The reviewer checked the diff, plan/spec, source, manifest, import/audit configuration and read-only artifact checker; it did not run Lean/Lake, axiom audits, native runtime or hosted CI, and did not independently authenticate archive ancestry. Owner serial commands supply local kernel evidence. The Important mission gaps remain requirements, not deferred minors or accepted deviations.

Final strict Generated audit: **8,582 theorems / 11,781 declarations**, observed/whitelist **`[propext, Quot.sound]`** (+9/+13 from the baseline). The refreshed portable axiom listing has exactly 8,582 unique entries; wrapped audit output was normalized and every dependency checked against the strict whitelist. Foundation audit: 52 theorems, observed `[propext, Quot.sound]`, historical policy unchanged. World compatibility: 9,667 theorems / 13,408 declarations, historical observed/whitelist `[propext, Quot.sound, Classical.choice]` reported separately. Inventory unchanged: 20 product modules, 37 test/audit modules, 63 certified closure modules, 28 test targets, 32 World inventory modules. Inventory tests: 13 passed. All ten artifact checks passed; fixture literal SHA-256 remains `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`. Lean remains `leanprover/lean4:v4.16.0`. The existing Bridge.Certificate unnecessarySimpa warning remains. Native-runtime and hosted-Linux checks were not rerun or inferred.

The twelve owner commands ran serially; eleven exited 0 and the absent correspondence target exited 1. The long strict-audit command rebuilt existing source-certificate proofs; its Lake workers ran concurrently within that single Lake process. No independent Lake process overlapped it.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02CertificateTest` | 0 |
| `lake build kadmosGeneratedK02CorrespondenceTest` | 1 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldTest kadmosWorldAudit kadmosWorldAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |

A separate pinned Lean interface probe exited 1: `balanceProgram` and `checkGenerated_balanceProgram` are present, while `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject`, `k02_balance_one_call`, `CanonicalGlobals`, `ProgramDerives` and `parseGenerated_sound` remain unknown. Constructor/step proof roots still contain boundary facts, not universal execution proofs. The correspondence module/test target was not replaced with a placeholder. Source-derived module/class/helper execution, collection/default/loop coverage, HeapWF preservation, uniform entrypoint ranks and whole-source admission remain open. No task-complete ledger line, full-mission acceptance, push or merge; retain the plan workspace for resumption.

## Final-closure attempt from 7d01221 — 2026-10-12

**Stage 3c remains incomplete.** This attempt added no production theorem, changed no executor or trust policy, and did not create an empty correspondence module/target. Tasks 2B, 3 and 4 are still open. The following commands were run as serial actual subprocesses against the unchanged Lean source at `7d012216b4c49679efa5c7182354d8188f810a49`. Existing constructor/step targets prove finite boundary facts, not the requested universal statements.

| Command | Exit |
| --- | --- |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02CorrespondenceTest` | 1 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02SimulationTest kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake env lean <universal-interface probe>` | 1 |

The correspondence build reports an unknown target. The interface probe reports all five requested declarations unknown: `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject`, and `k02_balance_one_call`. These two exit-1 results are failed acceptance gates, not successful negative tests. The ten other commands exit 0. Strict Generated audit remains **8,582 theorems / 11,781 declarations**, observed and allowed axioms **`[propext, Quot.sound]`**. The fresh 8,582-entry dependency output exactly matches the tracked [portable listing](2026-10-12-t398-generated-axioms.txt); no axiom entry changed. Foundation audit remains 52 theorems. Inventory mutation suite passes 13 tests; artifact checker passes ten checks. The existing Bridge.Certificate unnecessarySimpa warning remains. Native-runtime and hosted-Linux evidence was not rerun or inferred.

Two private symbolic-constructor reduction approaches were interrupted (exit 130) after large term expansion and memory pressure. An earlier exploratory version failed elaboration. No interrupted or failed probe is a proof or evidence of mathematical impossibility. No exploratory `Lean` metaprogram import entered production or certified test roots.

### Kernel-checked representation counterexample

A separate actual Lean subprocess exits 0 on the following diagnostic. It proves that `BalanceRep` alone does not imply a usable canonical `step` method, even when execution selects the actual source-bound `balanceProgram .ts`. Its heap shape is valid, but method lookup and the actual step wrapper fail with `unboundLocal "step"`. This refutes only a branch theorem for arbitrary machines from `BalanceRep` alone; it does **not** refute the requested constructor-origin one-call theorem. Branch composition needs constructor provenance or a program-indexed invariant binding stored methods, default values, captures and globals.

```lean
import HarmoniaTests.KadmosGeneratedK02ConstructorProof
open Harmonia.Applications.Kadmos.Generated
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def bareBalanceMachine : TargetMachine :=
  { TargetMachine.empty with
    objects := [(4, balanceHeapObject .ts TargetMachine.empty 100),
      (3, emptyBalanceHistory .ts TargetMachine.empty),
      (2, balanceHeapObject .ts TargetMachine.empty 100)] ++ TargetMachine.empty.objects
    nextObject := 5
    checker := ⟨"Ready", 2, 3, none, some 4, false, []⟩ }

theorem bareBalanceRep : BalanceRep .ts 100 bareBalanceMachine := by
  apply balanceRepCheck_sound
  decide +kernel

theorem bareBalanceHasNoStep :
    readPropertyValue .ts bareBalanceMachine (.object bareBalanceMachine.checkerRef) "step" =
      .error (.unboundLocal "step") := by
  rfl

#print axioms bareBalanceRep
#print axioms bareBalanceHasNoStep

theorem bareBalanceStepFails :
    targetStep HarmoniaTests.KadmosGeneratedK02ClosedPrograms.balanceTsProgram
      bareBalanceMachine (canonicalDebitRequest .ts 0) =
      .error (.unboundLocal "step") := by
  decide +kernel

#print axioms bareBalanceStepFails

theorem bareCanonicalBalanceStepFails :
    targetStep (balanceProgram .ts) bareBalanceMachine (canonicalDebitRequest .ts 0) =
      .error (.unboundLocal "step") := by
  rw [kadmos_generated_balanceProgram_ts]
  exact bareBalanceStepFails

#print axioms bareCanonicalBalanceStepFails
```

Observed axiom output: `bareBalanceRep` uses `[propext]`; `bareBalanceHasNoStep` has no axioms; `bareBalanceStepFails` and `bareCanonicalBalanceStepFails` use `[propext, Quot.sound]`. This diagnostic is recorded here rather than added to the certified theorem inventory; it supplies no universal constructor or branch proof.

### Independent physical review

Actual read-only `codex exec` ran **gpt-6.1-sol/high**, session `01a133a9-048e-72c2-aa87-01e5b81c179e`, exit 0. It inspected the clean base, plan/spec, grammar/admission, executable and relational semantics, observations/reference cases, emitted BALANCE sources, test roots and audit registration. Its verdict is **REVISE; final closure not accepted**. Findings: the five universal deliverables and target remain absent; whole-source `ProgramDerives`/`SourceParses`/validation/soundness/uniqueness remain absent; ranked execution still lacks reached imports, definitions/defaults, collections, loops and helper paths; `BalanceRep`/`HeapWF` do not certify closure bodies or module bindings. The reviewer independently identified the same provenance issue by inspecting method-body replacement, without using the later owner kernel diagnostic. No counterexample to the intended canonical one-call theorem was established.

The reviewer ran no Lean/Lake, runtime, audit or hosted tests and made no edits. Owner commands above supply the local kernel/audit evidence. Missing mission requirements remain open requirements, not deferred minor findings or accepted deviations. This documentation receipt is not an implementation-completion commit. The plan workspace is retained because the plan is unfinished.

## Kernel-certified constructor preparation phases — 2026-10-12

**Stage 3c and Tasks 2B, 3 and 4 remain incomplete.** Resumed from clean `43edb9d106e2791b3434d8db3b946048f0ee5a1d` in the specified isolated branch/worktree. This implementation certifies fixed preparation and symbolic allocation composition; it does not prove constructor totality, any universal branch, or correspondence. The five requested universal declarations remain absent, and the correspondence build still fails.

`TargetSemantics.lean` adds `targetPrepareConstructor`, `targetConstructFromPrepared` and `targetConstructorCall`, plus two generic phase equalities. The existing `targetConstructWithFuel` body is byte-identical to the base. Module initialization, TS method installation/class fields, retained module frame, allocation, actual receiver dispatch and source-exception handling are preserved. Every phase retains fuel 100 at the canonical entrypoint. No generated helper becomes a primitive and no constructor outcome is assumed.

`BalanceSimulation.lean` proves `balancePreparation_total`, `balancePreparation_success`, `balancePreparation_heapWF`, `balancePreparation_frameWF`, `balanceProgram_lang`, `targetConstruct_balance_prepared` and `targetConstruct_balance_call`. Closed kernel reflection covers the actual seed-independent preparation for both languages. Physical heap/frame checks derive live addresses and captures. Existing `allocateSeed_balance (balance_natAbs hb)` then composes symbolically for every `0 ≤ b ≤ S`. The resulting equality still has `targetConstructorCall` on its right-hand side: success of that actual generated call and its postheap representation are open obligations. Preparation does not establish `CanonicalGlobals` or the full generated helper semantics.

Ruling: relocate the unchanged closed BALANCE AST declarations and their source-decoder equality proofs from the test module into production `BalancePrograms`, retaining test aliases. This avoids repeatedly reducing the raw decoder at each program-field access during closed preparation. The cost is one additional exact Generated/World inventory module. Source text, parsed AST content, admission logic and trust policy are unchanged; these are decoder-binding certificates, not independent whole-source grammar soundness. Both inventory arrays register the new module and the certified import closure reaches it.

Observed RED→GREEN: a Lean interface probe first rejected the three missing phase interfaces. The implemented generic phase probe passed, and the final ConstructorProof target exports all nine phase facts with axiom prints. The module/frame proof initially failed to synthesize `Decidable (FrameWF ...)`; explicitly unfolding that Boolean-check predicate repaired elaboration without a classical instance. Eight phase facts print `[propext, Quot.sound]`; `balanceProgram_lang` prints `[propext]`. No `sorry`, `admit`, native proof decision, custom axiom, Mathlib or production Lean metaprogram import was introduced.

Private exploratory evaluation confirmed preparation success for each language. A direct raw-decoder kernel preparation build was interrupted in favor of the reusable source/AST certificate rewrite. Two coarse symbolic constructor probes were also interrupted; neither supplies a proof, counterexample or impossibility result. Private candidate pre-seed machine literals, produced by evaluator `Repr`, passed separate **exact kernel equalities** against `targetPrepareConstructor 100` on the source-bound ASTs, with `[propext, Quot.sound]`. Those literals and exploratory metaprograms are not production source, not included in the certified inventory and not staged. Further constructor proof work should use smaller reset/helper/body boundaries; the current generic relation still lacks reached collections, defaults, loops, switch and other source forms. All requested universal proofs and checked whole-source grammar integration remain open.

Independent physical read-only final `codex exec` review used **gpt-6.1-sol/high**, session `01a133d0-7e97-73c0-9e5f-cb4741fd554d`, exit 0. It accepted the partial preparation/constructor-phase slice with no Critical, Important or Minor correctness defect, and **rejected Stage 3c completion** for the missing universal declarations/modules/target. It inspected all six source/test/policy postimages, both inventories, exact AST relocation, all nine phase facts, original wrapper preservation and the plan/refined spec. SHA-256 postimages matched before and after its review; the owner reconfirmed them afterward. It ran no Lean/Lake, axiom audit, runtime or hosted verification and made no edits. Owner commands below provide local kernel/audit evidence. No source postimage changed after final review.

Final Generated strict audit: **8,605 theorems / 11,812 declarations**, observed and allowed `[propext, Quot.sound]` (+23/+31 from base). The refreshed portable listing has exactly 8,605 unique entries, all checked against the strict whitelist. Foundation audit: 52 theorems, observed `[propext, Quot.sound]`, historical policy unchanged. World compatibility: 9,693 theorems / 13,442 declarations, historical observed/allowed `[propext, Quot.sound, Classical.choice]` reported separately. Inventory: 21 product modules, 37 test/audit modules, 64 certified closure modules, 28 test targets, 33 World inventory modules. Inventory mutation suite: 13 passed. Artifact checker: ten files passed; artifact self-tests: eight passed. Fixture literal SHA-256 remains `3006d2ece39affff067b4116fe16a3aeb61cff4fd9ba0dac2fba43fd574382c3`; toolchain remains `leanprover/lean4:v4.16.0`. Existing Bridge.Certificate unnecessarySimpa warning persists. Native-runtime and hosted-Linux verification were not rerun or inferred.

The final suite used serial actual subprocesses: twelve commands exited 0, and the missing correspondence target exited 1.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02CorrespondenceTest` | 1 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02SimulationTest kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldAudit` | 0 |

A subsequent serial `lake env lean` interface probe exited 1 for all five absent names: `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject` and `k02_balance_one_call`. This and the correspondence build are failed acceptance gates, not successful negative tests. Existing constructor/branch boundary facts remain finite evidence. No correspondence placeholder, weakened universal statement, task-complete ledger line, push or merge was added. The unfinished plan workspace is retained.

## Property assignment syntax and reverse adequacy — 2026-10-13

**T-398 and Tasks 2A/2B/3/4 remain IN_PROGRESS.** Physical owner resumed from `2b9997d0a7502e5b702fc7d06d597b205610c8bd` in the designated isolated `feat/t396-generated-correspondence` worktree and adopted the six modified Lean files explicitly named by Yong. No push, PR merge or unrelated-worktree change occurs in this checkpoint.

The source grammar now distinguishes writable local/property/index lvalues from internal field and tuple targets. A separate declarative WritableReceiverChain premise excludes TS optional receiver chains through property/index/call/non-null/cast paths, with a structurally proved Boolean check; index keys and call arguments remain independent expressions. Because parentheses are erased by the AST, parenthesized optional receivers are conservatively excluded from this partial writable slice. Assignment certificates check complete statement spelling, language terminator, both child spans, ordering, enclosing bounds/layout, independently validated lvalue and RHS expressions. Four actual TS/Python busy/context publication spans derive their low-level property assignments; wrong receiver/private field and aliased child-span mutations are rejected. These are owned statement fragments, not whole-file checked syntax or program uniqueness.

`TargetSimulation` adds ordered property assignment transitions, four ranked derivation cases, continuation runs and forward adequacy. `execPropertyAssign_sound` supplies reverse adequacy for `ScalarSyntax receiver` and `ScalarSyntax value`: every successful executor outcome has a derivation with rank below the supplied depth. Receiver-raised, RHS-raised, successful checker/own-object write and nonobject-TypeError paths retain the executor's exact order, heap, frame and control. The RHS is evaluated before invalid-receiver rejection. Outer target errors remain errors and cannot produce a successful derivation. Semantic rules contain primitive write/tag premises, not evaluator-success premises. `TargetSemantics` is unchanged.

RED: actual serial `lake build kadmosGeneratedK02SimulationTest` exited 1 at line 818 with unknown `execPropertyAssign_sound`; the failed elaboration temporarily reported `sorryAx` for its dependent test. GREEN: the repaired target exits 0 and the universal scalar-property-assignment test prints `[propext, Quot.sound]`. The final strict imported-environment scan has **8,707 theorems / 11,957 declarations**, observed [propext, Quot.sound], whitelist [propext, Quot.sound]. The refreshed portable listing has exactly 8,707 distinct theorem entries and every dependency was checked against that whitelist. The six source postimages contain zero `sorry`, `admit`, `sorryAx`, custom axioms or `Classical.choice`.

All fifteen final owner commands below ran as actual subprocesses, with exactly one `lake build` active at a time; each exited 0. Existing closed constructor/branch facts remain finite kernel evidence, not universal correspondence. The only replayed warning is the existing Bridge.Certificate unnecessarySimpa warning. Foundation and historical World policies remain unchanged; World may allow/report `Classical.choice` separately and is not the Generated certificate. Artifact/inventory mutations and audit rejection roots were rerun. Toolchain remains `leanprover/lean4:v4.16.0`; emitted artifacts and host contracts are unchanged. Separate JavaScript parser diagnostics rejected unparenthesized optional-chain assignment (node --check exit 1) and accepted the parenthesized receiver (exit 0); these are review reproductions, not emitted-checker runtime verification. Emitted native-runtime and hosted Linux checks were not rerun or inferred.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02SourceGrammarTest` | 0 |
| `lake build kadmosGeneratedK02SourceValidatorTest` | 0 |
| `lake build kadmosGeneratedK02StatementCertificateTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldAudit` | 0 |

The five universal declarations `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject`, and `k02_balance_one_call` remain open, along with checked whole-source admission and reached helper/loop/default semantics. No correspondence completion or merge readiness is claimed. Independent physical read-only CLI review and its test-driven repair are recorded below before this slice is committed.

Independent physical read-only `codex exec` review used **gpt-6.1-sol/medium**, session `01a13918-bf9d-7f90-abd0-1a9a10d54498`, exit 0. Verdict before repair: **REVISE**, zero Critical, one Important, zero Minor. It found that ordinary expression syntax admitted TS optional receiver chains as writable property/index targets, including `a?.b.c = true;`. The owner reproduced four kernel failures (property, index, call receiver chain and full assignment certificate), added the independent writable-chain grammar/check/soundness, and observed all four GREEN. Three positive kernel checks retain optional reads, index-key optional reads and call-argument optional reads; a declarative theorem excludes the invalid target. The fresh fifteen-command suite above then passed on the repaired six postimages. No new reviewer ACCEPT verdict is inferred from the owner's repair checks. No second review was dispatched for this test-backed repair.

Review limitations are resolved as follows: the previously pending portable listing and receipt are now refreshed from the repaired strict scan, with exactly 8,707 unique entries and dependency-set checks; emitted runtime/hosted Linux evidence remains unverified for this checkpoint; whole-source grammar and universal correspondence remain required open gates. These are not waived requirements or deferred minor findings. The repaired source postimages were held fixed through final verification. Existing Foundation audit reports 52 theorems and observed `[propext, Quot.sound]`; historical World compatibility reports 9,749 theorems / 13,541 declarations and observed/allowed `[propext, Quot.sound, Classical.choice]` separately. Inventory remains 21 product modules / 37 test-audit modules / 64 certified closure modules / 28 test targets / 33 World inventory modules.

## Stored-body and reached step-prefix equations — 2026-10-14

**T-398 and Tasks 2A/2B/3/4 remain IN_PROGRESS.** Continuation from local property checkpoint `03aed98bd3feecf30943db0dba94b941f3688d03`, in the same isolated branch/worktree. No push, PR merge or unrelated-worktree modification is part of this checkpoint.

`callClosure_eq_of_provided` and `evalStoredCall_eq` peel actual callee/argument/provided-parameter derivations from invocation, preserving the unknown stored body, all body control/error outcomes and the executor's exact depth edges. `callClosure` adds no fuel decrement. These equations have no body-success premise or conclusion. Primitive checker method binding allocates the actual receiver-bound closure.

Closed kernel certificates establish actual prepared constructor lookup for both languages, exclude the getter fallback, and certify qualified name and the single source parameter/default. Symbolic source-bound allocation plus callee/argument/binding paths then prove `targetConstruct_balance_body` for every bounded b: the canonical target constructor equals execution of the actual stored constructor body at depth 99, with exact fresh caller/parameter cells, captures and receiver. Reset/helper/body success, HeapWF preservation and BalanceRep of the final heap remain open.

`TargetSemantics` appends the physical canonical DEBIT payload/request/cell recipe, call expression and `targetStepWithFuel_eq_debitEntry`. Every prior declaration is byte-preserved. `targetStep_balance_entry` covers all safe signed n in both languages, leaves the actual generated step call on the RHS, and preserves source exceptions/outer target errors. It concludes no successful verdict and requires no fabricated preheap representation.

The prepared actual `step` closure's first busy-check statement is selected together with its untouched throw branch and remainder. A small closed kernel prefix check plus generic structural inversion proves the exact source-bound AST decomposition and excludes selector fallbacks. `balanceStep_idle_prefix` proves the reached idle branch at rank 2 from explicit receiver/idle preconditions; retained tests derive unfueled runs and execution at depth 3. This is the busy prefix only: it does not establish constructor preservation of the step method store or the amount guard/effect/bounds/invariant/finalizer paths.

RED interface probes for stored calls, actual constructor lookup/body entry, canonical DEBIT entry and source step prefix failed before implementation. GREEN production/test roots are included below. Several coarse prefix reductions were deliberately interrupted with owned CLI processes; private evaluator checks were diagnostics, and separate private TS/Python kernel probes completed. None of those interruptions or evaluator outputs is a universal execution proof or an impossibility result. Final evidence is the repaired certified production/test roots and strict scan below. No private IO/metaprogram probe is imported or staged.

Final strict Generated scan: **8,759 theorems / 12,041 declarations**, observed [propext, Quot.sound], allowed [propext, Quot.sound]. Exactly 8,759 unique portable theorem entries were extracted and every dependency set checked. Zero sorry/admit/sorryAx/custom axiom/Classical.choice in the slice; no policy weakening or toolchain upgrade. Historical World compatibility reports 9,819 / 13,643, observed [propext, Quot.sound, Classical.choice], allowed [propext, Quot.sound, Classical.choice], separately. Foundation gates passed with their existing policy unchanged. Emitted artifacts, compiler pin and runtime assumptions are unchanged; emitted native-runtime and hosted Linux checks were not rerun or inferred.

Nineteen final owner CLI commands ran serially (one Lake build active at a time); heavy TS/Python witnesses were built individually before aggregate roots. Every command exited 0.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldAudit` | 0 |

`targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject` and `k02_balance_one_call` remain open, as do independent checked whole-source admission and full reached-path/provenance obligations. No placeholder declaration, weakened universal theorem or fake correspondence target is added. This is a partial prerequisite checkpoint, not Stage 3c completion or merge readiness. Independent physical read-only `codex exec` review used **gpt-6.1-sol/medium**, session `01a13975-218d-7aa2-a1c1-e401fd7b11c6`, exit 0: **ACCEPT for this local partial checkpoint / REJECT Stage 3c completion**, zero Critical, Important or Minor findings. It checked source/spec/plan, byte preservation, forbidden tokens, all nineteen receipt logs, and exact portable-list/log dependency equality (8,759 unique entries). It ran no Lean/Lake/builds, runtime or network checks; serial execution and build-time postimage identity remain owner evidence. The six frozen source hashes are unchanged through verification/review. No code repair was requested. Native runtime, hosted Linux, checked whole-source admission, full constructor/branch paths and universal correspondence remain unestablished here.

## Constructor/reset structural execution checkpoint — 2026-10-14

**T-398 and Tasks 2A/2B/3/4 remain IN_PROGRESS.** Physical continuation from clean local `1bec7d9525bb7bac4f753e5581498527cda61a2a`, on the existing isolated `feat/t396-generated-correspondence` worktree. No push, merge of PR #5 or unrelated-worktree edits.

The complete small TS/Python constructor ASTs are kernel-certified against the actual stored parsed methods. Python's type-guard and all six initialization writes, reset call and final seed-copy nodes are retained. Canonical input-argument/object reads are proved for every symbolic b via generic allocation equations. Closed preparation facts plus preservation of older host cells establish actual unshadowed `type`/`dict` reads. `balanceConstructor_python_canonical_after_guard` executes the real exact-dict guard at depth 98 and reduces the constructor body to the untouched initialization/reset/copy suffix; it concludes no constructor success.

Actual prepared reset lookup, parameter/default and freshness are certified. Constructor-entry allocations preserve its physical method lookup and stored closure. `evalReceiverObjectCall_eq` and `balanceConstructor_reset_call_eq_body` bind the actual receiver/provided object parameter and expose the retained reset body. The latter starts at the canonical constructor frame; for Python it is explicitly not claimed to be the reached post-initialization reset invocation.

`balanceConstructor_ts_snapshots_eq` composes the TS body-at-99, expression statement at 98, reset call at 97, stored reset body at 96, idle guard and busy write to enter the actual reset snapshot/remainder at depth **94**. The real constructor seed-copy suffix still executes only after reset returns normally. The equation retains outer target errors, source exceptions and statement control. It has no reset/helper-success premise or conclusion.

Narrow certificates and generic structural inversion retain both languages' actual reset/step throw branches and entire remaining snapshot/try/helper ASTs. `balanceReset_idle_entry` and `balanceStep_idle_entry` peel the idle check and actual busy=true assignment at their exact sibling depths. `balanceSetBusy_preserves_bindings` establishes unchanged methods, closures, globals, cells and objects for that single write. It does not establish preservation by the full constructor or final `CanonicalGlobals`.

Generic equations expose one sequence edge, normal/exit behavior, expression-statement exception translation, short-circuit conjunction and false conditional. Two retained control regressions distinguish `StmtOutcome.control` from stale `frame.control` and require an actual returned head to skip an unsupported suffix. Original production declaration prefixes are byte-preserved versus `1bec7d9`; `TargetSemantics`, toolchain, emitted artifacts, reference models and host contracts are unchanged.

RED interface probes preceded this batch. Diagnostic failed elaborations and a terminated broad preparation-expansion probe (owned Lean exit 143) are retained privately and are not successful proof evidence. A generic host-type probe isolated the simplification bottleneck; controlled unfold/dsimp establishes the primitive equation without broad host matcher traversal. Final evidence below is against frozen five production/test postimages. No private IO/metaprogram probe is imported or staged.

Strict Generated audit: **8,841 theorems / 12,146 declarations**, observed and allowed **[propext, Quot.sound]** only. Exactly 8,841 unique portable theorem entries match the scan and every dependency set is checked. No sorry/admit/sorryAx/custom axiom/Classical.choice/native_decide/Mathlib is added to certified Generated modules; no policy relaxation or toolchain upgrade. Foundation gates retain their policy. Historical World compatibility is separate and may report its previously allowed Classical.choice.

The following nineteen physical owner commands ran sequentially, with one Lake build process at a time. All exited 0; heavy TS/Python witnesses were built individually before aggregate roots.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldAudit` | 0 |

Full constructor/reset/helper success, final HeapWF/BalanceRep and step-store/CanonicalGlobals preservation, request/sanitizer/guard/effect/bounds/invariant/finalizer paths, independent checked whole-source admission and all five universal declarations (`targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject`, `k02_balance_one_call`) remain open. The final universal interface probe exits 1 for those absent names: this is a failed acceptance gate, not a successful negative test. Existing bounded witnesses remain finite kernel facts. Native-runtime and hosted-Linux checks were not rerun or inferred. Stage 3c completion and merge readiness are not claimed. Independent read-only physical CLI review is recorded below before local checkpoint integration.

Independent physical read-only `codex exec` review used **gpt-6.1-sol / medium**, session `01a139ab-d34a-7af3-8775-ec967ff0ac70`, exit 0: **ACCEPT local partial checkpoint / REJECT Stage 3c completion**. Zero Critical, Important or Minor findings. The reviewer inspected all nineteen logs, five frozen source/test hashes, original production/test byte prefixes, plan/specs, control/default/fuel composition and exact equality of all 8,841 portable theorem names/dependency sets with the strict scan. It ran no Lean/Lake/build/runtime/network commands and made no edits. Physical serial execution and build-time identity are owner evidence supported by the inspected receipts. Frozen postimages remain unchanged after review; no code repair was requested. Foundation audit observed 52 theorems with [propext, Quot.sound] under its unchanged policy; historical World compatibility reports 9,917 theorems / 13,768 declarations under its existing [propext, Quot.sound, Classical.choice] policy, separately from Generated.

## Python constructor initialization, snapshots and seed copy — 2026-10-14

**T-398 and Tasks 2A/2B/3/4 remain IN_PROGRESS.** Physical owner continuation from clean local `43bf2b0277c848160750d90d409018f350bfee23` in the same isolated `5b89` / `feat/t396-generated-correspondence` workspace. No push, PR #5 merge or unrelated-worktree change. User-authorized read-only delegation performed source analysis only, without edits or builds; independent physical CLI review is recorded below before local integration.

`balanceConstructor_python_initialized` executes all six source writes in order: constructor seed null, `_INITIAL` state, allocated empty dict context, allocated empty list history, busy false and undo null. Its generic allocation/receiver/capture lemmas reproduce the actual constructor-entry recipe, avoiding normalization of the physical preparation during equality conversion. A closed kernel certificate identifies the actual captured `_INITIAL` cell **71**, its `"Ready"` value and its age below `nextCell`; the canonical read is then proved through both fresh caller/parameter cells and receiver binding for every symbolic b. This is a checked physical binding, not an assumed global `_INITIAL` (there is no such global binding).

`balanceConstructor_python_canonical_initialized` reaches the reset/copy sequence at depth **92** after the real guard and six writes. Initialization preserves methods, stored closures, globals and cells; it allocates two objects and does not assert final HeapWF or BalanceRep. The actual reset method's stored provenance and the constructor argument survive initialization. `balanceConstructor_python_reset_call_eq_body` binds reset from that reached heap, rather than reusing the earlier pre-initialization heap. `balanceConstructor_python_snapshots_eq` composes the exact depths **99 → 98 → 92 → 91 → 90 → 89 → 87**, retaining the actual reset snapshot/remainder at 87, closure result, all target errors/source exceptions, and the seed-copy suffix at 91. TS's existing snapshot entry remains 94. Neither equation assumes reset success.

Small closed kernel snapshot-spine checks certify four reset snapshot heads in each language and four TS/five Python step snapshot heads, including Python's additional undo snapshot. Generic constructive inversion retains the original head statements, rollback definition, protected body, catch type, binder, handler, cleanup and terminal empty tail. `balanceReset_snapshots_eq` and `balanceStep_snapshots_eq` expose one exact sibling edge without an outcome premise. `balanceReset_protected_shape` / `balanceStep_protected_shape` exclude selector fallbacks. `execTryCatchFinally_eq` and `execProtectedSyntax_eq` preserve the executor's caught-frame clearing and finalizer control override, restoring `handled.control` when cleanup is normal. These structural equations do not execute the remaining snapshot copies or generated try-body helpers.

`hostDict_balance` and `balancePython_context_copy` prove the actual shallow `dict(self.__context)` operation on a symbolic canonical balance object. `balanceConstructor_python_seed_copy` executes the real post-reset Python suffix at every budget ≥6 from explicit receiver/dict/context reads, allocates the copied context at `nextObject`, writes `__constructor_seed` and returns normal with the caller frame. Method/closure/global/cell bindings and context/history/busy fields are preserved by this suffix. Full reset execution must still establish those physical reads at the reached suffix; this is not a constructor-success or final-representation premise hidden inside a universal theorem. The algebraic allocation equations do not assert address freshness or HeapWF preservation for arbitrary malformed input heaps.

RED missing-interface probes preceded the initialization/snapshot and copy slices; the latter actual Lean invocation exited 1 for both missing names. Generic six-write and captured-cell proofs, complete canonical prefix/snapshot composition, structural/finalizer equations and seed-copy proofs passed isolated kernel probes before production integration. Several broad conversion/profile processes were deliberately terminated by their owner (exit 143); low-budget conversion timeouts and a discarded profile syntax probe are diagnostic failures, not successful verification or impossibility evidence. A private evaluator helped locate captured cell 71; the retained closed kernel theorem is the proof. Final equality composition uses generic receiver/capture recipes, explicit transitivity/congruence and generic call/control equations, rather than whole-program reduction. No private IO/profile/evaluator code is imported or staged. All pre-existing production declarations and the original constructor-test prefix are byte-preserved.

Final frozen-source serial verification and the strict axiom scan are recorded below. The five universal declarations (`targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject`, `k02_balance_one_call`) remain required open gates, along with complete reset/default/override/bounds/invariant execution, reached-path/provenance obligations, final HeapWF/BalanceRep and full-constructor step-store/CanonicalGlobals preservation, TS post-reset copy execution and independent checked whole-source admission. Structural snapshot selection is not dynamic branch correspondence. Separate emitted native-runtime and hosted-Linux checks are not inferred from these proofs or artifact/inventory checks. Stage 3c completion and merge readiness are not claimed.


The final frozen-source suite ran **nineteen owner CLI commands sequentially**, with one Lake build process at a time. All exited 0; four source/test SHA256 postimages were checked before each command and after the suite, and remain unchanged. Both heavy constructor and step witness languages were built individually before their aggregate roots.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build foundationsTest foundationsAudit foundationsAuditRejection` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosWorldAudit` | 0 |

Strict Generated scan: **8,912 theorems / 12,252 declarations**, observed and allowed **[propext, Quot.sound]** only. The refreshed portable listing contains exactly 8,912 unique names and every dependency set equals the emitted scan. Inventory is unchanged: 21 product modules / 37 test-audit modules / 64 certified closure modules / 28 test targets / 33 World inventory modules. All 13 inventory self-tests and 8 artifact self-tests pass. Foundation audit reports 52 theorems with observed [propext, Quot.sound] under its unchanged policy. Historical World compatibility is separate: 9,988 theorems / 13,874 declarations, observed/allowed [propext, Quot.sound, Classical.choice]. No Generated policy relaxation, toolchain upgrade, new import, custom axiom, Classical.choice, native_decide, sorry/admit/sorryAx or Mathlib addition. Existing emitted artifacts and host/serializer contracts are unchanged.

Two additional final **acceptance gates failed**, as required to report incomplete work: the universal interface probe exits 1 for all five absent theorem names, and `lake build kadmosGeneratedK02CorrespondenceTest` exits 1 because that target is absent. The four new initialization/snapshot interface names in the same probe resolve. These are open acceptance failures, not successful negative regressions. The nineteen existing suite passes do not establish universal correspondence, whole-source admission, final BalanceRep or merge readiness.


Independent physical read-only `codex exec` review used **gpt-6.1-sol / medium**, session `01a139e7-762f-73b0-9b60-56ead4a1d2d5`, exit0: **ACCEPT local partial Task2B/3 checkpoint / REJECT Stage3c completion and universal correspondence**. Zero Critical, Important or Minor defects within the scoped continuation. The reviewer inspected all nineteen logs, four frozen SHA256 postimages, original source/test prefixes, source/spec/plan, depth/control/finalizer/copy semantics, Init-only external import leaves, forbidden constructs and exact equality of the8,912 portable names/dependency sets with the strict scan. It made no edits/Git mutations and ran no Lean/Lake/build/target-runtime/network processes or further delegation. Physical serial execution and build-time identity remain owner evidence supported by the inspected receipts, rather than independently rerun verification. Four code/test postimages remain unchanged after review; no repair was requested. All completion blockers above remain unwaived. A bytecode cache produced by the artifact self-tests was removed and is not staged. No push or merge.

## Reset snapshot and publication execution — 2026-10-14

**T-398 and Tasks 2A/2B/3/4 remain IN_PROGRESS.** Continuation from clean local `830287a` on `feat/t396-generated-correspondence` in the existing isolated `5b89` worktree. No push or PR #5 merge is authorized for this batch.

The pinned TS/Python reset sources contain state, context and history snapshots followed by a `rollback` closure definition. Neither source has a `previousConstructorSeed` snapshot. This batch follows those actual four statements. Small closed `decide +kernel` checks inspect the three snapshot heads, rollback name/empty parameters, the 12-statement TS / 11-statement Python protected sequence, the first candidate-default copy, the four publication writes and the exact `busy = false` cleanup. Structural inversion retains the original rollback/protected/handler subtrees and excludes selector fallbacks. No helper is replaced by an ideal result.

`balanceReset_snapshot_execute` composes all four statements at depths `k+8 → k+4` and returns the actual protected suffix on a concrete heap/frame recipe. TS snapshots its class default context `{balance: 100}`; Python snapshots its initialized empty dict. Context/history copies allocate their own objects. The rollback closure captures the fresh snapshot cells, receives its own callable cell and is sealed only in TS. Generic four-sibling composition keeps the source statement abstract. The receiver, host-binding, object-shape, fresh-address and Python unbound-name conditions remain explicit physical premises; this theorem does **not** discharge every such condition for the full canonical constructor path. Reset-entry receiver binding is proved through the generic allocation recipe for every symbolic seed. The state-snapshot regression retains its physical receiver and Python address conditions.

`balanceConstructor_ts_seed_copy` executes the actual post-reset spread suffix at every depth `k+6`, allocates an ordinary object with the exact mutable/enumerable balance descriptor, and writes the copied constructor-seed address. It requires the live canonical context and physical freshness; it does not infer final HeapWF. The Python suffix theorem is preserved. `balanceReset_candidate_ts_execute` / `balanceReset_candidate_python_execute` execute the first protected defaults-copy statement from explicit captured/default-object reads. Python's real `_DEFAULTS` mapping proxy is copied to a mutable dict with no proxy prototype. Remaining override/type/descriptor loops, bounds and invariant helper calls have not been executed universally.

`balanceReset_publication_execute` executes the actual final four try-body writes from a physical candidate read and the Python `_INITIAL = Ready` read: state Ready, candidate context, allocated empty history and cleared undo. TS retains its `WorldState` cast node. Publication preserves the held busy bit; `balanceReset_cleanup_execute` separately executes the actual finalizer. These are conditional suffix proofs, not a proof that execution reaches publication after validation. No final `BalanceRep`, full reset-body totality or `targetConstruct_sound` is claimed.

The only interpreter-module additions are exact generic parameter-free function installation and TS empty-array allocation equations; existing executable definitions are unchanged. The function-installation recipe explicitly models the interpreter's cell/permission maps, including malformed duplicate-address input, without assuming address freshness. All pre-existing product/test declarations are unchanged. Toolchain, source pins, host contracts, Core/Distributed/legacy experiments and audit policies are unchanged. No source World interpreter call, native decision, new import, custom axiom or admitted proof is introduced.

The initial tracked missing-interface probe reports Lean errors for the three absent requested slice names. Disposable proof/conversion/progress diagnostics were interrupted and are not verification passes. The owner inspected a process sample that showed a large kernel type-checker cache being freed under memory paging; no diagnostic code or machine log is imported or staged.

All **60 final owner CLI commands exited 0**, sequentially, with one target per Lake build invocation. SHA256 postimages of the four code/test files were checked before and after every command and remain unchanged. This covers the full build, every named library/test/audit/rejection target (Foundation, Distributed, World, Bridge, Generated, Quorum and CAP), five individual heavy constructor/step language/case leaves, and four inventory/artifact checks. The initial four-command suite attempt stopped on a small test-wrapper reduction error; the complete successful run below supersedes it.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build foundationsTest` | 0 |
| `lake build foundationsAudit` | 0 |
| `lake build foundationsAuditRejection` | 0 |
| `lake build distributedTest` | 0 |
| `lake build distributedAudit` | 0 |
| `lake build distributedAuditRejection` | 0 |
| `lake build kadmosWorldTest` | 0 |
| `lake build kadmosWorldAudit` | 0 |
| `lake build kadmosWorldAuditRejection` | 0 |
| `lake build kadmosBridgeSyntaxTest` | 0 |
| `lake build kadmosBridgeCertificateTest` | 0 |
| `lake build kadmosBridgeFixturesTest` | 0 |
| `lake build kadmosBridgeAudit` | 0 |
| `lake build kadmosBridgeAuditRejection` | 0 |
| `lake build kadmosGeneratedK02LexerTest` | 0 |
| `lake build kadmosGeneratedK02SourceGrammarTest` | 0 |
| `lake build kadmosGeneratedK02SourceLexTest` | 0 |
| `lake build kadmosGeneratedK02SourceValidatorTest` | 0 |
| `lake build kadmosGeneratedK02SourceModuleTest` | 0 |
| `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` | 0 |
| `lake build kadmosGeneratedK02StatementCertificateTest` | 0 |
| `lake build kadmosGeneratedK02PythonLinesTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02ClosedProgramsTest` | 0 |
| `lake build kadmosGeneratedK02MachineTest` | 0 |
| `lake build kadmosGeneratedK02ExpressionParserTest` | 0 |
| `lake build kadmosGeneratedK02StatementParserTest` | 0 |
| `lake build kadmosGeneratedK02TSParserTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02ProgramParserTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSParseTest` | 0 |
| `lake build kadmosGeneratedK02BalancePythonParseTest` | 0 |
| `lake build kadmosGeneratedK02OrderTSParseTest` | 0 |
| `lake build kadmosGeneratedK02OrderPythonParseTest` | 0 |
| `lake build kadmosGeneratedK02CertificateTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSCertificateTest` | 0 |
| `lake build kadmosGeneratedK02BalancePythonCertificateTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosGeneratedK02JSONTest` | 0 |
| `lake build kadmosGeneratedK02RegexTest` | 0 |
| `lake build quorumTest` | 0 |
| `lake build quorumAudit` | 0 |
| `lake build quorumAuditRejection` | 0 |
| `lake build capTest` | 0 |
| `lake build capAudit` | 0 |
| `lake build capAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |

Strict Generated scan: **8983 theorems / 12361 declarations**, observed and allowed **[propext, Quot.sound]** only. The portable listing contains exactly 8983 unique names, and every axiom dependency set was checked equal to the scan. Independent physical read-only `codex exec` review used **gpt-6.1-sol / high**, session `01a13a56-a808-7b72-af8f-21a24604720c`, actual exit 0: **ACCEPT partial local checkpoint / NOT ACCEPTED full mission**. Zero Critical, Important or Minor findings. The reviewer confirmed unchanged old bodies/executable definitions, source order/depths, descriptor/prototype/capture behavior, explicit physical premises, cast/publication/busy cleanup, structural composition over opaque statements, meaningful budget/mutation regressions, Init-only/pinned/strict trust constraints, all four frozen signatures, all 60 serial owner exits, and exact equality of every one of the 8,983 names/dependency sets. It changed no files or Git/worktrees and ran no Lean/Lake, target runtime, network or delegated review.

Review scope rulings: independent reproduction was prohibited in this read-only sub-pass; the inspected actual owner CLI results remain verification evidence, while the reviewer supplies an independent static proof/scope audit. Native TS/Python and hosted-Linux correctness remain unsupported by this batch. Cost of these limits: no independent execution replication or new runtime/Linux guarantee is claimed; those gates must be satisfied separately before full integration. No fixes or deferred minors were requested. Code/test postimages remain unchanged after review.

The universal interface/correspondence acceptance gates remain open, as do independent whole-source grammar/soundness, canonical helper/global preservation, final heap representation and full universal branch correspondence. Finite kernel constructor/step witnesses, source-byte checks and these conditional execution equations do not establish those gates. No emitted native-runtime or hosted-Linux result is inferred from local Lean/inventory checks.

The two full-mission acceptance probes still exit 1: the five universal interface names are absent, and `kadmosGeneratedK02CorrespondenceTest` is an unknown target. The four newly checked reset/copy/publication/candidate names resolve in the same interface probe. These are open acceptance failures, separate from the 60 existing verification passes.

Foundation audit: 52 theorems, observed `[propext, Quot.sound]` under its unchanged historical whitelist. Distributed: 336 / 594; World: 10,060 / 13,984; Bridge: 1,691 / 2,163; their compatibility policies remain separate from the strict Generated policy. Quorum: 15 / 17; CAP: 63 / 157. Exact Generated inventory is unchanged (21 product, 37 test/audit, 64 closure modules, 28 targets, 33 World inventory modules); all 13 inventory and 8 artifact mutation tests pass. Artifact checks cover ten pinned files. The sole pre-existing linter warning is Bridge/Certificate.lean:185 (`unnecessarySimpa`); it is not introduced by this batch.

## Canonical reset physical premises and middle entry — 2026-10-14

Continuation from clean `83be4bf` on isolated `feat/t396-generated-correspondence`. This is a **partial T-398 checkpoint**, with no push or merge of PR #5. Universal `targetConstruct_sound`, final `BalanceRep`/HeapWF, full reset validation, universal step correspondence and independent whole-source soundness remain open.

The physical projection layer separates the supplied seed descriptor payload from allocation addresses, frames/captures, cells/globals, checker fields, object prototypes and the cell counter. Closed `decide +kernel` certificates check primitive observations at the zero-payload entry; structural payload-lookup and address-map lemmas lift them to **every `b : Int`**, including all `0 ≤ b ≤ 9007199254740991`. This does not claim that unbounded seeds pass allocation: actual `targetConstruct` reachability still uses the existing bounded-seed theorem. No reset-success, BalanceRep, assumed canonical host read, arithmetic enumeration or new axiom is a premise of this lift. Projections discard stored code before symbolic comparison; no proof evaluates full source AST subtrees by raw WHNF on symbolic `b`.

`balanceReset_canonical_snapshot_execute` discharges every physical premise of the four actual snapshot statements in TS and Python: context/history heap reads, object freshness, dict/clone hosts and fresh Python snapshot locals. The fourth statement installs the real rollback closure, preserving its source body and captured addresses. Python uses its actual post-initialization reset entry, including the six constructor writes; its snapshot context is empty, while TS snapshots default balance 100.

`balanceReset_canonical_candidate_execute` proves the actual defaults copy after those snapshots with no caller-supplied physical premise. TS reads live `contextDefaults` object 17. Python reads `_DEFAULTS` object 68, a frozen mapping proxy with prototype 67, then copies its own descriptors to an ordinary mutable dict. The candidate still contains default balance 100 here; supplied balance overlay is not yet proved.

`balanceReset_middle_shapes` certifies all middle sibling headers (TS 1..7, Python 1..6), retaining actual branch/loop bodies. It identifies seed selection/overlay entry, bounds helper call/rejection and invariant helper call/rejection without claiming their success. The first middle statement executes universally: TS allocates mutable `overrides = undefined`; Python selects the supplied object as `ctx`, bypassing the constructor-seed fallback. The canonical candidate frame retains the physical seed parameter. `balanceReset_canonical_body_prefix_execute` composes statements 0 and 1 at their actual sibling budgets and stops at the unchanged statement-2 continuation.

Additional source-selected presence lemmas choose TS's `else` branch and Python's `if` branch for a supplied object. The nested Python plain-dict guard is selected by a closed header certificate; its expression evaluates to false from explicit physical `ctx`, `type`, `dict` and object-kind premises. These conditional guard results do not discharge the canonical middle-entry host/heap premises or execute the overlay loop. TS's descriptor/prototype checks, supplied balance overlay, numeric/bounds helper, and invariant loop on `balance >= 0` / `balance <= 9007199254740991` remain unexecuted universally.

`balanceConstructor_canonical_snapshots_eq` advances both real constructors through the snapshots while retaining caller restoration and the actual post-reset seed-copy suffix. The regression `kadmos_generated_constructor_snapshot_continuation` connects this equation to the bounded-input `targetConstruct` API. Conditional `balanceReset_protected_normal` / `balanceReset_canonical_snapshots_normal` compose a supplied normal protected-body result with actual finally cleanup (`busy = false`). Body success and its postconditions are still explicit obligations; neither constructor success nor execution of the seed-copy suffix is claimed.

Only BalanceSimulation and the two requested regression roots change, plus this receipt and the exact dependency listing. Executable interpreter definitions, pinned source ASTs/bytes, imports, Core/Distributed/legacy experiments, audit policies and `leanprover/lean4:v4.16.0` are unchanged. The cell counter is projected from the same nine-field footprint; reads compare projected fields instead of whole machines, and protected-execution/parameter rewrites supply their arguments explicitly. The final composition section uses resource limits `maxHeartbeats = 10000000`, `maxRecDepth = 65536`, matching existing closed certificates; these do not change semantics or proof trust. No scratch module, extra completion wrapper, native decision, source World interpreter call, custom axiom or admitted proof is imported.

The baseline missing-interface probe exited 1 for the new canonical snapshot/candidate/middle names. Development probes and failed/interrupted integrations are not verification passes. Earlier suite attempts stopped on a missing final reflexivity step in the new API regression and on public-equation unfolding in the low-fuel regression; the complete final frozen-source suite below supersedes both attempts. Regressions cover symbolic inputs and actual bounded API entry, complete middle headers, wrong guard/helper names, source presence branches, a real one-argument type-host call, insufficient fuel, sibling budgets and conditional finally frame/control behavior.

All **60 final owner CLI commands exited 0**, serially, with one target per Lake build invocation. The three code/test SHA256 postimages were checked before and after each command and stayed unchanged. This includes the full build, all named library/test/audit/rejection targets, five individual heavy constructor/step language/case leaves, and four inventory/artifact checks.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02ConstructorProofPython` | 0 |
| `lake build kadmosGeneratedK02ConstructorProofTest` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofCases` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofTS` | 0 |
| `lake build HarmoniaTests.KadmosGeneratedK02BalanceStepProofPython` | 0 |
| `lake build kadmosGeneratedK02BalanceStepProofTest` | 0 |
| `lake build foundationsTest` | 0 |
| `lake build foundationsAudit` | 0 |
| `lake build foundationsAuditRejection` | 0 |
| `lake build distributedTest` | 0 |
| `lake build distributedAudit` | 0 |
| `lake build distributedAuditRejection` | 0 |
| `lake build kadmosWorldTest` | 0 |
| `lake build kadmosWorldAudit` | 0 |
| `lake build kadmosWorldAuditRejection` | 0 |
| `lake build kadmosBridgeSyntaxTest` | 0 |
| `lake build kadmosBridgeCertificateTest` | 0 |
| `lake build kadmosBridgeFixturesTest` | 0 |
| `lake build kadmosBridgeAudit` | 0 |
| `lake build kadmosBridgeAuditRejection` | 0 |
| `lake build kadmosGeneratedK02LexerTest` | 0 |
| `lake build kadmosGeneratedK02SourceGrammarTest` | 0 |
| `lake build kadmosGeneratedK02SourceLexTest` | 0 |
| `lake build kadmosGeneratedK02SourceValidatorTest` | 0 |
| `lake build kadmosGeneratedK02SourceModuleTest` | 0 |
| `lake build kadmosGeneratedK02PythonBooleanSyntaxTest` | 0 |
| `lake build kadmosGeneratedK02StatementCertificateTest` | 0 |
| `lake build kadmosGeneratedK02PythonLinesTest` | 0 |
| `lake build kadmosGeneratedK02SimulationTest` | 0 |
| `lake build kadmosGeneratedK02ClosedProgramsTest` | 0 |
| `lake build kadmosGeneratedK02MachineTest` | 0 |
| `lake build kadmosGeneratedK02ExpressionParserTest` | 0 |
| `lake build kadmosGeneratedK02StatementParserTest` | 0 |
| `lake build kadmosGeneratedK02TSParserTest` | 0 |
| `lake build kadmosGeneratedK02SemanticsTest` | 0 |
| `lake build kadmosGeneratedK02ProgramParserTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSParseTest` | 0 |
| `lake build kadmosGeneratedK02BalancePythonParseTest` | 0 |
| `lake build kadmosGeneratedK02OrderTSParseTest` | 0 |
| `lake build kadmosGeneratedK02OrderPythonParseTest` | 0 |
| `lake build kadmosGeneratedK02CertificateTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSCertificateTest` | 0 |
| `lake build kadmosGeneratedK02BalancePythonCertificateTest` | 0 |
| `lake build kadmosGeneratedK02BalanceTSStepTest` | 0 |
| `lake build kadmosGeneratedK02Audit` | 0 |
| `lake build kadmosGeneratedK02AuditRejection` | 0 |
| `lake build kadmosGeneratedK02JSONTest` | 0 |
| `lake build kadmosGeneratedK02RegexTest` | 0 |
| `lake build quorumTest` | 0 |
| `lake build quorumAudit` | 0 |
| `lake build quorumAuditRejection` | 0 |
| `lake build capTest` | 0 |
| `lake build capAudit` | 0 |
| `lake build capAuditRejection` | 0 |
| `python3 scripts/check_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_audit.py` | 0 |
| `python3 scripts/check_kadmos_generated_k02_artifacts.py` | 0 |
| `python3 scripts/test_kadmos_generated_k02_artifacts.py` | 0 |

Strict Generated audit: **9148 theorems / 12578 declarations**, observed and allowed **[propext, Quot.sound]** only. The portable listing contains exactly 9148 unique names and every dependency set equals the actual scan. No admitted or unreported protocol axiom is accepted. Independent physical read-only `codex exec` review used **gpt-6-astra / high**, session `01a13aaa-e72a-7720-bf8e-606a97477801`, actual exit **0**: **ACCEPT partial checkpoint / NOT ACCEPTED full mission**, with **zero Critical, Important or Minor findings**. It independently confirmed all three frozen source/test hashes, all 60 serial exit-0 records/logs, and exact equality of every theorem name and dependency set. It performed no file/Git mutation, Lean/Lake or target-runtime execution, network or delegation.

The final full-mission acceptance probes still exit **1**: `targetConstruct_sound`, `step_guard_reject`, `step_accept`, `step_bounds_reject` and `k02_balance_one_call` remain absent, and `kadmosGeneratedK02CorrespondenceTest` is an unknown target. The nine new canonical/middle/guard interfaces in that probe resolve. These are open acceptance failures, separate from the 60 passing existing verification commands; no correspondence target stub was added.

Foundation audit: 52 theorems, observed `[propext, Quot.sound]` under its unchanged historical whitelist. Compatibility counts: Distributed 336 / 594; World 10,224 / 14,200; Bridge 1,691 / 2,163; Quorum 15 / 17; CAP 63 / 157. Their policies remain separate from the strict Generated policy. Exact Generated inventory is unchanged (21 product, 37 test/audit, 64 closure modules, 28 targets, 33 World inventory modules). All 13 inventory and 8 artifact mutation tests pass; artifact checks cover ten pinned files. The pre-existing Bridge/Certificate.lean:185 `unnecessarySimpa` warning is unchanged. No native TS/Python or hosted-Linux guarantee is inferred from this batch's local Lean/inventory evidence.

Review scope rulings: independent execution reproduction remains outside this static sub-pass; the actual owner CLI/kernel results are the verification evidence. Native TS/Python correctness and hosted-Linux portability also remain outside this batch. Cost of these limits: no independent reproduction, native-runtime or Linux guarantee is claimed; those require separate evidence before full integration. No fixes or deferred minors were requested. All five reviewed postimages matched before this review-metadata update; the three compiled source/test postimages still match the final 60-command run. T-398 remains IN_PROGRESS, and PR #5 remains unmergeable.
