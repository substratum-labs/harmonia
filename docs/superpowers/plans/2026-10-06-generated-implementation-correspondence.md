# T-396 Generated Implementation Correspondence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. Native physical CLI execution is already selected; no virtual subagent workflow. Product execution begins only after parent-owned actual Grok preflight ACCEPT.

**Goal:** Prove that default construction and state/context getters parsed from actual emitted TypeScript and Python checkers correspond to initialization of two Stage3b certified Harmonia worlds.

**Architecture:** Preserve Stage3b's source-bound `World`. Export exact compiler outputs; a Lean checker consumes complete emitted source strings and extracts a restricted constructor/getter target program. An independent target machine executes the parsed selected operations; Lean proves its successful initial result and getter outputs correspond to `initialize`. The step pipeline is exercised physically but remains unproved.

**Tech Stack:** Lean 4.16.0/Init/Lake, pinned Kadmos TypeScript compiler, Node 26 local probe, Python 3, existing Python inventory scripts and Linux CI.

**Spec:** `docs/superpowers/specs/2026-10-06-generated-implementation-correspondence-design.md`

## Global Constraints

- Keep `lean-toolchain` exactly `leanprover/lean4:v4.16.0`; use Init only, no new dependencies, no `native_decide`, `sorry`, `admit`, `sorryAx` or custom certified axioms.
- Preserve Core, Distributed, legacy, World, Interpreter and Bridge semantics; no Kadmos or other-repository edits.
- Use the clean pinned read-only Kadmos commit `fda8c6e42825b35afe5484a4af9d84d9d206ba9a` for local output regeneration; hosted Linux uses tracked artifacts.
- Run Lake serially. Keep generated binaries, `.lake/`, caches, logs and credentials out of Git.
- A successful certificate proves only the parsed constructor/getter fragment under independent Lean target semantics. Host interpreter/serialization assumptions and the unproved `step` pipeline must be stated in every report.
- The old Kadmos application inventory scans all `Harmonia/Applications`; register new sources there. Do not broaden the Bridge selector to the whole application namespace. Keep Foundation 52 and Distributed 336/594 separate; do not assert fixed old application/Bridge totals.

## Review Focus

1. A changed initial phase/default or omitted bounds/invariant call must reject certification, including when the source digest is updated (Task 2 and 3 hostile tests).
2. Python JSON double quoting and TS JSON literal escaping must preserve exact keys, order and safe integer tokens (Task 1 and 2).
3. A getter returning a live context object rather than a copy must reject or fail its copy-semantic test (Task 2 and 3).
4. An opaque step-section mutation must reject the whole-file shape, while the report still declines any step theorem (Task 2 and 4).
5. A malformed fixture with duplicate/unknown fields or unsafe number must fail before theorem use, while an accepted balance/order constructor remains nonvacuous (Task 1 and 3).

---

## File map and stable interfaces

- `tools/export_kadmos_generated.mjs`: pinned-source compiler runner and exact UTF-8 TS/Python output plus Lean-source-string fixture writer; reuses Stage3b's YAML/parsed/profiles; never writes Kadmos.
- `conformance/kadmos-generated/{balance,order_phase}/{world_checker.ts,ports.d.ts,world_checker.py,ports.py}` and `conformance/kadmos-generated/provenance.json`: exact tracked generated outputs and identities.
- `Harmonia/Applications/Kadmos/Generated/TargetSyntax.lean`: `TargetLang`, `TargetOp`, `TargetProgram`, restricted whole-file parser and strict embedded data decode.
- `Harmonia/Applications/Kadmos/Generated/TargetSemantics.lean`: independently defined target store, constructor/getter execution and operation lemmas.
- `Harmonia/Applications/Kadmos/Generated/ArtifactCertificate.lean`: Bridge binding and simulation theorem.
- `Harmonia/Applications/Kadmos/Generated/Fixtures.lean`: exact source strings and closed accepted/hostile certificates.
- `HarmoniaTests/KadmosGeneratedSyntax.lean`, `KadmosGeneratedSemantics.lean`, `KadmosGeneratedCertificate.lean`, `KadmosGeneratedAxiomAudit.lean`, `KadmosGeneratedAuditRejection.lean`, `KadmosGeneratedRejection/{Unused,Unsafe}.lean`: test, audit and isolated traps.
- `scripts/check_kadmos_generated_artifacts.py`, `scripts/test_kadmos_generated_artifacts.py`, `scripts/check_kadmos_generated_audit.py`, `scripts/test_kadmos_generated_audit.py`: exact byte and source/target inventory gates.
- `lakefile.lean`, `HarmoniaTests/AuditPolicy.lean`, `Harmonia/Applications/Kadmos.lean`, `.github/workflows/foundations.yml`, `docs/verification/2026-10-06-generated-implementation-correspondence.md`: root and evidence integration. The umbrella import is added only if needed for the old application's real closure; audit manifests are updated for exact new modules.

## Task 1: Reproducible emitted program evidence

**Files:** create exporter, four files per fixture, provenance and artifact checker/test at the paths above; update verification record.

**Interfaces:** consumes existing `parseWorldSpec`, `compileWorldSpec`, `compileWorldSpecPython` and Stage3b fixture paths. Produces exact `world_checker.ts/.py` UTF-8 bytes and a deterministic Lean `String` literal for each; `check_artifacts(root: Path, kadmos: Path | None) -> dict[str,str]` verifies bytes and hashes. This task creates no Lean proof.

- [ ] **Step 1 RED:** Add Python artifact tests that mutate one byte of each output, edit an embedded default, duplicate a JSON key, use `-0`, and change a port file; run `python3 -m unittest scripts/test_kadmos_generated_artifacts.py` and observe failure because checker is absent.
- [ ] **Step 2 GREEN:** Compile pinned Kadmos with its installed `node_modules/.bin/tsc -p ... --outDir /private/tmp/...`; call both compiler functions on the actual Stage3b YAML parser results. Write deterministic exact outputs and a manifest with Kadmos commit, fixture SHA-256, parser output SHA-256, compiler-output SHA-256, exporter version and command. Check canonical complete source-string escaping round trip against UTF-8 bytes; do not export a pre-decoded target AST.
- [ ] **Step 3:** Run the Python artifact tests and physical `--kadmos --check` plus hermetic tracked-output `--check`, requiring all exit 0. In private tmp execute balance 30/130/20 and order STEP through emitted TS and Python; record full allowed/code/state/context/directive projections and exit statuses. Their finite equality is evidence only.
- [ ] **Step 4:** Commit Task 1 paths only after a clean status/diff review; do not stage private tmp output.

## Task 2: Parse selected emitted target operations and define target execution

**Files:** create `TargetSyntax.lean`, `TargetSemantics.lean`, `HarmoniaTests/KadmosGeneratedSyntax.lean`, `HarmoniaTests/KadmosGeneratedSemantics.lean`; add two test targets to `lakefile.lean`.

**Interfaces:**

```lean
def parseGenerated (lang : TargetLang) (source : String) : Except ParseError TargetProgram
def targetConstruct (program : TargetProgram) : Except TargetError TargetStore
def targetGetState (program : TargetProgram) (store : TargetStore) : String
def targetGetContext (program : TargetProgram) (store : TargetStore) : List (String × Int)
```

`TargetProgram` contains ordered embedded states/context/transition/invariants and parsed constructor/getter `TargetOp`s; unknown sections are opaque but must equal the pinned template bytes. `targetConstruct` evaluates target operations from an empty store, with its own bounds/invariant expression evaluator and ordered map lookup, never invoking `initialize`, `interpret` or Bridge `sourceEval`.

- [ ] **Step 1 RED:** Add closed `by decide +kernel` probes for both exact source strings, their parsed initial phase/defaults and getters; add mutations of `#state`, `#context`, `getContext` spread, `_INITIAL`, `_DEFAULTS`, `dict(self.context)`, and opaque step text. Run `lake build kadmosGeneratedSyntaxTest`; require missing declarations/failing expectations.
- [ ] **Step 2 GREEN:** Implement complete-source recognizer with anchored fixed sections, a restricted JSON/string parser for actual TS literal and Python doubly quoted JSON, and explicit selected-statement extraction. Reject unconsumed bytes, duplicate keys, unsupported escapes/numbers/order/operations. Do not treat a successful SHA check or externally supplied AST as parser success.
- [ ] **Step 3 RED/GREEN:** Add and run target-machine tests for balance Ready/100, order A/(1,0), ordered context entries, required constructor checks, and getter copy behavior. Implement target store and operations, independent integer expression evaluation of initial invariants (`balance >= 0`, `state == 'B' => y == x`) and bounded defaults. `lake build kadmosGeneratedSyntaxTest kadmosGeneratedSemanticsTest` must pass; temporarily change a selected parsed operation to confirm a relevant test fails, then restore.
- [ ] **Step 4:** Commit only these modules/tests/targets after reviewing that no operation implementation calls the reference evaluator.

## Task 3: Bridge certificate and nonvacuous kernel theorem

**Files:** create `ArtifactCertificate.lean`, `Fixtures.lean`, `HarmoniaTests/KadmosGeneratedCertificate.lean`; update product imports only as required by closure.

**Interfaces:**

```lean
def checkGenerated (lang : TargetLang) (source : String)
    (raw : Bridge.RawWorld) (w : World p v f a) : Except CertError TargetProgram
def targetRel (w : World p v f a) (s : State p v) (store : TargetStore) : Prop
-- theorem checkGenerated_initial_simulation has the statement in the design.
```

`checkGenerated` must require `Bridge.checkBridge raw w = .ok w` and exact indexed equality of embedded source data with the checked raw projection; no candidate target store is supplied by the exporter. The theorem derives successful target construction and getter observations from successful check and `initialize w = .ok s`.

- [ ] **Step 1 RED:** Add failing closed probes for both fixture/language pairs, an independently mutated world literal with recomputed provenance, altered initial phase/default and removed invariant call. Add explicit concrete `initialize` equalities for both certified worlds; run `lake build kadmosGeneratedCertificateTest` and observe failure before certificate implementation.
- [ ] **Step 2 GREEN:** Prove parser extraction facts and target-construction simulation by induction on parsed operations and indexed lists, with safe-int arithmetic (`omega` as needed); prove `targetRel`, state/context getter and copy results. Use `by decide +kernel` only for closed artifact checks. Never make target semantics an alias of `initialize`/`interpret`.
- [ ] **Step 3:** Run `lake build kadmosGeneratedCertificateTest`; prove four fixture certificates plus Ready/100 and A/(1,0) getter theorems. Mutation of a selected initializer/getter or embedded data must fail `checkGenerated` even when its external manifest is recomputed. State the theorem's exact source-string and host-semantics premises in the test comments and verification record.
- [ ] **Step 4:** Commit Task 3 modules/tests after checking proof dependencies and no forbidden tokens.

## Task 4: Separate certified audit, inventories and Linux gate

**Files:** create Generated audit and rejection Lean modules, four Python policy/artifact scripts if not already created, update `lakefile.lean`, `AuditPolicy.lean`, old Kadmos inventory manifest, `.github/workflows/foundations.yml`, verification record.

**Interfaces:** exact targets `kadmosGeneratedSyntaxTest`, `kadmosGeneratedSemanticsTest`, `kadmosGeneratedCertificateTest`, `kadmosGeneratedAudit`, `kadmosGeneratedAuditRejection`. `check_kadmos_generated_audit.py` composes the unchanged old application audit, inventories only exact Generated products/probes/audit, checks imports/root closure/trap isolation and forbidden source tokens. Its declaration selector is namespace **or source module** for those exact files, so unused/escaped axioms cannot hide.

- [ ] **Step 1 RED:** Add inventory mutation tests for a nested unregistered Generated file, missing import, extra certified root, unused axiom, escaped unsafe axiom, trap imported by a certified root, and whole-application namespace selection. Run `python3 scripts/check_kadmos_generated_audit.py --self-test`; see intentional initial failures.
- [ ] **Step 2 GREEN:** Register exact source manifests and new Lake roots; add trap-free certified and isolated rejection roots. Run new inventory self-tests/checks and all old inventory suites. Foundation and Distributed counts remain separately reported; update old application closure only for genuine new imports.
- [ ] **Step 3:** Add Linux CI steps after Bridge checks, serially: artifact self-test/check, source inventory self-test/check, three tests, certified audit, fresh `lake env lean HarmoniaTests/KadmosGeneratedAxiomAudit.lean`, isolated rejection target. No sibling checkout requirement or policy weakening.
- [ ] **Step 4 verification:** Run `lake build`, then all 14 pre-existing dedicated targets and five new targets **serially**; run old/new inventories and artifact checks; run fresh audits where source closure changed. Record command, exit code, theorem/declaration counts and actual axiom sets. Confirm no `sorry`/`admit`/`sorryAx`/unreported axiom in certified roots; verify TS/Python physical examples and hostile source mutation, `git diff --check`, no untracked generated binary/cache, and clean pinned Kadmos.
- [ ] **Step 5:** Commit documentation and gate files locally; perform an independent physical review through parent coordination before any integration. Parent owns Grok verdict, hosted Linux, publication and merge. Report the narrow certified theorem and every remaining unproved bridge.

## Self-review and execution handoff

The four tasks cover exact compiler provenance, source-string parsing, independent target construction/read semantics, Bridge simulation and isolated audit/CI. Task interfaces use `TargetProgram`/`TargetStore` consistently. The plan intentionally does not implement `step`; physical step vectors are named finite evidence. Current Stage3b certificate covers exactly the balance/order worlds, so the constructor theorem has concrete witnesses and no vacuous malformed-world theorem. The chief residual risk is that modeled target operations have no kernel proof of Node/CPython semantics; an external comparison remains a trust boundary. Parent sends the full design to physical Grok and independently judges ACCEPT/REVISE before any task above starts.
