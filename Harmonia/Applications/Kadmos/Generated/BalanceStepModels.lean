import Harmonia.Applications.Kadmos.Generated.BalanceSimulation

/-! Physical models and source opening for one canonical DEBIT call.
Native diagnostics proposed the data; the execution proofs check it in Lean.
The original constructor heap, AST bodies and every intermediate allocation
are retained. Source prefix selectors preserve their untouched continuation. -/
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option smartUnfolding false

-- Initial physical bridge; these projections do not inspect either numeric input.
theorem balanceStep_canonical_method (lang : TargetLang) (b : Int) :
    (balanceCanonicalConstructed lang b).classMethods.lookup "step" =
      some (if lang == .ts then 11 else 19) := by
  cases lang <;> rfl

def balanceStepCanonicalUnbound (lang : TargetLang) (b : Int) : TargetClosure :=
  ((closureAt (balanceCanonicalConstructed lang b) (if lang == .ts then 11 else 19)).toOption).getD
    ⟨"", [], [], .empty, [], none⟩

theorem balanceStep_canonical_closure (lang : TargetLang) (b : Int) :
    closureAt (balanceCanonicalConstructed lang b) (if lang == .ts then 11 else 19) =
      .ok (balanceStepCanonicalUnbound lang b) := by
  cases lang <;> rfl

theorem balanceStep_canonical_body (lang : TargetLang) (b : Int) :
    (balanceStepCanonicalUnbound lang b).body =
      balanceSourceBody (balanceProgram lang) "WorldChecker.step" := by
  cases lang <;> rfl

def balanceStepCanonicalBound (lang : TargetLang) (b n : Int) : TargetMachine × TargetFrame :=
  let e := debitCallEntry lang (balanceCanonicalConstructed lang b) n
  let c := { balanceStepCanonicalUnbound lang b with receiver := some e.1.checkerRef }
  let m := (allocClosure e.1 c).1
  let f : TargetFrame := ⟨c.qualifiedName, [], [], c.captures, c.receiver, .normal⟩
  ((allocCell m (.object ((balanceCanonicalConstructed lang b).nextObject + 1)) true).1,
    { f with locals := [("request", m.nextCell)] })

theorem balanceStep_canonical_call_open (lang : TargetLang) (b n : Int) (k : Nat) :
    evalExpr (k + 5) (balanceProgram lang)
      (debitCallEntry lang (balanceCanonicalConstructed lang b) n).1
      (debitCallEntry lang (balanceCanonicalConstructed lang b) n).2
      (debitCallExpression lang) = (do
        let result ← execStmt (k + 4) (balanceProgram lang)
          (balanceStepCanonicalBound lang b n).1 (balanceStepCanonicalBound lang b n).2
          (balanceStepCanonicalUnbound lang b).body
        closureResult lang result) := by
  let caller := (debitCallEntry lang (balanceCanonicalConstructed lang b) n).1
  let frame := (debitCallEntry lang (balanceCanonicalConstructed lang b) n).2
  let method := { balanceStepCanonicalUnbound lang b with receiver := some caller.checkerRef }
  let bound := (allocClosure caller method).1
  have hr : localValue caller frame (if lang == .ts then "this" else "self") =
      .ok (.object caller.checkerRef) := by cases lang <;> rfl
  have hf : readCheckerField caller "step" = .error (.unboundLocal "step") := by cases lang <;> rfl
  have hm : caller.classMethods.lookup "step" = some (if lang == .ts then 11 else 19) :=
    balanceStep_canonical_method lang b
  have hc : closureAt caller (if lang == .ts then 11 else 19) =
      .ok (balanceStepCanonicalUnbound lang b) := by cases lang <;> rfl
  have hRead : readPropertyValue (balanceProgram lang).lang caller
      (.object caller.checkerRef) "step" = .ok ⟨bound, .ok (.closure caller.nextClosure)⟩ := by
    rw [balanceProgram_lang]
    exact readCheckerMethod_bound hf hm hc
  have he : DepthDerivesExpr (balanceProgram lang) caller frame
      (.property (.local (if lang == .ts then "this" else "self")) "step")
      ⟨bound, .ok (.closure caller.nextClosure)⟩ 1 := .property (.localRead hr) hRead
  have hv : localValue bound frame "request" =
      .ok (.object ((balanceCanonicalConstructed lang b).nextObject + 1)) := by
    cases lang <;> rfl
  have ha : DepthDerivesArgs (balanceProgram lang) bound frame
      (.sequence (.local "request") .empty)
      ⟨bound, .ok [.object ((balanceCanonicalConstructed lang b).nextObject + 1)]⟩ 1 :=
    .cons (.localRead hv) .empty
  have hs : closureAt bound caller.nextClosure = .ok method := by
    simp [bound, closureAt, allocClosure, List.lookup]
  have hpShape : method.params = [⟨"request", none⟩] := by cases lang <;> rfl
  have hp : DepthBindsProvided (balanceProgram lang) bound (closureFrame method)
      method.params method.pythonDefaults [.object ((balanceCanonicalConstructed lang b).nextObject + 1)]
      (balanceStepCanonicalBound lang b n).1 (balanceStepCanonicalBound lang b n).2 1 := by
    rw [hpShape]
    exact .cons (by simp) .empty
  have hk : 1 < k + 4 := Nat.lt_of_lt_of_le (by decide : 1 < 4) (Nat.le_add_left 4 k)
  have h := evalStoredCall_eq he ha hs hp (k := k + 4) hk hk hk
  simpa only [balanceProgram_lang, debitCallExpression] using h

theorem balanceStep_stored_source (lang : TargetLang) :
    (balanceStoredStep lang).2.body = balanceSourceBody (balanceProgram lang) "WorldChecker.step" := by
  cases lang <;> unfold balanceStoredStep balanceStepLookup balancePreparation
  · rw [balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; with_unfolding_all rfl
  · rw [balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; with_unfolding_all rfl

theorem balanceStep_canonical_stored (lang : TargetLang) (b : Int) :
    (balanceStepCanonicalUnbound lang b).body = (balanceStoredStep lang).2.body :=
  (balanceStep_canonical_body lang b).trans (balanceStep_stored_source lang).symm

/-- Source siblings before the protected step body. -/
def balanceStepSnapshots (lang : TargetLang) : TargetStmt := restStmt (balanceStepAfterBusy lang)
def balanceStepProtected (lang : TargetLang) : ProtectedSyntax :=
  protectedSyntax (firstStmt (dropStmts (if lang == .ts then 4 else 5) (balanceStepSnapshots lang)))
def takeStepStmts : Nat → TargetStmt → TargetStmt
 | 0, _ => .empty
 | k + 1, .sequence head tail => .sequence head (takeStepStmts k tail)
 | _, _ => .empty

def balanceStepSnapshotStart (lang : TargetLang) (b n : Int) : TargetMachine × TargetFrame :=
 let e := balanceStepCanonicalBound lang b n
 (balanceSetBusy e.1 true, e.2)

-- Native diagnostics use this to discover literal postheaps; certificates below must prove them.
def balanceStepSnapshotRun (lang : TargetLang) (b n : Int) : Except TargetError StmtOutcome :=
 let e := balanceStepSnapshotStart lang b n
 execStmt 97 (balanceProgram lang) e.1 e.2
   (takeStepStmts (if lang == .ts then 4 else 5) (balanceStepSnapshots lang))
def balanceStepPrefixRun (lang : TargetLang) (b n : Int) : Except TargetError StmtOutcome := do
 let s ← balanceStepSnapshotRun lang b n
 execStmt (if lang == .ts then 91 else 90) (balanceProgram lang) s.machine s.frame
   (takeStepStmts (if lang == .ts then 18 else 21) (balanceStepProtected lang).body)

def balanceStepTsSnapshots (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .ts b
 { m with
    cells := [(74, TargetValue.closure 20),
 (73, TargetValue.object 49),
 (72, TargetValue.object 48),
 (71, TargetValue.string "Ready"),
 (70, TargetValue.object 47),
 (69, TargetValue.object 47)] ++ m.cells
    objects := [(49, ⟨ObjectKind.jsArray, some 0, [], [], [], false, false⟩),
 (48, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (47, ⟨ObjectKind.jsOrdinary, some 0, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 46), none, none, true, true, true⟩)], [], [], false, false⟩),
 (46, ⟨ObjectKind.jsOrdinary, some 0, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(20, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rollback", [("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (19, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step", [("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩)] ++ m.closures
    generators := [] ++ m.generators
    writableCells := [(74, false),  (73, false),  (72, false),  (71, false),  (70, true),  (69, true),  (68, false),  (67, false),  (66, false),  (65, false),  (64, false),  (63, true),  (62, true),  (61, false),  (60, false),  (59, false),  (58, true),  (57, false),  (56, true),  (55, false),  (54, false),  (53, true),  (52, false),  (51, true),  (50, false),  (49, false),  (48, true),  (47, false),  (46, false),  (45, false),  (44, true),  (43, true),  (42, false),  (41, false),  (40, true),  (39, true),  (38, true),  (37, false),  (36, false),  (35, false),  (34, false),  (33, true),  (32, false),  (31, false),  (30, false),  (29, false),  (28, false),  (27, false),  (26, true),  (25, false),  (24, false),  (23, false),  (22, false),  (21, false),  (20, true),  (19, true),  (18, true),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 75
    nextObject := 50
    nextClosure := 21
    checker := { state := "Ready",   context := 23,   history := 44,   undo := none,   constructorSeed := some 45,   busy := true,   instanceAttrs := [] } }

def balanceStepTsSnapshotsFrame : TargetFrame := { qualifiedName := "WorldChecker.step",   remaining := [],   locals := [("rollback", 74),              ("snapshotHistory", 73),              ("snapshotContext", 72),              ("snapshotState", 71),              ("request", 70)],   captures := [("sanitizeWorldPayload", 17),                ("deepFreezeWorld", 16),                ("evaluateWorld", 15),                ("booleanWorld", 14),                ("transitionDefinitions", 13),                ("invariantDefinitions", 12),                ("stateDefinitions", 11),                ("contextDefinitions", 10),                ("contextDefaults", 9),                ("world", 8),                ("nodeTypes", 7)],   receiver := some 1,   control := ControlResult.normal }

def balanceStepTsPrefix (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .ts b
 { m with
    cells := [(95, TargetValue.closure 24),
 (94, TargetValue.object 14),
 (93, TargetValue.object 14),
 (92, TargetValue.closure 22),
 (91, TargetValue.object 57),
 (90, (TargetValue.number (NumberTag.jsNumber) n)),
 (89, (TargetValue.number (NumberTag.jsNumber) n)),
 (88, TargetValue.object 55),
 (87, TargetValue.string "amount"),
 (86, TargetValue.object 53),
 (85, TargetValue.object 0),
 (84, TargetValue.object 52),
 (83, TargetValue.number (NumberTag.jsNumber) 0),
 (82, TargetValue.object 46),
 (81, TargetValue.object 53),
 (80, TargetValue.null),
 (79, TargetValue.string "DEBIT"),
 (78, TargetValue.object 51),
 (77, TargetValue.undefined),
 (76, TargetValue.object 50),
 (75, TargetValue.closure 21),
 (74, TargetValue.closure 20),
 (73, TargetValue.object 49),
 (72, TargetValue.object 48),
 (71, TargetValue.string "Ready"),
 (70, TargetValue.object 47),
 (69, TargetValue.object 47)] ++ m.cells
    objects := [(59, ⟨ObjectKind.jsOrdinary, some 0, [], [], [], false, false⟩),
 (58, ⟨ObjectKind.jsOrdinary, some 0, [("eventPayload", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (57, ⟨ObjectKind.jsOrdinary, some 0, [("step", ⟨some (TargetValue.number (NumberTag.jsNumber) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (56, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (55, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (54, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "amount"], [], false, false⟩),
 (53, ⟨ObjectKind.jsNullPrototype, none, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (52, ⟨ObjectKind.jsSet, some 0, [], [], [TargetValue.object 46], false, false⟩),
 (51, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some (TargetValue.object 46), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (50, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (49, ⟨ObjectKind.jsArray, some 0, [], [], [], false, false⟩),
 (48, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (47, ⟨ObjectKind.jsOrdinary, some 0, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 46), none, none, true, true, true⟩)], [], [], false, false⟩),
 (46, ⟨ObjectKind.jsOrdinary, some 0, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(24, ⟨"WorldChecker.step.env", [{ name := "at", defaultValue := none }, { name := "values", defaultValue := none }], [none, none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.env", [("env", 95),  ("transition", 94),  ("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (23, ⟨"WorldChecker.step.lambda", [{ name := "item", defaultValue := none }], [none], TargetStmt.returnValue   (TargetExpr.andThen     (TargetExpr.binary       (BinaryOp.strictEq)       (TargetExpr.property         (TargetExpr.local "item")         "id")       (TargetExpr.local "snapshotAction"))     (TargetExpr.binary       (BinaryOp.strictEq)       (TargetExpr.property         (TargetExpr.local "item")         "from")       (TargetExpr.local "snapshotState"))), [("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (22, ⟨"WorldChecker.step.reject", [{ name := "code", defaultValue := none },  { name := "message", defaultValue := none },  { name := "violatedInvariant", defaultValue := none }], [none, none, none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.reject", [("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (21, ⟨"WorldChecker.step.rejectRequest", [{ name := "message", defaultValue := none }], [none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rejectRequest", [("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (20, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rollback", [("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (19, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step", [("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩)] ++ m.closures
    generators := [] ++ m.generators
    writableCells := [(95, false),  (94, false),  (93, true),  (92, false),  (91, false),  (90, true),  (89, false),  (88, false),  (87, false),  (86, false),  (85, false),  (84, true),  (83, true),  (82, true),  (81, true),  (80, false),  (79, false),  (78, false),  (77, false),  (76, false),  (75, false),  (74, false),  (73, false),  (72, false),  (71, false),  (70, true),  (69, true),  (68, false),  (67, false),  (66, false),  (65, false),  (64, false),  (63, true),  (62, true),  (61, false),  (60, false),  (59, false),  (58, true),  (57, false),  (56, true),  (55, false),  (54, false),  (53, true),  (52, false),  (51, true),  (50, false),  (49, false),  (48, true),  (47, false),  (46, false),  (45, false),  (44, true),  (43, true),  (42, false),  (41, false),  (40, true),  (39, true),  (38, true),  (37, false),  (36, false),  (35, false),  (34, false),  (33, true),  (32, false),  (31, false),  (30, false),  (29, false),  (28, false),  (27, false),  (26, true),  (25, false),  (24, false),  (23, false),  (22, false),  (21, false),  (20, true),  (19, true),  (18, true),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 96
    nextObject := 60
    nextClosure := 25
    checker := { state := "Ready",   context := 23,   history := 44,   undo := none,   constructorSeed := some 45,   busy := true,   instanceAttrs := [] } }

def balanceStepTsPrefixFrame : TargetFrame := { qualifiedName := "WorldChecker.step",   remaining := [],   locals := [("env", 95),              ("transition", 94),              ("reject", 92),              ("record", 91),              ("safePayload", 81),              ("snapshotDirective", 80),              ("snapshotAction", 79),              ("descPayload", 78),              ("descDirective", 77),              ("descAction", 76),              ("rejectRequest", 75),              ("rollback", 74),              ("snapshotHistory", 73),              ("snapshotContext", 72),              ("snapshotState", 71),              ("request", 70)],   captures := [("sanitizeWorldPayload", 17),                ("deepFreezeWorld", 16),                ("evaluateWorld", 15),                ("booleanWorld", 14),                ("transitionDefinitions", 13),                ("invariantDefinitions", 12),                ("stateDefinitions", 11),                ("contextDefinitions", 10),                ("contextDefaults", 9),                ("world", 8),                ("nodeTypes", 7)],   receiver := some 1,   control := ControlResult.normal }

def balanceStepTsRejected (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .ts b
 { m with
    cells := [(139, (TargetValue.number (NumberTag.jsNumber) n)),
 (138, TargetValue.string "amount"),
 (137, TargetValue.object 77),
 (136, TargetValue.object 77),
 (135, TargetValue.string "eventPayload"),
 (134, TargetValue.string "DEBIT"),
 (133, TargetValue.string "action"),
 (132, TargetValue.string "Ready"),
 (131, TargetValue.string "state"),
 (130, TargetValue.number (NumberTag.jsNumber) 1),
 (129, TargetValue.string "step"),
 (128, TargetValue.object 76),
 (127, TargetValue.object 57),
 (126, TargetValue.undefined),
 (125, TargetValue.string "Guard condition failed"),
 (124, TargetValue.string "GUARD_FAILED"),
 (123, TargetValue.bool false),
 (122, TargetValue.bool false),
 (121, TargetValue.undefined),
 (120, TargetValue.undefined),
 (119, TargetValue.number (NumberTag.jsNumber) 0),
 (118, (TargetValue.number (NumberTag.jsNumber) n)),
 (117, TargetValue.number (NumberTag.jsNumber) 0),
 (116, TargetValue.undefined),
 (115, TargetValue.undefined),
 (114, TargetValue.number (NumberTag.jsNumber) 0),
 (113, TargetValue.string "0"),
 (112, TargetValue.number (NumberTag.jsNumber) 6),
 (111, TargetValue.number (NumberTag.jsNumber) 5),
 (110, TargetValue.string ">"),
 (109, TargetValue.string "amount"),
 (108, TargetValue.bool false),
 (107, TargetValue.string "event"),
 (106, TargetValue.number (NumberTag.jsNumber) 0),
 (105, TargetValue.closure 26),
 (104, TargetValue.closure 25),
 (103, TargetValue.number (NumberTag.jsNumber) 5),
 (102, TargetValue.object 64),
 (101, TargetValue.object 62),
 (100, TargetValue.object 61),
 (99, TargetValue.object 60),
 (98, TargetValue.string "event.amount > 0"),
 (97, TargetValue.object 23),
 (96, TargetValue.string "Ready"),
 (95, TargetValue.closure 24),
 (94, TargetValue.object 14),
 (93, TargetValue.object 14),
 (92, TargetValue.closure 22),
 (91, TargetValue.object 57),
 (90, (TargetValue.number (NumberTag.jsNumber) n)),
 (89, (TargetValue.number (NumberTag.jsNumber) n)),
 (88, TargetValue.object 55),
 (87, TargetValue.string "amount"),
 (86, TargetValue.object 53),
 (85, TargetValue.object 0),
 (84, TargetValue.object 52),
 (83, TargetValue.number (NumberTag.jsNumber) 0),
 (82, TargetValue.object 46),
 (81, TargetValue.object 53),
 (80, TargetValue.null),
 (79, TargetValue.string "DEBIT"),
 (78, TargetValue.object 51),
 (77, TargetValue.undefined),
 (76, TargetValue.object 50),
 (75, TargetValue.closure 21),
 (74, TargetValue.closure 20),
 (73, TargetValue.object 49),
 (72, TargetValue.object 48),
 (71, TargetValue.string "Ready"),
 (70, TargetValue.object 47),
 (69, TargetValue.object 47)] ++ m.cells
    objects := [(80, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.object 76], [], false, false⟩),
 (79, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "amount"], [], false, false⟩),
 (78, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "step",
 TargetValue.string "state",
 TargetValue.string "action",
 TargetValue.string "eventPayload"], [], false, false⟩),
 (77, ⟨ObjectKind.jsNullPrototype, none, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, false, false⟩)], [], [], true, false⟩),
 (76, ⟨ObjectKind.jsOrdinary, some 0, [("step", ⟨some (TargetValue.number (NumberTag.jsNumber) 1), none, none, true, false, false⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, false, false⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, false, false⟩),
 ("eventPayload", ⟨some (TargetValue.object 77), none, none, true, false, false⟩)], [], [], true, false⟩),
 (75, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.object 57], [], false, false⟩),
 (74, ⟨ObjectKind.jsOrdinary, some 0, [], [], [], false, false⟩),
 (73, ⟨ObjectKind.jsOrdinary, some 0, [("code", ⟨some (TargetValue.string "GUARD_FAILED"), none, none, true, true, true⟩),
 ("message", ⟨some (TargetValue.string "Guard condition failed"), none, none, true, true, true⟩),
 ("shortestCounterexampleTrace", ⟨some (TargetValue.object 80), none, none, true, true, true⟩)], [], [], false, false⟩),
 (72, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (71, ⟨ObjectKind.jsOrdinary, some 0, [("allowed", ⟨some (TargetValue.bool false), none, none, true, true, true⟩),
 ("previousState", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("currentState", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("context", ⟨some (TargetValue.object 72), none, none, true, true, true⟩),
 ("directiveAllowed", ⟨some (TargetValue.null), none, none, true, true, true⟩),
 ("violation", ⟨some (TargetValue.object 73), none, none, true, true, true⟩)], [], [], false, false⟩),
 (70, ⟨ObjectKind.jsArray, some 0, [], [], [], false, false⟩),
 (69, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (68, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^\\d/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (67, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^[A-Za-z_][A-Za-z_0-9]*$/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (66, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^[A-Za-z_]/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (65, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^\\d/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (64, ⟨ObjectKind.jsOrdinary, some 0, [("=>", ⟨some (TargetValue.number (NumberTag.jsNumber) 1), none, none, true, true, true⟩),
 ("||", ⟨some (TargetValue.number (NumberTag.jsNumber) 2), none, none, true, true, true⟩),
 ("&&", ⟨some (TargetValue.number (NumberTag.jsNumber) 3), none, none, true, true, true⟩),
 ("==", ⟨some (TargetValue.number (NumberTag.jsNumber) 4), none, none, true, true, true⟩),
 ("!=", ⟨some (TargetValue.number (NumberTag.jsNumber) 4), none, none, true, true, true⟩),
 (">", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 (">=", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 ("<", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 ("<=", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 ("+", ⟨some (TargetValue.number (NumberTag.jsNumber) 6), none, none, true, true, true⟩),
 ("-", ⟨some (TargetValue.number (NumberTag.jsNumber) 6), none, none, true, true, true⟩),
 ("*", ⟨some (TargetValue.number (NumberTag.jsNumber) 7), none, none, true, true, true⟩),
 ("/", ⟨some (TargetValue.number (NumberTag.jsNumber) 7), none, none, true, true, true⟩)], [], [], false, false⟩),
 (63, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/\\s+/g"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (62, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "event",
 TargetValue.string ".",
 TargetValue.string "amount",
 TargetValue.string ">",
 TargetValue.string "0"], [], false, false⟩),
 (61, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string   "/=>|==|!=|>=|<=|&&|\\|\\||[()+\\-*/<>!.]|\\d+(?:\\.\\d+)?|[A-Za-z_][A-Za-z_0-9]*|'(?:[^'\\\\]|\\\\.)*'/g"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (60, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("event", ⟨some (TargetValue.object 53), none, none, true, true, true⟩),
 ("request", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (59, ⟨ObjectKind.jsOrdinary, some 0, [], [], [], false, false⟩),
 (58, ⟨ObjectKind.jsOrdinary, some 0, [("eventPayload", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (57, ⟨ObjectKind.jsOrdinary, some 0, [("step", ⟨some (TargetValue.number (NumberTag.jsNumber) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (56, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (55, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (54, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "amount"], [], false, false⟩),
 (53, ⟨ObjectKind.jsNullPrototype, none, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (52, ⟨ObjectKind.jsSet, some 0, [], [], [TargetValue.object 46], false, false⟩),
 (51, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some (TargetValue.object 46), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (50, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (49, ⟨ObjectKind.jsArray, some 0, [], [], [], false, false⟩),
 (48, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (47, ⟨ObjectKind.jsOrdinary, some 0, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 46), none, none, true, true, true⟩)], [], [], false, false⟩),
 (46, ⟨ObjectKind.jsOrdinary, some 0, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(28, ⟨"WorldChecker.step.reject.lambda", [{ name := "r", defaultValue := none }], [none], TargetStmt.returnValue   (TargetExpr.call     (TargetExpr.local "deepFreezeWorld")     (TargetExpr.sequence       (TargetExpr.call         (TargetExpr.local "structuredClone")         (TargetExpr.sequence           (TargetExpr.local "r")           (TargetExpr.empty)))       (TargetExpr.empty))), [("violatedInvariant", 126),  ("message", 125),  ("code", 124),  ("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (27, ⟨"WorldChecker.getContext", [], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.getContext", [("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (26, ⟨"module.evaluateWorld.parse", [{ name := "minimum", defaultValue := some (TargetExpr.integer 0) }], [none], balanceSourceBody (balanceProgram .ts) "module.evaluateWorld.parse", [("parse", 105),  ("numeric", 104),  ("index", 103),  ("priority", 102),  ("tokens", 101),  ("pattern", 100),  ("env", 99),  ("expression", 98),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], none⟩),
 (25, ⟨"module.evaluateWorld.numeric", [{ name := "value", defaultValue := none }], [none], balanceSourceBody (balanceProgram .ts) "module.evaluateWorld.numeric", [("numeric", 104),  ("index", 103),  ("priority", 102),  ("tokens", 101),  ("pattern", 100),  ("env", 99),  ("expression", 98),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], none⟩),
 (24, ⟨"WorldChecker.step.env", [{ name := "at", defaultValue := none }, { name := "values", defaultValue := none }], [none, none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.env", [("env", 95),  ("transition", 94),  ("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (23, ⟨"WorldChecker.step.lambda", [{ name := "item", defaultValue := none }], [none], TargetStmt.returnValue   (TargetExpr.andThen     (TargetExpr.binary       (BinaryOp.strictEq)       (TargetExpr.property         (TargetExpr.local "item")         "id")       (TargetExpr.local "snapshotAction"))     (TargetExpr.binary       (BinaryOp.strictEq)       (TargetExpr.property         (TargetExpr.local "item")         "from")       (TargetExpr.local "snapshotState"))), [("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (22, ⟨"WorldChecker.step.reject", [{ name := "code", defaultValue := none },  { name := "message", defaultValue := none },  { name := "violatedInvariant", defaultValue := none }], [none, none, none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.reject", [("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (21, ⟨"WorldChecker.step.rejectRequest", [{ name := "message", defaultValue := none }], [none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rejectRequest", [("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (20, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rollback", [("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (19, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step", [("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩)] ++ m.closures
    generators := [] ++ m.generators
    writableCells := [(139, false),  (138, false),  (137, true),  (136, false),  (135, false),  (134, false),  (133, false),  (132, false),  (131, false),  (130, false),  (129, false),  (128, true),  (127, true),  (126, true),  (125, true),  (124, true),  (123, false),  (122, false),  (121, false),  (120, false),  (119, true),  (118, true),  (117, false),  (116, false),  (115, false),  (114, true),  (113, false),  (112, true),  (111, false),  (110, false),  (109, false),  (108, true),  (107, false),  (106, true),  (105, false),  (104, false),  (103, true),  (102, false),  (101, false),  (100, false),  (99, true),  (98, true),  (97, true),  (96, true),  (95, false),  (94, false),  (93, true),  (92, false),  (91, false),  (90, true),  (89, false),  (88, false),  (87, false),  (86, false),  (85, false),  (84, true),  (83, true),  (82, true),  (81, true),  (80, false),  (79, false),  (78, false),  (77, false),  (76, false),  (75, false),  (74, false),  (73, false),  (72, false),  (71, false),  (70, true),  (69, true),  (68, false),  (67, false),  (66, false),  (65, false),  (64, false),  (63, true),  (62, true),  (61, false),  (60, false),  (59, false),  (58, true),  (57, false),  (56, true),  (55, false),  (54, false),  (53, true),  (52, false),  (51, true),  (50, false),  (49, false),  (48, true),  (47, false),  (46, false),  (45, false),  (44, true),  (43, true),  (42, false),  (41, false),  (40, true),  (39, true),  (38, true),  (37, false),  (36, false),  (35, false),  (34, false),  (33, true),  (32, false),  (31, false),  (30, false),  (29, false),  (28, false),  (27, false),  (26, true),  (25, false),  (24, false),  (23, false),  (22, false),  (21, false),  (20, true),  (19, true),  (18, true),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 140
    nextObject := 81
    nextClosure := 29
    checker := { state := "Ready",   context := 69,   history := 70,   undo := none,   constructorSeed := some 45,   busy := false,   instanceAttrs := [] } }

def balanceStepPySnapshots (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .python b
 { m with
    cells := [(150, TargetValue.closure 27),
 (149, TargetValue.null),
 (148, TargetValue.object 105),
 (147, TargetValue.object 104),
 (146, TargetValue.string "Ready"),
 (145, TargetValue.object 103),
 (144, TargetValue.object 103)] ++ m.cells
    objects := [(105, ⟨ObjectKind.pythonList, none, [], [], [], false, false⟩),
 (104, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (103, ⟨ObjectKind.pythonDict, none, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 102), none, none, true, true, true⟩)], [], [], false, false⟩),
 (102, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyInt) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(27, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .python) "WorldChecker.step.rollback", [("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (26, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [none], balanceSourceBody (balanceProgram .python) "WorldChecker.step", [("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩)] ++ m.closures
    generators := [] ++ m.generators
    writableCells := [(150, true),  (149, true),  (148, true),  (147, true),  (146, true),  (145, true),  (144, true),  (143, true),  (142, true),  (141, true),  (140, true),  (139, true),  (138, true),  (137, true),  (136, true),  (135, true),  (134, true),  (133, true),  (132, true),  (131, true),  (130, true),  (129, true),  (128, true),  (127, true),  (126, true),  (125, true),  (124, true),  (123, true),  (122, true),  (121, true),  (120, true),  (119, true),  (118, true),  (117, true),  (116, true),  (115, true),  (114, true),  (113, true),  (112, true),  (111, true),  (110, true),  (109, true),  (108, true),  (107, true),  (106, true),  (105, true),  (104, true),  (103, true),  (102, true),  (101, true),  (100, true),  (99, true),  (98, true),  (97, true),  (96, true),  (95, true),  (94, true),  (93, true),  (92, true),  (91, true),  (90, true),  (89, true),  (88, true),  (87, true),  (86, true),  (85, true),  (84, true),  (83, true),  (82, true),  (81, true),  (80, true),  (79, true),  (78, true),  (77, true),  (76, true),  (75, true),  (74, true),  (73, true),  (72, true),  (71, true),  (70, true),  (69, true),  (68, true),  (67, true),  (66, true),  (65, true),  (64, true),  (63, true),  (62, true),  (61, true),  (60, true),  (59, true),  (58, true),  (57, true),  (56, true),  (55, true),  (54, true),  (53, true),  (52, true),  (51, true),  (50, true),  (49, true),  (48, true),  (47, true),  (46, true),  (45, true),  (44, true),  (43, true),  (42, true),  (41, true),  (40, true),  (39, true),  (38, true),  (37, true),  (36, true),  (35, true),  (34, true),  (33, true),  (32, true),  (31, true),  (30, true),  (29, true),  (28, true),  (27, true),  (26, true),  (25, true),  (24, true),  (23, true),  (22, true),  (21, true),  (20, true),  (19, true),  (18, false),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 151
    nextObject := 106
    nextClosure := 28
    checker := { state := "Ready",   context := 79,   history := 100,   undo := none,   constructorSeed := some 101,   busy := true,   instanceAttrs := [] } }

def balanceStepPySnapshotsFrame : TargetFrame := { qualifiedName := "WorldChecker.step",   remaining := [],   locals := [("rollback", 150),              ("previous_undo", 149),              ("original_history", 148),              ("original_context", 147),              ("previous", 146),              ("request", 145)],   captures := [("step", 99),                ("reset", 98),                ("_invariant", 97),                ("_bounds", 96),                ("getContext", 95),                ("get_context", 94),                ("getState", 93),                ("get_state", 92),                ("rollback_last_step", 91),                ("history", 90),                ("context", 89),                ("state", 88),                ("__init__", 87),                ("sanitize_world_payload", 86),                ("evaluate_world", 85),                ("_safe_integer", 84),                ("_div", 83),                ("_number", 82),                ("_boolean", 81),                ("_UNDEFINED", 80),                ("_MAX_INTEGER", 79),                ("_EFFECT", 78),                ("_NAME", 77),                ("_TOKEN", 76),                ("_PRECEDENCE", 75),                ("_DEFAULTS", 74),                ("_INITIAL", 71),                ("_WORLD", 69),                ("_freeze", 26),                ("IWorldChecker", 25),                ("Any", 24),                ("types", 23),                ("re", 22),                ("math", 21),                ("json", 20),                ("copy", 19)],   receiver := some 1,   control := ControlResult.normal }

def balanceStepPyPrefix (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .python b
 { m with
    cells := [(177, TargetValue.closure 31),
 (176, TargetValue.object 61),
 (175, TargetValue.object 61),
 (174, TargetValue.closure 30),
 (173, TargetValue.object 122),
 (172, TargetValue.object 114),
 (171, TargetValue.number (NumberTag.pyInt) 1),
 (170, (TargetValue.number (NumberTag.pyInt) n)),
 (169, (TargetValue.number (NumberTag.pyInt) n)),
 (168, TargetValue.string "amount"),
 (167, TargetValue.object 114),
 (166, TargetValue.number (NumberTag.pyInt) 102),
 (165, TargetValue.number (NumberTag.pyInt) 0),
 (164, TargetValue.object 102),
 (163, TargetValue.closure 29),
 (162, TargetValue.object 110),
 (161, TargetValue.object 102),
 (160, TargetValue.null),
 (159, TargetValue.string "DEBIT"),
 (158, TargetValue.object 102),
 (157, TargetValue.string "eventPayload"),
 (156, TargetValue.object 102),
 (155, TargetValue.bool false),
 (154, TargetValue.null),
 (153, TargetValue.bool true),
 (152, TargetValue.string "DEBIT"),
 (151, TargetValue.closure 28),
 (150, TargetValue.closure 27),
 (149, TargetValue.null),
 (148, TargetValue.object 105),
 (147, TargetValue.object 104),
 (146, TargetValue.string "Ready"),
 (145, TargetValue.object 103),
 (144, TargetValue.object 103)] ++ m.cells
    objects := [(123, ⟨ObjectKind.pythonGenerator, none, [], [], [], false, false⟩),
 (122, ⟨ObjectKind.pythonDict, none, [("step", ⟨some (TargetValue.number (NumberTag.pyInt) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 114), none, none, true, true, true⟩)], [], [], false, false⟩),
 (121, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (120, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.strType),
 TargetValue.builtin (BuiltinId.boolType)], [], false, false⟩),
 (119, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.list),
 TargetValue.builtin (BuiltinId.tuple),
 TargetValue.builtin (BuiltinId.set)], [], false, false⟩),
 (118, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "__proto__",
 TargetValue.string "constructor",
 TargetValue.string "prototype"], [], false, false⟩),
 (117, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 115], [], false, false⟩),
 (116, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 115], [], false, false⟩),
 (115, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "amount",
 (TargetValue.number (NumberTag.pyInt) n)], [], false, false⟩),
 (114, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyFloat) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (113, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (112, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.strType),
 TargetValue.builtin (BuiltinId.boolType)], [], false, false⟩),
 (111, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.list),
 TargetValue.builtin (BuiltinId.tuple),
 TargetValue.builtin (BuiltinId.set)], [], false, false⟩),
 (110, ⟨ObjectKind.pythonSet, none, [], [], [TargetValue.number (NumberTag.pyInt) 102], false, false⟩),
 (109, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 106,
 TargetValue.object 107], [], false, false⟩),
 (108, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 106,
 TargetValue.object 107], [], false, false⟩),
 (107, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "eventPayload",
 TargetValue.object 102], [], false, false⟩),
 (106, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "transitionId",
 TargetValue.string "DEBIT"], [], false, false⟩),
 (105, ⟨ObjectKind.pythonList, none, [], [], [], false, false⟩),
 (104, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (103, ⟨ObjectKind.pythonDict, none, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 102), none, none, true, true, true⟩)], [], [], false, false⟩),
 (102, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyInt) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(31, ⟨"WorldChecker.step.lambda", [{ name := "state", defaultValue := none }, { name := "values", defaultValue := none }], [none, none], TargetStmt.returnValue   (TargetExpr.object     (TargetExpr.objectSpread       (TargetExpr.local "values")       (TargetExpr.objectEntry         "state"         (TargetExpr.local "state")         (TargetExpr.objectEntry           "event"           (TargetExpr.orElse             (TargetExpr.local "payload")             (TargetExpr.object               (TargetExpr.empty)))           (TargetExpr.objectEntry             "request"             (TargetExpr.orElse               (TargetExpr.local "payload")               (TargetExpr.object                 (TargetExpr.empty)))             (TargetExpr.empty)))))), [("transition", 176),  ("reject", 174),  ("record", 173),  ("payload", 172),  ("proposed", 160),  ("action", 159),  ("value", 158),  ("key", 157),  ("raw_payload", 156),  ("has_proposed", 155),  ("proposed_val", 154),  ("has_action", 153),  ("action_val", 152),  ("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (30, ⟨"WorldChecker.step.reject", [{ name := "code", defaultValue := none },  { name := "message", defaultValue := none },  { name := "invariant", defaultValue := some (TargetExpr.null) }], [none, none, some (TargetValue.null)], balanceSourceBody (balanceProgram .python) "WorldChecker.step.reject", [("reject", 174),  ("record", 173),  ("payload", 172),  ("proposed", 160),  ("action", 159),  ("value", 158),  ("key", 157),  ("raw_payload", 156),  ("has_proposed", 155),  ("proposed_val", 154),  ("has_action", 153),  ("action_val", 152),  ("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (29, ⟨"module.sanitize_world_payload.copy", [{ name := "value", defaultValue := none },  { name := "depth", defaultValue := some (TargetExpr.integer 0) }], [none,  some (TargetValue.number    (NumberTag.pyInt)    0)], balanceSourceBody (balanceProgram .python) "module.sanitize_world_payload.copy", [("copy", 163),  ("seen", 162),  ("raw", 161),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], none⟩),
 (28, ⟨"WorldChecker.step.security_reject", [{ name := "message", defaultValue := none },  { name := "action", defaultValue := some (TargetExpr.string "<invalid>") }], [none, some (TargetValue.string "<invalid>")], balanceSourceBody (balanceProgram .python) "WorldChecker.step.security_reject", [("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (27, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .python) "WorldChecker.step.rollback", [("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (26, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [none], balanceSourceBody (balanceProgram .python) "WorldChecker.step", [("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩)] ++ m.closures
    generators := [(123,   { valueExpr := TargetExpr.local "item",     binders := ["item"],     filterExpr := TargetExpr.andThen                     (TargetExpr.binary                       (BinaryOp.eq)                       (TargetExpr.index                         (TargetExpr.local "item")                         (TargetExpr.string "id"))                       (TargetExpr.local "action"))                     (TargetExpr.binary                       (BinaryOp.eq)                       (TargetExpr.index                         (TargetExpr.local "item")                         (TargetExpr.string "from"))                       (TargetExpr.local "previous")),     remaining := [],     frame := { qualifiedName := "WorldChecker.step.generator",                remaining := [],                locals := [("item", 175)],                captures := [("reject", 174),                             ("record", 173),                             ("payload", 172),                             ("proposed", 160),                             ("action", 159),                             ("value", 158),                             ("key", 157),                             ("raw_payload", 156),                             ("has_proposed", 155),                             ("proposed_val", 154),                             ("has_action", 153),                             ("action_val", 152),                             ("security_reject", 151),                             ("rollback", 150),                             ("previous_undo", 149),                             ("original_history", 148),                             ("original_context", 147),                             ("previous", 146),                             ("request", 145),                             ("step", 99),                             ("reset", 98),                             ("_invariant", 97),                             ("_bounds", 96),                             ("getContext", 95),                             ("get_context", 94),                             ("getState", 93),                             ("get_state", 92),                             ("rollback_last_step", 91),                             ("history", 90),                             ("context", 89),                             ("state", 88),                             ("__init__", 87),                             ("sanitize_world_payload", 86),                             ("evaluate_world", 85),                             ("_safe_integer", 84),                             ("_div", 83),                             ("_number", 82),                             ("_boolean", 81),                             ("_UNDEFINED", 80),                             ("_MAX_INTEGER", 79),                             ("_EFFECT", 78),                             ("_NAME", 77),                             ("_TOKEN", 76),                             ("_PRECEDENCE", 75),                             ("_DEFAULTS", 74),                             ("_INITIAL", 71),                             ("_WORLD", 69),                             ("_freeze", 26),                             ("IWorldChecker", 25),                             ("Any", 24),                             ("types", 23),                             ("re", 22),                             ("math", 21),                             ("json", 20),                             ("copy", 19)],                receiver := some 1,                control := ControlResult.normal } })] ++ m.generators
    writableCells := [(177, true),  (176, true),  (175, true),  (174, true),  (173, true),  (172, true),  (171, true),  (170, true),  (169, true),  (168, true),  (167, true),  (166, true),  (165, true),  (164, true),  (163, true),  (162, true),  (161, true),  (160, true),  (159, true),  (158, true),  (157, true),  (156, true),  (155, true),  (154, true),  (153, true),  (152, true),  (151, true),  (150, true),  (149, true),  (148, true),  (147, true),  (146, true),  (145, true),  (144, true),  (143, true),  (142, true),  (141, true),  (140, true),  (139, true),  (138, true),  (137, true),  (136, true),  (135, true),  (134, true),  (133, true),  (132, true),  (131, true),  (130, true),  (129, true),  (128, true),  (127, true),  (126, true),  (125, true),  (124, true),  (123, true),  (122, true),  (121, true),  (120, true),  (119, true),  (118, true),  (117, true),  (116, true),  (115, true),  (114, true),  (113, true),  (112, true),  (111, true),  (110, true),  (109, true),  (108, true),  (107, true),  (106, true),  (105, true),  (104, true),  (103, true),  (102, true),  (101, true),  (100, true),  (99, true),  (98, true),  (97, true),  (96, true),  (95, true),  (94, true),  (93, true),  (92, true),  (91, true),  (90, true),  (89, true),  (88, true),  (87, true),  (86, true),  (85, true),  (84, true),  (83, true),  (82, true),  (81, true),  (80, true),  (79, true),  (78, true),  (77, true),  (76, true),  (75, true),  (74, true),  (73, true),  (72, true),  (71, true),  (70, true),  (69, true),  (68, true),  (67, true),  (66, true),  (65, true),  (64, true),  (63, true),  (62, true),  (61, true),  (60, true),  (59, true),  (58, true),  (57, true),  (56, true),  (55, true),  (54, true),  (53, true),  (52, true),  (51, true),  (50, true),  (49, true),  (48, true),  (47, true),  (46, true),  (45, true),  (44, true),  (43, true),  (42, true),  (41, true),  (40, true),  (39, true),  (38, true),  (37, true),  (36, true),  (35, true),  (34, true),  (33, true),  (32, true),  (31, true),  (30, true),  (29, true),  (28, true),  (27, true),  (26, true),  (25, true),  (24, true),  (23, true),  (22, true),  (21, true),  (20, true),  (19, true),  (18, false),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 178
    nextObject := 124
    nextClosure := 32
    checker := { state := "Ready",   context := 79,   history := 100,   undo := none,   constructorSeed := some 101,   busy := true,   instanceAttrs := [] } }

def balanceStepPyPrefixFrame : TargetFrame := { qualifiedName := "WorldChecker.step",   remaining := [],   locals := [("environment", 177),              ("transition", 176),              ("reject", 174),              ("record", 173),              ("payload", 172),              ("proposed", 160),              ("action", 159),              ("value", 158),              ("key", 157),              ("raw_payload", 156),              ("has_proposed", 155),              ("proposed_val", 154),              ("has_action", 153),              ("action_val", 152),              ("security_reject", 151),              ("rollback", 150),              ("previous_undo", 149),              ("original_history", 148),              ("original_context", 147),              ("previous", 146),              ("request", 145)],   captures := [("step", 99),                ("reset", 98),                ("_invariant", 97),                ("_bounds", 96),                ("getContext", 95),                ("get_context", 94),                ("getState", 93),                ("get_state", 92),                ("rollback_last_step", 91),                ("history", 90),                ("context", 89),                ("state", 88),                ("__init__", 87),                ("sanitize_world_payload", 86),                ("evaluate_world", 85),                ("_safe_integer", 84),                ("_div", 83),                ("_number", 82),                ("_boolean", 81),                ("_UNDEFINED", 80),                ("_MAX_INTEGER", 79),                ("_EFFECT", 78),                ("_NAME", 77),                ("_TOKEN", 76),                ("_PRECEDENCE", 75),                ("_DEFAULTS", 74),                ("_INITIAL", 71),                ("_WORLD", 69),                ("_freeze", 26),                ("IWorldChecker", 25),                ("Any", 24),                ("types", 23),                ("re", 22),                ("math", 21),                ("json", 20),                ("copy", 19)],   receiver := some 1,   control := ControlResult.normal }

def balanceStepPyRejected (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .python b
 { m with
    cells := [(204, TargetValue.object 136),
 (203, TargetValue.null),
 (202, TargetValue.string "Guard condition failed"),
 (201, TargetValue.string "GUARD_FAILED"),
 (200, TargetValue.bool false),
 (199, TargetValue.bool false),
 (198, TargetValue.number (NumberTag.pyFloat) 0),
 (197, (TargetValue.number (NumberTag.pyFloat) n)),
 (196, TargetValue.number (NumberTag.pyFloat) 0),
 (195, TargetValue.number (NumberTag.pyFloat) 0),
 (194, TargetValue.string "0"),
 (193, TargetValue.number (NumberTag.pyInt) 6),
 (192, TargetValue.number (NumberTag.pyInt) 5),
 (191, TargetValue.string ">"),
 (190, TargetValue.string "amount"),
 (189, TargetValue.bool false),
 (188, TargetValue.string "event"),
 (187, TargetValue.number (NumberTag.pyInt) 0),
 (186, TargetValue.closure 32),
 (185, TargetValue.number (NumberTag.pyInt) 5),
 (184, TargetValue.regexMatch { full := "0", start := 15, stop := 16, groups := [] }),
 (183, TargetValue.number (NumberTag.pyInt) 16),
 (182, TargetValue.object 125),
 (181, TargetValue.object 124),
 (180, TargetValue.string "event.amount > 0"),
 (179, TargetValue.object 104),
 (178, TargetValue.string "Ready"),
 (177, TargetValue.closure 31),
 (176, TargetValue.object 61),
 (175, TargetValue.object 61),
 (174, TargetValue.closure 30),
 (173, TargetValue.object 122),
 (172, TargetValue.object 114),
 (171, TargetValue.number (NumberTag.pyInt) 1),
 (170, (TargetValue.number (NumberTag.pyInt) n)),
 (169, (TargetValue.number (NumberTag.pyInt) n)),
 (168, TargetValue.string "amount"),
 (167, TargetValue.object 114),
 (166, TargetValue.number (NumberTag.pyInt) 102),
 (165, TargetValue.number (NumberTag.pyInt) 0),
 (164, TargetValue.object 102),
 (163, TargetValue.closure 29),
 (162, TargetValue.object 110),
 (161, TargetValue.object 102),
 (160, TargetValue.null),
 (159, TargetValue.string "DEBIT"),
 (158, TargetValue.object 102),
 (157, TargetValue.string "eventPayload"),
 (156, TargetValue.object 102),
 (155, TargetValue.bool false),
 (154, TargetValue.null),
 (153, TargetValue.bool true),
 (152, TargetValue.string "DEBIT"),
 (151, TargetValue.closure 28),
 (150, TargetValue.closure 27),
 (149, TargetValue.null),
 (148, TargetValue.object 105),
 (147, TargetValue.object 104),
 (146, TargetValue.string "Ready"),
 (145, TargetValue.object 103),
 (144, TargetValue.object 103)] ++ m.cells
    objects := [(142, ⟨ObjectKind.pythonDict, none, [("allowed", ⟨some (TargetValue.bool false), none, none, true, true, true⟩),
 ("previousState", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("currentState", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("context", ⟨some (TargetValue.object 104), none, none, true, true, true⟩),
 ("directiveAllowed", ⟨some (TargetValue.null), none, none, true, true, true⟩),
 ("violation", ⟨some (TargetValue.object 136), none, none, true, true, true⟩)], [], [], false, false⟩),
 (141, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 139], [], false, false⟩),
 (140, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyFloat) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (139, ⟨ObjectKind.pythonDict, none, [("step", ⟨some (TargetValue.number (NumberTag.pyInt) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 140), none, none, true, true, true⟩)], [], [], false, false⟩),
 (138, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 139], [], false, false⟩),
 (137, ⟨ObjectKind.pythonList, none, [], [], [], false, false⟩),
 (136, ⟨ObjectKind.pythonDict, none, [("code", ⟨some (TargetValue.string "GUARD_FAILED"), none, none, true, true, true⟩),
 ("message", ⟨some (TargetValue.string "Guard condition failed"), none, none, true, true, true⟩),
 ("shortestCounterexampleTrace", ⟨some (TargetValue.object 141), none, none, true, true, true⟩)], [], [], false, false⟩),
 (135, ⟨ObjectKind.pythonList, none, [], [], [], false, false⟩),
 (134, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (133, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (132, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (131, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "==",
 TargetValue.string "!="], [], false, false⟩),
 (130, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "=>",
 TargetValue.string "||",
 TargetValue.string "&&"], [], false, false⟩),
 (129, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "true",
 TargetValue.string "false"], [], false, false⟩),
 (128, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "!",
 TargetValue.string "-"], [], false, false⟩),
 (127, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "true",
 TargetValue.string "false"], [], false, false⟩),
 (126, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "!",
 TargetValue.string "-"], [], false, false⟩),
 (125, ⟨ObjectKind.pythonList, none, [], [TargetValue.string "event",
 TargetValue.string ".",
 TargetValue.string "amount",
 TargetValue.string ">",
 TargetValue.string "0"], [], false, false⟩),
 (124, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("event", ⟨some (TargetValue.object 114), none, none, true, true, true⟩),
 ("request", ⟨some (TargetValue.object 114), none, none, true, true, true⟩)], [], [], false, false⟩),
 (123, ⟨ObjectKind.pythonGenerator, none, [], [], [], false, false⟩),
 (122, ⟨ObjectKind.pythonDict, none, [("step", ⟨some (TargetValue.number (NumberTag.pyInt) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 114), none, none, true, true, true⟩)], [], [], false, false⟩),
 (121, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (120, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.strType),
 TargetValue.builtin (BuiltinId.boolType)], [], false, false⟩),
 (119, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.list),
 TargetValue.builtin (BuiltinId.tuple),
 TargetValue.builtin (BuiltinId.set)], [], false, false⟩),
 (118, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "__proto__",
 TargetValue.string "constructor",
 TargetValue.string "prototype"], [], false, false⟩),
 (117, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 115], [], false, false⟩),
 (116, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 115], [], false, false⟩),
 (115, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "amount",
 (TargetValue.number (NumberTag.pyInt) n)], [], false, false⟩),
 (114, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyFloat) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (113, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (112, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.strType),
 TargetValue.builtin (BuiltinId.boolType)], [], false, false⟩),
 (111, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.list),
 TargetValue.builtin (BuiltinId.tuple),
 TargetValue.builtin (BuiltinId.set)], [], false, false⟩),
 (110, ⟨ObjectKind.pythonSet, none, [], [], [TargetValue.number (NumberTag.pyInt) 102], false, false⟩),
 (109, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 106,
 TargetValue.object 107], [], false, false⟩),
 (108, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 106,
 TargetValue.object 107], [], false, false⟩),
 (107, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "eventPayload",
 TargetValue.object 102], [], false, false⟩),
 (106, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "transitionId",
 TargetValue.string "DEBIT"], [], false, false⟩),
 (105, ⟨ObjectKind.pythonList, none, [], [], [], false, false⟩),
 (104, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (103, ⟨ObjectKind.pythonDict, none, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 102), none, none, true, true, true⟩)], [], [], false, false⟩),
 (102, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyInt) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(32, ⟨"module.evaluate_world.parse", [{ name := "minimum", defaultValue := some (TargetExpr.integer 0) }], [some (TargetValue.number    (NumberTag.pyInt)    0)], balanceSourceBody (balanceProgram .python) "module.evaluate_world.parse", [("parse", 186),  ("position", 185),  ("match", 184),  ("offset", 183),  ("tokens", 182),  ("environment", 181),  ("expression", 180),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], none⟩),
 (31, ⟨"WorldChecker.step.lambda", [{ name := "state", defaultValue := none }, { name := "values", defaultValue := none }], [none, none], TargetStmt.returnValue   (TargetExpr.object     (TargetExpr.objectSpread       (TargetExpr.local "values")       (TargetExpr.objectEntry         "state"         (TargetExpr.local "state")         (TargetExpr.objectEntry           "event"           (TargetExpr.orElse             (TargetExpr.local "payload")             (TargetExpr.object               (TargetExpr.empty)))           (TargetExpr.objectEntry             "request"             (TargetExpr.orElse               (TargetExpr.local "payload")               (TargetExpr.object                 (TargetExpr.empty)))             (TargetExpr.empty)))))), [("transition", 176),  ("reject", 174),  ("record", 173),  ("payload", 172),  ("proposed", 160),  ("action", 159),  ("value", 158),  ("key", 157),  ("raw_payload", 156),  ("has_proposed", 155),  ("proposed_val", 154),  ("has_action", 153),  ("action_val", 152),  ("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (30, ⟨"WorldChecker.step.reject", [{ name := "code", defaultValue := none },  { name := "message", defaultValue := none },  { name := "invariant", defaultValue := some (TargetExpr.null) }], [none, none, some (TargetValue.null)], balanceSourceBody (balanceProgram .python) "WorldChecker.step.reject", [("reject", 174),  ("record", 173),  ("payload", 172),  ("proposed", 160),  ("action", 159),  ("value", 158),  ("key", 157),  ("raw_payload", 156),  ("has_proposed", 155),  ("proposed_val", 154),  ("has_action", 153),  ("action_val", 152),  ("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (29, ⟨"module.sanitize_world_payload.copy", [{ name := "value", defaultValue := none },  { name := "depth", defaultValue := some (TargetExpr.integer 0) }], [none,  some (TargetValue.number    (NumberTag.pyInt)    0)], balanceSourceBody (balanceProgram .python) "module.sanitize_world_payload.copy", [("copy", 163),  ("seen", 162),  ("raw", 161),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], none⟩),
 (28, ⟨"WorldChecker.step.security_reject", [{ name := "message", defaultValue := none },  { name := "action", defaultValue := some (TargetExpr.string "<invalid>") }], [none, some (TargetValue.string "<invalid>")], balanceSourceBody (balanceProgram .python) "WorldChecker.step.security_reject", [("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (27, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .python) "WorldChecker.step.rollback", [("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (26, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [none], balanceSourceBody (balanceProgram .python) "WorldChecker.step", [("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩)] ++ m.closures
    generators := [(123,   { valueExpr := TargetExpr.local "item",     binders := ["item"],     filterExpr := TargetExpr.andThen                     (TargetExpr.binary                       (BinaryOp.eq)                       (TargetExpr.index                         (TargetExpr.local "item")                         (TargetExpr.string "id"))                       (TargetExpr.local "action"))                     (TargetExpr.binary                       (BinaryOp.eq)                       (TargetExpr.index                         (TargetExpr.local "item")                         (TargetExpr.string "from"))                       (TargetExpr.local "previous")),     remaining := [],     frame := { qualifiedName := "WorldChecker.step.generator",                remaining := [],                locals := [("item", 175)],                captures := [("reject", 174),                             ("record", 173),                             ("payload", 172),                             ("proposed", 160),                             ("action", 159),                             ("value", 158),                             ("key", 157),                             ("raw_payload", 156),                             ("has_proposed", 155),                             ("proposed_val", 154),                             ("has_action", 153),                             ("action_val", 152),                             ("security_reject", 151),                             ("rollback", 150),                             ("previous_undo", 149),                             ("original_history", 148),                             ("original_context", 147),                             ("previous", 146),                             ("request", 145),                             ("step", 99),                             ("reset", 98),                             ("_invariant", 97),                             ("_bounds", 96),                             ("getContext", 95),                             ("get_context", 94),                             ("getState", 93),                             ("get_state", 92),                             ("rollback_last_step", 91),                             ("history", 90),                             ("context", 89),                             ("state", 88),                             ("__init__", 87),                             ("sanitize_world_payload", 86),                             ("evaluate_world", 85),                             ("_safe_integer", 84),                             ("_div", 83),                             ("_number", 82),                             ("_boolean", 81),                             ("_UNDEFINED", 80),                             ("_MAX_INTEGER", 79),                             ("_EFFECT", 78),                             ("_NAME", 77),                             ("_TOKEN", 76),                             ("_PRECEDENCE", 75),                             ("_DEFAULTS", 74),                             ("_INITIAL", 71),                             ("_WORLD", 69),                             ("_freeze", 26),                             ("IWorldChecker", 25),                             ("Any", 24),                             ("types", 23),                             ("re", 22),                             ("math", 21),                             ("json", 20),                             ("copy", 19)],                receiver := some 1,                control := ControlResult.normal } })] ++ m.generators
    writableCells := [(204, true),  (203, true),  (202, true),  (201, true),  (200, true),  (199, true),  (198, true),  (197, true),  (196, true),  (195, true),  (194, true),  (193, true),  (192, true),  (191, true),  (190, true),  (189, true),  (188, true),  (187, true),  (186, true),  (185, true),  (184, true),  (183, true),  (182, true),  (181, true),  (180, true),  (179, true),  (178, true),  (177, true),  (176, true),  (175, true),  (174, true),  (173, true),  (172, true),  (171, true),  (170, true),  (169, true),  (168, true),  (167, true),  (166, true),  (165, true),  (164, true),  (163, true),  (162, true),  (161, true),  (160, true),  (159, true),  (158, true),  (157, true),  (156, true),  (155, true),  (154, true),  (153, true),  (152, true),  (151, true),  (150, true),  (149, true),  (148, true),  (147, true),  (146, true),  (145, true),  (144, true),  (143, true),  (142, true),  (141, true),  (140, true),  (139, true),  (138, true),  (137, true),  (136, true),  (135, true),  (134, true),  (133, true),  (132, true),  (131, true),  (130, true),  (129, true),  (128, true),  (127, true),  (126, true),  (125, true),  (124, true),  (123, true),  (122, true),  (121, true),  (120, true),  (119, true),  (118, true),  (117, true),  (116, true),  (115, true),  (114, true),  (113, true),  (112, true),  (111, true),  (110, true),  (109, true),  (108, true),  (107, true),  (106, true),  (105, true),  (104, true),  (103, true),  (102, true),  (101, true),  (100, true),  (99, true),  (98, true),  (97, true),  (96, true),  (95, true),  (94, true),  (93, true),  (92, true),  (91, true),  (90, true),  (89, true),  (88, true),  (87, true),  (86, true),  (85, true),  (84, true),  (83, true),  (82, true),  (81, true),  (80, true),  (79, true),  (78, true),  (77, true),  (76, true),  (75, true),  (74, true),  (73, true),  (72, true),  (71, true),  (70, true),  (69, true),  (68, true),  (67, true),  (66, true),  (65, true),  (64, true),  (63, true),  (62, true),  (61, true),  (60, true),  (59, true),  (58, true),  (57, true),  (56, true),  (55, true),  (54, true),  (53, true),  (52, true),  (51, true),  (50, true),  (49, true),  (48, true),  (47, true),  (46, true),  (45, true),  (44, true),  (43, true),  (42, true),  (41, true),  (40, true),  (39, true),  (38, true),  (37, true),  (36, true),  (35, true),  (34, true),  (33, true),  (32, true),  (31, true),  (30, true),  (29, true),  (28, true),  (27, true),  (26, true),  (25, true),  (24, true),  (23, true),  (22, true),  (21, true),  (20, true),  (19, true),  (18, false),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 205
    nextObject := 143
    nextClosure := 33
    checker := { state := "Ready",   context := 134,   history := 135,   undo := none,   constructorSeed := some 101,   busy := false,   instanceAttrs := [] } }


def balanceStepPyGuard (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .python b
 { m with
    cells := [(199, TargetValue.bool (decide (0 < n))),
 (198, TargetValue.number (NumberTag.pyFloat) 0),
 (197, (TargetValue.number (NumberTag.pyFloat) n)),
 (196, TargetValue.number (NumberTag.pyFloat) 0),
 (195, TargetValue.number (NumberTag.pyFloat) 0),
 (194, TargetValue.string "0"),
 (193, TargetValue.number (NumberTag.pyInt) 6),
 (192, TargetValue.number (NumberTag.pyInt) 5),
 (191, TargetValue.string ">"),
 (190, TargetValue.string "amount"),
 (189, TargetValue.bool (decide (0 < n))),
 (188, TargetValue.string "event"),
 (187, TargetValue.number (NumberTag.pyInt) 0),
 (186, TargetValue.closure 32),
 (185, TargetValue.number (NumberTag.pyInt) 5),
 (184, TargetValue.regexMatch { full := "0", start := 15, stop := 16, groups := [] }),
 (183, TargetValue.number (NumberTag.pyInt) 16),
 (182, TargetValue.object 125),
 (181, TargetValue.object 124),
 (180, TargetValue.string "event.amount > 0"),
 (179, TargetValue.object 104),
 (178, TargetValue.string "Ready"),
 (177, TargetValue.closure 31),
 (176, TargetValue.object 61),
 (175, TargetValue.object 61),
 (174, TargetValue.closure 30),
 (173, TargetValue.object 122),
 (172, TargetValue.object 114),
 (171, TargetValue.number (NumberTag.pyInt) 1),
 (170, (TargetValue.number (NumberTag.pyInt) n)),
 (169, (TargetValue.number (NumberTag.pyInt) n)),
 (168, TargetValue.string "amount"),
 (167, TargetValue.object 114),
 (166, TargetValue.number (NumberTag.pyInt) 102),
 (165, TargetValue.number (NumberTag.pyInt) 0),
 (164, TargetValue.object 102),
 (163, TargetValue.closure 29),
 (162, TargetValue.object 110),
 (161, TargetValue.object 102),
 (160, TargetValue.null),
 (159, TargetValue.string "DEBIT"),
 (158, TargetValue.object 102),
 (157, TargetValue.string "eventPayload"),
 (156, TargetValue.object 102),
 (155, TargetValue.bool false),
 (154, TargetValue.null),
 (153, TargetValue.bool true),
 (152, TargetValue.string "DEBIT"),
 (151, TargetValue.closure 28),
 (150, TargetValue.closure 27),
 (149, TargetValue.null),
 (148, TargetValue.object 105),
 (147, TargetValue.object 104),
 (146, TargetValue.string "Ready"),
 (145, TargetValue.object 103),
 (144, TargetValue.object 103)] ++ m.cells
    objects := [(133, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (132, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (131, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "==",
 TargetValue.string "!="], [], false, false⟩),
 (130, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "=>",
 TargetValue.string "||",
 TargetValue.string "&&"], [], false, false⟩),
 (129, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "true",
 TargetValue.string "false"], [], false, false⟩),
 (128, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "!",
 TargetValue.string "-"], [], false, false⟩),
 (127, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "true",
 TargetValue.string "false"], [], false, false⟩),
 (126, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "!",
 TargetValue.string "-"], [], false, false⟩),
 (125, ⟨ObjectKind.pythonList, none, [], [TargetValue.string "event",
 TargetValue.string ".",
 TargetValue.string "amount",
 TargetValue.string ">",
 TargetValue.string "0"], [], false, false⟩),
 (124, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("event", ⟨some (TargetValue.object 114), none, none, true, true, true⟩),
 ("request", ⟨some (TargetValue.object 114), none, none, true, true, true⟩)], [], [], false, false⟩),
 (123, ⟨ObjectKind.pythonGenerator, none, [], [], [], false, false⟩),
 (122, ⟨ObjectKind.pythonDict, none, [("step", ⟨some (TargetValue.number (NumberTag.pyInt) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 114), none, none, true, true, true⟩)], [], [], false, false⟩),
 (121, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (120, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.strType),
 TargetValue.builtin (BuiltinId.boolType)], [], false, false⟩),
 (119, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.list),
 TargetValue.builtin (BuiltinId.tuple),
 TargetValue.builtin (BuiltinId.set)], [], false, false⟩),
 (118, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "__proto__",
 TargetValue.string "constructor",
 TargetValue.string "prototype"], [], false, false⟩),
 (117, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 115], [], false, false⟩),
 (116, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 115], [], false, false⟩),
 (115, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "amount",
 (TargetValue.number (NumberTag.pyInt) n)], [], false, false⟩),
 (114, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyFloat) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (113, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.int),
 TargetValue.builtin (BuiltinId.float)], [], false, false⟩),
 (112, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.strType),
 TargetValue.builtin (BuiltinId.boolType)], [], false, false⟩),
 (111, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.builtin (BuiltinId.list),
 TargetValue.builtin (BuiltinId.tuple),
 TargetValue.builtin (BuiltinId.set)], [], false, false⟩),
 (110, ⟨ObjectKind.pythonSet, none, [], [], [TargetValue.number (NumberTag.pyInt) 102], false, false⟩),
 (109, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 106,
 TargetValue.object 107], [], false, false⟩),
 (108, ⟨ObjectKind.pythonList, none, [], [TargetValue.object 106,
 TargetValue.object 107], [], false, false⟩),
 (107, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "eventPayload",
 TargetValue.object 102], [], false, false⟩),
 (106, ⟨ObjectKind.pythonTuple, none, [], [TargetValue.string "transitionId",
 TargetValue.string "DEBIT"], [], false, false⟩),
 (105, ⟨ObjectKind.pythonList, none, [], [], [], false, false⟩),
 (104, ⟨ObjectKind.pythonDict, none, [("balance", ⟨some ((TargetValue.number (NumberTag.pyInt) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (103, ⟨ObjectKind.pythonDict, none, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 102), none, none, true, true, true⟩)], [], [], false, false⟩),
 (102, ⟨ObjectKind.pythonDict, none, [("amount", ⟨some ((TargetValue.number (NumberTag.pyInt) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(32, ⟨"module.evaluate_world.parse", [{ name := "minimum", defaultValue := some (TargetExpr.integer 0) }], [some (TargetValue.number    (NumberTag.pyInt)    0)], balanceSourceBody (balanceProgram .python) "module.evaluate_world.parse", [("parse", 186),  ("position", 185),  ("match", 184),  ("offset", 183),  ("tokens", 182),  ("environment", 181),  ("expression", 180),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], none⟩),
 (31, ⟨"WorldChecker.step.lambda", [{ name := "state", defaultValue := none }, { name := "values", defaultValue := none }], [none, none], TargetStmt.returnValue   (TargetExpr.object     (TargetExpr.objectSpread       (TargetExpr.local "values")       (TargetExpr.objectEntry         "state"         (TargetExpr.local "state")         (TargetExpr.objectEntry           "event"           (TargetExpr.orElse             (TargetExpr.local "payload")             (TargetExpr.object               (TargetExpr.empty)))           (TargetExpr.objectEntry             "request"             (TargetExpr.orElse               (TargetExpr.local "payload")               (TargetExpr.object                 (TargetExpr.empty)))             (TargetExpr.empty)))))), [("transition", 176),  ("reject", 174),  ("record", 173),  ("payload", 172),  ("proposed", 160),  ("action", 159),  ("value", 158),  ("key", 157),  ("raw_payload", 156),  ("has_proposed", 155),  ("proposed_val", 154),  ("has_action", 153),  ("action_val", 152),  ("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (30, ⟨"WorldChecker.step.reject", [{ name := "code", defaultValue := none },  { name := "message", defaultValue := none },  { name := "invariant", defaultValue := some (TargetExpr.null) }], [none, none, some (TargetValue.null)], balanceSourceBody (balanceProgram .python) "WorldChecker.step.reject", [("reject", 174),  ("record", 173),  ("payload", 172),  ("proposed", 160),  ("action", 159),  ("value", 158),  ("key", 157),  ("raw_payload", 156),  ("has_proposed", 155),  ("proposed_val", 154),  ("has_action", 153),  ("action_val", 152),  ("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (29, ⟨"module.sanitize_world_payload.copy", [{ name := "value", defaultValue := none },  { name := "depth", defaultValue := some (TargetExpr.integer 0) }], [none,  some (TargetValue.number    (NumberTag.pyInt)    0)], balanceSourceBody (balanceProgram .python) "module.sanitize_world_payload.copy", [("copy", 163),  ("seen", 162),  ("raw", 161),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], none⟩),
 (28, ⟨"WorldChecker.step.security_reject", [{ name := "message", defaultValue := none },  { name := "action", defaultValue := some (TargetExpr.string "<invalid>") }], [none, some (TargetValue.string "<invalid>")], balanceSourceBody (balanceProgram .python) "WorldChecker.step.security_reject", [("security_reject", 151),  ("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (27, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .python) "WorldChecker.step.rollback", [("rollback", 150),  ("previous_undo", 149),  ("original_history", 148),  ("original_context", 147),  ("previous", 146),  ("request", 145),  ("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩),
 (26, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [none], balanceSourceBody (balanceProgram .python) "WorldChecker.step", [("step", 99),  ("reset", 98),  ("_invariant", 97),  ("_bounds", 96),  ("getContext", 95),  ("get_context", 94),  ("getState", 93),  ("get_state", 92),  ("rollback_last_step", 91),  ("history", 90),  ("context", 89),  ("state", 88),  ("__init__", 87),  ("sanitize_world_payload", 86),  ("evaluate_world", 85),  ("_safe_integer", 84),  ("_div", 83),  ("_number", 82),  ("_boolean", 81),  ("_UNDEFINED", 80),  ("_MAX_INTEGER", 79),  ("_EFFECT", 78),  ("_NAME", 77),  ("_TOKEN", 76),  ("_PRECEDENCE", 75),  ("_DEFAULTS", 74),  ("_INITIAL", 71),  ("_WORLD", 69),  ("_freeze", 26),  ("IWorldChecker", 25),  ("Any", 24),  ("types", 23),  ("re", 22),  ("math", 21),  ("json", 20),  ("copy", 19)], some 1⟩)] ++ m.closures
    generators := [(123,   { valueExpr := TargetExpr.local "item",     binders := ["item"],     filterExpr := TargetExpr.andThen                     (TargetExpr.binary                       (BinaryOp.eq)                       (TargetExpr.index                         (TargetExpr.local "item")                         (TargetExpr.string "id"))                       (TargetExpr.local "action"))                     (TargetExpr.binary                       (BinaryOp.eq)                       (TargetExpr.index                         (TargetExpr.local "item")                         (TargetExpr.string "from"))                       (TargetExpr.local "previous")),     remaining := [],     frame := { qualifiedName := "WorldChecker.step.generator",                remaining := [],                locals := [("item", 175)],                captures := [("reject", 174),                             ("record", 173),                             ("payload", 172),                             ("proposed", 160),                             ("action", 159),                             ("value", 158),                             ("key", 157),                             ("raw_payload", 156),                             ("has_proposed", 155),                             ("proposed_val", 154),                             ("has_action", 153),                             ("action_val", 152),                             ("security_reject", 151),                             ("rollback", 150),                             ("previous_undo", 149),                             ("original_history", 148),                             ("original_context", 147),                             ("previous", 146),                             ("request", 145),                             ("step", 99),                             ("reset", 98),                             ("_invariant", 97),                             ("_bounds", 96),                             ("getContext", 95),                             ("get_context", 94),                             ("getState", 93),                             ("get_state", 92),                             ("rollback_last_step", 91),                             ("history", 90),                             ("context", 89),                             ("state", 88),                             ("__init__", 87),                             ("sanitize_world_payload", 86),                             ("evaluate_world", 85),                             ("_safe_integer", 84),                             ("_div", 83),                             ("_number", 82),                             ("_boolean", 81),                             ("_UNDEFINED", 80),                             ("_MAX_INTEGER", 79),                             ("_EFFECT", 78),                             ("_NAME", 77),                             ("_TOKEN", 76),                             ("_PRECEDENCE", 75),                             ("_DEFAULTS", 74),                             ("_INITIAL", 71),                             ("_WORLD", 69),                             ("_freeze", 26),                             ("IWorldChecker", 25),                             ("Any", 24),                             ("types", 23),                             ("re", 22),                             ("math", 21),                             ("json", 20),                             ("copy", 19)],                receiver := some 1,                control := ControlResult.normal } })] ++ m.generators
    writableCells := [(199, true),  (198, true),  (197, true),  (196, true),  (195, true),  (194, true),  (193, true),  (192, true),  (191, true),  (190, true),  (189, true),  (188, true),  (187, true),  (186, true),  (185, true),  (184, true),  (183, true),  (182, true),  (181, true),  (180, true),  (179, true),  (178, true),  (177, true),  (176, true),  (175, true),  (174, true),  (173, true),  (172, true),  (171, true),  (170, true),  (169, true),  (168, true),  (167, true),  (166, true),  (165, true),  (164, true),  (163, true),  (162, true),  (161, true),  (160, true),  (159, true),  (158, true),  (157, true),  (156, true),  (155, true),  (154, true),  (153, true),  (152, true),  (151, true),  (150, true),  (149, true),  (148, true),  (147, true),  (146, true),  (145, true),  (144, true),  (143, true),  (142, true),  (141, true),  (140, true),  (139, true),  (138, true),  (137, true),  (136, true),  (135, true),  (134, true),  (133, true),  (132, true),  (131, true),  (130, true),  (129, true),  (128, true),  (127, true),  (126, true),  (125, true),  (124, true),  (123, true),  (122, true),  (121, true),  (120, true),  (119, true),  (118, true),  (117, true),  (116, true),  (115, true),  (114, true),  (113, true),  (112, true),  (111, true),  (110, true),  (109, true),  (108, true),  (107, true),  (106, true),  (105, true),  (104, true),  (103, true),  (102, true),  (101, true),  (100, true),  (99, true),  (98, true),  (97, true),  (96, true),  (95, true),  (94, true),  (93, true),  (92, true),  (91, true),  (90, true),  (89, true),  (88, true),  (87, true),  (86, true),  (85, true),  (84, true),  (83, true),  (82, true),  (81, true),  (80, true),  (79, true),  (78, true),  (77, true),  (76, true),  (75, true),  (74, true),  (73, true),  (72, true),  (71, true),  (70, true),  (69, true),  (68, true),  (67, true),  (66, true),  (65, true),  (64, true),  (63, true),  (62, true),  (61, true),  (60, true),  (59, true),  (58, true),  (57, true),  (56, true),  (55, true),  (54, true),  (53, true),  (52, true),  (51, true),  (50, true),  (49, true),  (48, true),  (47, true),  (46, true),  (45, true),  (44, true),  (43, true),  (42, true),  (41, true),  (40, true),  (39, true),  (38, true),  (37, true),  (36, true),  (35, true),  (34, true),  (33, true),  (32, true),  (31, true),  (30, true),  (29, true),  (28, true),  (27, true),  (26, true),  (25, true),  (24, true),  (23, true),  (22, true),  (21, true),  (20, true),  (19, true),  (18, false),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 200
    nextObject := 134
    nextClosure := 33
    checker := { state := "Ready",   context := 79,   history := 100,   undo := none,   constructorSeed := some 101,   busy := true,   instanceAttrs := [] } }


def balanceStepTsGuard (b n : Int) : TargetMachine :=
 let m := balanceCanonicalConstructed .ts b
 { m with
    cells := [(122, (TargetValue.bool (decide (0 < n)))),
 (121, TargetValue.undefined),
 (120, TargetValue.undefined),
 (119, TargetValue.number (NumberTag.jsNumber) 0),
 (118, (TargetValue.number (NumberTag.jsNumber) n)),
 (117, TargetValue.number (NumberTag.jsNumber) 0),
 (116, TargetValue.undefined),
 (115, TargetValue.undefined),
 (114, TargetValue.number (NumberTag.jsNumber) 0),
 (113, TargetValue.string "0"),
 (112, TargetValue.number (NumberTag.jsNumber) 6),
 (111, TargetValue.number (NumberTag.jsNumber) 5),
 (110, TargetValue.string ">"),
 (109, TargetValue.string "amount"),
 (108, (TargetValue.bool (decide (0 < n)))),
 (107, TargetValue.string "event"),
 (106, TargetValue.number (NumberTag.jsNumber) 0),
 (105, TargetValue.closure 26),
 (104, TargetValue.closure 25),
 (103, TargetValue.number (NumberTag.jsNumber) 5),
 (102, TargetValue.object 64),
 (101, TargetValue.object 62),
 (100, TargetValue.object 61),
 (99, TargetValue.object 60),
 (98, TargetValue.string "event.amount > 0"),
 (97, TargetValue.object 23),
 (96, TargetValue.string "Ready"),
 (95, TargetValue.closure 24),
 (94, TargetValue.object 14),
 (93, TargetValue.object 14),
 (92, TargetValue.closure 22),
 (91, TargetValue.object 57),
 (90, (TargetValue.number (NumberTag.jsNumber) n)),
 (89, (TargetValue.number (NumberTag.jsNumber) n)),
 (88, TargetValue.object 55),
 (87, TargetValue.string "amount"),
 (86, TargetValue.object 53),
 (85, TargetValue.object 0),
 (84, TargetValue.object 52),
 (83, TargetValue.number (NumberTag.jsNumber) 0),
 (82, TargetValue.object 46),
 (81, TargetValue.object 53),
 (80, TargetValue.null),
 (79, TargetValue.string "DEBIT"),
 (78, TargetValue.object 51),
 (77, TargetValue.undefined),
 (76, TargetValue.object 50),
 (75, TargetValue.closure 21),
 (74, TargetValue.closure 20),
 (73, TargetValue.object 49),
 (72, TargetValue.object 48),
 (71, TargetValue.string "Ready"),
 (70, TargetValue.object 47),
 (69, TargetValue.object 47)] ++ m.cells
    objects := [(68, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^\\d/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (67, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^[A-Za-z_][A-Za-z_0-9]*$/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (66, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^[A-Za-z_]/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (65, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/^\\d/"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (64, ⟨ObjectKind.jsOrdinary, some 0, [("=>", ⟨some (TargetValue.number (NumberTag.jsNumber) 1), none, none, true, true, true⟩),
 ("||", ⟨some (TargetValue.number (NumberTag.jsNumber) 2), none, none, true, true, true⟩),
 ("&&", ⟨some (TargetValue.number (NumberTag.jsNumber) 3), none, none, true, true, true⟩),
 ("==", ⟨some (TargetValue.number (NumberTag.jsNumber) 4), none, none, true, true, true⟩),
 ("!=", ⟨some (TargetValue.number (NumberTag.jsNumber) 4), none, none, true, true, true⟩),
 (">", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 (">=", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 ("<", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 ("<=", ⟨some (TargetValue.number (NumberTag.jsNumber) 5), none, none, true, true, true⟩),
 ("+", ⟨some (TargetValue.number (NumberTag.jsNumber) 6), none, none, true, true, true⟩),
 ("-", ⟨some (TargetValue.number (NumberTag.jsNumber) 6), none, none, true, true, true⟩),
 ("*", ⟨some (TargetValue.number (NumberTag.jsNumber) 7), none, none, true, true, true⟩),
 ("/", ⟨some (TargetValue.number (NumberTag.jsNumber) 7), none, none, true, true, true⟩)], [], [], false, false⟩),
 (63, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string "/\\s+/g"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (62, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "event",
 TargetValue.string ".",
 TargetValue.string "amount",
 TargetValue.string ">",
 TargetValue.string "0"], [], false, false⟩),
 (61, ⟨ObjectKind.regexPattern, some 0, [("source", ⟨some (TargetValue.string   "/=>|==|!=|>=|<=|&&|\\|\\||[()+\\-*/<>!.]|\\d+(?:\\.\\d+)?|[A-Za-z_][A-Za-z_0-9]*|'(?:[^'\\\\]|\\\\.)*'/g"), none, none, true, true, true⟩)], [], [], false, false⟩),
 (60, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("event", ⟨some (TargetValue.object 53), none, none, true, true, true⟩),
 ("request", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (59, ⟨ObjectKind.jsOrdinary, some 0, [], [], [], false, false⟩),
 (58, ⟨ObjectKind.jsOrdinary, some 0, [("eventPayload", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (57, ⟨ObjectKind.jsOrdinary, some 0, [("step", ⟨some (TargetValue.number (NumberTag.jsNumber) 1), none, none, true, true, true⟩),
 ("state", ⟨some (TargetValue.string "Ready"), none, none, true, true, true⟩),
 ("action", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 53), none, none, true, true, true⟩)], [], [], false, false⟩),
 (56, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (55, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (54, ⟨ObjectKind.jsArray, some 0, [], [TargetValue.string "amount"], [], false, false⟩),
 (53, ⟨ObjectKind.jsNullPrototype, none, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (52, ⟨ObjectKind.jsSet, some 0, [], [], [TargetValue.object 46], false, false⟩),
 (51, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some (TargetValue.object 46), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (50, ⟨ObjectKind.jsOrdinary, some 0, [("value", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("get", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("set", ⟨some (TargetValue.undefined), none, none, true, true, true⟩),
 ("enumerable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("writable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩),
 ("configurable", ⟨some (TargetValue.bool true), none, none, true, true, true⟩)], [], [], false, false⟩),
 (49, ⟨ObjectKind.jsArray, some 0, [], [], [], false, false⟩),
 (48, ⟨ObjectKind.jsOrdinary, some 0, [("balance", ⟨some ((TargetValue.number (NumberTag.jsNumber) b)), none, none, true, true, true⟩)], [], [], false, false⟩),
 (47, ⟨ObjectKind.jsOrdinary, some 0, [("transitionId", ⟨some (TargetValue.string "DEBIT"), none, none, true, true, true⟩),
 ("eventPayload", ⟨some (TargetValue.object 46), none, none, true, true, true⟩)], [], [], false, false⟩),
 (46, ⟨ObjectKind.jsOrdinary, some 0, [("amount", ⟨some ((TargetValue.number (NumberTag.jsNumber) n)), none, none, true, true, true⟩)], [], [], false, false⟩)] ++ m.objects
    closures := [(26, ⟨"module.evaluateWorld.parse", [{ name := "minimum", defaultValue := some (TargetExpr.integer 0) }], [none], balanceSourceBody (balanceProgram .ts) "module.evaluateWorld.parse", [("parse", 105),  ("numeric", 104),  ("index", 103),  ("priority", 102),  ("tokens", 101),  ("pattern", 100),  ("env", 99),  ("expression", 98),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], none⟩),
 (25, ⟨"module.evaluateWorld.numeric", [{ name := "value", defaultValue := none }], [none], balanceSourceBody (balanceProgram .ts) "module.evaluateWorld.numeric", [("numeric", 104),  ("index", 103),  ("priority", 102),  ("tokens", 101),  ("pattern", 100),  ("env", 99),  ("expression", 98),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], none⟩),
 (24, ⟨"WorldChecker.step.env", [{ name := "at", defaultValue := none }, { name := "values", defaultValue := none }], [none, none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.env", [("env", 95),  ("transition", 94),  ("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (23, ⟨"WorldChecker.step.lambda", [{ name := "item", defaultValue := none }], [none], TargetStmt.returnValue   (TargetExpr.andThen     (TargetExpr.binary       (BinaryOp.strictEq)       (TargetExpr.property         (TargetExpr.local "item")         "id")       (TargetExpr.local "snapshotAction"))     (TargetExpr.binary       (BinaryOp.strictEq)       (TargetExpr.property         (TargetExpr.local "item")         "from")       (TargetExpr.local "snapshotState"))), [("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (22, ⟨"WorldChecker.step.reject", [{ name := "code", defaultValue := none },  { name := "message", defaultValue := none },  { name := "violatedInvariant", defaultValue := none }], [none, none, none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.reject", [("reject", 92),  ("record", 91),  ("safePayload", 81),  ("snapshotDirective", 80),  ("snapshotAction", 79),  ("descPayload", 78),  ("descDirective", 77),  ("descAction", 76),  ("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (21, ⟨"WorldChecker.step.rejectRequest", [{ name := "message", defaultValue := none }], [none], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rejectRequest", [("rejectRequest", 75),  ("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (20, ⟨"WorldChecker.step.rollback", [], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step.rollback", [("rollback", 74),  ("snapshotHistory", 73),  ("snapshotContext", 72),  ("snapshotState", 71),  ("request", 70),  ("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩),
 (19, ⟨"WorldChecker.step", [{ name := "request", defaultValue := none }], [], balanceSourceBody (balanceProgram .ts) "WorldChecker.step", [("sanitizeWorldPayload", 17),  ("deepFreezeWorld", 16),  ("evaluateWorld", 15),  ("booleanWorld", 14),  ("transitionDefinitions", 13),  ("invariantDefinitions", 12),  ("stateDefinitions", 11),  ("contextDefinitions", 10),  ("contextDefaults", 9),  ("world", 8),  ("nodeTypes", 7)], some 1⟩)] ++ m.closures
    generators := [] ++ m.generators
    writableCells := [(122, false),  (121, false),  (120, false),  (119, true),  (118, true),  (117, false),  (116, false),  (115, false),  (114, true),  (113, false),  (112, true),  (111, false),  (110, false),  (109, false),  (108, true),  (107, false),  (106, true),  (105, false),  (104, false),  (103, true),  (102, false),  (101, false),  (100, false),  (99, true),  (98, true),  (97, true),  (96, true),  (95, false),  (94, false),  (93, true),  (92, false),  (91, false),  (90, true),  (89, false),  (88, false),  (87, false),  (86, false),  (85, false),  (84, true),  (83, true),  (82, true),  (81, true),  (80, false),  (79, false),  (78, false),  (77, false),  (76, false),  (75, false),  (74, false),  (73, false),  (72, false),  (71, false),  (70, true),  (69, true),  (68, false),  (67, false),  (66, false),  (65, false),  (64, false),  (63, true),  (62, true),  (61, false),  (60, false),  (59, false),  (58, true),  (57, false),  (56, true),  (55, false),  (54, false),  (53, true),  (52, false),  (51, true),  (50, false),  (49, false),  (48, true),  (47, false),  (46, false),  (45, false),  (44, true),  (43, true),  (42, false),  (41, false),  (40, true),  (39, true),  (38, true),  (37, false),  (36, false),  (35, false),  (34, false),  (33, true),  (32, false),  (31, false),  (30, false),  (29, false),  (28, false),  (27, false),  (26, true),  (25, false),  (24, false),  (23, false),  (22, false),  (21, false),  (20, true),  (19, true),  (18, true),  (17, false),  (16, false),  (15, false),  (14, false),  (13, false),  (12, false),  (11, false),  (10, false),  (9, false),  (8, false),  (7, false),  (6, false),  (5, false),  (4, false),  (3, false),  (2, false),  (1, false),  (0, false)]
    nextCell := 123
    nextObject := 69
    nextClosure := 27
    checker := { state := "Ready",   context := 23,   history := 44,   undo := none,   constructorSeed := some 45,   busy := true,   instanceAttrs := [] } }


/-- Actual guard RHS selected from the stored protected step subtree. -/
def balanceStepGuardExpression (lang : TargetLang) : TargetExpr :=
 let s := firstStmt (protectedSyntax (firstStmt (dropStmts (if lang == .ts then 18 else 21)
   (balanceStepProtected lang).body))).body
 match s with
 | .letLocal _ _ e => e
 | .assign _ e => e
 | _ => .undefined

def balanceStepGuardRun (lang : TargetLang) (b n : Int) : Except TargetError ExprOutcome :=
 let m := if lang == .ts then balanceStepTsPrefix b n else balanceStepPyPrefix b n
 let f := if lang == .ts then balanceStepTsPrefixFrame else balanceStepPyPrefixFrame
 evalExpr (if lang == .ts then 69 else 65) (balanceProgram lang) m f (balanceStepGuardExpression lang)


set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option Elab.async false

def stepPrefixShape : Nat → TargetStmt → Bool
 | 0, _ => true
 | n + 1, .sequence _ tail => stepPrefixShape n tail
 | _, _ => false

private theorem takeStepStmts_zero (s : TargetStmt) : takeStepStmts 0 s = .empty := by
 with_unfolding_all rfl

private theorem takeStepStmts_succ (n : Nat) (head tail : TargetStmt) :
 takeStepStmts (n + 1) (.sequence head tail) = .sequence head (takeStepStmts n tail) := by
 with_unfolding_all rfl

theorem execStepPrefix_normal (n k : Nat) (program : TargetProgram)
    (m : TargetMachine) (f : TargetFrame) (s : TargetStmt) (final : TargetMachine) (ff : TargetFrame)
    (shape : stepPrefixShape n s = true)
    (run : execStmt (k + n + 1) program m f (takeStepStmts n s) = .ok ⟨final, ff, .normal⟩) :
    execStmt (k + n + 1) program m f s =
      execStmt (k + 1) program final ff (dropStmts n s) := by
  induction n generalizing m f s with
  | zero =>
    rw [takeStepStmts_zero] at run
    have he : execStmt (k + 0 + 1) program m f .empty = .ok ⟨m, f, .normal⟩ :=
      execStmt_adequate (.empty : DepthDerivesStmt program m f .empty ⟨m, f, .normal⟩ 0)
        (Nat.zero_lt_succ (k + 0))
    rw [he] at run
    have same : (⟨m, f, .normal⟩ : StmtOutcome) = ⟨final, ff, .normal⟩ := Except.ok.inj run
    have hm := congrArg StmtOutcome.machine same
    have hf := congrArg StmtOutcome.frame same
    dsimp only at hm hf
    subst final ff
    with_unfolding_all rfl
  | succ n ih =>
    cases s <;> try simp [stepPrefixShape] at shape
    rename_i head tail
    have fuel : k + (n + 1) + 1 = (k + n + 1) + 1 := by rfl
    rw [fuel, execSequence_eq]
    simp only [takeStepStmts_succ, fuel, execSequence_eq] at run
    cases he : execStmt (k + n + 1) program m f head with
    | error e => simp [he, Bind.bind, Except.bind] at run
    | ok out =>
      cases out with
      | mk middle mf control =>
        cases control <;> simp only [he, Bind.bind, Except.bind] at run ⊢
        · exact ih middle mf tail (by exact shape) run
        all_goals cases run



set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option Elab.async false

def balanceStepCanonicalSnapshots (lang : TargetLang) (b n : Int) : TargetMachine × TargetFrame :=
 match lang with
 | .ts => (balanceStepTsSnapshots b n, balanceStepTsSnapshotsFrame)
 | .python => (balanceStepPySnapshots b n, balanceStepPySnapshotsFrame)

def balanceStepCanonicalPrefix (lang : TargetLang) (b n : Int) : TargetMachine × TargetFrame :=
 match lang with
 | .ts => (balanceStepTsPrefix b n, balanceStepTsPrefixFrame)
 | .python => (balanceStepPyPrefix b n, balanceStepPyPrefixFrame)

theorem balanceStep_canonical_snapshots_entry (lang : TargetLang) (b n : Int) :
 evalExpr 100 (balanceProgram lang)
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).1
   (debitCallEntry lang (balanceCanonicalConstructed lang b) n).2
   (debitCallExpression lang) = (do
     let body ← execStmt 97 (balanceProgram lang)
       (balanceStepSnapshotStart lang b n).1 (balanceStepSnapshotStart lang b n).2
       (balanceStepSnapshots lang)
     closureResult lang body) := by
 rw [balanceStep_canonical_call_open lang b n 95, balanceStep_canonical_stored]
 rw [balanceStep_idle_entry (k := 98) (by cases lang <;> rfl) (by cases lang <;> rfl) (by decide)]
 rfl

theorem stepPrefixShape_of_snapshot {n s} (h : snapshotTryCheck n s = true) :
 stepPrefixShape n s = true := by
 induction n generalizing s with
 | zero => rfl
 | succ n ih =>
   have hs := snapshotTryCheck_sequence h
   rw [hs.1]
   exact ih hs.2

theorem balanceStep_prefix_shape (lang : TargetLang) :
 stepPrefixShape (if lang == .ts then 18 else 21) (balanceStepProtected lang).body = true := by
 cases lang <;> unfold balanceStepProtected balanceStepSnapshots balanceStepAfterBusy
 · rw [balanceStep_stored_source, balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
 · rw [balanceStep_stored_source, balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem balanceStep_cleanup_shape (lang : TargetLang) :
 (balanceStepProtected lang).cleanup = .sequence
   (.assign (.property (resetReceiver lang) (if lang == .ts then "#busy" else "_busy")) (.bool false)) .empty := by
 cases lang <;> unfold balanceStepProtected balanceStepSnapshots balanceStepAfterBusy
 · rw [balanceStep_stored_source, balanceProgram_of_parse BalancePrograms.balanceTsProgram_source]; decide +kernel
 · rw [balanceStep_stored_source, balanceProgram_of_parse BalancePrograms.balancePyProgram_source]; decide +kernel

theorem balanceStep_payload_local (lang : TargetLang) (b n : Int) :
 let p := balanceStepCanonicalPrefix lang b n
 localValue p.1 p.2 (if lang == .ts then "safePayload" else "payload") =
   .ok (.object (if lang == .ts then 53 else 114)) := by
 cases lang <;> rfl

theorem balanceStep_payload_amount (lang : TargetLang) (b n : Int) :
 let p := balanceStepCanonicalPrefix lang b n
 readOwn p.1 (if lang == .ts then 53 else 114) "amount" =
   .ok (some ⟨some (.number (if lang == .ts then .jsNumber else .pyFloat) n), none, none, true, true, true⟩) := by
 cases lang <;> rfl

theorem balanceStep_snapshot_values (lang : TargetLang) (b n : Int) :
 let p := balanceStepCanonicalSnapshots lang b n
 balanceContextValue lang p.1 (if lang == .ts then 48 else 104) = .ok b ∧
 decodeBalanceHistory lang p.1 (if lang == .ts then 49 else 105) = .ok [] ∧
 (lang = .python → localValue p.1 p.2 "previous_undo" = .ok .null) := by
 cases lang
 · refine ⟨rfl, rfl, ?_⟩
   intro h; cases h
 · exact ⟨rfl, rfl, fun _ => rfl⟩

theorem balanceStep_prefix_admitted (lang : TargetLang) (b n : Int) :
 let p := balanceStepCanonicalPrefix lang b n
 localValue p.1 p.2 (if lang == .ts then "snapshotState" else "previous") = .ok (.string "Ready") ∧
 localValue p.1 p.2 (if lang == .ts then "snapshotAction" else "action") = .ok (.string "DEBIT") ∧
 localValue p.1 p.2 (if lang == .ts then "snapshotDirective" else "proposed") = .ok .null ∧
 localValue p.1 p.2 (if lang == .ts then "descDirective" else "has_proposed") =
   .ok (if lang == .ts then .undefined else .bool false) ∧
 localValue p.1 p.2 "rollback" = .ok (.closure (if lang == .ts then 20 else 27)) ∧
 localValue p.1 p.2 (if lang == .ts then "rejectRequest" else "security_reject") =
   .ok (.closure (if lang == .ts then 21 else 28)) ∧
 localValue p.1 p.2 "reject" = .ok (.closure (if lang == .ts then 22 else 30)) ∧
 localValue p.1 p.2 "transition" = .ok (.object (if lang == .ts then 14 else 61)) ∧
 localValue p.1 p.2 (if lang == .ts then "env" else "environment") =
   .ok (.closure (if lang == .ts then 24 else 31)) ∧
 readOwn p.1 (if lang == .ts then 57 else 122) "proposedDirective" = .ok none ∧
 readOwn p.1 (if lang == .ts then 57 else 122) "eventPayload" =
   .ok (some ⟨some (.object (if lang == .ts then 53 else 114)), none, none, true, true, true⟩) := by
 cases lang <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩



set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
set_option smartUnfolding false
set_option Elab.async false

def balanceStepGuardRejected (lang : TargetLang) (b n : Int) : TargetOutcome :=
 match lang with
 | .ts => ⟨balanceStepTsRejected b n, .object 71⟩
 | .python => ⟨balanceStepPyRejected b n, .object 142⟩

theorem balanceStep_guardRejected_projection (lang : TargetLang) (b n : Int) :
 targetProjection lang (balanceStepGuardRejected lang b n) =
   .ok ⟨false, "Ready", [("balance", b)], none⟩ := by
 cases lang <;> rfl

theorem balanceStep_guardRejected_code (lang : TargetLang) (b n : Int) :
 targetViolationCode (balanceStepGuardRejected lang b n) = .ok (some "GUARD_FAILED") := by
 cases lang <;> rfl

theorem balanceStep_guardRejected_frame (lang : TargetLang) (b n : Int) :
 balanceView lang (balanceStepGuardRejected lang b n).machine =
   .ok ⟨"Ready", b, [], none, b, false⟩ := by
 cases lang <;> rfl

theorem balanceStep_guardRejected_WF_zero (lang : TargetLang) :
 HeapWF lang (balanceStepGuardRejected lang 0 0).machine := by
 cases lang <;> decide +kernel

theorem balanceStep_guardRejected_WF_footprint (lang : TargetLang) (b n : Int) :
 heapWFCheck lang (balanceStepGuardRejected lang b n).machine =
   heapWFCheck lang (balanceStepGuardRejected lang 0 0).machine := by
 cases lang <;> with_unfolding_all rfl

theorem balanceStep_guardRejected_WF (lang : TargetLang) (b n : Int) :
 HeapWF lang (balanceStepGuardRejected lang b n).machine := by
 exact (balanceStep_guardRejected_WF_footprint lang b n).trans (balanceStep_guardRejected_WF_zero lang)

end Harmonia.Applications.Kadmos.Generated
