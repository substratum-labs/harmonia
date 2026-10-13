import Harmonia.Applications.Kadmos.Generated.TargetSemantics

namespace Harmonia.Applications.Kadmos.Generated

/-- Unfueled execution configurations. The current rule slice covers scalar
    leaves, ordered binary evaluation and elementary statement/control paths;
    calls and collection/helper execution remain to add. -/
inductive TargetFocus where
  | eval (expr : TargetExpr)
  | exec (stmt : TargetStmt)
  | value (value : TargetValue)
  | exit (control : ControlResult)
  deriving Repr

/-- Continuations own ordered children and pending statement actions. A
    finalizer saves the outcome control before a caught frame is cleared. -/
inductive ResumeFrame where
  | binaryLeft (op : BinaryOp) (right : TargetExpr)
  | binaryRight (op : BinaryOp) (left : TargetValue)
  | stmtIf (yes no : TargetStmt)
  | stmtSequence (rest : TargetStmt)
  | stmtReturn | stmtThrow
  | stmtAssignField (name : String)
  | stmtProtect (catchType binder : Option String) (handler cleanup : TargetStmt)
  | stmtHandledFinally (cleanup : TargetStmt)
  | stmtFinally (saved : ControlResult)
  deriving Repr

structure TargetConfig where
  machine : TargetMachine
  frame : TargetFrame
  focus : TargetFocus
  continuation : List ResumeFrame
  deriving Repr

def exprResultFocus : Except TargetValue TargetValue → TargetFocus
  | .ok value => .value value
  | .error value => .exit (.raised value)

def integerValue (lang : TargetLang) (n : Int) : TargetValue :=
  .number (if lang == .ts then .jsNumber else .pyInt) n

/-- No evaluator or depth budget occurs in a transition premise. The binary
    primitive is the existing basic operation, never a generated helper body.
    Python list addition has allocation semantics and is outside this slice. -/
inductive SmallStep (program : TargetProgram) : TargetConfig → TargetConfig → Prop where
  | undefined {m f c} :
      SmallStep program ⟨m, f, .eval .undefined, c⟩ ⟨m, f, .value .undefined, c⟩
  | null {m f c} :
      SmallStep program ⟨m, f, .eval .null, c⟩ ⟨m, f, .value .null, c⟩
  | bool {m f c} (b : Bool) :
      SmallStep program ⟨m, f, .eval (.bool b), c⟩ ⟨m, f, .value (.bool b), c⟩
  | integer {m f c} (n : Int) :
      SmallStep program ⟨m, f, .eval (.integer n), c⟩
        ⟨m, f, .value (integerValue program.lang n), c⟩
  | string {m f c} (s : String) :
      SmallStep program ⟨m, f, .eval (.string s), c⟩ ⟨m, f, .value (.string s), c⟩
  | localRead {m f c name value} (h : localValue m f name = .ok value) :
      SmallStep program ⟨m, f, .eval (.local name), c⟩ ⟨m, f, .value value, c⟩
  | global {m f c name value} (h : localValue m f name = .ok value) :
      SmallStep program ⟨m, f, .eval (.global name), c⟩ ⟨m, f, .value value, c⟩
  | checkerField {m f c name value} (h : readCheckerField m name = .ok value) :
      SmallStep program ⟨m, f, .eval (.checkerField name), c⟩ ⟨m, f, .value value, c⟩
  | binaryEnter {m f c op left right} :
      SmallStep program ⟨m, f, .eval (.binary op left right), c⟩
        ⟨m, f, .eval left, .binaryLeft op right :: c⟩
  | binaryNext {m f c op left right} :
      SmallStep program ⟨m, f, .value left, .binaryLeft op right :: c⟩
        ⟨m, f, .eval right, .binaryRight op left :: c⟩
  | binaryLeftRaised {m f c op right value} :
      SmallStep program ⟨m, f, .exit (.raised value), .binaryLeft op right :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | binaryRightRaised {m f c op left value} :
      SmallStep program ⟨m, f, .exit (.raised value), .binaryRight op left :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | binaryFinish {m f c op left right result}
      (hOp : op ≠ .add)
      (hApply : binaryValue program.lang m op left right = .ok result) :
      SmallStep program ⟨m, f, .value right, .binaryRight op left :: c⟩
        ⟨m, f, exprResultFocus result, c⟩

  | stmtIfEnter {m f c cond yes no} :
      SmallStep program ⟨m, f, .exec (.ifThenElse cond yes no), c⟩
        ⟨m, f, .eval cond, .stmtIf yes no :: c⟩
  | stmtIfTrue {m f c yes no value}
      (h : sourceTruthy program.lang m value = .ok true) :
      SmallStep program ⟨m, f, .value value, .stmtIf yes no :: c⟩
        ⟨m, f, .exec yes, c⟩
  | stmtIfFalse {m f c yes no value}
      (h : sourceTruthy program.lang m value = .ok false) :
      SmallStep program ⟨m, f, .value value, .stmtIf yes no :: c⟩
        ⟨m, f, .exec no, c⟩
  | stmtIfRaised {m f c yes no value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtIf yes no :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtEmpty {m f c} :
      SmallStep program ⟨m, f, .exec .empty, c⟩ ⟨m, f, .exit .normal, c⟩
  | stmtSequence {m f c first rest} :
      SmallStep program ⟨m, f, .exec (.sequence first rest), c⟩
        ⟨m, f, .exec first, .stmtSequence rest :: c⟩
  | stmtSequenceNext {m f c rest} :
      SmallStep program ⟨m, f, .exit .normal, .stmtSequence rest :: c⟩
        ⟨m, f, .exec rest, c⟩
  | stmtSequenceExit {m f c rest control} (h : control ≠ .normal) :
      SmallStep program ⟨m, f, .exit control, .stmtSequence rest :: c⟩
        ⟨m, f, .exit control, c⟩
  | stmtReturnVoid {m f c} :
      SmallStep program ⟨m, f, .exec .returnVoid, c⟩
        ⟨m, f, .exit (.returned .undefined), c⟩
  | stmtReturnEnter {m f c expr} :
      SmallStep program ⟨m, f, .exec (.returnValue expr), c⟩
        ⟨m, f, .eval expr, .stmtReturn :: c⟩
  | stmtReturnFinish {m f c value} :
      SmallStep program ⟨m, f, .value value, .stmtReturn :: c⟩
        ⟨m, f, .exit (.returned value), c⟩
  | stmtReturnRaised {m f c value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtReturn :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtThrowEnter {m f c expr} :
      SmallStep program ⟨m, f, .exec (.throwValue expr), c⟩
        ⟨m, f, .eval expr, .stmtThrow :: c⟩
  | stmtThrowFinish {m f c value} :
      SmallStep program ⟨m, f, .value value, .stmtThrow :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtThrowRaised {m f c value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtThrow :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtRethrow {m f c value} (h : f.control = .raised value) :
      SmallStep program ⟨m, f, .exec .rethrow, c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtBreak {m f c label} :
      SmallStep program ⟨m, f, .exec (.breakTarget label), c⟩
        ⟨m, f, .exit (.broke label), c⟩
  | stmtContinue {m f c label} :
      SmallStep program ⟨m, f, .exec (.continueTarget label), c⟩
        ⟨m, f, .exit (.continued label), c⟩
  | stmtAssignFieldEnter {m f c name expr} :
      SmallStep program ⟨m, f, .exec (.assign (.field name) expr), c⟩
        ⟨m, f, .eval expr, .stmtAssignField name :: c⟩
  | stmtAssignFieldFinish {m final f c name value}
      (h : writeCheckerField m name value = .ok final) :
      SmallStep program ⟨m, f, .value value, .stmtAssignField name :: c⟩
        ⟨final, f, .exit .normal, c⟩
  | stmtAssignFieldRaised {m f c name value} :
      SmallStep program ⟨m, f, .exit (.raised value), .stmtAssignField name :: c⟩
        ⟨m, f, .exit (.raised value), c⟩
  | stmtProtectEnter {m f c body catchType binder handler cleanup} :
      SmallStep program ⟨m, f, .exec (.tryCatchFinally body catchType binder handler cleanup), c⟩
        ⟨m, f, .exec body, .stmtProtect catchType binder handler cleanup :: c⟩
  | stmtProtectUncaught {m f c control catchType binder handler cleanup}
      (h : controlCaught catchType control = false) :
      SmallStep program ⟨m, f, .exit control, .stmtProtect catchType binder handler cleanup :: c⟩
        ⟨m, f, .exec cleanup, .stmtFinally control :: c⟩
  | stmtProtectCaught {m f c errorValue catchType binder handler cleanup}
      (h : controlCaught catchType (.raised errorValue) = true) :
      SmallStep program
        ⟨m, f, .exit (.raised errorValue), .stmtProtect catchType binder handler cleanup :: c⟩
        ⟨(bindCatchFrame m f binder errorValue).1,
          (bindCatchFrame m f binder errorValue).2,
          .exec handler, .stmtHandledFinally cleanup :: c⟩
  | stmtHandlerExit {m f c control cleanup} :
      SmallStep program ⟨m, f, .exit control, .stmtHandledFinally cleanup :: c⟩
        ⟨m, { f with control := .normal }, .exec cleanup, .stmtFinally control :: c⟩
  | stmtFinallyNormal {m f c saved} :
      SmallStep program ⟨m, f, .exit .normal, .stmtFinally saved :: c⟩
        ⟨m, f, .exit saved, c⟩
  | stmtFinallyOverride {m f c saved control} (h : control ≠ .normal) :
      SmallStep program ⟨m, f, .exit control, .stmtFinally saved :: c⟩
        ⟨m, f, .exit control, c⟩

inductive Runs (program : TargetProgram) : TargetConfig → TargetConfig → Prop where
  | refl (config) : Runs program config config
  | tail {first middle last} : Runs program first middle →
      SmallStep program middle last → Runs program first last

theorem Runs.single {program first last} (h : SmallStep program first last) :
    Runs program first last := .tail (.refl first) h

theorem Runs.trans {program first middle last}
    (hFirst : Runs program first middle) (hLast : Runs program middle last) :
    Runs program first last := by
  induction hLast with
  | refl => exact hFirst
  | tail _ hStep ih => exact .tail ih hStep

/-- A separately indexed diagnostic trace count. Counting is relational:
    Prop-valued Runs proofs cannot be eliminated into a Nat function. The count
    is never an executable fuel premise and never uses TargetMachine.fuel. -/
inductive CountedRuns (program : TargetProgram) :
    TargetConfig → TargetConfig → Nat → Prop where
  | refl (config) : CountedRuns program config config 0
  | tail {first middle last n} : CountedRuns program first middle n →
      SmallStep program middle last → CountedRuns program first last (n + 1)

theorem CountedRuns.single {program first last} (h : SmallStep program first last) :
    CountedRuns program first last 1 := .tail (.refl first) h

theorem CountedRuns.trans {program first middle last n m}
    (hFirst : CountedRuns program first middle n)
    (hLast : CountedRuns program middle last m) :
    CountedRuns program first last (n + m) := by
  induction hLast with
  | refl => simpa using hFirst
  | tail _ step ih => simpa [Nat.add_assoc] using CountedRuns.tail ih step

theorem CountedRuns.forget {program first last n}
    (h : CountedRuns program first last n) : Runs program first last := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact .tail ih step

def ExprRuns (program : TargetProgram) (machine : TargetMachine)
    (frame : TargetFrame) (expr : TargetExpr) (outcome : ExprOutcome) : Prop :=
  Runs program ⟨machine, frame, .eval expr, []⟩
    ⟨outcome.machine, frame, exprResultFocus outcome.result, []⟩

/-- Semantic derivations, independent of evaluator success. Sibling children
    share the predecessor depth: their maximum, not their sum, determines rank.
    This initial slice intentionally does not assert coverage of all syntax. -/
inductive DepthDerivesExpr (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetExpr → ExprOutcome → Nat → Prop where
  | undefined {m f} : DepthDerivesExpr program m f .undefined ⟨m, .ok .undefined⟩ 0
  | null {m f} : DepthDerivesExpr program m f .null ⟨m, .ok .null⟩ 0
  | bool {m f} (b : Bool) : DepthDerivesExpr program m f (.bool b) ⟨m, .ok (.bool b)⟩ 0
  | integer {m f} (n : Int) : DepthDerivesExpr program m f (.integer n)
      ⟨m, .ok (integerValue program.lang n)⟩ 0
  | string {m f} (s : String) : DepthDerivesExpr program m f (.string s) ⟨m, .ok (.string s)⟩ 0
  | localRead {m f name value} (h : localValue m f name = .ok value) :
      DepthDerivesExpr program m f (.local name) ⟨m, .ok value⟩ 0
  | global {m f name value} (h : localValue m f name = .ok value) :
      DepthDerivesExpr program m f (.global name) ⟨m, .ok value⟩ 0
  | checkerField {m f name value} (h : readCheckerField m name = .ok value) :
      DepthDerivesExpr program m f (.checkerField name) ⟨m, .ok value⟩ 0
  | binaryLeftRaised {m f left right op final value rank}
      (hLeft : DepthDerivesExpr program m f left ⟨final, .error value⟩ rank) :
      DepthDerivesExpr program m f (.binary op left right) ⟨final, .error value⟩ (1 + rank)
  | binaryRightRaised {m f left right op middle final lv value leftRank rightRank}
      (hLeft : DepthDerivesExpr program m f left ⟨middle, .ok lv⟩ leftRank)
      (hRight : DepthDerivesExpr program middle f right ⟨final, .error value⟩ rightRank) :
      DepthDerivesExpr program m f (.binary op left right) ⟨final, .error value⟩
        (1 + max leftRank rightRank)
  | binary {m f left right op middle final lv rv result leftRank rightRank}
      (hOp : op ≠ .add)
      (hLeft : DepthDerivesExpr program m f left ⟨middle, .ok lv⟩ leftRank)
      (hRight : DepthDerivesExpr program middle f right ⟨final, .ok rv⟩ rightRank)
      (hApply : binaryValue program.lang final op lv rv = .ok result) :
      DepthDerivesExpr program m f (.binary op left right) ⟨final, result⟩
        (1 + max leftRank rightRank)

theorem expr_path_runs_cont {program machine frame expr outcome rank}
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (continuation : List ResumeFrame) :
    Runs program ⟨machine, frame, .eval expr, continuation⟩
      ⟨outcome.machine, frame, exprResultFocus outcome.result, continuation⟩ := by
  induction h generalizing continuation with
  | undefined => exact Runs.single .undefined
  | null => exact Runs.single .null
  | bool b => exact Runs.single (.bool b)
  | integer n => exact Runs.single (.integer n)
  | string s => exact Runs.single (.string s)
  | localRead h => exact .single (.localRead h)
  | global h => exact .single (.global h)
  | checkerField h => exact .single (.checkerField h)
  | binaryLeftRaised _ ih =>
      exact ((Runs.single .binaryEnter).trans (ih _)).tail .binaryLeftRaised
  | binaryRightRaised _ _ ihLeft ihRight =>
      exact (((Runs.single .binaryEnter).trans (ihLeft _)).tail
        .binaryNext |>.trans (ihRight _)).tail .binaryRightRaised
  | binary hOp _ _ hApply ihLeft ihRight =>
      exact (((Runs.single .binaryEnter).trans (ihLeft _)).tail
        .binaryNext |>.trans (ihRight _)).tail (.binaryFinish hOp hApply)

theorem expr_path_runs {program machine frame expr outcome rank}
    (h : DepthDerivesExpr program machine frame expr outcome rank) :
    ExprRuns program machine frame expr outcome := expr_path_runs_cont h []

theorem evalExpr_adequate {program machine frame expr outcome rank k}
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (hr : rank < k) : evalExpr k program machine frame expr = .ok outcome := by
  induction h generalizing k with
  | undefined => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | null => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | bool b => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | integer n => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | string s => cases k with
      | zero => exfalso; omega
      | succ k => simp only [evalExpr]; rfl
  | localRead h | global h | checkerField h =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          simp [evalExpr, h, Bind.bind, Pure.pure, Except.bind, Except.pure]
          rfl
  | @binaryLeftRaised m f left right op final value rank hLeft ih =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hl : rank < k := by omega
          simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, ih hl]
  | @binaryRightRaised m f left right op middle final lv value leftRank rightRank hLeft hRight ihLeft ihRight =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hl : leftRank < k := by omega
          have hr' : rightRank < k := by omega
          simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, ihLeft hl, ihRight hr']
  | @binary m f left right op middle final lv rv result leftRank rightRank hOp hLeft hRight hApply ihLeft ihRight =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
          have hl : leftRank < k := by omega
          have hr' : rightRank < k := by omega
          simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, ihLeft hl, ihRight hr', hOp, hApply]

/-- Adequacy forces any two supported paths of the same expression to have
    the same result, even if their derivation ranks differ. -/
theorem DepthDerivesExpr.deterministic {program m f expr out₁ out₂ r₁ r₂}
    (h₁ : DepthDerivesExpr program m f expr out₁ r₁)
    (h₂ : DepthDerivesExpr program m f expr out₂ r₂) : out₁ = out₂ := by
  have hk₁ : r₁ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hk₂ : r₂ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact Except.ok.inj ((evalExpr_adequate h₁ hk₁).symm.trans (evalExpr_adequate h₂ hk₂))

/-- Syntax coverage of this read-only proof slice; `.add` needs a separate
    Python list-concatenation rule before entering the common binary case. -/
inductive ScalarSyntax : TargetExpr → Prop where
  | undefined : ScalarSyntax .undefined
  | null : ScalarSyntax .null
  | bool (b : Bool) : ScalarSyntax (.bool b)
  | integer (n : Int) : ScalarSyntax (.integer n)
  | string (s : String) : ScalarSyntax (.string s)
  | localRead (name : String) : ScalarSyntax (.local name)
  | global (name : String) : ScalarSyntax (.global name)
  | checkerField (name : String) : ScalarSyntax (.checkerField name)
  | binary {op left right} (hOp : op ≠ .add)
      (hLeft : ScalarSyntax left) (hRight : ScalarSyntax right) :
      ScalarSyntax (.binary op left right)

/-- Evaluator soundness for the explicitly covered syntax, including raised
    source outcomes on either ordered child. No success premise occurs in the
    semantic derivation constructors themselves. -/
theorem evalScalar_sound {program machine frame expr outcome k}
    (hs : ScalarSyntax expr)
    (h : evalExpr k program machine frame expr = .ok outcome) :
    ∃ rank, DepthDerivesExpr program machine frame expr outcome rank ∧ rank < k := by
  induction hs generalizing k machine outcome with
  | undefined =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .undefined, by omega⟩
  | null =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .null, by omega⟩
  | bool b =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .bool b, by omega⟩
  | integer n =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .integer n, by omega⟩
  | string s =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k => simp only [evalExpr] at h; cases h; exact ⟨0, .string s, by omega⟩
  | localRead name =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hv : localValue machine frame name with
          | error e =>
              simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
          | ok value =>
              simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
              cases h
              exact ⟨0, .localRead hv, by omega⟩
  | global name =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hv : localValue machine frame name with
          | error e =>
              simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
          | ok value =>
              simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
              cases h
              exact ⟨0, .global hv, by omega⟩
  | checkerField name =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hv : readCheckerField machine name with
          | error e =>
              simp [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
          | ok value =>
              simp only [evalExpr, hv, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
              cases h
              exact ⟨0, .checkerField hv, by omega⟩
  | @binary op left right hOp _ _ ihLeft ihRight =>
      cases k with
      | zero => simp [evalExpr] at h
      | succ k =>
          cases hLeft : evalExpr k program machine frame left with
          | error err => simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft] at h
          | ok lhs =>
              rcases lhs with ⟨middle, lhs⟩
              obtain ⟨leftRank, leftPath, leftBound⟩ := ihLeft hLeft
              cases lhs with
              | error value =>
                  have heq : outcome = ⟨middle, .error value⟩ := by
                    simpa [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft] using h.symm
                  subst outcome
                  exact ⟨1 + leftRank, .binaryLeftRaised leftPath, by omega⟩
              | ok lv =>
                  cases hRight : evalExpr k program middle frame right with
                  | error err => simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight] at h
                  | ok rhs =>
                      rcases rhs with ⟨final, rhs⟩
                      obtain ⟨rightRank, rightPath, rightBound⟩ := ihRight hRight
                      cases rhs with
                      | error value =>
                          have heq : outcome = ⟨final, .error value⟩ := by
                            simpa [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight] using h.symm
                          subst outcome
                          exact ⟨1 + max leftRank rightRank,
                            .binaryRightRaised leftPath rightPath, by omega⟩
                      | ok rv =>
                          cases hApply : binaryValue program.lang final op lv rv with
                          | error err => simp [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight, hOp, hApply] at h
                          | ok result =>
                              have heq : outcome = ⟨final, result⟩ := by
                                simpa [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map, evalExpr, hLeft, hRight, hOp, hApply] using h.symm
                              subst outcome
                              exact ⟨1 + max leftRank rightRank,
                                .binary hOp leftPath rightPath hApply, by omega⟩

/-- Expression derivations in the scalar slice still preserve the machine.
    General Runs now include statement writes and cannot claim this property. -/
theorem DepthDerivesExpr.machine_eq {program m f expr out rank}
    (h : DepthDerivesExpr program m f expr out rank) : out.machine = m := by
  induction h with
  | undefined | null | bool | integer | string | localRead | global | checkerField => rfl
  | binaryLeftRaised _ ih => exact ih
  | binaryRightRaised _ _ ihLeft ihRight => exact ihRight.trans ihLeft
  | binary _ _ _ _ ihLeft ihRight => exact ihRight.trans ihLeft


/-- Ranked statement derivations. Each recursive sequence tail is a depth edge;
    first/rest, body/cleanup and expression siblings share predecessor fuel. -/
inductive DepthDerivesStmt (program : TargetProgram) :
    TargetMachine → TargetFrame → TargetStmt → StmtOutcome → Nat → Prop where
  | ifTrue {m f cond yes no middle value out rCond rBranch}
      (hCond : DepthDerivesExpr program m f cond ⟨middle, .ok value⟩ rCond)
      (hTruth : sourceTruthy program.lang middle value = .ok true)
      (hBranch : DepthDerivesStmt program middle f yes out rBranch) :
      DepthDerivesStmt program m f (.ifThenElse cond yes no) out
        (1 + max rCond rBranch)
  | ifFalse {m f cond yes no middle value out rCond rBranch}
      (hCond : DepthDerivesExpr program m f cond ⟨middle, .ok value⟩ rCond)
      (hTruth : sourceTruthy program.lang middle value = .ok false)
      (hBranch : DepthDerivesStmt program middle f no out rBranch) :
      DepthDerivesStmt program m f (.ifThenElse cond yes no) out
        (1 + max rCond rBranch)
  | ifRaised {m f cond yes no final value rank}
      (hCond : DepthDerivesExpr program m f cond ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.ifThenElse cond yes no)
        ⟨final, f, .raised value⟩ (1 + rank)
  | empty {m f} : DepthDerivesStmt program m f .empty ⟨m, f, .normal⟩ 0
  | returnVoid {m f} :
      DepthDerivesStmt program m f .returnVoid ⟨m, f, .returned .undefined⟩ 0
  | breakTarget {m f} (label : String) :
      DepthDerivesStmt program m f (.breakTarget label) ⟨m, f, .broke label⟩ 0
  | continueTarget {m f} (label : String) :
      DepthDerivesStmt program m f (.continueTarget label) ⟨m, f, .continued label⟩ 0
  | rethrow {m f value} (h : f.control = .raised value) :
      DepthDerivesStmt program m f .rethrow ⟨m, f, .raised value⟩ 0
  | sequenceNormal {m f first rest middle midFrame final rankFirst rankRest}
      (hFirst : DepthDerivesStmt program m f first ⟨middle, midFrame, .normal⟩ rankFirst)
      (hRest : DepthDerivesStmt program middle midFrame rest final rankRest) :
      DepthDerivesStmt program m f (.sequence first rest) final (1 + max rankFirst rankRest)
  | sequenceExit {m f first rest out rank}
      (hFirst : DepthDerivesStmt program m f first out rank)
      (hExit : out.control ≠ .normal) :
      DepthDerivesStmt program m f (.sequence first rest) out (1 + rank)
  | returnValue {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank) :
      DepthDerivesStmt program m f (.returnValue expr) ⟨final, f, .returned value⟩ (1 + rank)
  | returnRaised {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.returnValue expr) ⟨final, f, .raised value⟩ (1 + rank)
  | throwValue {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .ok value⟩ rank) :
      DepthDerivesStmt program m f (.throwValue expr) ⟨final, f, .raised value⟩ (1 + rank)
  | throwRaised {m f expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.throwValue expr) ⟨final, f, .raised value⟩ (1 + rank)
  | assignField {m f name expr middle final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨middle, .ok value⟩ rank)
      (hWrite : writeCheckerField middle name value = .ok final) :
      DepthDerivesStmt program m f (.assign (.field name) expr) ⟨final, f, .normal⟩ (1 + rank)
  | assignFieldRaised {m f name expr final value rank}
      (hExpr : DepthDerivesExpr program m f expr ⟨final, .error value⟩ rank) :
      DepthDerivesStmt program m f (.assign (.field name) expr) ⟨final, f, .raised value⟩ (1 + rank)
  | finallyNormal {m f body catchType binder handler cleanup attempted final finalFrame rb rc}
      (hBody : DepthDerivesStmt program m f body attempted rb)
      (hUncaught : controlCaught catchType attempted.control = false)
      (hCleanup : DepthDerivesStmt program attempted.machine attempted.frame cleanup
        ⟨final, finalFrame, .normal⟩ rc) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        ⟨final, finalFrame, attempted.control⟩ (1 + max rb rc)
  | finallyOverride {m f body catchType binder handler cleanup attempted final rb rc}
      (hBody : DepthDerivesStmt program m f body attempted rb)
      (hUncaught : controlCaught catchType attempted.control = false)
      (hCleanup : DepthDerivesStmt program attempted.machine attempted.frame cleanup final rc)
      (hExit : final.control ≠ .normal) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        final (1 + max rb rc)

  | caughtFinallyNormal {m f body catchType binder handler cleanup middle midFrame errorValue
      handled final finalFrame rb rh rc}
      (hBody : DepthDerivesStmt program m f body ⟨middle, midFrame, .raised errorValue⟩ rb)
      (hCaught : controlCaught catchType (.raised errorValue) = true)
      (hHandler : DepthDerivesStmt program (bindCatchFrame middle midFrame binder errorValue).1
        (bindCatchFrame middle midFrame binder errorValue).2 handler handled rh)
      (hCleanup : DepthDerivesStmt program handled.machine
        { handled.frame with control := .normal } cleanup ⟨final, finalFrame, .normal⟩ rc) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        ⟨final, finalFrame, handled.control⟩ (1 + max rb (max rh rc))
  | caughtFinallyOverride {m f body catchType binder handler cleanup middle midFrame errorValue
      handled final rb rh rc}
      (hBody : DepthDerivesStmt program m f body ⟨middle, midFrame, .raised errorValue⟩ rb)
      (hCaught : controlCaught catchType (.raised errorValue) = true)
      (hHandler : DepthDerivesStmt program (bindCatchFrame middle midFrame binder errorValue).1
        (bindCatchFrame middle midFrame binder errorValue).2 handler handled rh)
      (hCleanup : DepthDerivesStmt program handled.machine
        { handled.frame with control := .normal } cleanup final rc)
      (hExit : final.control ≠ .normal) :
      DepthDerivesStmt program m f (.tryCatchFinally body catchType binder handler cleanup)
        final (1 + max rb (max rh rc))

def StmtRuns (program : TargetProgram) (machine : TargetMachine) (frame : TargetFrame)
    (stmt : TargetStmt) (outcome : StmtOutcome) : Prop :=
  Runs program ⟨machine, frame, .exec stmt, []⟩
    ⟨outcome.machine, outcome.frame, .exit outcome.control, []⟩

theorem stmt_path_runs_cont {program machine frame stmt outcome rank}
    (h : DepthDerivesStmt program machine frame stmt outcome rank)
    (continuation : List ResumeFrame) :
    Runs program ⟨machine, frame, .exec stmt, continuation⟩
      ⟨outcome.machine, outcome.frame, .exit outcome.control, continuation⟩ := by
  induction h generalizing continuation with
  | ifTrue hc ht hb ih =>
      exact (((Runs.single .stmtIfEnter).trans (expr_path_runs_cont hc _)).trans
        (.single (.stmtIfTrue ht))).trans (ih _)
  | ifFalse hc ht hb ih =>
      exact (((Runs.single .stmtIfEnter).trans (expr_path_runs_cont hc _)).trans
        (.single (.stmtIfFalse ht))).trans (ih _)
  | ifRaised hc =>
      exact ((Runs.single .stmtIfEnter).trans (expr_path_runs_cont hc _)).trans
        (.single .stmtIfRaised)
  | empty => exact .single .stmtEmpty
  | returnVoid => exact .single .stmtReturnVoid
  | breakTarget label => exact .single .stmtBreak
  | continueTarget label => exact .single .stmtContinue
  | rethrow h => exact .single (.stmtRethrow h)
  | sequenceNormal hFirst hRest ihFirst ihRest =>
      exact ((Runs.single .stmtSequence).trans (ihFirst _)).trans
        ((Runs.single .stmtSequenceNext).trans (ihRest _))
  | sequenceExit hFirst hExit ih =>
      exact ((Runs.single .stmtSequence).trans (ih _)).trans
        (.single (.stmtSequenceExit hExit))
  | returnValue hExpr =>
      exact ((Runs.single .stmtReturnEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtReturnFinish)
  | returnRaised hExpr =>
      exact ((Runs.single .stmtReturnEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtReturnRaised)
  | throwValue hExpr =>
      exact ((Runs.single .stmtThrowEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtThrowFinish)
  | throwRaised hExpr =>
      exact ((Runs.single .stmtThrowEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtThrowRaised)
  | assignField hExpr hWrite =>
      exact ((Runs.single .stmtAssignFieldEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single (.stmtAssignFieldFinish hWrite))
  | assignFieldRaised hExpr =>
      exact ((Runs.single .stmtAssignFieldEnter).trans (expr_path_runs_cont hExpr _)).trans
        (.single .stmtAssignFieldRaised)
  | finallyNormal hBody hUncaught hCleanup ihBody ihCleanup =>
      exact ((((Runs.single .stmtProtectEnter).trans (ihBody _)).trans
        (.single (.stmtProtectUncaught hUncaught))).trans (ihCleanup _)).trans
          (.single .stmtFinallyNormal)
  | finallyOverride hBody hUncaught hCleanup hExit ihBody ihCleanup =>
      exact ((((Runs.single .stmtProtectEnter).trans (ihBody _)).trans
        (.single (.stmtProtectUncaught hUncaught))).trans (ihCleanup _)).trans
          (.single (.stmtFinallyOverride hExit))

  | caughtFinallyNormal hb hc hh hcl ihb ihh ihcl =>
      exact ((((((Runs.single .stmtProtectEnter).trans (ihb _)).trans
        (.single (.stmtProtectCaught hc))).trans (ihh _)).trans
          (.single .stmtHandlerExit)).trans (ihcl _)).trans (.single .stmtFinallyNormal)
  | caughtFinallyOverride hb hc hh hcl he ihb ihh ihcl =>
      exact ((((((Runs.single .stmtProtectEnter).trans (ihb _)).trans
        (.single (.stmtProtectCaught hc))).trans (ihh _)).trans
          (.single .stmtHandlerExit)).trans (ihcl _)).trans (.single (.stmtFinallyOverride he))

theorem stmt_path_runs {program machine frame stmt outcome rank}
    (h : DepthDerivesStmt program machine frame stmt outcome rank) :
    StmtRuns program machine frame stmt outcome := stmt_path_runs_cont h []

/-- Reverse adequacy for the supported statement paths, including a mutating
    finalizer. No executable success is a premise of a semantic derivation. -/
theorem execStmt_adequate {program machine frame stmt outcome rank k}
    (h : DepthDerivesStmt program machine frame stmt outcome rank)
    (hr : rank < k) : execStmt k program machine frame stmt = .ok outcome := by
  induction h generalizing k with
  | @ifTrue m f cond yes no middle value out rc rb hc ht hb ih
  | @ifFalse m f cond yes no middle value out rc rb hc ht hb ih =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hck : rc < k := by omega
          have hbk : rb < k := by omega
          simp [execStmt, evalExpr_adequate hc hck, ht, ih hbk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @ifRaised m f cond yes no final value rank hc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : rank < k := by omega
          simp [execStmt, evalExpr_adequate hc hk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | empty | returnVoid | breakTarget | continueTarget =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k => simp only [execStmt]
  | rethrow h =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k => simp [execStmt, h]
  | @sequenceNormal m f first rest middle midFrame final r1 r2 h1 h2 ih1 ih2 =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have h1k : r1 < k := by omega
          have h2k : r2 < k := by omega
          simp [execStmt, ih1 h1k, ih2 h2k,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @sequenceExit m f first rest out r h1 hExit ih =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          cases hc : out.control <;> simp_all [execStmt, ih hk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @returnValue m f expr final value r hExpr
  | @returnRaised m f expr final value r hExpr
  | @throwValue m f expr final value r hExpr
  | @throwRaised m f expr final value r hExpr
  | @assignFieldRaised m f name expr final value r hExpr =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate hExpr hk,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @assignField m f name expr middle final value r hExpr hWrite =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hk : r < k := by omega
          simp [execStmt, evalExpr_adequate hExpr hk, hWrite,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @finallyNormal m f body ct binder handler cleanup attempted final finalFrame rb rc hb hu hc ihb ihc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hck : rc < k := by omega
          cases hctrl : attempted.control <;>
            simp only [hctrl] at hu <;>
            simp only [execStmt, ihb hbk, ihc hck, hctrl, hu, Bool.false_eq_true,
              ↓reduceIte, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @finallyOverride m f body ct binder handler cleanup attempted final rb rc hb hu hc he ihb ihc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hck : rc < k := by omega
          cases hctrl : attempted.control <;> cases hf : final.control <;>
            simp only [hctrl] at hu <;>
            simp only [execStmt, ihb hbk, ihc hck, hctrl, hf, hu, Bool.false_eq_true,
              ↓reduceIte, Bind.bind, Pure.pure, Except.bind, Except.pure]
          all_goals first | exact False.elim (he hf) | rfl

  | @caughtFinallyNormal m f body ct binder handler cleanup middle midFrame err handled final ff rb rh rc hb ht hh hc ihb ihh ihc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hhk : rh < k := by omega
          have hck : rc < k := by omega
          simp only [execStmt, ihb hbk, ht, ↓reduceIte,
            ihh hhk, ihc hck, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | @caughtFinallyOverride m f body ct binder handler cleanup middle midFrame err handled final rb rh rc hb ht hh hc he ihb ihh ihc =>
      cases k with
      | zero => exact False.elim (by omega)
      | succ k =>
          have hbk : rb < k := by omega
          have hhk : rh < k := by omega
          have hck : rc < k := by omega
          cases hf : final.control <;>
            simp only [execStmt, ihb hbk, ht, ↓reduceIte,
              ihh hhk, ihc hck, hf, Bind.bind, Pure.pure, Except.bind, Except.pure]
          all_goals first | exact False.elim (he hf) | rfl

/-- Two supported statement paths cannot choose different control or heaps. -/
theorem DepthDerivesStmt.deterministic {program m f stmt out₁ out₂ r₁ r₂}
    (h₁ : DepthDerivesStmt program m f stmt out₁ r₁)
    (h₂ : DepthDerivesStmt program m f stmt out₂ r₂) : out₁ = out₂ := by
  have hk₁ : r₁ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hk₂ : r₂ < max r₁ r₂ + 1 := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact Except.ok.inj ((execStmt_adequate h₁ hk₁).symm.trans (execStmt_adequate h₂ hk₂))

/-- Finite address/descriptor checks. Values stored in the heap do not
    recursively traverse objects: liveness checks references, including cycles. -/
def liveValueCheck (m : TargetMachine) : TargetValue → Bool
  | .object ref => (m.objects.lookup ref).isSome
  | .closure ref => (m.closures.lookup ref).isSome
  | .boundBuiltin _ receiver => liveValueCheck m receiver
  | _ => true

def uniqueKeys {α β : Type} [BEq α] : List (α × β) → Bool
  | [] => true
  | entry :: rest => !(rest.any (fun other => entry.1 == other.1)) && uniqueKeys rest

def liveOptionalObject (m : TargetMachine) : Option ObjRef → Bool
  | none => true
  | some ref => (m.objects.lookup ref).isSome

def liveControlCheck (m : TargetMachine) : ControlResult → Bool
  | .returned value | .raised value => liveValueCheck m value
  | _ => true

def frameWFCheck (m : TargetMachine) (f : TargetFrame) : Bool :=
  (f.locals ++ f.captures).all (fun entry => (m.cells.lookup entry.2).isSome) &&
    liveOptionalObject m f.receiver && liveControlCheck m f.control

def descriptorWFCheck (m : TargetMachine) (d : Descriptor) : Bool :=
  (match d.value with | none => true | some value => liveValueCheck m value) &&
    (match d.get with | none => true | some ref => (m.closures.lookup ref).isSome) &&
    (match d.set with | none => true | some ref => (m.closures.lookup ref).isSome)

def objectWFCheck (m : TargetMachine) (o : HeapObject) : Bool :=
  liveOptionalObject m o.prototype && uniqueKeys o.own &&
    o.own.all (fun entry => descriptorWFCheck m entry.2) &&
    o.items.all (liveValueCheck m) && o.setMembers.all (liveValueCheck m)

def closureWFCheck (m : TargetMachine) (c : TargetClosure) : Bool :=
  c.captures.all (fun entry => (m.cells.lookup entry.2).isSome) &&
    c.pythonDefaults.all (fun value => match value with
      | none => true | some value => liveValueCheck m value) &&
    liveOptionalObject m c.receiver

def generatorWFCheck (m : TargetMachine) (ref : ObjRef) (g : GeneratorState) : Bool :=
  ((m.objects.lookup ref).map HeapObject.kind == some .pythonGenerator) &&
    frameWFCheck m g.frame && g.remaining.all (liveValueCheck m)

/-- Shared heap invariant, applicable before construction as well as after it.
    Canonical checker container shapes are a separate representation predicate.
    No evaluator success, ideal constructor, or fixed allocation IDs are assumed. -/
def heapWFCheck (_lang : TargetLang) (m : TargetMachine) : Bool :=
  uniqueKeys m.objects && uniqueKeys m.cells && uniqueKeys m.closures &&
    uniqueKeys m.generators && uniqueKeys m.writableCells &&
    m.objects.all (fun entry => entry.1 < m.nextObject && objectWFCheck m entry.2 &&
      (entry.2.kind != .pythonGenerator || (m.generators.lookup entry.1).isSome)) &&
    m.cells.all (fun entry => entry.1 < m.nextCell && liveValueCheck m entry.2) &&
    m.closures.all (fun entry => entry.1 < m.nextClosure && closureWFCheck m entry.2) &&
    m.generators.all (fun entry => generatorWFCheck m entry.1 entry.2) &&
    m.writableCells.all (fun entry => (m.cells.lookup entry.1).isSome) &&
    m.cells.all (fun entry => (m.writableCells.lookup entry.1).isSome) &&
    m.globals.all (fun entry => (m.cells.lookup entry.2).isSome) &&
    m.frames.all (frameWFCheck m) &&
    m.classMethods.all (fun entry => (m.closures.lookup entry.2).isSome) &&
    m.callableObjects.all (fun entry => (m.objects.lookup entry.1).isSome) &&
    ((m.objects.lookup m.objectPrototype).map HeapObject.kind == some .jsPrototype) &&
    (m.objects.lookup m.checkerRef).isSome &&
    (m.objects.lookup m.checker.context).isSome &&
    (m.objects.lookup m.checker.history).isSome &&
    liveOptionalObject m m.checker.undo && liveOptionalObject m m.checker.constructorSeed &&
    m.checker.instanceAttrs.all (fun entry => liveValueCheck m entry.2)

def HeapWF (lang : TargetLang) (m : TargetMachine) : Prop := heapWFCheck lang m = true

instance (lang : TargetLang) (m : TargetMachine) : Decidable (HeapWF lang m) :=
  inferInstanceAs (Decidable (heapWFCheck lang m = true))

/-- The structural invariant entails freshness of the next object address.
    The host clone can therefore preserve every older object on replacement. -/
theorem HeapWF.object_fresh {lang m} (h : HeapWF lang m) :
    ∀ e ∈ m.objects, e.1 ≠ m.nextObject := by
  unfold HeapWF heapWFCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨_, _, _, _, _, ho, _⟩ := h
  intro entry hEntry
  have hLive := (List.all_eq_true.mp ho) entry hEntry
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hLive
  exact Nat.ne_of_lt hLive.1.1

def FrameWF (m : TargetMachine) (f : TargetFrame) : Prop := frameWFCheck m f = true

theorem scalar_runs_heapWF {program machine frame expr outcome rank lang}
    (h : DepthDerivesExpr program machine frame expr outcome rank)
    (hwf : HeapWF lang machine) : HeapWF lang outcome.machine := by
  rw [h.machine_eq]
  exact hwf

end Harmonia.Applications.Kadmos.Generated
