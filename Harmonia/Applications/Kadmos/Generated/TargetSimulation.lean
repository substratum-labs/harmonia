import Harmonia.Applications.Kadmos.Generated.TargetSemantics

namespace Harmonia.Applications.Kadmos.Generated

/-- Unfueled execution configurations. The initial rule slice covers scalar
    leaves and ordered binary evaluation; calls and statements remain to add. -/
inductive TargetFocus where
  | eval (expr : TargetExpr)
  | exec (stmt : TargetStmt)
  | value (value : TargetValue)
  | exit (control : ControlResult)
  deriving Repr

/-- Each continuation owns the remaining ordered children of one binary node.
    The left rule installs the right child; the right rule retains its value. -/
inductive ResumeFrame where
  | binaryLeft (op : BinaryOp) (right : TargetExpr)
  | binaryRight (op : BinaryOp) (left : TargetValue)
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

/-- Syntax coverage of this first proof slice; `.add` needs a separate
    Python list-concatenation rule before entering the common binary case. -/
inductive ScalarSyntax : TargetExpr → Prop where
  | undefined : ScalarSyntax .undefined
  | null : ScalarSyntax .null
  | bool (b : Bool) : ScalarSyntax (.bool b)
  | integer (n : Int) : ScalarSyntax (.integer n)
  | string (s : String) : ScalarSyntax (.string s)
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

/-- Scalar rules preserve the entire heap, independent of any chosen heap
    invariant. This will not hold for the future allocation/write rules. -/
theorem SmallStep.machine_eq {program first last}
    (h : SmallStep program first last) : last.machine = first.machine := by
  cases h <;> rfl

theorem Runs.machine_eq {program first last}
    (h : Runs program first last) : last.machine = first.machine := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact step.machine_eq.trans ih

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

def FrameWF (m : TargetMachine) (f : TargetFrame) : Prop := frameWFCheck m f = true

theorem scalar_runs_heapWF {program first last lang}
    (h : Runs program first last) (hwf : HeapWF lang first.machine) :
    HeapWF lang last.machine := by
  rw [h.machine_eq]
  exact hwf

end Harmonia.Applications.Kadmos.Generated
