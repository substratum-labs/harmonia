import Harmonia.Applications.Kadmos.World
namespace Harmonia.Applications.Kadmos

inductive Verdict where
  | accepted | rejected (reason : RejectReason)
  deriving DecidableEq
structure Observation where
  verdict : Verdict
  directive : Option String
  deriving DecidableEq
structure Result (p v : Nat) where
  state : State p v
  observation : Observation

def setContext (c : Fin v → Int) (x : Fin v) (n : Int) : Fin v → Int :=
  fun y => if y=x then n else c y
@[simp] theorem setContext_self : setContext c x n x = n := by simp [setContext]
theorem setContext_other (h : y ≠ x) : setContext c x n y = c y := by simp [setContext,h]

def runEffect (q : Fin p) (i : Fin f → Int) (e : Effect p v f) (c : Fin v → Int) :
    Except EvalError (Fin v → Int) := do
  let n ← requireInt (← eval q c i e.rhs)
  return setContext c e.target n

def runEffects (q : Fin p) (i : Fin f → Int) :
    List (Effect p v f) → (Fin v → Int) → Except EvalError (Fin v → Int)
  | [], c => .ok c
  | e :: es, c => (runEffect q i e c).bind (runEffects q i es)
@[simp] theorem runEffects_nil : runEffects q i [] c = .ok c := rfl
theorem runEffects_cons : runEffects q i (e::es) c = (runEffect q i e c).bind (runEffects q i es) := rfl

theorem runEffects_append (q : Fin p) (i : Fin f → Int) (xs ys : List (Effect p v f)) (c : Fin v → Int) :
    runEffects q i (xs++ys) c = (runEffects q i xs c).bind (runEffects q i ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons e es ih =>
    simp only [List.cons_append, runEffects_cons]
    cases h : runEffect q i e c with
    | error err => rfl
    | ok c' => exact ih c'

def runTransitionEffects (t : Transition p v f) (i : Fin f → Int) (s : State p v) :
    Except EvalError (Fin v → Int) := runEffects t.target i t.effects s.context

theorem runTransitionEffects_target (t : Transition p v f) (i : Fin f → Int) (s : State p v) :
    runTransitionEffects t i s = runEffects t.target i t.effects s.context := rfl

def lookupAction (w : World p v f a) (id : String) : Option (Fin a) :=
  (List.ofFn fun k : Fin a => k).find? (fun k => w.actionIds k == id)

/-- The witness is constructed only after the two actual runtime postchecks.
    It adds no assumption about raw effects preserving invariants. -/
def publishCandidate (w : World p v f a) (s : State p v) :
    Except RejectReason {t : State p v // Good w t} :=
  match hb : checkBounds w s with
  | some j => .error (.bounds j)
  | none => match hi : checkInvariants w s with
    | some j => .error (.invariant j)
    | none => .ok ⟨s, by simp [Good,checkState,hb,hi]⟩

theorem publishCandidate_ok {w : World p v f a} {s : State p v}
    (hb : checkBounds w s = none) (hi : checkInvariants w s = none) :
    publishCandidate w s = .ok ⟨s,by simp [Good,checkState,hb,hi]⟩ := by
  unfold publishCandidate
  split
  · simp [hb] at *
  · split
    · simp [hi] at *
    · rfl

def runAction (w : World p v f a) (k : Fin a) (s : State p v) (r : Request f) :
    Except RejectReason {t : State p v // Good w t} := do
  let t := w.transitions k
  if t.source ≠ s.phase then throw .wrongPhase
  if r.proposedDirective ≠ t.directive then throw .unauthorizedDirective
  let input ← decode r.payload
  let value ← (eval s.phase s.context input t.guard).mapError RejectReason.guardError
  let guard ← (requireBool value).mapError RejectReason.guardError
  if !guard then throw .guardFalse
  let ctx ← (runTransitionEffects t input s).mapError RejectReason.effectError
  publishCandidate w ⟨t.target,ctx⟩

def attempt (w : World p v f a) (s : State p v) (r : Request f) :
    Except RejectReason (Fin a × {t : State p v // Good w t}) :=
  match «initialize» w with
  | .error e => .error (.malformedSpec e)
  | .ok _ => match lookupAction w r.actionId with
    | none => .error .unknownAction
    | some k => (runAction w k s r).map (fun t => (k,t))

/-- Total pure interpretation; only this function supplies Foundation's Step. -/
def interpret (w : World p v f a) (s : State p v) (r : Request f) : Result p v :=
  match attempt w s r with
  | .error e => ⟨s,⟨.rejected e,none⟩⟩
  | .ok (k,t) => ⟨t.val,⟨.accepted,(w.transitions k).directive⟩⟩

theorem rejection_frame {w : World p v f a} {s : State p v} {r : Request f}
    (h : (interpret w s r).observation.verdict = .rejected e) :
    (interpret w s r).state = s ∧ (interpret w s r).observation.directive = none := by
  unfold interpret at *
  split at h
  · exact ⟨rfl,rfl⟩
  · cases h

theorem accepted_good {w : World p v f a} {s : State p v} {r : Request f}
    (h : (interpret w s r).observation.verdict = .accepted) : Good w (interpret w s r).state := by
  unfold interpret at *
  split at h
  · cases h
  · exact Subtype.property _

theorem attempt_action {w : World p v f a} {s : State p v} {r : Request f}
    {k : Fin a} {t : {u : State p v // Good w u}}
    (h : attempt w s r = .ok (k,t)) : lookupAction w r.actionId = some k := by
  cases hi : «initialize» w with
  | error e => simp [attempt,hi] at h
  | ok initial =>
    cases hl : lookupAction w r.actionId with
    | none => simp [attempt,hi,hl] at h
    | some j =>
      cases hr : runAction w j s r with
      | error e => simp [attempt,hi,hl,hr,Except.map] at h
      | ok u =>
        simp [attempt,hi,hl,hr,Except.map] at h
        exact congrArg some h.1

theorem accepted_directive {w : World p v f a} {s : State p v} {r : Request f}
    {k : Fin a} (hl : lookupAction w r.actionId = some k)
    (h : (interpret w s r).observation.verdict = .accepted) :
    (interpret w s r).observation.directive = (w.transitions k).directive := by
  unfold interpret at *
  split at h
  · cases h
  · have hk := attempt_action ‹attempt w s r = .ok _›
    rw [hl] at hk
    cases Option.some.inj hk
    rfl

theorem interpret_malformedSpec {w : World p v f a} (h : «initialize» w = .error e)
    (s : State p v) (r : Request f) : interpret w s r = ⟨s,⟨.rejected (.malformedSpec e),none⟩⟩ := by
  simp [interpret,attempt,h]
end Harmonia.Applications.Kadmos
