import Init

/- A deliberately narrow reference subset of existing Kadmos WorldSpec.
   Fin references are typed; expression sorts are checked dynamically. -/
namespace Harmonia.Applications.Kadmos

structure State (p v : Nat) where
  phase : Fin p
  context : Fin v → Int

inductive RawPrimitive where
  | missing | null | int (n : Int) | bool (b : Bool) | string (s : String) | invalidNumber
  deriving DecidableEq
inductive Value where
  | int (n : Int) | bool (b : Bool)
  deriving DecidableEq
inductive Expr (p v f : Nat) where
  | int (n : Int) | bool (b : Bool)
  | context (x : Fin v) | request (x : Fin f) | stateIs (q : Fin p)
  | add (l r : Expr p v f) | sub (l r : Expr p v f)
  | eqInt (l r : Expr p v f) | lt (l r : Expr p v f) | le (l r : Expr p v f)
  | not (e : Expr p v f) | and (l r : Expr p v f)
  | or (l r : Expr p v f) | implies (l r : Expr p v f)
structure VarDef where
  min : Int
  max : Int
  defaultValue : Option Int
structure Effect (p v f : Nat) where
  target : Fin v
  rhs : Expr p v f
structure Transition (p v f : Nat) where
  source : Fin p
  target : Fin p
  guard : Expr p v f
  effects : List (Effect p v f)
  directive : Option String
structure World (p v f a : Nat) where
  phaseIds : Fin p → String
  initialFlags : Fin p → Bool
  terminalFlags : Fin p → Bool
  contextIds : Fin v → String
  variables : Fin v → VarDef
  fieldIds : Fin f → String
  actionIds : Fin a → String
  transitions : Fin a → Transition p v f
  invariants : List (String × Expr p v 0)
structure Request (f : Nat) where
  actionId : String
  payload : Fin f → RawPrimitive
  proposedDirective : Option String
inductive EvalError where
  | expectedInt | expectedBool | overflow
  deriving DecidableEq
inductive SpecError where
  | phaseIds | contextIds | fieldIds | actionIds | invariantIds | initialCount
  | terminalSource | invalidBounds | invalidDefault | initialInvariant
  deriving DecidableEq
inductive RejectReason where
  | malformedSpec (e : SpecError) | unknownAction | wrongPhase | unauthorizedDirective
  | inputType (index : Nat) | inputRange (index : Nat) | guardFalse
  | guardError (e : EvalError) | effectError (e : EvalError)
  | bounds (index : Nat) | invariant (index : Nat)
  deriving DecidableEq

def S : Int := 9007199254740991
def safeInt (n : Int) : Prop := -S ≤ n ∧ n ≤ S
instance (n : Int) : Decidable (safeInt n) := inferInstanceAs (Decidable (-S ≤ n ∧ n ≤ S))

def checkedInt (n : Int) : Except EvalError Int :=
  if safeInt n then .ok n else .error .overflow

theorem checkedInt_safe (h : checkedInt n = .ok m) : safeInt m := by
  unfold checkedInt at h
  split at h
  · cases h; assumption
  · cases h

def requireInt : Value → Except EvalError Int
  | .int n => checkedInt n
  | .bool _ => .error .expectedInt
def requireBool : Value → Except EvalError Bool
  | .bool b => .ok b
  | .int _ => .error .expectedBool

def rawInt : RawPrimitive → Int
  | .int n => n
  | _ => 0
def inputValid (r : RawPrimitive) : Prop := r = .int (rawInt r) ∧ safeInt (rawInt r)
instance (r : RawPrimitive) : Decidable (inputValid r) :=
  inferInstanceAs (Decidable (r = .int (rawInt r) ∧ safeInt (rawInt r)))
def inputError (j : Nat) : RawPrimitive → RejectReason
  | .int _ | .invalidNumber => .inputRange j
  | _ => .inputType j

def firstInputError (raw : Fin f → RawPrimitive) : List (Fin f) → RejectReason
  | [] => .inputType 0 -- unreachable when the complete table failed validation
  | j :: js => if inputValid (raw j) then firstInputError raw js else inputError j.val (raw j)

def decode (raw : Fin f → RawPrimitive) : Except RejectReason (Fin f → Int) :=
  if ∀ j, inputValid (raw j) then .ok (fun j => rawInt (raw j))
  else .error (firstInputError raw (List.ofFn id))

theorem decode_field {raw : Fin f → RawPrimitive} {input : Fin f → Int}
    (h : decode raw = .ok input) (j : Fin f) :
    raw j = .int (input j) ∧ safeInt (input j) := by
  unfold decode at h
  split at h
  · cases h; exact ‹∀ j, inputValid (raw j)› j
  · cases h

theorem decode_invalid {raw : Fin f → RawPrimitive} {j : Fin f} (h : ¬ inputValid (raw j)) : ∃ e, decode raw = .error e := by
  unfold decode
  split
  · exact False.elim (h (‹∀ j, inputValid (raw j)› j))
  · exact ⟨_,rfl⟩

def eval (phase : Fin p) (ctx : Fin v → Int) (input : Fin f → Int) :
    Expr p v f → Except EvalError Value
  | .int n => return .int (← checkedInt n)
  | .bool b => .ok (.bool b)
  | .context x => return .int (← checkedInt (ctx x))
  | .request x => return .int (← checkedInt (input x))
  | .stateIs q => .ok (.bool (decide (phase = q)))
  | .add l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    let ln ← requireInt lv
    let rn ← requireInt rv
    return .int (← checkedInt (ln + rn))
  | .sub l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    let ln ← requireInt lv
    let rn ← requireInt rv
    return .int (← checkedInt (ln - rn))
  | .eqInt l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    return .bool (decide ((← requireInt lv) = (← requireInt rv)))
  | .lt l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    return .bool (decide ((← requireInt lv) < (← requireInt rv)))
  | .le l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    return .bool (decide ((← requireInt lv) ≤ (← requireInt rv)))
  | .not e => do
    return .bool (!(← requireBool (← eval phase ctx input e)))
  | .and l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    let lb ← requireBool lv
    let rb ← requireBool rv
    return .bool (lb && rb)
  | .or l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    let lb ← requireBool lv
    let rb ← requireBool rv
    return .bool (lb || rb)
  | .implies l r => do
    let lv ← eval phase ctx input l
    let rv ← eval phase ctx input r
    let lb ← requireBool lv
    let rb ← requireBool rv
    return .bool (!lb || rb)

def inBounds (w : World p v f a) (s : State p v) (j : Fin v) : Prop :=
  safeInt (s.context j) ∧ (w.variables j).min ≤ s.context j ∧ s.context j ≤ (w.variables j).max
instance (w : World p v f a) (s : State p v) (j : Fin v) : Decidable (inBounds w s j) :=
  inferInstanceAs (Decidable (safeInt (s.context j) ∧ (w.variables j).min ≤ s.context j ∧
    s.context j ≤ (w.variables j).max))
def firstBoundError (w : World p v f a) (s : State p v) : List (Fin v) → Nat
  | [] => 0
  | j :: js => if inBounds w s j then firstBoundError w s js else j.val

def checkBounds (w : World p v f a) (s : State p v) : Option Nat :=
  if ∀ j, inBounds w s j then none else some (firstBoundError w s (List.ofFn id))

def invariantPass : Except EvalError Value → Bool
  | .ok (.bool true) => true
  | _ => false

def checkInvariantList (phase : Fin p) (ctx : Fin v → Int) :
    List (String × Expr p v 0) → Nat → Option Nat
  | [], _ => none
  | (_,e) :: es, k =>
    if invariantPass (eval phase ctx Fin.elim0 e) then checkInvariantList phase ctx es (k+1)
    else some k

def checkInvariants (w : World p v f a) (s : State p v) : Option Nat :=
  checkInvariantList s.phase s.context w.invariants 0
def checkState (w : World p v f a) (s : State p v) : Bool :=
  (checkBounds w s).isNone && (checkInvariants w s).isNone
def Good (w : World p v f a) (s : State p v) : Prop := checkState w s = true

theorem good_bounds {w : World p v f a} {s : State p v} (h : Good w s) (j : Fin v) : inBounds w s j := by
  unfold Good checkState checkBounds at h
  split at h
  · exact ‹∀ j, inBounds w s j› j
  · simp at h

def namesValid (names : List String) : Bool :=
  names.all (fun name => name != "") && decide names.Nodup

def validateWorld (w : World p v f a) : Except SpecError (Fin p) := do
  if !namesValid (List.ofFn w.phaseIds) then throw .phaseIds
  if !namesValid (List.ofFn w.contextIds) then throw .contextIds
  if !namesValid (List.ofFn w.fieldIds) then throw .fieldIds
  if !namesValid (List.ofFn w.actionIds) then throw .actionIds
  if !namesValid (w.invariants.map Prod.fst) then throw .invariantIds
  let q ← match (List.ofFn id).filter w.initialFlags with
    | [q] => .ok q
    | _ => .error .initialCount
  if (List.ofFn id).any (fun k => w.terminalFlags (w.transitions k).source) then throw .terminalSource
  if !(decide (∀ j, 0 ≤ (w.variables j).min ∧ (w.variables j).min ≤ (w.variables j).max ∧
      (w.variables j).max ≤ S)) then throw .invalidBounds
  if !(decide (∀ j, safeInt ((w.variables j).defaultValue.getD 0) ∧
      (w.variables j).min ≤ (w.variables j).defaultValue.getD 0 ∧
      (w.variables j).defaultValue.getD 0 ≤ (w.variables j).max)) then throw .invalidDefault
  return q

def «initialize» (w : World p v f a) : Except SpecError (State p v) :=
  match validateWorld w with
  | .error e => .error e
  | .ok q =>
    let s : State p v := ⟨q,fun j => (w.variables j).defaultValue.getD 0⟩
    if checkState w s = true then .ok s else .error .initialInvariant

theorem initialize_good {w : World p v f a} {s : State p v} (h : «initialize» w = .ok s) : Good w s := by
  unfold «initialize» at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h; assumption
    · cases h
end Harmonia.Applications.Kadmos
