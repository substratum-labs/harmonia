import Harmonia.Applications.Kadmos.Bridge.Syntax
namespace Harmonia.Applications.Kadmos.Bridge

structure RawState where
  id : String
  initial : Bool
  terminal : Bool
  description : Option String
structure RawVariable where
  «type» : String
  min : Option Int
  max : Option Int
  default : Option Int
  unit : Option String
  description : Option String
structure RawInvariant where
  id : String
  predicate : String
  description : Option String
inductive RawGuard where | bool (b : Bool) | expr (s : String)
structure RawTransition where
  id : String
  «from» : String
  to : String
  guard : RawGuard
  effects : List String
  directive : Option String
structure RawWorld where
  version : String
  name : String
  description : Option String
  states : List RawState
  context : List (String × RawVariable)
  invariants : List RawInvariant
  transitions : List RawTransition
  fields : List String
  extras : List String

def NamesWF (raw : RawWorld) (fieldNames : List String) : Prop :=
  (List.ofFn (fun j : Fin raw.states.length => raw.states[j].id)).Nodup ∧
  (raw.context.map Prod.fst).Nodup ∧ fieldNames.Nodup
instance (raw : RawWorld) (fieldNames : List String) : Decidable (NamesWF raw fieldNames) := inferInstanceAs
  (Decidable ((List.ofFn (fun j : Fin raw.states.length => raw.states[j].id)).Nodup ∧
    (raw.context.map Prod.fst).Nodup ∧ fieldNames.Nodup))

private def lookupName (names : Fin n → String) (id : String) : Except BridgeError (Fin n) :=
  match (List.ofFn fun j : Fin n => j).find? (fun j => names j == id) with
  | some j => .ok j
  | none => .error (.unbound id)

theorem lookupName_sound {n : Nat} {names : Fin n → String} {id : String} {j : Fin n}
    (h : lookupName names id = .ok j) : names j = id := by
  unfold lookupName at h
  cases hf : (List.ofFn fun k : Fin n => k).find? (fun k => names k == id) with
  | none => simp [hf] at h
  | some k =>
    simp [hf] at h
    cases h
    have hv := List.find?_some hf
    exact of_decide_eq_true hv

theorem sourceSafe_int {ρ : SourceEnv} {e : SourceExpr} (hs : sourceSafe ρ e)
    {n : Int} (he : sourceEval ρ e = .ok (.int n)) : safeInt n := by
  induction hs generalizing n with
  | int m h => simp [sourceEval] at he; cases he; exact h
  | bool b => simp [sourceEval] at he
  | context id h => simp [sourceEval] at he; cases he; exact h
  | field o id h => simp [sourceEval] at he; cases he; exact h
  | stateEq id => simp [sourceEval] at he
  | add l r hl hr hs ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl with
        | bool b => simp [sourceEval,hL,hR,srcInt,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
        | int x =>
          cases vr with
          | bool b => simp [sourceEval,hL,hR,srcInt,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
          | int y =>
            simp [sourceEval,hL,hR,srcInt,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
            cases he
            exact hs x y hL hR
  | sub l r hl hr hs ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl with
        | bool b => simp [sourceEval,hL,hR,srcInt,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
        | int x =>
          cases vr with
          | bool b => simp [sourceEval,hL,hR,srcInt,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
          | int y =>
            simp [sourceEval,hL,hR,srcInt,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
            cases he
            exact hs x y hL hR
  | eqInt l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | lt l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | le l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | gt l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | ge l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | and l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | or l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | implies l r hl hr ihl ihr =>
    cases hL : sourceEval ρ l with
    | error err => simp [sourceEval,hL,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok vl =>
      cases hR : sourceEval ρ r with
      | error err => simp [sourceEval,hL,hR,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
      | ok vr =>
        cases vl <;> cases vr <;> simp [sourceEval,hL,hR,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
  | not e h ih =>
    cases hE : sourceEval ρ e with
    | error err => simp [sourceEval,hE,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he
    | ok v => cases v <;> simp [sourceEval,hE,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure] at he

theorem requireInt_source (hs : sourceSafe ρ e) (h : sourceEval ρ e = .ok v) :
    requireInt v = srcInt v := by
  cases v with
  | bool b => rfl
  | int n =>
    have hn := sourceSafe_int hs h
    simp [requireInt,srcInt,checkedInt,hn]

theorem requireBool_source (v : Value) : requireBool v = srcBool v := by
  cases v <;> rfl

theorem names_injective {n : Nat} (names : Fin n → String)
    (hn : (List.ofFn names).Nodup) (i j : Fin n) (h : names i = names j) : i = j := by
  apply Fin.ext
  apply List.getElem?_inj (xs := List.ofFn names) (by simpa using i.isLt) hn
  simpa using congrArg some h

def EnvsAgree (raw : RawWorld) (fieldNames : List String) (ρ : SourceEnv)
    (q : Fin raw.states.length) (c : Fin raw.context.length → Int)
    (i : Fin fieldNames.length → Int) : Prop :=
  ρ.phase = raw.states[q].id ∧
  (∀ j : Fin raw.context.length, ρ.context (raw.context[j].1) = c j) ∧
  (∀ j : Fin fieldNames.length, ρ.fields fieldNames[j] = i j)

inductive ExprSort where | int | bool deriving DecidableEq

def inferSort : SourceExpr → Except BridgeError ExprSort
  | .int _ | .context _ | .field _ _ => .ok .int
  | .bool _ | .stateEq _ => .ok .bool
  | .add l r | .sub l r => do
    if (← inferSort l) != .int || (← inferSort r) != .int then throw (.wrongSort "arithmetic")
    return .int
  | .eqInt l r | .lt l r | .le l r | .gt l r | .ge l r => do
    if (← inferSort l) != .int || (← inferSort r) != .int then throw (.wrongSort "comparison")
    return .bool
  | .and l r | .or l r | .implies l r => do
    if (← inferSort l) != .bool || (← inferSort r) != .bool then throw (.wrongSort "logic")
    return .bool
  | .not e => do
    if (← inferSort e) != .bool then throw (.wrongSort "not")
    return .bool

private def phaseIds (raw : RawWorld) (j : Fin raw.states.length) : String := raw.states[j].id
private def contextIds (raw : RawWorld) (j : Fin raw.context.length) : String := (raw.context[j]).1
private def fieldIds (names : List String) (j : Fin names.length) : String := names[j]

def lowerExpr (raw : RawWorld) (fieldNames : List String) :
    SourceExpr → Except BridgeError (Expr raw.states.length raw.context.length fieldNames.length)
  | .int n => if safeInt n then .ok (.int n) else .error (.unsafeLiteral n)
  | .bool b => .ok (.bool b)
  | .context id => do return .context (← lookupName (contextIds raw) id)
  | .field _ id => do return .request (← lookupName (fieldIds fieldNames) id)
  | .stateEq id => do return .stateIs (← lookupName (phaseIds raw) id)
  | .add l r => do return .add (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .sub l r => do return .sub (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .eqInt l r => do return .eqInt (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .lt l r => do return .lt (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .le l r => do return .le (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .gt l r => do return .not (.le (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r))
  | .ge l r => do return .not (.lt (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r))
  | .and l r => do return .and (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .or l r => do return .or (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .implies l r => do return .implies (← lowerExpr raw fieldNames l) (← lowerExpr raw fieldNames r)
  | .not e => do return .not (← lowerExpr raw fieldNames e)

theorem lowerExpr_sound (raw : RawWorld) (fieldNames : List String)
    (ρ : SourceEnv) (q : Fin raw.states.length)
    (c : Fin raw.context.length → Int) (i : Fin fieldNames.length → Int)
    (hn : NamesWF raw fieldNames) (ha : EnvsAgree raw fieldNames ρ q c i)
    {e : SourceExpr} {x : Expr raw.states.length raw.context.length fieldNames.length}
    (hs : sourceSafe ρ e) (hl : lowerExpr raw fieldNames e = .ok x) :
    sourceEval ρ e = eval q c i x := by
  induction hs generalizing x with
  | int n hsafe =>
    simp [lowerExpr,hsafe] at hl
    cases hl
    simp [sourceEval,eval,checkedInt,hsafe,Functor.map,Except.map,Pure.pure,Except.pure,Bind.bind,Except.bind]
  | bool b =>
    simp [lowerExpr] at hl
    cases hl
    rfl
  | context id hsafe =>
    cases hk : lookupName (contextIds raw) id with
    | error err => simp [lowerExpr,hk,Functor.map,Except.map] at hl
    | ok j =>
      simp [lowerExpr,hk,Functor.map,Except.map] at hl
      cases hl
      have hid := lookupName_sound hk
      have hv : ρ.context id = c j := by rw [← hid]; exact ha.2.1 j
      have hs2 : safeInt (c j) := by rw [← hv]; exact hsafe
      simp [sourceEval,eval,checkedInt,hs2,hv,Functor.map,Except.map,Pure.pure,Except.pure,Bind.bind,Except.bind]
  | field o id hsafe =>
    cases hk : lookupName (fieldIds fieldNames) id with
    | error err => simp [lowerExpr,hk,Functor.map,Except.map] at hl
    | ok j =>
      simp [lowerExpr,hk,Functor.map,Except.map] at hl
      cases hl
      have hid := lookupName_sound hk
      have hv : ρ.fields id = i j := by rw [← hid]; exact ha.2.2 j
      have hs2 : safeInt (i j) := by rw [← hv]; exact hsafe
      simp [sourceEval,eval,checkedInt,hs2,hv,Functor.map,Except.map,Pure.pure,Except.pure,Bind.bind,Except.bind]
  | stateEq id =>
    cases hk : lookupName (phaseIds raw) id with
    | error err => simp [lowerExpr,hk,Functor.map,Except.map] at hl
    | ok j =>
      simp [lowerExpr,hk,Functor.map,Except.map] at hl
      cases hl
      have hid := lookupName_sound hk
      have heq : (ρ.phase == id) = decide (q = j) := by
        by_cases hq : q = j
        · subst j
          change (ρ.phase == id) = decide (q = q)
          simp [ha.1,phaseIds] at hid ⊢
          exact hid
        · have hd : ρ.phase ≠ id := by
            intro hp
            have hnq : phaseIds raw q = phaseIds raw j := by
              calc phaseIds raw q = ρ.phase := ha.1.symm
                _ = id := hp
                _ = phaseIds raw j := hid.symm
            exact hq (names_injective (phaseIds raw) hn.1 q j hnq)
          simp [hd,hq]
      simp [sourceEval,eval,heq]
  | add l r hlS hrS hsum ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
            all_goals
              first | exact hsum _ _ eL eR | omega
  | sub l r hlS hrS hsum ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
            all_goals
              first | exact hsum _ _ eL eR | omega
  | eqInt l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | lt l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | le l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | gt l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | ge l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | and l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | or l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | implies l r hlS hrS ihl ihr =>
    cases hL : lowerExpr raw fieldNames l with
    | error err => simp [lowerExpr,hL,Bind.bind,Except.bind] at hl
    | ok xl =>
      cases hR : lowerExpr raw fieldNames r with
      | error err => simp [lowerExpr,hL,hR,Bind.bind,Except.bind] at hl
      | ok xr =>
        simp [lowerExpr,hL,hR,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
        cases hl
        have il := ihl hL
        have ir := ihr hR
        cases eL : sourceEval ρ l with
        | error err =>
          have evl : eval q c i xl = .error err := by rw [← il, eL]
          simp [sourceEval,eval,eL,evl,Bind.bind,Except.bind,Functor.map,Except.map]
        | ok vl =>
          cases eR : sourceEval ρ r with
          | error err =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .error err := by rw [← ir, eR]
            simp [sourceEval,eval,eL,eR,evl,evr,Bind.bind,Except.bind,Functor.map,Except.map]
          | ok vr =>
            have evl : eval q c i xl = .ok vl := by rw [← il, eL]
            have evr : eval q c i xr = .ok vr := by rw [← ir, eR]
            have rL := requireInt_source hlS eL
            have rR := requireInt_source hrS eR
            cases vl <;> cases vr <;> simp_all [sourceEval,eval,evl,evr,rL,rR,checkedInt,requireBool,srcInt,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]
  | not e hs ih =>
    cases hE : lowerExpr raw fieldNames e with
    | error err => simp [lowerExpr,hE,Bind.bind,Except.bind] at hl
    | ok xe =>
      simp [lowerExpr,hE,Bind.bind,Except.bind,Pure.pure,Except.pure] at hl
      cases hl
      have ie := ih hE
      cases ev : sourceEval ρ e with
      | error err =>
        have eve : eval q c i xe = .error err := by rw [← ie,ev]
        simp [sourceEval,eval,ev,eve,Bind.bind,Except.bind,Functor.map,Except.map]
      | ok v =>
        have eve : eval q c i xe = .ok v := by rw [← ie,ev]
        cases v <;> simp [sourceEval,eval,ev,eve,requireBool,srcBool,Bind.bind,Except.bind,Functor.map,Except.map,Pure.pure,Except.pure]

def lowerGuard (raw : RawWorld) (g : RawGuard) : Except BridgeError (Expr raw.states.length raw.context.length raw.fields.length) := do
  let e ← match g with
    | .bool b => .ok (.bool b)
    | .expr s => parseSourceExpr s
  if (← inferSort e) != .bool then throw (.wrongSort "guard")
  lowerExpr raw raw.fields e

def lowerInvariant (raw : RawWorld) (s : String) : Except BridgeError (Expr raw.states.length raw.context.length 0) := do
  let e ← parseSourceExpr s
  if (← inferSort e) != .bool then throw (.wrongSort "invariant")
  lowerExpr raw [] e

private def trimWS (s : String) : String :=
  String.mk (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

private def assignment (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | [] | [_] => none
  | lhs :: rhsParts =>
    let name := trimWS lhs
    let rhs := trimWS (String.intercalate "=" rhsParts)
    if name != "" && rhs != "" then some (name,rhs) else none

def lowerEffect (raw : RawWorld) (s : String) : Except BridgeError (Effect raw.states.length raw.context.length raw.fields.length) := do
  let some (name,rhs) := assignment s | throw (.malformedEffect 0)
  let target ← lookupName (contextIds raw) name
  let e ← parseSourceExpr rhs
  if (← inferSort e) != .int then throw (.wrongSort "effect")
  return ⟨target, ← lowerExpr raw raw.fields e⟩

private def lowerTransition (raw : RawWorld) (t : RawTransition) : Except BridgeError
    (Transition raw.states.length raw.context.length raw.fields.length) := do
  let source ← lookupName (phaseIds raw) t.«from»
  let target ← lookupName (phaseIds raw) t.to
  let guard ← lowerGuard raw t.guard
  let effects ← t.effects.mapM (lowerEffect raw)
  return ⟨source,target,guard,effects,t.directive⟩

private def finTableM : (n : Nat) → (Fin n → Except BridgeError α) → Except BridgeError (Fin n → α)
  | 0, _ => .ok Fin.elim0
  | n+1, f => do
    let head ← f 0
    let tail ← finTableM n (fun j => f j.succ)
    return Fin.cases head tail

private def varDef (raw : RawWorld) (j : Fin raw.context.length) : Except BridgeError VarDef := do
  let v := (raw.context[j]).2
  if v.«type» != "integer" then throw (.invalidBounds (contextIds raw j))
  let some min := v.min | throw (.invalidBounds (contextIds raw j))
  let some max := v.max | throw (.invalidBounds (contextIds raw j))
  if !(decide (0 ≤ min ∧ min ≤ max ∧ max ≤ S)) then throw (.invalidBounds (contextIds raw j))
  let d := v.default.getD 0
  if !(decide (safeInt d ∧ min ≤ d ∧ d ≤ max)) then throw (.invalidBounds (contextIds raw j))
  return ⟨min,max,v.default⟩

private def sourceFields : SourceExpr → List String
  | .field _ id => [id]
  | .add l r | .sub l r | .eqInt l r | .lt l r | .le l r
  | .gt l r | .ge l r | .and l r | .or l r | .implies l r => sourceFields l ++ sourceFields r
  | .not e => sourceFields e
  | _ => []

private def usedFields (raw : RawWorld) : Except BridgeError (List String) := do
  let chunks ← raw.transitions.mapM (fun t => do
    let guard ← match t.guard with
      | .bool b => .ok (.bool b)
      | .expr s => parseSourceExpr s
    let effects ← t.effects.mapM (fun e => do
      let some (_,rhs) := assignment e | throw (.malformedEffect 0)
      return sourceFields (← parseSourceExpr rhs))
    return sourceFields guard ++ effects.flatten)
  return chunks.flatten

private def asciiLetter (c : Char) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)
private def validBinding (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (asciiLetter c || c == '_') && cs.all (fun d => asciiLetter d || d == '_' || d.isDigit)
private def reserved (s : String) : Bool :=
  ["state","event","request","true","false","null"].contains s

private def projectWorldChecked (raw : RawWorld) (_ : NamesWF raw raw.fields) : Except BridgeError
    (World raw.states.length raw.context.length raw.fields.length raw.transitions.length) := do
  if raw.version != "kadmos.world.v0" || raw.name == "" then throw .projection
  if !raw.extras.isEmpty then throw (.unknownProperty raw.extras.head!)
  if !(raw.context.all (fun pair => validBinding pair.1 && !reserved pair.1)) then throw (.reserved "context")
  if !(raw.fields.all (fun name => validBinding name && !reserved name)) then throw (.invalidProfile "field")
  let used ← usedFields raw
  if !(raw.fields.all used.contains) then throw (.invalidProfile "unused field")
  let variables ← finTableM raw.context.length (varDef raw)
  let transitions ← finTableM raw.transitions.length (fun j => lowerTransition raw raw.transitions[j])
  let invariants ← raw.invariants.mapM (fun i => do return (i.id, ← lowerInvariant raw i.predicate))
  return ⟨phaseIds raw, (fun j => raw.states[j].initial),
    (fun j => raw.states[j].terminal), contextIds raw,
    variables, fieldIds raw.fields, (fun j => raw.transitions[j].id),
    transitions, invariants⟩


inductive ExprCode (p v f : Nat) where
  | int (n : Int) | bool (b : Bool)
  | context (x : Fin v) | request (x : Fin f) | stateIs (q : Fin p)
  | add (l r : ExprCode p v f) | sub (l r : ExprCode p v f)
  | eqInt (l r : ExprCode p v f) | lt (l r : ExprCode p v f) | le (l r : ExprCode p v f)
  | not (e : ExprCode p v f) | and (l r : ExprCode p v f)
  | or (l r : ExprCode p v f) | implies (l r : ExprCode p v f)
  deriving DecidableEq

def encodeExpr : Expr p v f → ExprCode p v f
  | .int n => .int n | .bool b => .bool b
  | .context x => .context x | .request x => .request x | .stateIs q => .stateIs q
  | .add l r => .add (encodeExpr l) (encodeExpr r)
  | .sub l r => .sub (encodeExpr l) (encodeExpr r)
  | .eqInt l r => .eqInt (encodeExpr l) (encodeExpr r)
  | .lt l r => .lt (encodeExpr l) (encodeExpr r)
  | .le l r => .le (encodeExpr l) (encodeExpr r)
  | .not e => .not (encodeExpr e)
  | .and l r => .and (encodeExpr l) (encodeExpr r)
  | .or l r => .or (encodeExpr l) (encodeExpr r)
  | .implies l r => .implies (encodeExpr l) (encodeExpr r)

def decodeExpr : ExprCode p v f → Expr p v f
  | .int n => .int n | .bool b => .bool b
  | .context x => .context x | .request x => .request x | .stateIs q => .stateIs q
  | .add l r => .add (decodeExpr l) (decodeExpr r)
  | .sub l r => .sub (decodeExpr l) (decodeExpr r)
  | .eqInt l r => .eqInt (decodeExpr l) (decodeExpr r)
  | .lt l r => .lt (decodeExpr l) (decodeExpr r)
  | .le l r => .le (decodeExpr l) (decodeExpr r)
  | .not e => .not (decodeExpr e)
  | .and l r => .and (decodeExpr l) (decodeExpr r)
  | .or l r => .or (decodeExpr l) (decodeExpr r)
  | .implies l r => .implies (decodeExpr l) (decodeExpr r)

theorem decode_encode (e : Expr p v f) : decodeExpr (encodeExpr e) = e := by
  induction e <;> simp [encodeExpr, decodeExpr, *]

theorem encodeExpr_injective {l r : Expr p v f} (h : encodeExpr l = encodeExpr r) : l = r := by
  have hd := congrArg decodeExpr h
  simpa [decode_encode] using hd

instance : DecidableEq (Expr p v f) := fun l r =>
  if h : encodeExpr l = encodeExpr r then
    isTrue (encodeExpr_injective h)
  else isFalse (fun he => h (congrArg encodeExpr he))


structure TransitionCode (p v f : Nat) where
  source : Fin p
  target : Fin p
  guard : ExprCode p v f
  effects : List (Fin v × ExprCode p v f)
  directive : Option String
  deriving DecidableEq

def encodeTransition (t : Transition p v f) : TransitionCode p v f :=
  ⟨t.source,t.target,encodeExpr t.guard,t.effects.map (fun e => (e.target,encodeExpr e.rhs)),t.directive⟩
def decodeTransition (t : TransitionCode p v f) : Transition p v f :=
  ⟨t.source,t.target,decodeExpr t.guard,t.effects.map (fun e => ⟨e.1,decodeExpr e.2⟩),t.directive⟩
theorem decode_encode_transition (t : Transition p v f) : decodeTransition (encodeTransition t) = t := by
  cases t with
  | mk src tgt grd eff dir =>
    simp [encodeTransition,decodeTransition,decode_encode]
    induction eff with
    | nil => rfl
    | cons e es ih => cases e; simp [decode_encode,ih]
theorem encodeTransition_injective {l r : Transition p v f} (h : encodeTransition l = encodeTransition r) : l = r := by
  have hd := congrArg decodeTransition h
  simpa [decode_encode_transition] using hd

structure WorldCode (p v f a : Nat) where
  phaseIds : List String
  initialFlags : List Bool
  terminalFlags : List Bool
  contextIds : List String
  variables : List (Int × Int × Option Int)
  fieldIds : List String
  actionIds : List String
  transitions : List (TransitionCode p v f)
  invariants : List (String × ExprCode p v 0)
  deriving DecidableEq

def encodeWorld (w : World p v f a) : WorldCode p v f a :=
  ⟨List.ofFn w.phaseIds, List.ofFn w.initialFlags, List.ofFn w.terminalFlags,
   List.ofFn w.contextIds,
   List.ofFn (fun j => ((w.variables j).min,(w.variables j).max,(w.variables j).defaultValue)),
   List.ofFn w.fieldIds,List.ofFn w.actionIds,
   List.ofFn (fun j => encodeTransition (w.transitions j)),
   w.invariants.map (fun x => (x.1,encodeExpr x.2))⟩

theorem ofFn_inj {n : Nat} {α : Type} {f g : Fin n → α}
    (h : List.ofFn f = List.ofFn g) : f = g := by
  funext j
  have hj := congrArg (fun xs : List α => xs[j.val]?) h
  simpa using hj

theorem encodeWorld_injective {l r : World p v f a} (h : encodeWorld l = encodeWorld r) : l = r := by
  have hp : l.phaseIds = r.phaseIds := ofFn_inj (congrArg WorldCode.phaseIds h)
  have hi : l.initialFlags = r.initialFlags := ofFn_inj (congrArg WorldCode.initialFlags h)
  have ht : l.terminalFlags = r.terminalFlags := ofFn_inj (congrArg WorldCode.terminalFlags h)
  have hc : l.contextIds = r.contextIds := ofFn_inj (congrArg WorldCode.contextIds h)
  have hf : l.fieldIds = r.fieldIds := ofFn_inj (congrArg WorldCode.fieldIds h)
  have ha : l.actionIds = r.actionIds := ofFn_inj (congrArg WorldCode.actionIds h)
  have hv : l.variables = r.variables := by
    funext j
    have he := congrArg WorldCode.variables h
    have hj := congrArg (fun xs : List (Int × Int × Option Int) => xs[j.val]?) he
    have heq : ((l.variables j).min,(l.variables j).max,(l.variables j).defaultValue) =
      ((r.variables j).min,(r.variables j).max,(r.variables j).defaultValue) := by simpa [encodeWorld] using hj
    cases hl : l.variables j with
    | mk m1 M1 d1 =>
      cases hr : r.variables j with
      | mk m2 M2 d2 =>
        simp [hl,hr] at heq ⊢
        exact heq
  have htr : l.transitions = r.transitions := by
    funext j
    have he := congrArg WorldCode.transitions h
    have hj := congrArg (fun xs : List (TransitionCode p v f) => xs[j.val]?) he
    apply encodeTransition_injective
    simpa [encodeWorld] using hj
  have hinv : l.invariants = r.invariants := by
    have back (xs : List (String × Expr p v 0)) :
        (xs.map (fun x => (x.1,encodeExpr x.2))).map
          (fun x => (x.1,decodeExpr x.2)) = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => cases x; simp [decode_encode,ih]
    have he := congrArg WorldCode.invariants h
    have hd := congrArg (List.map (fun x : String × ExprCode p v 0 => (x.1,decodeExpr x.2))) he
    simpa [encodeWorld,back] using hd
  cases l; cases r
  simp_all

def worldEq (l r : World p v f a) : Bool := decide (encodeWorld l = encodeWorld r)
theorem worldEq_iff (l r : World p v f a) : worldEq l r = true ↔ l = r := by
  constructor
  · intro h
    exact encodeWorld_injective (of_decide_eq_true h)
  · intro h; cases h; simp [worldEq]


def projectWorld (raw : RawWorld) : Except BridgeError
    (World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :=
  if h : NamesWF raw raw.fields then projectWorldChecked raw h
  else .error (.duplicate "name table")

theorem projectWorld_names_wf {raw : RawWorld} {w : World raw.states.length raw.context.length raw.fields.length raw.transitions.length}
    (h : projectWorld raw = .ok w) : NamesWF raw raw.fields := by
  by_cases hn : NamesWF raw raw.fields
  · exact hn
  · simp [projectWorld,hn] at h

def checkBridge (raw : RawWorld)
    (candidate : World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :
    Except BridgeError (World raw.states.length raw.context.length raw.fields.length raw.transitions.length) :=
  match projectWorld raw with
  | .error e => .error e
  | .ok projected =>
    if worldEq projected candidate then
      match «initialize» candidate with
      | .error e => .error (.malformedWorld e)
      | .ok _ => .ok candidate
    else .error .projection

theorem checkBridge_names_wf {raw : RawWorld} {candidate w :
    World raw.states.length raw.context.length raw.fields.length raw.transitions.length}
    (h : checkBridge raw candidate = .ok w) : NamesWF raw raw.fields := by
  cases hp : projectWorld raw with
  | error e => simp [checkBridge,hp] at h
  | ok projected => exact projectWorld_names_wf hp

theorem checkBridge_exact {raw : RawWorld} {candidate w :
    World raw.states.length raw.context.length raw.fields.length raw.transitions.length}
    (h : checkBridge raw candidate = .ok w) :
    w = candidate ∧ projectWorld raw = .ok candidate ∧
      ∃ initial, «initialize» candidate = .ok initial := by
  cases hp : projectWorld raw with
  | error e => simp [checkBridge,hp] at h
  | ok projected =>
    by_cases he : worldEq projected candidate = true
    · have heq := (worldEq_iff projected candidate).mp he
      cases heq
      cases hi : «initialize» candidate with
      | error e => simp [checkBridge,hp,he,hi] at h
      | ok initial =>
        simp [checkBridge,hp,he,hi] at h
        exact ⟨h.symm,rfl,⟨initial,rfl⟩⟩
    · have hf : worldEq projected candidate = false := Bool.eq_false_iff.mpr he
      simp [checkBridge,hp,hf] at h

end Harmonia.Applications.Kadmos.Bridge
