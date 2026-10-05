import Harmonia.Distributed.Protocol
namespace Harmonia.Distributed
universe u
variable {M L P : Type u}

def Take (pool : List T) (e : T) (rest : List T) : Prop := pool.Perm (e :: rest)
namespace Take
theorem length (h : Take pool e rest) : pool.length = rest.length + 1 := by
  exact h.length_eq
theorem perm_left (h : pool.Perm pool') : Take pool e rest ↔ Take pool' e rest :=
  ⟨fun ht => h.symm.trans ht, fun ht => h.trans ht⟩
theorem middle (pre suffix : List T) (e : T) : Take (pre ++ e :: suffix) e (pre ++ suffix) :=
  List.perm_middle
theorem rest_unique (h : Take pool e r) (h' : Take pool e r') : r.Perm r' :=
  (h.symm.trans h').cons_inv
end Take

def allocate (actor : M) : Nat → List (Outgoing M L P) → List (Transmission M L P)
  | _, [] => []
  | n, out :: tail =>
    ⟨n, ⟨actor,out.recipient,out.logical,out.payload⟩⟩ :: allocate actor (n+1) tail

def Publish (actor : M) (n : Nat) (outs : List (Outgoing M L P))
    (base result : List (Transmission M L P)) : Prop := result.Perm (base ++ allocate actor n outs)
def freshCopy (e : Transmission M L P) (n : Nat) : Transmission M L P := ⟨n,e.envelope⟩

theorem allocate_length (actor : M) (n : Nat) (outs : List (Outgoing M L P)) :
    (allocate actor n outs).length = outs.length := by
  induction outs generalizing n with
  | nil => rfl
  | cons out tail ih => simp [allocate, ih]

theorem allocate_ids (actor : M) (n : Nat) (outs : List (Outgoing M L P)) :
    (allocate actor n outs).map (fun e => e.tid) =
      (List.range outs.length).map (fun i => n + i) := by
  induction outs generalizing n with
  | nil => rfl
  | cons out tail ih =>
    simp only [allocate, List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_map, ih]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp
    omega

theorem allocate_bounds (actor : M) (n : Nat) (outs : List (Outgoing M L P))
    (he : e ∈ allocate actor n outs) : n ≤ e.tid ∧ e.tid < n + outs.length := by
  induction outs generalizing n with
  | nil => simp [allocate] at he
  | cons out tail ih =>
    simp only [allocate, List.mem_cons] at he
    cases he with
    | inl h => subst e; simp
    | inr h => have hb := ih (n+1) h; simp only [List.length_cons]; omega

theorem allocate_fresh (actor : M) (n : Nat) (outs : List (Outgoing M L P)) :
    ((allocate actor n outs).map (fun e => e.tid)).Nodup ∧
    ∀ e, e ∈ allocate actor n outs → n ≤ e.tid ∧ e.tid < n + outs.length := by
  refine ⟨?_, fun _ h => allocate_bounds actor n outs h⟩
  induction outs generalizing n with
  | nil => simp [allocate]
  | cons out tail ih =>
    simp only [allocate, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (n+1)⟩
    intro hm
    obtain ⟨e, he, hid⟩ := List.mem_map.mp hm
    have hb := allocate_bounds actor (n+1) tail he
    omega

theorem allocate_sender (actor : M) (n : Nat) (outs : List (Outgoing M L P))
    (he : e ∈ allocate actor n outs) : e.envelope.sender = actor := by
  induction outs generalizing n with
  | nil => simp [allocate] at he
  | cons out tail ih =>
    simp only [allocate, List.mem_cons] at he
    cases he with
    | inl h => subst e; rfl
    | inr h => exact ih (n+1) h

namespace Publish
theorem perm_base (h : base.Perm base') : Publish actor n outs base result ↔ Publish actor n outs base' result :=
  ⟨fun hp => hp.trans (h.append_right _), fun hp => hp.trans (h.symm.append_right _)⟩
theorem perm_result (h : result.Perm result') : Publish actor n outs base result ↔ Publish actor n outs base result' :=
  ⟨fun hp => h.symm.trans hp, fun hp => h.trans hp⟩
end Publish
end Harmonia.Distributed
