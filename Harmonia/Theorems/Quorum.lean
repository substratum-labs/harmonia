import Init

/- Quorums are finite lists with `Nodup` hypotheses. `U` bounds membership and
its list length supplies the population bound; the counting lemmas remain valid
when `U` itself has duplicates. Faults are bounded by list length, so a repeated
fault entry only strengthens the assumption. No network or protocol semantics
are assumed here. -/
namespace Harmonia.Quorum

universe u
variable {N : Type u} [DecidableEq N]

def inter (A B : List N) : List N := A.filter (fun x => decide (x ∈ B))
def diff (A B : List N) : List N := A.filter (fun x => decide (x ∉ B))

theorem partition_length (A B : List N) :
    (inter A B).length + (diff A B).length = A.length := by
  simp only [inter, diff, ← List.countP_eq_length_filter]
  have h := List.length_eq_countP_add_countP (fun x => decide (x ∈ B)) (l := A)
  simpa using h.symm

/-- A union represented as B followed by A's nodes outside B obeys inclusion-exclusion. -/
theorem inclusion_exclusion (A B : List N) :
    (B ++ diff A B).length + (inter A B).length = A.length + B.length := by
  have h := partition_length A B
  simp only [List.length_append]
  omega

theorem subset_length_le (A U : List N) (hA : A.Nodup)
    (hSub : ∀ x ∈ A, x ∈ U) : A.length ≤ U.length := by
  induction A generalizing U with
  | nil => simp
  | cons a as ih =>
    have ha : a ∉ as := (List.nodup_cons.mp hA).1
    have has : as.Nodup := (List.nodup_cons.mp hA).2
    have hau : a ∈ U := hSub a (by simp)
    have htail : ∀ x ∈ as, x ∈ diff U [a] := by
      intro x hx
      apply List.mem_filter.mpr
      refine ⟨hSub x (by simp [hx]), ?_⟩
      have hne : x ≠ a := by
        intro heq; subst x; exact ha hx
      simpa [diff] using hne
    have hlen := ih (diff U [a]) has htail
    have hpart := partition_length U [a]
    have hpos : 0 < (inter U [a]).length :=
      List.length_pos_iff_exists_mem.mpr ⟨a, List.mem_filter.mpr ⟨hau, by simp⟩⟩
    simp only [List.length_cons] at *
    omega

theorem disjoint_cardinality (A B U : List N) (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U) :
    B.length + (diff A B).length ≤ U.length := by
  have hnodup : (B ++ diff A B).Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨hB, List.Pairwise.filter (fun x => decide (x ∉ B)) hA, ?_⟩
    intro b hb d hd heq
    subst d
    have hnot : b ∉ B := by
      have hh := (List.mem_filter.mp hd).2
      simpa using hh
    exact hnot hb
  have hsub : ∀ x ∈ B ++ diff A B, x ∈ U := by
    intro x hx
    rcases List.mem_append.mp hx with hb | hd
    · exact hBU x hb
    · exact hAU x (List.mem_filter.mp hd).1
  simpa using subset_length_le (B ++ diff A B) U hnodup hsub

theorem intersection_lower_bound (A B U : List N) (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U) :
    A.length + B.length ≤ (inter A B).length + U.length := by
  have hp := partition_length A B
  have hd := disjoint_cardinality A B U hA hB hAU hBU
  omega

theorem cft_intersection (A B U : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : U.length ≤ 2*f+1) (hQA : f+1 ≤ A.length) (hQB : f+1 ≤ B.length) :
    1 ≤ (inter A B).length := by
  have h := intersection_lower_bound A B U hA hB hAU hBU
  omega

theorem bft_intersection (A B U : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : U.length ≤ 3*f+1) (hQA : 2*f+1 ≤ A.length) (hQB : 2*f+1 ≤ B.length) :
    f+1 ≤ (inter A B).length := by
  have h := intersection_lower_bound A B U hA hB hAU hBU
  omega

/-- For arbitrary N ≥ 2f+1, quorums with at most f missing nodes intersect. -/
theorem cft_intersection_at_least (A B U : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : 2*f+1 ≤ U.length)
    (hQA : U.length ≤ A.length+f) (hQB : U.length ≤ B.length+f) :
    1 ≤ (inter A B).length := by
  have h := intersection_lower_bound A B U hA hB hAU hBU
  omega

/-- For arbitrary N ≥ 3f+1, quorums with at most f missing nodes share f+1 nodes. -/
theorem bft_intersection_at_least (A B U : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : 3*f+1 ≤ U.length)
    (hQA : U.length ≤ A.length+f) (hQB : U.length ≤ B.length+f) :
    f+1 ≤ (inter A B).length := by
  have h := intersection_lower_bound A B U hA hB hAU hBU
  omega

theorem bft_honest_cardinality (A B U F : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : U.length ≤ 3*f+1) (hQA : 2*f+1 ≤ A.length) (hQB : 2*f+1 ≤ B.length)
    (hF : F.length ≤ f) :
    1 ≤ (diff (inter A B) F).length := by
  have hi := bft_intersection A B U f hA hB hAU hBU hU hQA hQB
  have hpart := partition_length (inter A B) F
  have hfilter : (inter (inter A B) F).length ≤ F.length := by
    apply subset_length_le (inter (inter A B) F) F
    · exact List.Pairwise.filter (fun x => decide (x ∈ F))
        (List.Pairwise.filter (fun x => decide (x ∈ B)) hA)
    · intro x hx
      simpa using (List.mem_filter.mp hx).2
  omega

theorem bft_honest_exists (A B U F : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : U.length ≤ 3*f+1) (hQA : 2*f+1 ≤ A.length) (hQB : 2*f+1 ≤ B.length)
    (hF : F.length ≤ f) :
    ∃ x, x ∈ inter A B ∧ x ∉ F := by
  have h := bft_honest_cardinality A B U F f hA hB hAU hBU hU hQA hQB hF
  obtain ⟨x, hx⟩ := List.length_pos_iff_exists_mem.mp (by omega : 0 < (diff (inter A B) F).length)
  exact ⟨x, (List.mem_filter.mp hx).1, by simpa using (List.mem_filter.mp hx).2⟩

theorem bft_honest_exists_at_least (A B U F : List N) (f : Nat)
    (hA : A.Nodup) (hB : B.Nodup)
    (hAU : ∀ x ∈ A, x ∈ U) (hBU : ∀ x ∈ B, x ∈ U)
    (hU : 3*f+1 ≤ U.length)
    (hQA : U.length ≤ A.length+f) (hQB : U.length ≤ B.length+f)
    (hF : F.length ≤ f) :
    ∃ x, x ∈ inter A B ∧ x ∉ F := by
  have hi := bft_intersection_at_least A B U f hA hB hAU hBU hU hQA hQB
  have hpart := partition_length (inter A B) F
  have hfilter : (inter (inter A B) F).length ≤ F.length := by
    apply subset_length_le (inter (inter A B) F) F
    · exact List.Pairwise.filter (fun x => decide (x ∈ F))
        (List.Pairwise.filter (fun x => decide (x ∈ B)) hA)
    intro x hx
    simpa using (List.mem_filter.mp hx).2
  have hhonest : 0 < (diff (inter A B) F).length := by omega
  obtain ⟨x, hx⟩ := List.length_pos_iff_exists_mem.mp hhonest
  exact ⟨x, (List.mem_filter.mp hx).1, by simpa using (List.mem_filter.mp hx).2⟩

end Harmonia.Quorum
