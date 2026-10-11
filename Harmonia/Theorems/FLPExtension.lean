import Harmonia.Theorems.FLP

/-! Finite-schedule infrastructure for the FLP bivalence-extension argument.
An event remains enabled while that particular event is delayed; a schedule
that eventually performs it can be cut at its first occurrence. -/

namespace Harmonia.FLP

universe u v w

variable {Node : Type u} {Msg : Type v} {Local : Type w}
variable [DecidableEq Node] [DecidableEq Msg]

/-- Sending may add copies of a message, but an event with a different target
or payload cannot consume the pending occurrence required by `e`. -/
theorem enabled_after_different_event (protocol : Protocol Node Msg Local)
    (c : Config Node Msg Local) (e f : Event Node Msg)
    (hneq : f ≠ e) (he : Enabled c e) :
    Enabled (advance protocol c f) e := by
  by_cases htarget : f.target = e.target
  · cases hmsg : e.msg with
    | none => simp [Enabled, hmsg]
    | some m =>
      have hpayload : f.msg ≠ some m := by
        intro hm
        apply hneq
        cases f with
        | mk ft fm =>
          cases e with
          | mk et em =>
            simp only at htarget hm hmsg
            cases htarget
            cases hm
            cases hmsg
            rfl
      simp only [Enabled, hmsg] at he ⊢
      change 0 < c.buffer e.target m +
        Int.ofNat (protocol.send f.target (c.state f.target) f.msg e.target m) -
          (if f.msg = some m ∧ f.target = e.target then 1 else 0)
      have hnot : ¬ (f.msg = some m ∧ f.target = e.target) := by
        intro h
        exact hpayload h.1
      simp [hnot]
      have hsend : 0 ≤ Int.ofNat
          (protocol.send f.target (c.state f.target) f.msg e.target m) :=
        Int.ofNat_nonneg _
      omega
  · exact enabled_after_other protocol c f e htarget he

/-- Delaying `e` through a finite schedule never disables it. This permits
other events at the same process, provided they do not consume the particular
message (or null receive) denoted by `e`. -/
theorem enabled_after_schedule_avoiding_event (protocol : Protocol Node Msg Local)
    {c d : Config Node Msg Local} {events : List (Event Node Msg)}
    (hrun : Schedule protocol c events d) (e : Event Node Msg)
    (he : Enabled c e) (havoid : e ∉ events) : Enabled d e := by
  induction hrun with
  | nil => exact he
  | @cons c d f hf fs tail ih =>
    have hne : f ≠ e := by
      intro h
      have hm : e ∈ f :: fs := by simp [h]
      exact havoid hm
    have htail : e ∉ fs := by
      intro hm
      exact havoid (List.mem_cons_of_mem f hm)
    exact ih (enabled_after_different_event protocol c e f hne he) htail

/-- Split an enabled schedule at the first occurrence of `e`. The prefix
contains no `e`, and the suffix starts from the state after delivering it. -/
theorem schedule_split_first_occurrence (protocol : Protocol Node Msg Local)
    {c t : Config Node Msg Local} {events : List (Event Node Msg)}
    (hrun : Schedule protocol c events t) (e : Event Node Msg)
    (hpresent : e ∈ events) :
    ∃ before after mid,
      events = before ++ e :: after ∧ e ∉ before ∧
      Schedule protocol c before mid ∧ Enabled mid e ∧
      Schedule protocol (advance protocol mid e) after t := by
  induction hrun with
  | nil => cases hpresent
  | @cons c d f hf fs tail ih =>
    by_cases hfe : f = e
    · subst f
      exact ⟨[], fs, c, rfl, by simp, .nil _, hf, tail⟩
    · have htail : e ∈ fs := by
        cases List.mem_cons.mp hpresent with
        | inl h => exact False.elim (hfe h.symm)
        | inr h => exact h
      obtain ⟨before, after, mid, hsplit, havoid, hprefix, he, hsuffix⟩ := ih htail
      refine ⟨f :: before, after, mid, ?_, ?_, .cons f hf hprefix, he, hsuffix⟩
      · simp [hsplit]
      · intro hm
        cases List.mem_cons.mp hm with
        | inl h => exact hfe h.symm
        | inr h => exact havoid h

/-- A deciding schedule can be split at its first `e` while preserving the
decision fact at the final configuration. -/
theorem deciding_schedule_split_first_occurrence (protocol : Protocol Node Msg Local)
    {c t : Config Node Msg Local} {events : List (Event Node Msg)}
    (hrun : Schedule protocol c events t) (e : Event Node Msg)
    (hpresent : e ∈ events) {value : Decision} (hdecision : DecidedIn t value) :
    ∃ before after mid,
      events = before ++ e :: after ∧ e ∉ before ∧
      Schedule protocol c before mid ∧ Enabled mid e ∧
      Schedule protocol (advance protocol mid e) after t ∧ DecidedIn t value := by
  obtain ⟨before, after, mid, hsplit, havoid, hprefix, he, hsuffix⟩ :=
    schedule_split_first_occurrence protocol hrun e hpresent
  exact ⟨before, after, mid, hsplit, havoid, hprefix, he, hsuffix, hdecision⟩

/-- The finite consequence of termination under one fail-stop fault: from
every state accessible from `initial`, there is a deciding schedule in which
any designated process remains silent. This is a liveness premise, not a
consequence of the finite transition semantics alone. -/
def CrashDecidingReachable (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) : Prop :=
  ∀ c, Reachable protocol initial c → ∀ silent,
    ∃ events t value, Schedule protocol c events t ∧
      (∀ event ∈ events, event.target ≠ silent) ∧ DecidedIn t value

/-- Adjacent members of the set reached while delaying `e` cannot have
opposite univalent `e`-images. If `f` acts elsewhere, the diamond joins the
images. If `f` acts at `e`'s process, a deciding schedule that omits that
process replays after either image; persistence forces one decision value in
both. -/
theorem e_image_neighbor_consistent (protocol : Protocol Node Msg Local)
    (initial c : Config Node Msg Local) (e f : Event Node Msg)
    (haccessible : Reachable protocol initial c)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    (he : Enabled c e) (hf : Enabled c f) (hdifferent : f ≠ e)
    (value : Decision)
    (hleft : IsUnivalent protocol (advance protocol c e) value)
    (hright : IsUnivalent protocol
      (advance protocol (advance protocol c f) e) value.flip) :
    False := by
  have he' : Enabled (advance protocol c f) e :=
    enabled_after_different_event protocol c e f hdifferent he
  by_cases htarget : f.target = e.target
  · obtain ⟨events, t, crashValue, hrun, hother, hdec⟩ :=
      hcrash c haccessible e.target
    have hafterE := flp_lemma1_schedule protocol hrun e he hother
    have hafterF := flp_lemma1_schedule protocol hrun f hf (by
      intro event hm
      simpa [htarget] using hother event hm)
    have hafterEF := flp_lemma1_schedule protocol hafterF.1 e he' hother
    have hdecE : DecidedIn (advance protocol t e) crashValue :=
      hpersist t e crashValue hafterE.2 hdec
    have hdecFE : DecidedIn (advance protocol (advance protocol t f) e) crashValue := by
      have hdecF : DecidedIn (advance protocol t f) crashValue :=
        hpersist t f crashValue hafterF.2 hdec
      exact hpersist (advance protocol t f) e crashValue hafterEF.2 hdecF
    have hpossibleE : ReachableDecision protocol (advance protocol c e) crashValue :=
      ⟨advance protocol t e, Schedule.reachable protocol hafterE.1, hdecE⟩
    have hpossibleFE : ReachableDecision protocol
        (advance protocol (advance protocol c f) e) crashValue :=
      ⟨advance protocol (advance protocol t f) e,
        Schedule.reachable protocol hafterEF.1, hdecFE⟩
    cases value <;> cases crashValue
    · exact hright.2 hpossibleFE
    · exact hleft.2 hpossibleE
    · exact hleft.2 hpossibleE
    · exact hright.2 hpossibleFE
  · have heF : Enabled (advance protocol c e) f :=
      enabled_after_other protocol c e f (Ne.symm htarget) hf
    have hdiamond : advance protocol (advance protocol c e) f =
        advance protocol (advance protocol c f) e :=
      flp_lemma1_diamond protocol c e f (Ne.symm htarget)
    have hreach : Reachable protocol (advance protocol c e)
        (advance protocol (advance protocol c f) e) := by
      rw [← hdiamond]
      exact .tail (.refl _) f heF
    exact hleft.2 (reachableDecision_of_reachable protocol hreach hright.1)

end Harmonia.FLP
