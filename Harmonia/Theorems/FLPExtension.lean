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
        Int.natCast_nonneg _
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
    ∃ events t q value, Schedule protocol c events t ∧
      (∀ event ∈ events, event.target ≠ silent) ∧ q ≠ silent ∧
        t.decision q = some value

/-- If adjacent `e`-images can decide opposite values, one is bivalent.
This constructive form is stronger than the univalence contradiction: it
returns a bivalent witness without deciding reachability. -/
theorem e_image_neighbor_bivalence (protocol : Protocol Node Msg Local)
    (initial c : Config Node Msg Local) (e f : Event Node Msg)
    (haccessible : Reachable protocol initial c)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    (he : Enabled c e) (hf : Enabled c f) (hdifferent : f ≠ e)
    (value : Decision)
    (hleft : ReachableDecision protocol (advance protocol c e) value)
    (hright : ReachableDecision protocol
      (advance protocol (advance protocol c f) e) value.flip) :
    IsBivalent protocol (advance protocol c e) ∨
      IsBivalent protocol (advance protocol (advance protocol c f) e) := by
  have he' : Enabled (advance protocol c f) e :=
    enabled_after_different_event protocol c e f hdifferent he
  by_cases htarget : f.target = e.target
  · obtain ⟨events, t, q, crashValue, hrun, hother, _, hdecQ⟩ :=
      hcrash c haccessible e.target
    have hdec : DecidedIn t crashValue := ⟨q, hdecQ⟩
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
    · exact .inr ⟨hpossibleFE, hright⟩
    · exact .inl ⟨hleft, hpossibleE⟩
    · exact .inl ⟨hpossibleE, hleft⟩
    · exact .inr ⟨hright, hpossibleFE⟩
  · have heF : Enabled (advance protocol c e) f :=
      enabled_after_other protocol c e f (Ne.symm htarget) hf
    have hdiamond : advance protocol (advance protocol c e) f =
        advance protocol (advance protocol c f) e :=
      flp_lemma1_diamond protocol c e f (Ne.symm htarget)
    have hreach : Reachable protocol (advance protocol c e)
        (advance protocol (advance protocol c f) e) := by
      rw [← hdiamond]
      exact .tail (.refl _) f heF
    have hother : ReachableDecision protocol (advance protocol c e) value.flip :=
      reachableDecision_of_reachable protocol hreach hright
    cases value with
    | zero => exact .inl ⟨hleft, hother⟩
    | one => exact .inl ⟨hother, hleft⟩

/-- Opposite univalent values cannot occur across one e-avoiding step. -/
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
  have hb := e_image_neighbor_bivalence protocol initial c e f haccessible
    hcrash hpersist he hf hdifferent value hleft.1 hright.1
  cases hb with
  | inl h =>
    cases value with
    | zero => exact hleft.2 h.2
    | one => exact hleft.2 h.1
  | inr h =>
    cases value with
    | zero => exact hright.2 h.1
    | one => exact hright.2 h.2

theorem reachable_decision_of_crash_deciding (protocol : Protocol Node Msg Local)
    (initial c : Config Node Msg Local)
    (hcrash : CrashDecidingReachable protocol initial)
    (hc : Reachable protocol initial c) (silent : Node) :
    ∃ value, ReachableDecision protocol c value := by
  obtain ⟨events, t, q, value, hrun, _, _, hdec⟩ := hcrash c hc silent
  exact ⟨value, t, Schedule.reachable protocol hrun, ⟨q, hdec⟩⟩

/-- Along a finite schedule that delays `e`, opposite decision possibilities
at the initial and final `e`-images force a bivalent image at some prefix.
The returned prefix is itself a valid schedule and still avoids `e`. -/
theorem bivalent_e_image_along_schedule (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (e : Event Node Msg)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    {c d : Config Node Msg Local} {events : List (Event Node Msg)}
    (hrun : Schedule protocol c events d) :
    e ∉ events → Reachable protocol initial c → Enabled c e →
    ∀ value, ReachableDecision protocol (advance protocol c e) value →
      ReachableDecision protocol (advance protocol d e) value.flip →
      ∃ before mid, Schedule protocol c before mid ∧ e ∉ before ∧
        IsBivalent protocol (advance protocol mid e) := by
  induction hrun with
  | nil =>
    intro _ _ _ value hstart hend
    cases value with
    | zero => exact ⟨[], _, .nil _, by simp, ⟨hstart, hend⟩⟩
    | one => exact ⟨[], _, .nil _, by simp, ⟨hend, hstart⟩⟩
  | @cons c d f hf fs tail ih =>
    intro havoid haccess he value hstart hend
    have hneq : f ≠ e := by
      intro h
      have hm : e ∈ f :: fs := by simp [h]
      exact havoid hm
    have htailAvoid : e ∉ fs := by
      intro hm
      exact havoid (List.mem_cons_of_mem f hm)
    have he' : Enabled (advance protocol c f) e :=
      enabled_after_different_event protocol c e f hneq he
    have hnext : Reachable protocol initial (advance protocol c f) :=
      .tail haccess f hf
    have himage : Reachable protocol initial (advance protocol (advance protocol c f) e) :=
      .tail hnext e he'
    obtain ⟨nextValue, hnextDecision⟩ :=
      reachable_decision_of_crash_deciding protocol initial
        (advance protocol (advance protocol c f) e) hcrash himage e.target
    cases value with
    | zero =>
      cases nextValue with
      | zero =>
        obtain ⟨before, mid, hbefore, hbeforeAvoid, hb⟩ :=
          ih htailAvoid hnext he' .zero hnextDecision hend
        refine ⟨f :: before, mid, .cons f hf hbefore, ?_, hb⟩
        intro hm
        cases List.mem_cons.mp hm with
        | inl h => exact hneq h.symm
        | inr h => exact hbeforeAvoid h
      | one =>
        cases e_image_neighbor_bivalence protocol initial c e f haccess
            hcrash hpersist he hf hneq .zero hstart hnextDecision with
        | inl hb => exact ⟨[], c, .nil _, by simp, hb⟩
        | inr hb =>
          exact ⟨[f], advance protocol c f, .cons f hf (.nil _),
            by simp [Ne.symm hneq], hb⟩
    | one =>
      cases nextValue with
      | zero =>
        cases e_image_neighbor_bivalence protocol initial c e f haccess
            hcrash hpersist he hf hneq .one hstart hnextDecision with
        | inl hb => exact ⟨[], c, .nil _, by simp, hb⟩
        | inr hb =>
          exact ⟨[f], advance protocol c f, .cons f hf (.nil _),
            by simp [Ne.symm hneq], hb⟩
      | one =>
        obtain ⟨before, mid, hbefore, hbeforeAvoid, hb⟩ :=
          ih htailAvoid hnext he' .one hnextDecision hend
        refine ⟨f :: before, mid, .cons f hf hbefore, ?_, hb⟩
        intro hm
        cases List.mem_cons.mp hm with
        | inl h => exact hneq h.symm
        | inr h => exact hbeforeAvoid h

/-- A reachable decision from `c` yields an e-avoiding prefix whose e-image
still has that decision possibility. If the original deciding schedule uses
`e`, cut it at the first occurrence; otherwise apply `e` after the decision,
using write-once persistence. -/
theorem e_image_decision_from_reachable (protocol : Protocol Node Msg Local)
    (hpersist : DecisionsPersist protocol)
    (c : Config Node Msg Local) (e : Event Node Msg) (he : Enabled c e)
    (value : Decision) (hv : ReachableDecision protocol c value) :
    ∃ events d, Schedule protocol c events d ∧ e ∉ events ∧ Enabled d e ∧
      ReachableDecision protocol (advance protocol d e) value := by
  obtain ⟨t, hreach, hdec⟩ := hv
  obtain ⟨events, hrun⟩ := Reachable.schedule protocol hreach
  by_cases hpresent : e ∈ events
  · obtain ⟨before, after, mid, _, havoid, hbefore, henabled, hafter⟩ :=
      schedule_split_first_occurrence protocol hrun e hpresent
    exact ⟨before, mid, hbefore, havoid, henabled,
      ⟨t, Schedule.reachable protocol hafter, hdec⟩⟩
  · have henabled := enabled_after_schedule_avoiding_event protocol hrun e he hpresent
    have hdec' : DecidedIn (advance protocol t e) value :=
      hpersist t e value henabled hdec
    exact ⟨events, t, hrun, hpresent, henabled,
      ⟨advance protocol t e, .refl _, hdec'⟩⟩

/-- FLP Lemma 3: from a bivalent accessible configuration and any enabled
event, an adversary can run a finite schedule avoiding that event and then
apply it while retaining bivalence. The crash-deciding premise is the finite
form of one-fault termination used by the classical proof; global agreement
is needed later to turn this extension into a nondeciding fair run. -/
theorem flp_lemma3_bivalence_step (protocol : Protocol Node Msg Local)
    (initial c : Config Node Msg Local) (e : Event Node Msg)
    (haccessible : Reachable protocol initial c)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    (hbivalent : IsBivalent protocol c) (he : Enabled c e) :
    ∃ events d, Schedule protocol c events d ∧ e ∉ events ∧ Enabled d e ∧
      IsBivalent protocol (advance protocol d e) := by
  obtain ⟨eventsZero, dZero, hrunZero, havoidZero, _, hzero⟩ :=
    e_image_decision_from_reachable protocol hpersist c e he .zero hbivalent.1
  obtain ⟨eventsOne, dOne, hrunOne, havoidOne, _, hone⟩ :=
    e_image_decision_from_reachable protocol hpersist c e he .one hbivalent.2
  have himage : Reachable protocol initial (advance protocol c e) :=
    .tail haccessible e he
  obtain ⟨startValue, hstart⟩ :=
    reachable_decision_of_crash_deciding protocol initial
      (advance protocol c e) hcrash himage e.target
  cases startValue with
  | zero =>
    obtain ⟨before, mid, hbefore, havoid, hb⟩ :=
      bivalent_e_image_along_schedule protocol initial e hcrash hpersist
        hrunOne havoidOne haccessible he .zero hstart hone
    exact ⟨before, mid, hbefore, havoid,
      enabled_after_schedule_avoiding_event protocol hbefore e he havoid, hb⟩
  | one =>
    obtain ⟨before, mid, hbefore, havoid, hb⟩ :=
      bivalent_e_image_along_schedule protocol initial e hcrash hpersist
        hrunZero havoidZero haccessible he .one hstart hzero
    exact ⟨before, mid, hbefore, havoid,
      enabled_after_schedule_avoiding_event protocol hbefore e he havoid, hb⟩

end Harmonia.FLP
