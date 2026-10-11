import Harmonia.Theorems.FLPExtension

/-! A choice-free finite consequence of the FLP extension step. This rules out
any uniform finite decision bound; the full fair-run impossibility theorem
additionally needs an infinite adversarial scheduling construction. -/
namespace Harmonia.FLP

universe u v w
variable {Node : Type u} {Msg : Type v} {Local : Type w}
variable [DecidableEq Node] [DecidableEq Msg]

theorem arbitrarily_long_bivalent_schedules (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (node : Node)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    (hbivalent : IsBivalent protocol initial) :
    ∀ n, ∃ events d, Schedule protocol initial events d ∧
      n ≤ events.length ∧ IsBivalent protocol d := by
  intro n
  induction n with
  | zero => exact ⟨[], initial, .nil _, by simp, hbivalent⟩
  | succ n ih =>
    obtain ⟨events, d, hrun, hlength, hb⟩ := ih
    have haccess : Reachable protocol initial d := Schedule.reachable protocol hrun
    let e : Event Node Msg := ⟨node, none⟩
    have he : Enabled d e := by simp [Enabled, e]
    obtain ⟨before, mid, hbefore, _, hem, hbm⟩ :=
      flp_lemma3_bivalence_step protocol initial d e haccess hcrash hpersist hb he
    have hstage : Schedule protocol d (before ++ [e]) (advance protocol mid e) :=
      hbefore.append protocol (.cons e hem (.nil _))
    refine ⟨events ++ (before ++ [e]), advance protocol mid e,
      hrun.append protocol hstage, ?_, hbm⟩
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def UniformBoundedTermination (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) : Prop :=
  ∃ bound, ∀ {events d}, Schedule protocol initial events d →
    bound ≤ events.length → ∃ value, DecidedIn d value

/-- A deterministic asynchronous consensus protocol satisfying the finite
one-crash deciding premise, agreement, and decision persistence cannot have
one global finite upper bound on the number of events before decision. -/
theorem no_uniform_decision_bound (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (node : Node)
    (hcrash : CrashDecidingReachable protocol initial)
    (agreement : Agreement protocol initial)
    (hpersist : DecisionsPersist protocol)
    (hbivalent : IsBivalent protocol initial) :
    ¬ UniformBoundedTermination protocol initial := by
  intro hbounded
  obtain ⟨bound, hbound⟩ := hbounded
  obtain ⟨events, d, hrun, hlength, hb⟩ :=
    arbitrarily_long_bivalent_schedules protocol initial node hcrash
      hpersist hbivalent bound
  obtain ⟨value, hdec⟩ := hbound hrun hlength
  have hundecided := bivalent_undecided protocol initial d agreement hpersist
    (Schedule.reachable protocol hrun) hb
  cases value with
  | zero => exact hundecided.1 hdec
  | one => exact hundecided.2 hdec

/-- The finite choice-free FLP impossibility theorem: in an asynchronous system
with at least one crash failure, no deterministic consensus protocol can guarantee
a uniform finite decision bound while maintaining agreement, decision persistence,
and bivalence. -/
theorem flp_impossibility (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (node : Node)
    (hcrash : CrashDecidingReachable protocol initial)
    (agreement : Agreement protocol initial)
    (hpersist : DecisionsPersist protocol)
    (hbivalent : IsBivalent protocol initial) :
    ¬ UniformBoundedTermination protocol initial :=
  no_uniform_decision_bound protocol initial node hcrash agreement hpersist hbivalent

/-- A positive finite stage that ends in another bivalent configuration.
The relation is oriented for `Acc`: `BivalentStage protocol next current` says
`next` is a successor of `current`. -/
def BivalentStage (protocol : Protocol Node Msg Local)
    (next current : Config Node Msg Local) : Prop :=
  ∃ e before mid, Schedule protocol current before mid ∧
    Enabled mid e ∧ next = advance protocol mid e ∧ IsBivalent protocol next

/-- Every bivalent reachable state has a bivalent stage successor, so the
stage relation is not accessible there. This is a constructive statement in
`Prop`; it does not manufacture an infinite schedule. -/
theorem bivalent_stage_not_acc (protocol : Protocol Node Msg Local)
    (initial c : Config Node Msg Local) (node : Node)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    (haccessible : Reachable protocol initial c)
    (hbivalent : IsBivalent protocol c) :
    ¬ Acc (BivalentStage protocol) c := by
  have descend : ∀ x, Acc (BivalentStage protocol) x →
      Reachable protocol initial x → IsBivalent protocol x → False := by
    intro x hacc hx hbx
    induction hacc with
    | intro x _ ih =>
      let e : Event Node Msg := ⟨node, none⟩
      have he : Enabled x e := by simp [Enabled, e]
      obtain ⟨before, mid, hbefore, _, hem, hbnext⟩ :=
        flp_lemma3_bivalence_step protocol initial x e hx hcrash hpersist hbx he
      let next := advance protocol mid e
      have hstage : BivalentStage protocol next x :=
        ⟨e, before, mid, hbefore, hem, rfl, hbnext⟩
      have hreach : Reachable protocol initial next := by
        have hstep : Schedule protocol x (before ++ [e]) next :=
          hbefore.append protocol (.cons e hem (.nil _))
        exact hx.trans (Schedule.reachable protocol hstep)
      exact ih next hstage hreach hbnext
  intro hacc
  exact descend c hacc haccessible hbivalent

theorem bivalent_stages_not_well_founded (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local) (node : Node)
    (hcrash : CrashDecidingReachable protocol initial)
    (hpersist : DecisionsPersist protocol)
    (hbivalent : IsBivalent protocol initial) :
    ¬ WellFounded (BivalentStage protocol) := by
  intro hwf
  exact bivalent_stage_not_acc protocol initial initial node hcrash hpersist
    (.refl initial) hbivalent (hwf.apply initial)

end Harmonia.FLP
