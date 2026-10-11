import Harmonia.Theorems.FLPExtension
import Harmonia.Theorems.FLPInputs

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

/-- Reachable-state one-crash deciding implies the initial-state version for
any family of initial configurations. The reverse direction does not follow:
the initial premise contains no information about later reachable states. -/
theorem initial_crash_deciding_of_reachable (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local → Prop)
    (hcrash : ∀ c, initial c → CrashDecidingReachable protocol c) :
    Initial.CrashDeciding
      (initialSystem protocol initial IndistinguishableExcept
        (replay_other_process protocol) decision_other_process) := by
  let sys := initialSystem protocol initial IndistinguishableExcept
    (replay_other_process protocol) decision_other_process
  intro c silent hc
  obtain ⟨events, t, q, value, hrun, hother, hq, hd⟩ :=
    hcrash c hc c (.refl c) silent
  have convert : ∀ {a b es}, Schedule protocol a es b →
      Initial.Run sys a es b := by
    intro a b es h
    induction h with
    | nil => exact .nil
    | cons e he _ ih => exact .cons ⟨he, rfl⟩ ih
  exact ⟨events, t, q, value, convert hrun, hother, hq, hd⟩

/-- Connected finite FLP consequence. Binary validity and a finite input cube
force some initial bivalent configuration; Lemma 3 then rules out a uniform
finite decision bound for that configuration. This does not construct the
paper's infinite fair adversarial execution. -/
theorem flp_impossibility (protocol : Protocol Node Msg Local)
    (initialFor : (Node → Decision) → Config Node Msg Local)
    (nodes : List Node) (complete : ∀ n, n ∈ nodes)
    (hlocal : ∀ inputs inputs' p,
      (∀ q, q ≠ p → inputs q = inputs' q) →
      IndistinguishableExcept p (initialFor inputs) (initialFor inputs'))
    (valid : BinaryValidity protocol initialFor)
    (hcrash : ∀ inputs, CrashDecidingReachable protocol (initialFor inputs))
    (agreement : ∀ inputs, Agreement protocol (initialFor inputs))
    (hpersist : DecisionsPersist protocol)
    (node : Node) :
    ∃ inputs, ¬ UniformBoundedTermination protocol (initialFor inputs) := by
  let initial : Config Node Msg Local → Prop :=
    fun c => ∃ inputs, c = initialFor inputs
  have hinit : ∀ inputs, initial (initialFor inputs) := by
    intro inputs
    exact ⟨inputs, rfl⟩
  have hcrashInitial : Initial.CrashDeciding
      (initialSystem protocol initial IndistinguishableExcept
        (replay_other_process protocol) decision_other_process) := by
    apply initial_crash_deciding_of_reachable protocol initial
    intro c hc
    obtain ⟨inputs, rfl⟩ := hc
    exact hcrash inputs
  obtain ⟨c, ⟨inputs, rfl⟩, hb⟩ :=
    initial_bivalent_from_binary_inputs protocol initial initialFor nodes complete
      hinit hlocal hcrashInitial valid
  exact ⟨inputs, no_uniform_decision_bound protocol (initialFor inputs) node
    (hcrash inputs) (agreement inputs) hpersist hb⟩

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
