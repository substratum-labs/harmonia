import Harmonia.Core.Invariant
namespace Harmonia.Foundation

/-- Exact one-step forward simulation: action labels may differ, observations
are preserved through the supplied map, and every concrete successor matches. -/
structure ForwardSimulation (C : TransitionSystem CS CA CO)
    (B : TransitionSystem BS BA BO) (R : CS → BS → Prop) (obsMap : CO → BO) : Prop where
  initial : ∀ c, C.init c → ∃ b, B.init b ∧ R c b
  matchStep : ∀ c a o c' b, R c b → C.step c a o c' →
    ∃ ba b', B.step b ba (obsMap o) b' ∧ R c' b'

namespace ForwardSimulation
variable {C : TransitionSystem CS CA CO} {B : TransitionSystem BS BA BO}
    {R : CS → BS → Prop} {obsMap : CO → BO}

theorem lift (sim : ForwardSimulation C B R obsMap) (hr : R c b)
    (path : Execution C c labels c') :
    ∃ b' bs, Execution B b bs b' ∧ R c' b' ∧
      observations bs = (observations labels).map obsMap := by
  induction path generalizing b with
  | nil => exact ⟨b, [], .nil, hr, rfl⟩
  | cons hs _ ih =>
    obtain ⟨ba, bm, hb, hm⟩ := sim.matchStep _ _ _ _ b hr hs
    obtain ⟨b', bs, tail, hend, hobs⟩ := ih hm
    refine ⟨b', (ba, _) :: bs, .cons hb tail, hend, ?_⟩
    exact congrArg (List.cons _) hobs

 theorem reachable (sim : ForwardSimulation C B R obsMap) (h : Reachable C c) :
    ∃ b, Reachable B b ∧ R c b := by
  obtain ⟨ci, labels, hi, path⟩ := reachable_iff_execution.mp h
  obtain ⟨bi, hbi, hrel⟩ := sim.initial ci hi
  obtain ⟨b, bs, hpath, hr, _⟩ := sim.lift hrel path
  exact ⟨b, execution_reachable hbi hpath, hr⟩

/-- Transfer any abstract reachable-state safety property through R.
This does not assert liveness, reverse simulation, or bisimulation. -/
theorem transfer_invariant (sim : ForwardSimulation C B R obsMap)
    {I : BS → Prop} {J : CS → Prop}
    (safe : ∀ b, Reachable B b → I b)
    (entails : ∀ c b, R c b → I b → J c) (h : Reachable C c) : J c := by
  obtain ⟨b, hb, hr⟩ := sim.reachable h
  exact entails c b hr (safe b hb)
end ForwardSimulation
end Harmonia.Foundation
