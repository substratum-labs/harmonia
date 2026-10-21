import Harmonia.Examples.Foundation
namespace Harmonia.Foundation.Tests.Refinement
open Harmonia.Foundation Harmonia.Foundation.Examples

theorem witnessed : ∃ c, concrete.init c := concrete_initial

theorem path : Execution concrete (0, false)
    [((), (1, true)), ((), (2, false))] (2, false) :=
  .cons ⟨by decide, rfl, rfl⟩ (.cons ⟨by decide, rfl, rfl⟩ .nil)

theorem mapped_path : ∃ b' labels,
    Execution counter 0 labels b' ∧ (2, false).1 = b' ∧
      observations labels = [1, 2] := by
  exact ForwardSimulation.lift simulation rfl path

theorem zero_lift : ∃ b' labels,
    Execution counter 0 labels b' ∧ (0, false).1 = b' ∧
      observations labels = [] :=
  ForwardSimulation.lift simulation rfl (Execution.nil (s := (0, false)))

theorem concrete_reachable : Reachable concrete (2, false) :=
  execution_reachable rfl path

theorem safety (h : Reachable concrete c) : c.1 ≤ 2 :=
  ForwardSimulation.transfer_invariant simulation
    (fun _ hb => counter_safe hb) (fun _ _ hr hi => hr ▸ hi) h

theorem wrong_mapping : ¬ ForwardSimulation concrete counter
    (fun c b => c.1 = b) (fun _ => 99) := by
  intro sim
  obtain ⟨a, b, hs, hr⟩ := sim.matchStep (0, false) () (1, true) (1, true) 0
    rfl ⟨by decide, rfl, rfl⟩
  have hb : b = 1 := hs.2.1
  have ho : 99 = b := hs.2.2
  rw [hb] at ho
  cases ho

def emptyCounter : TransitionSystem Nat Unit Nat where
  init _ := False
  step := counter.step

theorem missing_abstract_initial : ¬ ForwardSimulation concrete emptyCounter
    (fun c b => c.1 = b) Prod.fst := by
  intro sim
  obtain ⟨b, hi, _⟩ := sim.initial (0, false) rfl
  exact hi

theorem lifted_reachability (h : Reachable concrete c) :
    ∃ b, Reachable counter b ∧ c.1 = b := simulation.reachable h
end Harmonia.Foundation.Tests.Refinement
