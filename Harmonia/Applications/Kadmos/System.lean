import Harmonia.Applications.Kadmos.Interpreter
import Harmonia.Core.Invariant
namespace Harmonia.Applications.Kadmos

def system (w : World p v f a) : Foundation.TransitionSystem (State p v) (Request f) Observation where
  init s := «initialize» w = .ok s
  step s r o t := interpret w s r = ⟨t,o⟩

theorem reachable_good {w : World p v f a} {initial : State p v}
    (_hi : «initialize» w = .ok initial) : ∀ s, Foundation.Reachable (system w) s → Good w s := by
  apply Foundation.invariant
  · intro s h; exact initialize_good h
  · intro s r o t hs step
    change interpret w s r = ⟨t,o⟩ at step
    cases hv : (interpret w s r).observation.verdict with
    | accepted =>
      have hg := accepted_good hv
      rw [step] at hg
      exact hg
    | rejected reason =>
      have hf := (rejection_frame hv).1
      rw [step] at hf
      change t = s at hf
      rw [hf]
      exact hs
end Harmonia.Applications.Kadmos
