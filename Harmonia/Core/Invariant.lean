import Harmonia.Core.Execution
namespace Harmonia.Foundation

def Initially (T : TransitionSystem S A O) (I : S → Prop) : Prop :=
  ∀ s, T.init s → I s

/-- Quantifies over every legal labeled successor, including nondeterminism. -/
def Preserved (T : TransitionSystem S A O) (I : S → Prop) : Prop :=
  ∀ s a o t, I s → T.step s a o t → I t

theorem invariant {T : TransitionSystem S A O} {I : S → Prop}
    (hi : Initially T I) (hp : Preserved T I) : ∀ s, Reachable T s → I s := by
  intro s hr
  induction hr with
  | init hs => exact hi _ hs
  | step _ hs ih => exact hp _ _ _ _ ih hs
end Harmonia.Foundation
