/- Generic relational semantics. No executability or determinism assumption. -/
namespace Harmonia.Foundation
universe u v w

structure TransitionSystem (S : Type u) (A : Type v) (O : Type w) where
  init : S → Prop
  step : S → A → O → S → Prop

inductive Reachable (T : TransitionSystem S A O) : S → Prop where
  | init : T.init s → Reachable T s
  | step : Reachable T s → T.step s a o t → Reachable T t

end Harmonia.Foundation
