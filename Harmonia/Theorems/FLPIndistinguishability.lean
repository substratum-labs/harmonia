import Harmonia.Theorems.FLPInitial

namespace Harmonia.FLP

universe u v w
variable {Node : Type u} {Msg : Type v} {Local : Type w}
variable [DecidableEq Node] [DecidableEq Msg]

/-- Configurations look the same to every process except one silent process.
All messages destined for active processes are also the same. -/
def IndistinguishableExcept (silent : Node)
    (c d : Config Node Msg Local) : Prop :=
  (∀ n, n ≠ silent → c.state n = d.state n) ∧
  (∀ n m, n ≠ silent → c.buffer n m = d.buffer n m) ∧
  (∀ n, n ≠ silent → c.decision n = d.decision n)

theorem replay_other_process (p : Protocol Node Msg Local)
    {silent : Node} {c d : Config Node Msg Local}
    {e : Event Node Msg}
    (h : IndistinguishableExcept silent c d)
    (htarget : e.target ≠ silent) (he : Enabled c e) :
    Enabled d e ∧
      IndistinguishableExcept silent (advance p c e) (advance p d e) := by
  have hstate := h.1 e.target htarget
  have henabled : Enabled d e := by
    cases hmsg : e.msg with
    | none => simp [Enabled, hmsg]
    | some m => simpa [Enabled, hmsg, (h.2.1 e.target m htarget).symm] using he
  refine ⟨henabled, ?_, ?_, ?_⟩
  · intro n hn
    by_cases hne : n = e.target
    · simp [advance, hne, hstate]
    · simp [advance, hne, h.1 n hn]
  · intro n m hn
    simp only [advance]
    rw [h.2.1 n m hn, hstate]
  · intro n hn
    by_cases hne : n = e.target
    · have hdecision := h.2.2 n hn
      have hd : c.decision e.target = d.decision e.target := by
        simpa only [hne] using hdecision
      simp [advance, hne, hstate, hd]
    · simp [advance, hne, h.2.2 n hn]

omit [DecidableEq Node] [DecidableEq Msg] in
theorem decision_other_process
    {silent q : Node} {c d : Config Node Msg Local} {value : Decision}
    (h : IndistinguishableExcept silent c d) (hq : q ≠ silent)
    (hv : c.decision q = some value) : d.decision q = some value := by
  rw [← h.2.2 q hq]
  exact hv

/-- Lemma 2 specialized to the concrete local-state and buffer relation.
The remaining finite input chain and crash-decision trace obligations are
visible parameters, rather than protocol axioms. -/
theorem initial_bivalent_from_crash (p : Protocol Node Msg Local)
    (initial : Config Node Msg Local → Prop)
    (hcrash : Initial.CrashDeciding
      (initialSystem p initial IndistinguishableExcept
        (replay_other_process p) decision_other_process))
    {first last : Config Node Msg Local}
    (hchain : Initial.InitialChain
      (initialSystem p initial IndistinguishableExcept
        (replay_other_process p) decision_other_process) first last)
    (hzero : ReachableDecision p first .zero)
    (hone : ReachableDecision p last .one) :
    ∃ c, initial c ∧ IsBivalent p c :=
  flp_lemma2_initial_bivalent p initial IndistinguishableExcept
    (replay_other_process p) decision_other_process hcrash hchain hzero hone

end Harmonia.FLP
