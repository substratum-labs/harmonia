import Harmonia.Theorems.FLPIndistinguishability

/-! Construct the adjacent initial-state chain by changing one binary input
at a time. The protocol-specific `initialFor` map must establish that changing
one input leaves all other processes' views unchanged. -/
namespace Harmonia.FLP

universe u v w
variable {Node : Type u} {Msg : Type v} {Local : Type w}
variable [DecidableEq Node] [DecidableEq Msg]

def mixedInput (covered : List Node) (n : Node) : Decision :=
  if n ∈ covered then .one else .zero

theorem mixedInput_append_single (covered : List Node) (p q : Node)
    (hqp : q ≠ p) :
    mixedInput covered q = mixedInput (covered ++ [p]) q := by
  simp [mixedInput, List.mem_append, hqp]

theorem binary_input_chain (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local → Prop)
    (initialFor : (Node → Decision) → Config Node Msg Local)
    (hinit : ∀ inputs, initial (initialFor inputs))
    (hlocal : ∀ inputs inputs' p,
      (∀ q, q ≠ p → inputs q = inputs' q) →
      IndistinguishableExcept p (initialFor inputs) (initialFor inputs'))
    (nodes : List Node) :
    Initial.InitialChain
      (initialSystem protocol initial IndistinguishableExcept
        (replay_other_process protocol) decision_other_process)
      (initialFor (mixedInput [])) (initialFor (mixedInput nodes)) := by
  let sys := initialSystem protocol initial IndistinguishableExcept
    (replay_other_process protocol) decision_other_process
  have build : ∀ covered remaining,
      Initial.InitialChain sys
        (initialFor (mixedInput covered))
        (initialFor (mixedInput (covered ++ remaining))) := by
    intro covered remaining
    induction remaining generalizing covered with
    | nil =>
      simpa using Initial.InitialChain.singleton (sys := sys)
        (hinit (mixedInput covered))
    | cons p rest ih =>
      have hadj : Initial.Adjacent sys
          (initialFor (mixedInput covered))
          (initialFor (mixedInput (covered ++ [p]))) := by
        refine ⟨p, hlocal _ _ p ?_⟩
        intro q hqp
        exact mixedInput_append_single covered p q hqp
      have htail := ih (covered ++ [p])
      have hcons : Initial.InitialChain sys
          (initialFor (mixedInput covered))
          (initialFor (mixedInput ((covered ++ [p]) ++ rest))) :=
        .cons (hinit (mixedInput covered)) hadj htail
      simpa only [List.append_assoc, List.singleton_append] using hcons
  simpa using build [] nodes

/-- Weak binary validity needed by FLP: uniform-zero and uniform-one inputs
each admit their corresponding decision. Agreement supplies exclusivity. -/
def BinaryValidity (protocol : Protocol Node Msg Local)
    (initialFor : (Node → Decision) → Config Node Msg Local) : Prop :=
  ReachableDecision protocol (initialFor (fun _ => .zero)) .zero ∧
  ReachableDecision protocol (initialFor (fun _ => .one)) .one

/-- Lemma 2 with an actual Hamming chain over a finite exhaustive node list.
The assumptions on `initialFor` and crash deciding are protocol obligations;
the input-chain and endpoint bridge are proved here. -/
theorem initial_bivalent_from_binary_inputs (protocol : Protocol Node Msg Local)
    (initial : Config Node Msg Local → Prop)
    (initialFor : (Node → Decision) → Config Node Msg Local)
    (nodes : List Node) (complete : ∀ n, n ∈ nodes)
    (hinit : ∀ inputs, initial (initialFor inputs))
    (hlocal : ∀ inputs inputs' p,
      (∀ q, q ≠ p → inputs q = inputs' q) →
      IndistinguishableExcept p (initialFor inputs) (initialFor inputs'))
    (hcrash : Initial.CrashDeciding
      (initialSystem protocol initial IndistinguishableExcept
        (replay_other_process protocol) decision_other_process))
    (valid : BinaryValidity protocol initialFor) :
    ∃ c, initial c ∧ IsBivalent protocol c := by
  have hchain := binary_input_chain protocol initial initialFor hinit hlocal nodes
  have hzero : initialFor (mixedInput ([] : List Node)) =
      initialFor (fun _ => .zero) := rfl
  have hone : initialFor (mixedInput nodes) =
      initialFor (fun _ => .one) := by
    congr 1
    funext n
    simp [mixedInput, complete n]
  exact initial_bivalent_from_crash protocol initial hcrash hchain
    (hzero ▸ valid.1) (hone ▸ valid.2)

end Harmonia.FLP
