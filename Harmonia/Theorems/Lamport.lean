import Harmonia.Theorems.Causal

namespace Harmonia.Causal.Lamport

open Harmonia.Causal

abbrev ScalarClock := Nat

/-- `before e` is the local clock immediately before event `e`.
Sending attaches `clock e`; receiving merges the attached scalar first. -/
structure Clocking (t : Trace) where
  clock : Event → Nat
  before : Event → Nat
  messageClock : MessageId → Nat
  local_precedes : ∀ {e f}, ProgramOrder t e f → clock e ≤ before f
  local_tick : ∀ {e}, t.kind e = .internal → clock e = before e + 1
  send_tick : ∀ {e m}, t.kind e = .send m → clock e = before e + 1
  receive_tick : ∀ {e m}, t.kind e = .receive m →
    clock e = max (before e) (messageClock m) + 1
  attach : ∀ {e m}, t.kind e = .send m → messageClock m = clock e

theorem Clocking.after_before {t : Trace} (c : Clocking t) (e : Event) :
    c.before e < c.clock e := by
  cases h : t.kind e with
  | internal =>
      rw [c.local_tick h]
      omega
  | send m =>
      rw [c.send_tick h]
      omega
  | receive m =>
      rw [c.receive_tick h]
      omega

theorem Clocking.local_sound {t : Trace} (c : Clocking t) {e f : Event}
    (h : ProgramOrder t e f) : c.clock e < c.clock f := by
  have hp := c.local_precedes h
  have ht := c.after_before f
  omega

theorem Clocking.message_sound {t : Trace} (c : Clocking t) {e f m : Event}
    (hs : t.kind e = .send m) (hr : t.kind f = .receive m) :
    c.clock e < c.clock f := by
  have ha := c.attach hs
  rw [c.receive_tick hr]
  omega

theorem Clocking.sound {t : Trace} (c : Clocking t) {e f : Event}
    (h : HappensBefore t e f) : c.clock e < c.clock f := by
  induction h with
  | local_step he => exact c.local_sound he
  | msg_step _ _ hs hr => exact c.message_sound hs hr
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-- Lexicographic order by scalar clock, node ID, then unique event ID. -/
def LamportTotalOrder {t : Trace} (c : Clocking t) (e f : Event) : Prop :=
  c.clock e < c.clock f ∨
    (c.clock e = c.clock f ∧
      (t.node e < t.node f ∨ (t.node e = t.node f ∧ e < f)))

theorem total_irrefl {t : Trace} (c : Clocking t) (e : Event) :
    ¬ LamportTotalOrder c e e := by
  simp [LamportTotalOrder]

theorem total_trans {t : Trace} (c : Clocking t) {e f g : Event}
    (hef : LamportTotalOrder c e f) (hfg : LamportTotalOrder c f g) :
    LamportTotalOrder c e g := by
  unfold LamportTotalOrder at *
  rcases hef with hcf | ⟨hcf, hnf⟩
  · rcases hfg with hcg | ⟨hcg, _⟩
    · exact Or.inl (Nat.lt_trans hcf hcg)
    · exact Or.inl (hcg ▸ hcf)
  · rcases hfg with hcg | ⟨hcg, hng⟩
    · exact Or.inl (hcf ▸ hcg)
    · have hclock := hcf.trans hcg
      rcases hnf with hnf | ⟨hnf, hef⟩
      · rcases hng with hng | ⟨hng, _⟩
        · exact Or.inr ⟨hclock, Or.inl (Nat.lt_trans hnf hng)⟩
        · exact Or.inr ⟨hclock, Or.inl (hng ▸ hnf)⟩
      · rcases hng with hng | ⟨hng, hfg⟩
        · exact Or.inr ⟨hclock, Or.inl (hnf ▸ hng)⟩
        · exact Or.inr ⟨hclock, Or.inr ⟨hnf.trans hng, Nat.lt_trans hef hfg⟩⟩

theorem total_trichotomy {t : Trace} (c : Clocking t) (e f : Event) :
    LamportTotalOrder c e f ∨ e = f ∨ LamportTotalOrder c f e := by
  unfold LamportTotalOrder
  rcases Nat.lt_trichotomy (c.clock e) (c.clock f) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy (t.node e) (t.node f) with n | n | n
    · exact Or.inl (Or.inr ⟨h, Or.inl n⟩)
    · rcases Nat.lt_trichotomy e f with i | i | i
      · exact Or.inl (Or.inr ⟨h, Or.inr ⟨n, i⟩⟩)
      · exact Or.inr (Or.inl i)
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, Or.inr ⟨n.symm, i⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, Or.inl n⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem total_extends_causality {t : Trace} (c : Clocking t) {e f : Event}
    (h : HappensBefore t e f) : LamportTotalOrder c e f :=
  Or.inl (c.sound h)

/-- Two independent processes may have differently numbered scalar clocks. -/
def independentTrace : Trace where
  events := [0, 1]
  nodup := by decide
  node := id
  kind := fun _ => .internal
  message_forward := by intros; contradiction
  send_unique := by intros; contradiction

def independentClock : Clocking independentTrace where
  clock := fun e => e + 1
  before := id
  messageClock := fun _ => 0
  local_precedes := by
    intro e f h
    have hn : e = f := h.2.2.1
    exact False.elim ((Nat.lt_irrefl _) (hn ▸ h.2.2.2))
  local_tick := by intros; rfl
  send_tick := by intros; contradiction
  receive_tick := by intros; contradiction
  attach := by intros; contradiction

theorem independent_no_causality {e f : Event}
    (h : HappensBefore independentTrace e f) : False := by
  induction h with
  | local_step he =>
      have hn : _ = _ := he.2.2.1
      simp only [independentTrace, id] at hn
      exact (Nat.ne_of_lt he.2.2.2) hn
  | msg_step _ _ hs _ => cases hs
  | trans _ _ ih _ => exact ih

theorem scalar_incomplete :
    independentClock.clock 0 < independentClock.clock 1 ∧
      Concurrent independentTrace 0 1 := by
  constructor
  · decide
  · exact ⟨(fun h => independent_no_causality h),
      (fun h => independent_no_causality h), by decide⟩

end Harmonia.Causal.Lamport
