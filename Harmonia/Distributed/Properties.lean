import Harmonia.Distributed.Semantics
namespace Harmonia.Distributed
universe u
variable {M D V L P : Type u}
def WF (s : State M D V L P) : Prop :=
  (s.pending.map (fun e => e.tid)).Nodup ∧ ∀ e, e ∈ s.pending → e.tid < s.next
def PoolEq (s t : State M D V L P) : Prop :=
  s.nodes = t.nodes ∧ s.next = t.next ∧ s.pending.Perm t.pending
namespace PoolEq
theorem refl (s : State M D V L P) : PoolEq s s := ⟨rfl,rfl,.refl _⟩
theorem symm (h : PoolEq s t) : PoolEq t s := ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩
theorem trans (h : PoolEq s t) (h' : PoolEq t r) : PoolEq s r :=
  ⟨h.1.trans h'.1,h.2.1.trans h'.2.1,h.2.2.trans h'.2.2⟩
theorem wf_iff (h : PoolEq s t) : WF s ↔ WF t := by
  constructor
  · rintro ⟨hd,hb⟩
    refine ⟨(h.2.2.map _).nodup hd, ?_⟩
    intro e he
    rw [← h.2.1]
    exact hb e (h.2.2.mem_iff.mpr he)
  · rintro ⟨hd,hb⟩
    refine ⟨(h.2.2.symm.map _).nodup hd, ?_⟩
    intro e he
    rw [h.2.1]
    exact hb e (h.2.2.mem_iff.mp he)
end PoolEq

variable {N C K : Type u} [DecidableEq N] {c : Config N}
variable {p : Protocol (Member c) D V L P C K} {f : FaultProfile}
variable {s t : State (Member c) D V L P}
namespace PoolEq
theorem init_iff (h : PoolEq s t) : (system c p f).init s ↔ (system c p f).init t := by
  have pools : s.pending = [] ↔ t.pending = [] := by
    constructor
    · intro hs; have hp := h.2.2.symm; rw [hs] at hp; exact hp.eq_nil
    · intro ht; have hp := h.2.2; rw [ht] at hp; exact hp.eq_nil
  simp only [system, pools, h.1, h.2.1]
end PoolEq

namespace Step
theorem frame (h : Step c p f s a t) (peer : Member c) (other : actorOf a ≠ some peer) :
    t.nodes peer = s.nodes peer := by
  cases h <;> simp only [actorOf, ne_eq, Option.some.injEq] at other
  case process => exact setNode_other (Ne.symm other)
  case deliver => exact setNode_other (Ne.symm other)
  case drop => rfl
  case duplicate => rfl
  case crash => exact setNode_other (Ne.symm other)
  case recover => exact setNode_other (Ne.symm other)

theorem crash_durable (h : Step c p f s (.crash actor) t) :
    (t.nodes actor).durable = (s.nodes actor).durable := by
  cases h; simp
theorem recover_durable (h : Step c p f s (.recover actor) t) :
    (t.nodes actor).durable = (s.nodes actor).durable := by
  cases h; simp
theorem next_monotone (h : Step c p f s a t) : s.next ≤ t.next := by
  cases h <;> simp

theorem permutation_lift {s' : State (Member c) D V L P}
    (eq : PoolEq s s') (h : Step c p f s a t) :
    ∃ t', Step c p f s' a t' ∧ PoolEq t t' := by
  rcases s with ⟨nodes,pool,n⟩
  rcases s' with ⟨nodes',pool',n'⟩
  rcases eq with ⟨hn,hnxt,hpool⟩
  cases hn; cases hnxt
  cases h with
  | process hr react pub =>
    exact ⟨_, .process hr react ((Publish.perm_base hpool).mp pub), PoolEq.refl _⟩
  | deliver hr take react pub =>
    exact ⟨_, .deliver hr ((Take.perm_left hpool).mp take) react pub, PoolEq.refl _⟩
  | drop ha take => exact ⟨_, .drop ha ((Take.perm_left hpool).mp take), PoolEq.refl _⟩
  | duplicate ha present copy =>
    exact ⟨_, .duplicate ha (hpool.mem_iff.mp present) (copy.trans (hpool.cons _)), PoolEq.refl _⟩
  | crash ha hr => exact ⟨_, .crash ha hr, ⟨rfl,rfl,hpool⟩⟩
  | recover ha hr => exact ⟨_, .recover ha hr, ⟨rfl,rfl,hpool⟩⟩

theorem deliver_consumes (h : Step c p f s (.deliver e outs) t) :
    ∃ rest, Take s.pending e rest ∧ Publish e.envelope.recipient s.next outs rest t.pending := by
  cases h with
  | deliver _ ht _ hp => exact ⟨_,ht,hp⟩
theorem deliver_length (h : Step c p f s (.deliver e outs) t) :
    t.pending.length + 1 = s.pending.length + outs.length := by
  obtain ⟨rest,ht,hp⟩ := deliver_consumes h
  have hl := ht.length_eq
  have hp' := hp.length_eq
  simp only [List.length_cons, List.length_append, allocate_length] at hl hp'
  omega
end Step

theorem execution_permutation {s' : State (Member c) D V L P} (eq : PoolEq s s')
    (path : Foundation.Execution (system c p f) s labels t) :
    ∃ t', Foundation.Execution (system c p f) s' labels t' ∧ PoolEq t t' := by
  induction path generalizing s' with
  | nil => exact ⟨_,.nil,eq⟩
  | cons hs tail ih =>
    obtain ⟨m',hm,heq⟩ := Step.permutation_lift eq hs.1
    obtain ⟨t',ht,hend⟩ := ih heq
    exact ⟨t',.cons ⟨hm,hs.2⟩ ht,hend⟩

-- Core helper: append two nodup lists whose elements are disjoint.
theorem nodup_append_of_disjoint {xs ys : List T} (hx : xs.Nodup) (hy : ys.Nodup)
    (disjoint : ∀ x, x ∈ xs → x ∈ ys → False) : (xs ++ ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hx
    apply List.nodup_cons.mpr
    refine ⟨?_, ih ht (fun y he => disjoint y (List.mem_cons_of_mem _ he))⟩
    intro hm
    cases List.mem_append.mp hm with
    | inl h => exact hn h
    | inr h => exact disjoint x (by simp) h

def PoolWF (pool : List (Transmission M L P)) (n : Nat) : Prop :=
  (pool.map (fun e => e.tid)).Nodup ∧ ∀ e, e ∈ pool → e.tid < n
namespace PoolWF
theorem perm (h : PoolWF pool n) (hp : pool.Perm pool') : PoolWF pool' n :=
  ⟨(hp.map _).nodup h.1,fun e he => h.2 e (hp.mem_iff.mpr he)⟩
theorem take (h : PoolWF pool n) (ht : Take pool e rest) : PoolWF rest n := by
  have hc := h.perm ht
  exact ⟨(List.nodup_cons.mp hc.1).2,fun x hx => hc.2 x (by simp [hx])⟩
theorem publish (h : PoolWF pool n) (hp : Publish actor n outs pool result) :
    PoolWF result (n + outs.length) := by
  have fresh := allocate_fresh actor n outs
  have nd : ((pool ++ allocate actor n outs).map (fun e => e.tid)).Nodup := by
    rw [List.map_append]
    apply nodup_append_of_disjoint h.1 fresh.1
    intro id ho hn
    obtain ⟨old,hold,hid⟩ := List.mem_map.mp ho
    obtain ⟨new,hnew,hnid⟩ := List.mem_map.mp hn
    have hb := h.2 old hold
    have hf := fresh.2 new hnew
    omega
  apply PoolWF.perm (pool := pool ++ allocate actor n outs) ⟨nd, ?_⟩ hp.symm
  intro e he
  cases List.mem_append.mp he with
  | inl old => have hb := h.2 e old; omega
  | inr new => exact (fresh.2 e new).2
end PoolWF

theorem wf_initial : Foundation.Initially (system c p f) WF := by
  intro s hi
  unfold WF
  rw [hi.1]
  simp

theorem wf_preserved : Foundation.Preserved (system c p f) WF := by
  intro s a o t hw hs
  cases hs.1 with
  | process _ _ hp => exact PoolWF.publish hw hp
  | deliver _ ht _ hp => exact PoolWF.publish (PoolWF.take hw ht) hp
  | drop _ ht => exact PoolWF.take hw ht
  | duplicate _ _ hc =>
    apply PoolWF.perm (pool := freshCopy _ s.next :: s.pending) ?_ hc.symm
    constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_,hw.1⟩
      intro hm
      obtain ⟨e,he,hid⟩ := List.mem_map.mp hm
      have hb := hw.2 e he
      simp only [freshCopy] at hid
      omega
    · intro e he
      cases List.mem_cons.mp he with
      | inl he => subst e; simp [freshCopy]
      | inr he => have hb := hw.2 e he; change e.tid < s.next+1; omega
  | crash _ _ => exact hw
  | recover _ _ => exact hw

theorem reachable_wf (h : Foundation.Reachable (system c p f) s) : WF s :=
  Foundation.invariant wf_initial wf_preserved s h

namespace Step
theorem duplicate_fresh (hw : WF s) (h : Step c p f s (.duplicate e) t) :
    (∀ old, old ∈ s.pending → old.tid ≠ s.next) ∧
    freshCopy e s.next ∈ t.pending ∧ e ∈ t.pending ∧
    (freshCopy e s.next).envelope = e.envelope ∧ t.next = s.next+1 := by
  cases h with
  | duplicate _ he hc =>
    refine ⟨fun old ho => Nat.ne_of_lt (hw.2 old ho), hc.mem_iff.mpr (by simp),
      hc.mem_iff.mpr (by simp [he]), rfl,rfl⟩
end Step

/-- Envelope publication, not occurrence allocation history or payload authentication. -/
def emitted (s : State M D V L P) : Label M L P C K → List (Envelope M L P)
  | .process actor _ outs => (allocate actor s.next outs).map (fun e => e.envelope)
  | .deliver e outs => (allocate e.envelope.recipient s.next outs).map (fun e => e.envelope)
  | _ => []

namespace Step
theorem pending_origin (h : Step c p f s a t) (he : e ∈ t.pending) :
    (∃ old, old ∈ s.pending ∧ old.envelope = e.envelope) ∨ e.envelope ∈ emitted s a := by
  cases h with
  | process _ _ hp =>
    cases List.mem_append.mp (hp.mem_iff.mp he) with
    | inl old => exact .inl ⟨e,old,rfl⟩
    | inr new => exact .inr (List.mem_map.mpr ⟨e,new,rfl⟩)
  | deliver _ ht _ hp =>
    cases List.mem_append.mp (hp.mem_iff.mp he) with
    | inl old => exact .inl ⟨e,ht.mem_iff.mpr (List.mem_cons_of_mem _ old),rfl⟩
    | inr new => exact .inr (List.mem_map.mpr ⟨e,new,rfl⟩)
  | drop _ ht => exact .inl ⟨e,ht.mem_iff.mpr (List.mem_cons_of_mem _ he),rfl⟩
  | duplicate _ present hc =>
    cases List.mem_cons.mp (hc.mem_iff.mp he) with
    | inl eq => subst e; exact .inl ⟨_,present,rfl⟩
    | inr old => exact .inl ⟨e,old,rfl⟩
  | crash _ _ => exact .inl ⟨e,he,rfl⟩
  | recover _ _ => exact .inl ⟨e,he,rfl⟩
end Step

inductive SentIn : {src dst : State (Member c) D V L P} →
    {labels : List (Label (Member c) L P C K × Label (Member c) L P C K)} →
    Foundation.Execution (system c p f) src labels dst → Envelope (Member c) L P → Prop where
  | head {src mid dst : State (Member c) D V L P}
      {action obs : Label (Member c) L P C K} {trace}
      (hs : (system c p f).step src action obs mid)
      (path : Foundation.Execution (system c p f) mid trace dst)
      (h : envelope ∈ emitted src action) : SentIn (.cons hs path) envelope
  | tail {src mid dst : State (Member c) D V L P}
      {action obs : Label (Member c) L P C K} {trace}
      (hs : (system c p f).step src action obs mid)
      (path : Foundation.Execution (system c p f) mid trace dst)
      (h : SentIn path envelope) : SentIn (.cons hs path) envelope

theorem pending_origin (path : Foundation.Execution (system c p f) s labels t)
    (he : e ∈ t.pending) :
    (∃ old, old ∈ s.pending ∧ old.envelope = e.envelope) ∨ SentIn path e.envelope := by
  induction path with
  | nil => exact .inl ⟨e,he,rfl⟩
  | cons hs tail ih =>
    cases ih he with
    | inr sent => exact .inr (.tail hs tail sent)
    | inl origin =>
      obtain ⟨mid,hm,eq⟩ := origin
      cases Step.pending_origin hs.1 hm with
      | inl before =>
        obtain ⟨old,ho,oeq⟩ := before
        exact .inl ⟨old,ho,oeq.trans eq⟩
      | inr published =>
        exact .inr (.head hs tail (eq ▸ published))

theorem provenance_history (hi : (system c p f).init s)
    (path : Foundation.Execution (system c p f) s labels t) (he : e ∈ t.pending) :
    SentIn path e.envelope := by
  cases pending_origin path he with
  | inl origin => obtain ⟨old,ho,_⟩ := origin; rw [hi.1] at ho; cases ho
  | inr sent => exact sent

namespace Step
theorem deliver_tid_absent (hw : WF s) (h : Step c p f s (.deliver e outs) t)
    (hold : old ∈ t.pending) : old.tid ≠ e.tid := by
  cases h with
  | deliver _ ht _ hp =>
    have consumed : e ∈ s.pending := ht.mem_iff.mpr (by simp)
    have bound := hw.2 e consumed
    have nd := (ht.map (fun e => e.tid)).nodup hw.1
    have absent := (List.nodup_cons.mp nd).1
    cases List.mem_append.mp (hp.mem_iff.mp hold) with
    | inl rest =>
      intro eq
      exact absent (List.mem_map.mpr ⟨old,rest,eq⟩)
    | inr new => have hb := allocate_bounds _ _ _ new; omega

theorem no_replay_reachable (hr : Foundation.Reachable (system c p f) s)
    (first : Step c p f s (.deliver e outs) t) : ¬ Step c p f t (.deliver e outs') r := by
  intro second
  obtain ⟨rest,ht,_⟩ := deliver_consumes second
  have he : e ∈ t.pending := ht.mem_iff.mpr (by simp)
  exact deliver_tid_absent (reachable_wf hr) first he rfl
end Step
end Harmonia.Distributed
