import Harmonia.Core.Refinement
import Harmonia.Distributed
import Harmonia.Theorems.Quorum

namespace Harmonia.VerifiedProtocols.QuorumLease
open Distributed
variable {N Val : Type} [DecidableEq N]

structure LeaseDurable (c : Config N) (Val : Type) where
  votedFor : Nat → Option (Member c)
  committed : Nat → Option (Member c × Val)

structure LeaseVolatile (c : Config N) (Val : Type) where
  collectedVotes : Nat → List (Member c)

inductive LeaseMsg (c : Config N) (Val : Type) where
  | voteGrant (epoch : Nat) (candidate : Member c)
  | fencedCommit (epoch : Nat) (leader : Member c) (val : Val)
  deriving DecidableEq

inductive LeaseCmd (c : Config N) (Val : Type) where
  | castVote (epoch : Nat) (candidate : Member c)
  | acquireAndCommit (epoch : Nat) (val : Val) (followers : List (Member c))
  deriving DecidableEq

def IsQuorum (c : Config N) (f : Nat) (voters : List (Member c)) : Prop :=
  (voters.map Subtype.val).Nodup ∧ 2 * f + 1 ≤ c.members.length ∧
    c.members.length ≤ (voters.map Subtype.val).length + f

inductive LeaseReact (c : Config N) (f : Nat) : Member c → LeaseDurable c Val →
    LeaseVolatile c Val → Input (Member c) Nat (LeaseMsg c Val) (LeaseCmd c Val) Empty →
    LeaseDurable c Val → LeaseVolatile c Val → List (Outgoing (Member c) Nat (LeaseMsg c Val)) → Prop where
  | castVote {actor d v e candidate} (guard : d.votedFor e = none) :
      LeaseReact c f actor d v (.scheduled (.local (.castVote e candidate)))
        { d with votedFor := fun e' => if e' = e then some candidate else d.votedFor e' }
        v [⟨candidate, e, .voteGrant e candidate⟩]
  | acquireAndCommit {actor d v e val followers}
      (quorum : IsQuorum c f (v.collectedVotes e)) (guard : d.committed e = none) :
      LeaseReact c f actor d v (.scheduled (.local (.acquireAndCommit e val followers)))
        { d with committed := fun e' => if e' = e then some (actor, val) else d.committed e' }
        v (followers.map fun peer => ⟨peer, e, .fencedCommit e actor val⟩)
  | voteGrant {actor d v e candidate sender l} (guard : candidate = actor) :
      LeaseReact c f actor d v (.message ⟨sender, actor, l, .voteGrant e candidate⟩) d
        ⟨fun e' => if e' = e then
          (if sender ∈ v.collectedVotes e then v.collectedVotes e else sender :: v.collectedVotes e)
          else v.collectedVotes e'⟩ []
  | fencedCommit {actor d v e leader val sender l}
      (authentic : sender = leader) (guard : d.committed e = none) :
      LeaseReact c f actor d v (.message ⟨sender, actor, l, .fencedCommit e leader val⟩)
        { d with committed := fun e' => if e' = e then some (leader, val) else d.committed e' } v []

def quorumLeaseProtocol (c : Config N) (f : Nat) :
    Protocol (Member c) (LeaseDurable c Val) (LeaseVolatile c Val) Nat (LeaseMsg c Val) (LeaseCmd c Val) Empty where
  initial _ d v := d.votedFor = (fun _ => none) ∧ d.committed = (fun _ => none) ∧
    v.collectedVotes = (fun _ => [])
  react := LeaseReact c f
  crashReset _ _ := ⟨fun _ => []⟩
  recover _ := ⟨fun _ => []⟩

abbrev LeaseState (c : Config N) (Val : Type) :=
  State (Member c) (LeaseDurable c Val) (LeaseVolatile c Val) Nat (LeaseMsg c Val)
abbrev LeaseLabel (c : Config N) (Val : Type) :=
  Label (Member c) Nat (LeaseMsg c Val) (LeaseCmd c Val) Empty

def sys (c : Config N) (f : Nat) (fp : FaultProfile) :=
  Distributed.system c (quorumLeaseProtocol (Val := Val) c f) fp

/-- A durable, persistent certificate; volatile tallies need not survive a crash. -/
def Certified (c : Config N) (f : Nat) (s : LeaseState c Val)
    (e : Nat) (leader : Member c) (val : Val) : Prop :=
  (s.nodes leader).durable.committed e = some (leader, val) ∧
  ∃ Q, IsQuorum c f Q ∧ ∀ voter ∈ Q, (s.nodes voter).durable.votedFor e = some leader

structure LeaseInv (c : Config N) (f : Nat) (s : LeaseState c Val) : Prop where
  votes_nodup : ∀ m e, (((s.nodes m).volatile.collectedVotes e).map Subtype.val).Nodup
  grant_in_flight_valid : ∀ t ∈ s.pending, ∀ e cand,
    t.envelope.payload = .voteGrant e cand → (s.nodes t.envelope.sender).durable.votedFor e = some cand
  collected_votes_valid : ∀ m e voter, voter ∈ (s.nodes m).volatile.collectedVotes e →
    (s.nodes voter).durable.votedFor e = some m
  leader_commit_has_quorum :
    (∀ t ∈ s.pending, ∀ e leader val, t.envelope.payload = .fencedCommit e leader val → Certified c f s e leader val) ∧
    (∀ n e leader val, (s.nodes n).durable.committed e = some (leader, val) → Certified c f s e leader val)
  commit_msg_authentic : ∀ t ∈ s.pending, ∀ e leader val,
    t.envelope.payload = .fencedCommit e leader val →
      (s.nodes leader).durable.committed e = some (leader, val)

omit [DecidableEq N] in
theorem mapped_members (c : Config N) (Q : List (Member c)) :
    ∀ x ∈ Q.map Subtype.val, x ∈ c.members := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact v.property

/-- Configuration membership is certified by `c.distinct`; the counting theorem
itself needs only the subset and cardinality premises. -/
theorem quorum_voters_intersect (c : Config N) (f : Nat) (Q₁ Q₂ : List (Member c))
    (h₁ : IsQuorum c f Q₁) (h₂ : IsQuorum c f Q₂) :
    ∃ v : Member c, v ∈ Q₁ ∧ v ∈ Q₂ := by
  have hi := Harmonia.Quorum.cft_intersection_at_least
    (Q₁.map Subtype.val) (Q₂.map Subtype.val) c.members f h₁.1 h₂.1
    (mapped_members c Q₁) (mapped_members c Q₂) h₁.2.1 h₁.2.2 h₂.2.2
  obtain ⟨x, hx⟩ := List.length_pos_iff_exists_mem.mp (by omega :
    0 < (Harmonia.Quorum.inter (Q₁.map Subtype.val) (Q₂.map Subtype.val)).length)
  have hm := List.mem_filter.mp hx
  obtain ⟨v, hv, he⟩ := List.mem_map.mp hm.1
  have hx₂ : x ∈ Q₂.map Subtype.val := by simpa using hm.2
  obtain ⟨w, hw, hwx⟩ := List.mem_map.mp hx₂
  have eq : w = v := Subtype.ext (hwx.trans he.symm)
  exact ⟨v, hv, eq ▸ hw⟩

theorem quorum_voters_intersect_exact (c : Config N) (f : Nat) (Q₁ Q₂ : List (Member c))
    (h₁ : (Q₁.map Subtype.val).Nodup) (h₂ : (Q₂.map Subtype.val).Nodup)
    (hN : c.members.length ≤ 2 * f + 1)
    (hq₁ : f + 1 ≤ (Q₁.map Subtype.val).length) (hq₂ : f + 1 ≤ (Q₂.map Subtype.val).length) :
    1 ≤ (Harmonia.Quorum.inter (Q₁.map Subtype.val) (Q₂.map Subtype.val)).length := by
  exact Harmonia.Quorum.cft_intersection _ _ c.members f h₁ h₂
    (mapped_members c Q₁) (mapped_members c Q₂) hN hq₁ hq₂

/-- Write-once durable facts survive every legal local update. -/
def DurableExtends (s t : LeaseState c Val) : Prop :=
  (∀ m e cand, (s.nodes m).durable.votedFor e = some cand →
    (t.nodes m).durable.votedFor e = some cand) ∧
  (∀ m e pair, (s.nodes m).durable.committed e = some pair →
    (t.nodes m).durable.committed e = some pair)

theorem certified_mono {s t : LeaseState c Val} (h : DurableExtends s t)
    (hc : Certified c f s e leader val) : Certified c f t e leader val := by
  obtain ⟨hl, Q, hq, hv⟩ := hc
  exact ⟨h.2 _ _ _ hl, Q, hq, fun voter hm => h.1 _ _ _ (hv voter hm)⟩

theorem leaseInv_initial (c : Config N) (f : Nat) (fp : FaultProfile)
    (s : LeaseState c Val) (h : (sys c f fp).init s) : LeaseInv c f s := by
  obtain ⟨hp, _, hn⟩ := h
  have hv : ∀ m, (s.nodes m).durable.votedFor = fun _ => none := fun m => (hn m).2.1
  have hc : ∀ m, (s.nodes m).durable.committed = fun _ => none := fun m => (hn m).2.2.1
  have ht : ∀ m, (s.nodes m).volatile.collectedVotes = fun _ => [] := fun m => (hn m).2.2.2
  constructor
  · intro m e; simp [ht]
  · simp [hp]
  · intro m e voter hm; simp [ht] at hm
  · constructor
    · simp [hp]
    · intro n e leader val he; simp [hc] at he
  · simp [hp]

/-- Reassemble the five clauses after changing nodes and publishing messages. -/
theorem rebuild {s t : LeaseState c Val} (h : LeaseInv c f s)
    (mono : DurableExtends s t)
    (nd : ∀ m e, (((t.nodes m).volatile.collectedVotes e).map Subtype.val).Nodup)
    (cv : ∀ m e voter, voter ∈ (t.nodes m).volatile.collectedVotes e →
      (t.nodes voter).durable.votedFor e = some m)
    (commits : ∀ m e leader val, (t.nodes m).durable.committed e = some (leader,val) →
      Certified c f t e leader val)
    (pending : ∀ x ∈ t.pending, x ∈ s.pending ∨
      ((∀ e cand, x.envelope.payload = .voteGrant e cand →
        (t.nodes x.envelope.sender).durable.votedFor e = some cand) ∧
       (∀ e leader val, x.envelope.payload = .fencedCommit e leader val →
        Certified c f t e leader val))) : LeaseInv c f t := by
  have grants : ∀ x ∈ t.pending, ∀ e cand, x.envelope.payload = .voteGrant e cand →
      (t.nodes x.envelope.sender).durable.votedFor e = some cand := by
    intro x hx e cand he
    rcases pending x hx with old | fresh
    · exact mono.1 _ _ _ (h.grant_in_flight_valid x old e cand he)
    · exact fresh.1 e cand he
  have certs : ∀ x ∈ t.pending, ∀ e leader val,
      x.envelope.payload = .fencedCommit e leader val → Certified c f t e leader val := by
    intro x hx e leader val he
    rcases pending x hx with old | fresh
    · exact certified_mono mono (h.leader_commit_has_quorum.1 x old e leader val he)
    · exact fresh.2 e leader val he
  exact ⟨nd, grants, cv, ⟨certs, commits⟩, fun x hx e leader val he => (certs x hx e leader val he).1⟩

theorem allocate_payload {M L P : Type} (actor : M) (n : Nat)
    (outs : List (Outgoing M L P)) (x : Transmission M L P)
    (hx : x ∈ allocate actor n outs) : ∃ out ∈ outs, x.envelope.payload = out.payload := by
  induction outs generalizing n with
  | nil => simp [allocate] at hx
  | cons out tail ih =>
    simp only [allocate, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨out, by simp, rfl⟩
    · obtain ⟨o, ho, he⟩ := ih (n+1) hx
      exact ⟨o, by simp [ho], he⟩

/-- Preservation for one atomic protocol reaction and its publication. -/
theorem reaction_preserved {c : Config N} {f : Nat} {s : LeaseState c Val}
    (h : LeaseInv c f s) {actor : Member c} {input d v outs result}
    (reaction : LeaseReact c f actor (s.nodes actor).durable (s.nodes actor).volatile input d v outs)
    (incoming : ∀ env, input = .message env → ∃ x ∈ s.pending, x.envelope = env)
    (publication : ∀ x ∈ result, x ∈ s.pending ∨ x ∈ allocate actor s.next outs) :
    LeaseInv c f ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩ := by
  let t : LeaseState c Val := ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩
  have finish
      (vm : ∀ e cand, (s.nodes actor).durable.votedFor e = some cand → d.votedFor e = some cand)
      (cm : ∀ e pair, (s.nodes actor).durable.committed e = some pair → d.committed e = some pair)
      (nd : ∀ e, ((v.collectedVotes e).map Subtype.val).Nodup)
      (cv : ∀ e voter, voter ∈ v.collectedVotes e → (t.nodes voter).durable.votedFor e = some actor)
      (cc : ∀ e leader val, d.committed e = some (leader,val) → Certified c f t e leader val)
      (og : ∀ x ∈ allocate actor s.next outs,
        (∀ e cand, x.envelope.payload = .voteGrant e cand → (t.nodes x.envelope.sender).durable.votedFor e = some cand) ∧
        (∀ e leader val, x.envelope.payload = .fencedCommit e leader val → Certified c f t e leader val)) :
      LeaseInv c f t := by
    have mono : DurableExtends s t := by
      constructor
      · intro m e cand he
        by_cases hm : m = actor
        · subst m; simpa [t] using vm e cand he
        · simpa [t, setNode, hm] using he
      · intro m e pair he
        by_cases hm : m = actor
        · subst m; simpa [t] using cm e pair he
        · simpa [t, setNode, hm] using he
    apply rebuild h mono
    · intro m e
      by_cases hm : m = actor
      · subst m; simpa [t] using nd e
      · simpa [t, setNode, hm] using h.votes_nodup m e
    · intro m e voter he
      by_cases hm : m = actor
      · subst m; apply cv e voter; simpa [t] using he
      · apply mono.1 _ _ _ (h.collected_votes_valid m e voter ?_)
        simpa [t, setNode, hm] using he
    · intro m e leader val he
      by_cases hm : m = actor
      · subst m; apply cc e leader val; simpa [t] using he
      · apply certified_mono mono (h.leader_commit_has_quorum.2 m e leader val ?_)
        simpa [t, setNode, hm] using he
    · intro x hx
      rcases publication x hx with old | fresh
      · exact Or.inl old
      · exact Or.inr (og x fresh)
  have mono_of
      (vm : ∀ e cand, (s.nodes actor).durable.votedFor e = some cand → d.votedFor e = some cand)
      (cm : ∀ e pair, (s.nodes actor).durable.committed e = some pair → d.committed e = some pair) :
      DurableExtends s t := by
    constructor
    · intro m e cand he
      by_cases hm : m = actor
      · subst m; simpa [t] using vm e cand he
      · simpa [t, setNode, hm] using he
    · intro m e pair he
      by_cases hm : m = actor
      · subst m; simpa [t] using cm e pair he
      · simpa [t, setNode, hm] using he
  cases reaction with
  | @castVote e candidate guard =>
    have vm : ∀ k cand, (s.nodes actor).durable.votedFor k = some cand →
        (if k = e then some candidate else (s.nodes actor).durable.votedFor k) = some cand := by
      intro k cand he
      by_cases hk : k = e
      · subst k; rw [guard] at he; cases he
      · simp [hk, he]
    have mono := mono_of vm (fun _ _ he => he)
    apply finish vm (fun _ _ he => he) (h.votes_nodup actor)
    · intro k voter hv; exact mono.1 _ _ _ (h.collected_votes_valid actor k voter hv)
    · intro k leader val he; exact certified_mono mono (h.leader_commit_has_quorum.2 actor k leader val he)
    · intro x hx
      simp only [allocate, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      constructor
      · intro k cand he
        cases he
        simp [t, setNode]
      · intro k leader val he; cases he
  | @acquireAndCommit e val followers quorum guard =>
    have cm : ∀ k pair, (s.nodes actor).durable.committed k = some pair →
        (if k = e then some (actor,val) else (s.nodes actor).durable.committed k) = some pair := by
      intro k pair he
      by_cases hk : k = e
      · subst k; rw [guard] at he; cases he
      · simp [hk, he]
    have mono := mono_of (fun _ _ he => he) cm
    have fresh : Certified c f t e actor val := by
      refine ⟨?_, (s.nodes actor).volatile.collectedVotes e, quorum, ?_⟩
      · simp [t, setNode]
      · intro voter hv; exact mono.1 _ _ _ (h.collected_votes_valid actor e voter hv)
    have cc : ∀ k leader value,
        (if k = e then some (actor,val) else (s.nodes actor).durable.committed k) = some (leader,value) →
        Certified c f t k leader value := by
      intro k leader value he
      by_cases hk : k = e
      · subst k; simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩; exact fresh
      · simp only [if_neg hk] at he
        exact certified_mono mono (h.leader_commit_has_quorum.2 actor k leader value he)
    apply finish (fun _ _ he => he) cm (h.votes_nodup actor)
    · intro k voter hv; exact mono.1 _ _ _ (h.collected_votes_valid actor k voter hv)
    · exact cc
    · intro x hx
      have payload : x.envelope.payload = .fencedCommit e actor val := by
        obtain ⟨out, ho, hp⟩ := allocate_payload actor s.next _ x hx
        obtain ⟨peer, _, rfl⟩ := List.mem_map.mp ho
        exact hp
      constructor
      · intro k cand he; rw [payload] at he; cases he
      · intro k leader value he
        rw [payload] at he
        cases he
        exact fresh
  | @voteGrant e candidate sender l guard =>
    subst candidate
    obtain ⟨x, hx, he⟩ := incoming ⟨sender,actor,l,.voteGrant e actor⟩ rfl
    have grant : (s.nodes sender).durable.votedFor e = some actor := by
      have valid := h.grant_in_flight_valid x hx e actor
      have hv := valid (by simp [he])
      simpa only [he] using hv
    have mono := mono_of (fun _ _ he => he) (fun _ _ he => he)
    apply finish (fun _ _ he => he) (fun _ _ he => he)
    · intro k
      by_cases hk : k = e
      · subst k
        simp only [if_pos rfl]
        by_cases hn : sender ∈ (s.nodes actor).volatile.collectedVotes e
        · simpa only [if_pos hn] using h.votes_nodup actor e
        · simp only [hn, ↓reduceIte, List.map_cons, List.nodup_cons]
          refine ⟨?_, h.votes_nodup actor e⟩
          intro hm
          obtain ⟨w, hw, eq⟩ := List.mem_map.mp hm
          have weq : w = sender := Subtype.ext eq
          exact hn (weq ▸ hw)
      · simpa [hk] using h.votes_nodup actor k
    · intro k voter hv
      by_cases hk : k = e
      · subst k; simp only [if_pos rfl] at hv
        by_cases hn : sender ∈ (s.nodes actor).volatile.collectedVotes e
        · simp only [if_pos hn] at hv
          exact mono.1 _ _ _ (h.collected_votes_valid actor e voter hv)
        · simp only [if_neg hn] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact mono.1 _ _ _ grant
          · exact mono.1 _ _ _ (h.collected_votes_valid actor e voter hv)
      · simp only [if_neg hk] at hv
        exact mono.1 _ _ _ (h.collected_votes_valid actor k voter hv)
    · intro k leader val he; exact certified_mono mono (h.leader_commit_has_quorum.2 actor k leader val he)
    · intro x hx; simp [allocate] at hx
  | @fencedCommit e leader val sender l authentic guard =>
    obtain ⟨x, hx, he⟩ := incoming ⟨sender,actor,l,.fencedCommit e leader val⟩ rfl
    have cert : Certified c f s e leader val := by
      apply h.leader_commit_has_quorum.1 x hx e leader val
      simp [he]
    have cm : ∀ k pair, (s.nodes actor).durable.committed k = some pair →
        (if k = e then some (leader,val) else (s.nodes actor).durable.committed k) = some pair := by
      intro k pair he
      by_cases hk : k = e
      · subst k; rw [guard] at he; cases he
      · simp [hk, he]
    have mono := mono_of (fun _ _ he => he) cm
    apply finish (fun _ _ he => he) cm (h.votes_nodup actor)
    · intro k voter hv; exact mono.1 _ _ _ (h.collected_votes_valid actor k voter hv)
    · intro k lead value he
      by_cases hk : k = e
      · subst k; simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩; exact certified_mono mono cert
      · simp only [if_neg hk] at he
        exact certified_mono mono (h.leader_commit_has_quorum.2 actor k lead value he)
    · intro x hx; simp [allocate] at hx

omit [DecidableEq N] in
/-- Faults can erase tallies and permute/copy/remove existing envelopes only. -/
theorem fault_preserved {c : Config N} {f : Nat} {s t : LeaseState c Val}
    (h : LeaseInv c f s)
    (votes : ∀ m, (t.nodes m).durable.votedFor = (s.nodes m).durable.votedFor)
    (commits : ∀ m, (t.nodes m).durable.committed = (s.nodes m).durable.committed)
    (tallies : ∀ m e, (t.nodes m).volatile.collectedVotes e = (s.nodes m).volatile.collectedVotes e ∨
      (t.nodes m).volatile.collectedVotes e = [])
    (pending : ∀ x ∈ t.pending, ∃ y ∈ s.pending, x.envelope = y.envelope) : LeaseInv c f t := by
  have mono : DurableExtends s t :=
    ⟨fun m e cand he => by simpa [votes m] using he,
     fun m e pair he => by simpa [commits m] using he⟩
  apply rebuild h mono
  · intro m e
    rcases tallies m e with same | empty
    · rw [same]; exact h.votes_nodup m e
    · simp [empty]
  · intro m e voter hv
    rcases tallies m e with same | empty
    · rw [same] at hv; exact mono.1 _ _ _ (h.collected_votes_valid m e voter hv)
    · simp [empty] at hv
  · intro m e leader val he
    rw [commits m] at he
    exact certified_mono mono (h.leader_commit_has_quorum.2 m e leader val he)
  · intro x hx
    obtain ⟨y, hy, he⟩ := pending x hx
    apply Or.inr
    constructor
    · intro e cand hp
      rw [he] at hp ⊢
      exact mono.1 _ _ _ (h.grant_in_flight_valid y hy e cand hp)
    · intro e leader val hp
      rw [he] at hp
      exact certified_mono mono (h.leader_commit_has_quorum.1 y hy e leader val hp)

theorem leaseInv_preserved (c : Config N) (f : Nat) (fp : FaultProfile)
    {s t : LeaseState c Val} {a : LeaseLabel c Val} (h : LeaseInv c f s)
    (step : Distributed.Step c (quorumLeaseProtocol (Val := Val) c f) fp s a t) : LeaseInv c f t := by
  cases step with
  | process running reaction publish =>
    apply reaction_preserved h reaction
    · intro env he; cases he
    · intro x hx
      have hm := publish.mem_iff.mp hx
      exact List.mem_append.mp hm
  | @deliver e rest d v outs result running take reaction publish =>
    apply reaction_preserved h reaction
    · intro env he
      cases he
      exact ⟨e, take.mem_iff.mpr (by simp), rfl⟩
    · intro x hx
      rcases List.mem_append.mp (publish.mem_iff.mp hx) with old | fresh
      · exact Or.inl (take.mem_iff.mpr (by simp [old]))
      · exact Or.inr fresh
  | @drop e rest allowed take =>
    apply fault_preserved (t := ⟨s.nodes, rest, s.next⟩) h (fun _ => rfl) (fun _ => rfl) (fun _ _ => Or.inl rfl)
    intro x hx
    exact ⟨x, take.mem_iff.mpr (by simp [hx]), rfl⟩
  | @duplicate e result allowed present copy =>
    apply fault_preserved (t := ⟨s.nodes, result, s.next+1⟩) h (fun _ => rfl) (fun _ => rfl) (fun _ _ => Or.inl rfl)
    intro x hx
    rcases List.mem_cons.mp (copy.mem_iff.mp hx) with rfl | old
    · exact ⟨_, present, rfl⟩
    · exact ⟨x, old, rfl⟩
  | @crash actor allowed running =>
    apply fault_preserved h
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m e; by_cases hm : m = actor
      · right; simp [setNode, hm, quorumLeaseProtocol]
      · left; simp [setNode, hm]
    · intro x hx; exact ⟨x, hx, rfl⟩
  | @recover actor allowed crashed =>
    apply fault_preserved h
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m e; by_cases hm : m = actor
      · right; simp [setNode, hm, quorumLeaseProtocol]
      · left; simp [setNode, hm]
    · intro x hx; exact ⟨x, hx, rfl⟩

theorem reachable_leaseInv (c : Config N) (f : Nat) (fp : FaultProfile)
    {s : LeaseState c Val} (hr : Foundation.Reachable (sys c f fp) s) : LeaseInv c f s := by
  apply Foundation.invariant (leaseInv_initial c f fp) ?_ s hr
  intro s a o t hi hs
  exact leaseInv_preserved c f fp hi hs.1

variable {c : Config N} {f e : Nat} {s t : LeaseState c Val}
variable {m₁ m₂ leader₁ leader₂ n₁ n₂ : Member c} {val₁ val₂ : Val}

def HasQuorumLease (c : Config N) (f : Nat) (s : LeaseState c Val)
    (e : Nat) (m : Member c) : Prop :=
  IsQuorum c f ((s.nodes m).volatile.collectedVotes e)

theorem quorum_candidates_unique
    {Q₁ Q₂ : List (Member c)} (hq₁ : IsQuorum c f Q₁) (hq₂ : IsQuorum c f Q₂)
    (hv₁ : ∀ voter ∈ Q₁, (s.nodes voter).durable.votedFor e = some m₁)
    (hv₂ : ∀ voter ∈ Q₂, (s.nodes voter).durable.votedFor e = some m₂) : m₁ = m₂ := by
  obtain ⟨v, h₁, h₂⟩ := quorum_voters_intersect c f Q₁ Q₂ hq₁ hq₂
  exact Option.some.inj ((hv₁ v h₁).symm.trans (hv₂ v h₂))

theorem lease_mutual_exclusion_of_inv (h : LeaseInv c f s)
    (h₁ : HasQuorumLease c f s e m₁) (h₂ : HasQuorumLease c f s e m₂) : m₁ = m₂ := by
  exact quorum_candidates_unique h₁ h₂
    (h.collected_votes_valid m₁ e) (h.collected_votes_valid m₂ e)

theorem quorum_lease_mutual_exclusion (c : Config N) (f : Nat) (fp : FaultProfile)
    {s : LeaseState c Val} {e : Nat} {m₁ m₂ : Member c}
    (hr : Foundation.Reachable (sys c f fp) s)
    (h₁ : HasQuorumLease c f s e m₁) (h₂ : HasQuorumLease c f s e m₂) : m₁ = m₂ := by
  exact lease_mutual_exclusion_of_inv (reachable_leaseInv c f fp hr) h₁ h₂

theorem certified_leader_unique
    (h₁ : Certified c f s e leader₁ val₁)
    (h₂ : Certified c f s e leader₂ val₂) : leader₁ = leader₂ := by
  obtain ⟨_, Q₁, hq₁, hv₁⟩ := h₁
  obtain ⟨_, Q₂, hq₂, hv₂⟩ := h₂
  exact quorum_candidates_unique hq₁ hq₂ hv₁ hv₂

theorem fenced_commit_safety_of_inv (h : LeaseInv c f s)
    (h₁ : (s.nodes n₁).durable.committed e = some (leader₁, val₁))
    (h₂ : (s.nodes n₂).durable.committed e = some (leader₂, val₂)) :
    leader₁ = leader₂ ∧ val₁ = val₂ := by
  have hc₁ := h.leader_commit_has_quorum.2 n₁ e leader₁ val₁ h₁
  have hc₂ := h.leader_commit_has_quorum.2 n₂ e leader₂ val₂ h₂
  have he := certified_leader_unique hc₁ hc₂
  subst leader₂
  exact ⟨rfl, (Prod.mk.inj (Option.some.inj (hc₁.1.symm.trans hc₂.1))).2⟩

theorem fenced_commit_leader_unique (c : Config N) (f : Nat) (fp : FaultProfile)
    {s : LeaseState c Val} {e : Nat} {n₁ n₂ leader₁ leader₂ : Member c}
    {val₁ val₂ : Val} (hr : Foundation.Reachable (sys c f fp) s)
    (h₁ : (s.nodes n₁).durable.committed e = some (leader₁, val₁))
    (h₂ : (s.nodes n₂).durable.committed e = some (leader₂, val₂)) : leader₁ = leader₂ :=
  (fenced_commit_safety_of_inv (reachable_leaseInv c f fp hr) h₁ h₂).1

theorem fenced_commit_safety (c : Config N) (f : Nat) (fp : FaultProfile)
    {s : LeaseState c Val} {e : Nat} {n₁ n₂ leader₁ leader₂ : Member c}
    {val₁ val₂ : Val} (hr : Foundation.Reachable (sys c f fp) s)
    (h₁ : (s.nodes n₁).durable.committed e = some (leader₁, val₁))
    (h₂ : (s.nodes n₂).durable.committed e = some (leader₂, val₂)) :
    leader₁ = leader₂ ∧ val₁ = val₂ :=
  fenced_commit_safety_of_inv (reachable_leaseInv c f fp hr) h₁ h₂

abbrev SeqLeaseState (c : Config N) (Val : Type) := Nat → Option (Member c × Val)

inductive SeqObs (c : Config N) (Val : Type) where
  | silent
  | committed (e : Nat) (leader : Member c) (val : Val)

def obsMap : LeaseLabel c Val → SeqObs c Val
  | .process actor (.local (.acquireAndCommit e val _)) _ => .committed e actor val
  | _ => .silent

inductive SeqLeaseStep (c : Config N) (Val : Type) :
    SeqLeaseState c Val → SeqObs c Val → SeqLeaseState c Val → Prop where
  | idle (b) : SeqLeaseStep c Val b .silent b
  | commit (b) (e) (leader) (val) (guard : b e = none) :
      SeqLeaseStep c Val b (.committed e leader val)
        (fun e' => if e' = e then some (leader,val) else b e')

def sequentialLeaseSpec (c : Config N) (Val : Type) :
    Foundation.TransitionSystem (SeqLeaseState c Val) (SeqObs c Val) (SeqObs c Val) where
  init b := b = fun _ => none
  step b a o b' := SeqLeaseStep c Val b a b' ∧ o = a

def LeaseSimRel (c : Config N) (f : Nat) (s : LeaseState c Val)
    (b : SeqLeaseState c Val) : Prop :=
  LeaseInv c f s ∧ (∀ e leader val,
    b e = some (leader,val) ↔ (s.nodes leader).durable.committed e = some (leader,val))

theorem acquire_epoch_empty (h : LeaseSimRel c f s b)
    (hq : IsQuorum c f ((s.nodes actor).volatile.collectedVotes E))
    (hg : (s.nodes actor).durable.committed E = none) : b E = none := by
  cases hb : b E with
  | none => rfl
  | some pair =>
    obtain ⟨leader,val⟩ := pair
    have hc := (h.2 E leader val).mp hb
    obtain ⟨hl, Q, hQ, hv⟩ := h.1.leader_commit_has_quorum.2 leader E leader val hc
    have he : actor = leader := quorum_candidates_unique hq hQ
      (h.1.collected_votes_valid actor E) hv
    subst leader
    rw [hg] at hl
    contradiction

theorem self_records_frame (s : LeaseState c Val) (actor : Member c)
    (d : LeaseDurable c Val) (v : LeaseVolatile c Val) (status : Status)
    (hc : d.committed = (s.nodes actor).durable.committed) :
    ∀ e leader val,
      (setNode s.nodes actor ⟨d,v,status⟩ leader).durable.committed e = some (leader,val) ↔
      (s.nodes leader).durable.committed e = some (leader,val) := by
  intro e leader val
  by_cases he : leader = actor
  · subst leader; simp [setNode, hc]
  · simp [setNode, he]

theorem self_records_follower (s : LeaseState c Val) (actor leader : Member c)
    (E : Nat) (value : Val) (v : LeaseVolatile c Val)
    (hg : (s.nodes actor).durable.committed E = none) (hne : actor ≠ leader) :
    ∀ e m val,
      (setNode s.nodes actor
        ⟨{(s.nodes actor).durable with committed := fun k => if k = E then some (leader,value) else (s.nodes actor).durable.committed k},v,.running⟩
        m).durable.committed e = some (m,val) ↔
      (s.nodes m).durable.committed e = some (m,val) := by
  intro e m val
  by_cases hm : m = actor
  · subst m
    by_cases he : e = E
    · subst e; simp [setNode, hg, Ne.symm hne]
    · simp [setNode, he]
  · simp [setNode, hm]

theorem sim_commit_update (h : LeaseSimRel c f s b) (actor : Member c) (E : Nat)
    (value : Val) (v : LeaseVolatile c Val) (hb : b E = none) :
    ∀ e m val,
      (if e = E then some (actor,value) else b e) = some (m,val) ↔
      (setNode s.nodes actor
        ⟨{(s.nodes actor).durable with committed := fun k => if k = E then some (actor,value) else (s.nodes actor).durable.committed k},v,.running⟩
        m).durable.committed e = some (m,val) := by
  intro e m val
  by_cases he : e = E
  · subst e
    by_cases hm : m = actor
    · subst m; simp [setNode]
    · have hn : ¬ (s.nodes m).durable.committed E = some (m,val) := by
        intro hc; have := (h.2 E m val).mpr hc; rw [hb] at this; contradiction
      simp [setNode, hm, Ne.symm hm, hn]
  · by_cases hm : m = actor
    · subst m; simpa [setNode, he] using h.2 e actor val
    · simpa [setNode, he, hm] using h.2 e m val

theorem quorum_lease_refines_spec (c : Config N) (f : Nat) (fp : FaultProfile) :
    Foundation.ForwardSimulation
      (Distributed.system c (quorumLeaseProtocol (Val := Val) c f) fp)
      (sequentialLeaseSpec c Val) (LeaseSimRel c f) obsMap := by
  constructor
  · intro s hi
    refine ⟨fun _ => none, rfl, leaseInv_initial c f fp s hi, ?_⟩
    intro e leader val
    have hc := (hi.2.2 leader).2.2.1
    simp [hc]
  · intro s a o t b hr hs
    obtain ⟨step, he⟩ := hs
    subst o
    have ht := leaseInv_preserved c f fp hr.1 step
    have idle : ∀ (eqobs : obsMap a = SeqObs.silent),
        (∀ e leader val, (t.nodes leader).durable.committed e = some (leader,val) ↔
          (s.nodes leader).durable.committed e = some (leader,val)) →
        ∃ ba b', (sequentialLeaseSpec c Val).step b ba (obsMap a) b' ∧ LeaseSimRel c f t b' := by
      intro eqobs hframe
      refine ⟨.silent, b, ⟨SeqLeaseStep.idle b, eqobs⟩, ht, ?_⟩
      intro e leader val
      exact (hr.2 e leader val).trans (hframe e leader val).symm
    cases step with
    | @process actor stimulus d v outs result running reaction publish =>
      cases reaction with
      | castVote guard =>
        apply idle rfl
        exact self_records_frame s actor _ _ _ rfl
      | @acquireAndCommit E value followers quorum guard =>
        have hb := acquire_epoch_empty hr quorum guard
        refine ⟨.committed E actor value,
          fun k => if k = E then some (actor,value) else b k,
          ⟨SeqLeaseStep.commit b E actor value hb, rfl⟩, ht, ?_⟩
        exact sim_commit_update hr actor E value _ hb
    | @deliver msg rest d v outs result running take reaction publish =>
      rcases msg with ⟨tid, sender, actor, l, payload⟩
      cases reaction with
      | voteGrant guard =>
        apply idle rfl
        exact self_records_frame s _ _ _ _ rfl
      | fencedCommit authentic guard =>
        rename_i E leader value
        have hc := hr.1.commit_msg_authentic ⟨tid,⟨sender,actor,l,.fencedCommit E leader value⟩⟩
          (take.mem_iff.mpr (by simp)) E leader value rfl
        have hne : actor ≠ leader := by
          intro he; subst actor
          rw [guard] at hc
          contradiction
        apply idle rfl
        exact self_records_follower s actor leader E value (s.nodes actor).volatile guard hne
    | drop allowed take =>
      apply idle rfl
      intro e leader val; rfl
    | duplicate allowed present copy =>
      apply idle rfl
      intro e leader val; rfl
    | crash allowed running =>
      apply idle rfl
      exact self_records_frame s _ _ _ _ rfl
    | recover allowed crashed =>
      apply idle rfl
      exact self_records_frame s _ _ _ _ rfl

/-- Agreement transferred from the sequential write-once state through refinement. -/
theorem quorum_lease_safety_via_refinement (c : Config N) (f : Nat) (fp : FaultProfile)
    {s : LeaseState c Val} (hr : Foundation.Reachable (sys c f fp) s) :
    ∀ e (n₁ n₂ leader₁ leader₂ : Member c) (val₁ val₂ : Val),
      (s.nodes n₁).durable.committed e = some (leader₁,val₁) →
      (s.nodes n₂).durable.committed e = some (leader₂,val₂) →
      leader₁ = leader₂ ∧ val₁ = val₂ := by
  apply (quorum_lease_refines_spec c f fp).transfer_invariant
    (I := fun b => ∀ e leader₁ leader₂ val₁ val₂,
      b e = some (leader₁,val₁) → b e = some (leader₂,val₂) →
      leader₁ = leader₂ ∧ val₁ = val₂)
    (J := fun s => ∀ e (n₁ n₂ leader₁ leader₂ : Member c) (val₁ val₂ : Val),
      (s.nodes n₁).durable.committed e = some (leader₁,val₁) →
      (s.nodes n₂).durable.committed e = some (leader₂,val₂) →
      leader₁ = leader₂ ∧ val₁ = val₂)
    (c := s)
  · intro b _ e leader₁ leader₂ val₁ val₂ h₁ h₂
    exact Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))
  · intro s b rel safe e n₁ n₂ leader₁ leader₂ val₁ val₂ h₁ h₂
    have hc₁ := (rel.1.leader_commit_has_quorum.2 n₁ e leader₁ val₁ h₁).1
    have hc₂ := (rel.1.leader_commit_has_quorum.2 n₂ e leader₂ val₂ h₂).1
    exact safe e leader₁ leader₂ val₁ val₂
      ((rel.2 e leader₁ val₁).mpr hc₁) ((rel.2 e leader₂ val₂).mpr hc₂)
  · exact hr

end Harmonia.VerifiedProtocols.QuorumLease
