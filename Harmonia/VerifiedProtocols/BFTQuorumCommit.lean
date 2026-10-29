import Harmonia.Core.Refinement
import Harmonia.Distributed
import Harmonia.Theorems.Quorum

namespace Harmonia.VerifiedProtocols.BFTQuorumCommit
open Distributed
variable {N Val : Type} [DecidableEq N] [DecidableEq Val]

structure BFTDurable (c : Config N) (Val : Type) where
  /-- Honest node's write-once vote per view `v` (`some (proposer, val)`). -/
  votedFor : Nat → Option (Member c × Val)
  /-- Node's write-once committed value per view `v` (`some (proposer, val)`). -/
  committed : Nat → Option (Member c × Val)

structure BFTVolatile (c : Config N) (Val : Type) where
  /-- Proposer's collected duplicate-free voters for `(view, val)`. Wiped on crash. -/
  tally : Nat → Val → List (Member c)

inductive BFTMsg (c : Config N) (Val : Type) where
  | vote (view : Nat) (proposer : Member c) (val : Val)
  | commitQC (view : Nat) (proposer : Member c) (val : Val)
  deriving DecidableEq

inductive BFTCmd (c : Config N) (Val : Type) where
  | castHonestVote (view : Nat) (proposer : Member c) (val : Val)
  | byzantineEquivocate (view : Nat) (proposer : Member c) (val : Val)
  | formQCAndCommit (view : Nat) (val : Val) (followers : List (Member c))
  deriving DecidableEq

def IsBFTQuorum (c : Config N) (f : Nat) (voters : List (Member c)) : Prop :=
  (voters.map Subtype.val).Nodup ∧ 3 * f + 1 ≤ c.members.length ∧
    c.members.length ≤ (voters.map Subtype.val).length + f

def FaultyBounded (c : Config N) (f : Nat) (faulty : List (Member c)) : Prop :=
  (faulty.map Subtype.val).length ≤ f

inductive BFTReact (c : Config N) (f : Nat) (faulty : List (Member c)) :
    Member c → BFTDurable c Val → BFTVolatile c Val →
    Input (Member c) Nat (BFTMsg c Val) (BFTCmd c Val) Empty →
    BFTDurable c Val → BFTVolatile c Val → List (Outgoing (Member c) Nat (BFTMsg c Val)) → Prop where
  | castHonestVote {actor d v view proposer val}
      (guard : d.votedFor view = none) :
      BFTReact c f faulty actor d v (.scheduled (.local (.castHonestVote view proposer val)))
        { d with votedFor := fun k => if k = view then some (proposer, val) else d.votedFor k }
        v [⟨proposer, view, .vote view proposer val⟩]
  | byzantineEquivocate {actor d v view proposer val}
      (isFaulty : actor ∈ faulty) :
      BFTReact c f faulty actor d v (.scheduled (.local (.byzantineEquivocate view proposer val)))
        d v [⟨proposer, view, .vote view proposer val⟩]
  | formQCAndCommit {actor d v view val followers}
      (quorum : IsBFTQuorum c f (v.tally view val))
      (guard : d.committed view = none) :
      BFTReact c f faulty actor d v (.scheduled (.local (.formQCAndCommit view val followers)))
        { d with committed := fun k => if k = view then some (actor, val) else d.committed k }
        v (followers.map fun peer => ⟨peer, view, .commitQC view actor val⟩)
  | recvVote {actor d v view proposer val sender l}
      (guard : proposer = actor) :
      BFTReact c f faulty actor d v (.message ⟨sender, actor, l, .vote view proposer val⟩) d
        ⟨fun k val' => if k = view ∧ val' = val then
          (if sender ∈ v.tally view val then v.tally view val else sender :: v.tally view val)
          else v.tally k val'⟩ []
  | recvCommitQC {actor d v view proposer val sender l}
      (authentic : sender = proposer) (guard : d.committed view = none) :
      BFTReact c f faulty actor d v (.message ⟨sender, actor, l, .commitQC view proposer val⟩)
        { d with committed := fun k => if k = view then some (proposer, val) else d.committed k } v []

def bftCommitProtocol (c : Config N) (f : Nat) (faulty : List (Member c)) :
    Protocol (Member c) (BFTDurable c Val) (BFTVolatile c Val) Nat (BFTMsg c Val) (BFTCmd c Val) Empty where
  initial _ d v := d.votedFor = (fun _ => none) ∧ d.committed = (fun _ => none) ∧
    v.tally = (fun _ _ => [])
  react := BFTReact c f faulty
  crashReset _ _ := ⟨fun _ _ => []⟩
  recover _ := ⟨fun _ _ => []⟩

abbrev BFTState (c : Config N) (Val : Type) :=
  State (Member c) (BFTDurable c Val) (BFTVolatile c Val) Nat (BFTMsg c Val)
abbrev BFTLabel (c : Config N) (Val : Type) :=
  Label (Member c) Nat (BFTMsg c Val) (BFTCmd c Val) Empty

def sys (c : Config N) (f : Nat) (faulty : List (Member c)) (fp : FaultProfile) :=
  Distributed.system c (bftCommitProtocol (Val := Val) c f faulty) fp

/-- A durable, persistent certificate; volatile tallies need not survive a crash. -/
def BFTCertified (c : Config N) (f : Nat) (faulty : List (Member c)) (s : BFTState c Val)
    (e : Nat) (leader : Member c) (val : Val) : Prop :=
  (s.nodes leader).durable.committed e = some (leader, val) ∧
  ∃ Q, IsBFTQuorum c f Q ∧ ∀ voter ∈ Q, voter ∉ faulty → (s.nodes voter).durable.votedFor e = some (leader, val)

structure BFTCommitInv (c : Config N) (f : Nat) (faulty : List (Member c))
    (s : BFTState c Val) : Prop where
  tally_nodup : ∀ m view val, (((s.nodes m).volatile.tally view val).map Subtype.val).Nodup
  vote_in_flight_honest : ∀ t ∈ s.pending, ∀ view proposer val,
    t.envelope.payload = .vote view proposer val → t.envelope.sender ∉ faulty →
      (s.nodes t.envelope.sender).durable.votedFor view = some (proposer, val)
  tally_honest_valid : ∀ m view val voter,
    voter ∈ (s.nodes m).volatile.tally view val → voter ∉ faulty →
      (s.nodes voter).durable.votedFor view = some (m, val)
  qc_has_quorum :
    (∀ t ∈ s.pending, ∀ view proposer val,
      t.envelope.payload = .commitQC view proposer val → BFTCertified c f faulty s view proposer val) ∧
    (∀ n view proposer val,
      (s.nodes n).durable.committed view = some (proposer, val) → BFTCertified c f faulty s view proposer val)
  qc_msg_authentic : ∀ t ∈ s.pending, ∀ view proposer val,
    t.envelope.payload = .commitQC view proposer val →
      (s.nodes proposer).durable.committed view = some (proposer, val)

omit [DecidableEq N] in
theorem mapped_members (c : Config N) (Q : List (Member c)) :
    ∀ x ∈ Q.map Subtype.val, x ∈ c.members := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact v.property

theorem bft_quorum_honest_voter (c : Config N) (f : Nat) (faulty : List (Member c))
    (Q₁ Q₂ : List (Member c))
    (hq₁ : IsBFTQuorum c f Q₁) (hq₂ : IsBFTQuorum c f Q₂)
    (hf : FaultyBounded c f faulty) :
    ∃ v : Member c, v ∈ Q₁ ∧ v ∈ Q₂ ∧ v ∉ faulty := by
  obtain ⟨x, hxInter, hxNotF⟩ := Harmonia.Quorum.bft_honest_exists_at_least
    (Q₁.map Subtype.val) (Q₂.map Subtype.val) c.members (faulty.map Subtype.val) f
    hq₁.1 hq₂.1 (mapped_members c Q₁) (mapped_members c Q₂)
    hq₁.2.1 hq₁.2.2 hq₂.2.2 hf
  have hm := List.mem_filter.mp hxInter
  obtain ⟨v, hv₁, heq₁⟩ := List.mem_map.mp hm.1
  have hx₂ : x ∈ Q₂.map Subtype.val := by simpa using hm.2
  obtain ⟨w, hv₂, heq₂⟩ := List.mem_map.mp hx₂
  have hwv : w = v := Subtype.ext (heq₂.trans heq₁.symm)
  refine ⟨v, hv₁, hwv ▸ hv₂, ?_⟩
  intro hvf
  exact hxNotF (List.mem_map.mpr ⟨v, hvf, heq₁⟩)

/-- Write-once durable facts survive every legal local update. -/
def DurableExtends (s t : BFTState c Val) : Prop :=
  (∀ m e cand, (s.nodes m).durable.votedFor e = some cand →
    (t.nodes m).durable.votedFor e = some cand) ∧
  (∀ m e pair, (s.nodes m).durable.committed e = some pair →
    (t.nodes m).durable.committed e = some pair)

omit [DecidableEq Val] in
theorem certified_mono {s t : BFTState c Val} (h : DurableExtends s t)
    (hc : BFTCertified c f faulty s e leader val) : BFTCertified c f faulty t e leader val := by
  obtain ⟨hl, Q, hq, hv⟩ := hc
  exact ⟨h.2 _ _ _ hl, Q, hq, fun voter hm honest => h.1 _ _ _ (hv voter hm honest)⟩

theorem bftCommitInv_initial (c : Config N) (f : Nat) (faulty : List (Member c)) (fp : FaultProfile)
    (s : BFTState c Val) (h : (sys c f faulty fp).init s) : BFTCommitInv c f faulty s := by
  obtain ⟨hp, _, hn⟩ := h
  have hv : ∀ m, (s.nodes m).durable.votedFor = fun _ => none := fun m => (hn m).2.1
  have hc : ∀ m, (s.nodes m).durable.committed = fun _ => none := fun m => (hn m).2.2.1
  have ht : ∀ m, (s.nodes m).volatile.tally = fun _ _ => [] := fun m => (hn m).2.2.2
  constructor
  · intro m e; simp [ht]
  · simp [hp]
  · intro m e val voter hm; simp [ht] at hm
  · constructor
    · simp [hp]
    · intro n e leader val he; simp [hc] at he
  · simp [hp]

omit [DecidableEq Val] in
/-- Reassemble the five clauses after changing nodes and publishing messages. -/
theorem rebuild {s t : BFTState c Val} (h : BFTCommitInv c f faulty s)
    (mono : DurableExtends s t)
    (nd : ∀ m e val, (((t.nodes m).volatile.tally e val).map Subtype.val).Nodup)
    (cv : ∀ m e val voter, voter ∈ (t.nodes m).volatile.tally e val → voter ∉ faulty →
      (t.nodes voter).durable.votedFor e = some (m, val))
    (commits : ∀ m e leader val, (t.nodes m).durable.committed e = some (leader,val) →
      BFTCertified c f faulty t e leader val)
    (pending : ∀ x ∈ t.pending, x ∈ s.pending ∨
      ((∀ e cand val, x.envelope.payload = .vote e cand val → x.envelope.sender ∉ faulty →
        (t.nodes x.envelope.sender).durable.votedFor e = some (cand, val)) ∧
       (∀ e leader val, x.envelope.payload = .commitQC e leader val →
        BFTCertified c f faulty t e leader val))) : BFTCommitInv c f faulty t := by
  have grants : ∀ x ∈ t.pending, ∀ e cand val, x.envelope.payload = .vote e cand val → x.envelope.sender ∉ faulty →
      (t.nodes x.envelope.sender).durable.votedFor e = some (cand, val) := by
    intro x hx e cand val he honest
    rcases pending x hx with old | fresh
    · exact mono.1 _ _ _ (h.vote_in_flight_honest x old e cand val he honest)
    · exact fresh.1 e cand val he honest
  have certs : ∀ x ∈ t.pending, ∀ e leader val,
      x.envelope.payload = .commitQC e leader val → BFTCertified c f faulty t e leader val := by
    intro x hx e leader val he
    rcases pending x hx with old | fresh
    · exact certified_mono mono (h.qc_has_quorum.1 x old e leader val he)
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
theorem reaction_preserved {c : Config N} {f : Nat} {faulty : List (Member c)} {s : BFTState c Val}
    (h : BFTCommitInv c f faulty s) {actor : Member c} {input d v outs result}
    (reaction : BFTReact c f faulty actor (s.nodes actor).durable (s.nodes actor).volatile input d v outs)
    (incoming : ∀ env, input = .message env → ∃ x ∈ s.pending, x.envelope = env)
    (publication : ∀ x ∈ result, x ∈ s.pending ∨ x ∈ allocate actor s.next outs) :
    BFTCommitInv c f faulty ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩ := by
  let t : BFTState c Val := ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩
  have finish
      (vm : ∀ e cand, (s.nodes actor).durable.votedFor e = some cand → d.votedFor e = some cand)
      (cm : ∀ e pair, (s.nodes actor).durable.committed e = some pair → d.committed e = some pair)
      (nd : ∀ e val, ((v.tally e val).map Subtype.val).Nodup)
      (cv : ∀ e val voter, voter ∈ v.tally e val → voter ∉ faulty → (t.nodes voter).durable.votedFor e = some (actor, val))
      (cc : ∀ e leader val, d.committed e = some (leader,val) → BFTCertified c f faulty t e leader val)
      (og : ∀ x ∈ allocate actor s.next outs,
        (∀ e cand val, x.envelope.payload = .vote e cand val → x.envelope.sender ∉ faulty → (t.nodes x.envelope.sender).durable.votedFor e = some (cand, val)) ∧
        (∀ e leader val, x.envelope.payload = .commitQC e leader val → BFTCertified c f faulty t e leader val)) :
      BFTCommitInv c f faulty t := by
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
    · intro m e val
      by_cases hm : m = actor
      · subst m; simpa [t] using nd e val
      · simpa [t, setNode, hm] using h.tally_nodup m e val
    · intro m e val voter he honest
      by_cases hm : m = actor
      · subst m; apply cv e val voter (by simpa [t] using he) honest
      · apply mono.1 _ _ _ (h.tally_honest_valid m e val voter ?_ honest)
        simpa [t, setNode, hm] using he
    · intro m e leader val he
      by_cases hm : m = actor
      · subst m; apply cc e leader val; simpa [t] using he
      · apply certified_mono mono (h.qc_has_quorum.2 m e leader val ?_)
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
  | @castHonestVote e candidate value guard =>
    have vm : ∀ k cand, (s.nodes actor).durable.votedFor k = some cand →
        (if k = e then some (candidate,value) else (s.nodes actor).durable.votedFor k) = some cand := by
      intro k cand he
      by_cases hk : k = e
      · subst k; rw [guard] at he; cases he
      · simp [hk, he]
    have mono := mono_of vm (fun _ _ he => he)
    apply finish vm (fun _ _ he => he) (h.tally_nodup actor)
    · intro k value voter hv honest; exact mono.1 _ _ _ (h.tally_honest_valid actor k value voter hv honest)
    · intro k leader val he; exact certified_mono mono (h.qc_has_quorum.2 actor k leader val he)
    · intro x hx
      simp only [allocate, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      constructor
      · intro k cand value he honest
        cases he
        simp [t, setNode]
      · intro k leader val he; cases he
  | @byzantineEquivocate e proposer value isFaulty =>
    have mono := mono_of (fun _ _ he => he) (fun _ _ he => he)
    apply finish (fun _ _ he => he) (fun _ _ he => he) (h.tally_nodup actor)
    · intro k val voter hv honest
      exact mono.1 _ _ _ (h.tally_honest_valid actor k val voter hv honest)
    · intro k leader val he; exact certified_mono mono (h.qc_has_quorum.2 actor k leader val he)
    · intro x hx
      simp only [allocate, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      constructor
      · intro _ _ _ _ honest; exact False.elim (honest isFaulty)
      · intro _ _ _ he; cases he
  | @formQCAndCommit e val followers quorum guard =>
    have cm : ∀ k pair, (s.nodes actor).durable.committed k = some pair →
        (if k = e then some (actor,val) else (s.nodes actor).durable.committed k) = some pair := by
      intro k pair he
      by_cases hk : k = e
      · subst k; rw [guard] at he; cases he
      · simp [hk, he]
    have mono := mono_of (fun _ _ he => he) cm
    have fresh : BFTCertified c f faulty t e actor val := by
      refine ⟨?_, (s.nodes actor).volatile.tally e val, quorum, ?_⟩
      · simp [t, setNode]
      · intro voter hv honest; exact mono.1 _ _ _ (h.tally_honest_valid actor e val voter hv honest)
    have cc : ∀ k leader value,
        (if k = e then some (actor,val) else (s.nodes actor).durable.committed k) = some (leader,value) →
        BFTCertified c f faulty t k leader value := by
      intro k leader value he
      by_cases hk : k = e
      · subst k; simp only at he
        rcases he with ⟨rfl, rfl⟩; exact fresh
      · simp only [ite_eq_right hk] at he
        exact certified_mono mono (h.qc_has_quorum.2 actor k leader value he)
    apply finish (fun _ _ he => he) cm (h.tally_nodup actor)
    · intro k value voter hv honest; exact mono.1 _ _ _ (h.tally_honest_valid actor k value voter hv honest)
    · exact cc
    · intro x hx
      have payload : x.envelope.payload = .commitQC e actor val := by
        obtain ⟨out, ho, hp⟩ := allocate_payload actor s.next _ x hx
        obtain ⟨peer, _, rfl⟩ := List.mem_map.mp ho
        exact hp
      constructor
      · intro k cand value he _; rw [payload] at he; cases he
      · intro k leader value he
        rw [payload] at he
        cases he
        exact fresh
  | @recvVote e candidate value sender l guard =>
    subst candidate
    obtain ⟨x, hx, he⟩ := incoming ⟨sender,actor,l,.vote e actor value⟩ rfl
    have grant (honest : sender ∉ faulty) : (s.nodes sender).durable.votedFor e = some (actor,value) := by
      have hv := h.vote_in_flight_honest x hx e actor value (by simp [he]) (by simpa [he] using honest)
      simpa only [he] using hv
    have mono := mono_of (fun _ _ he => he) (fun _ _ he => he)
    apply finish (fun _ _ he => he) (fun _ _ he => he)
    · intro k val
      by_cases hk : k = e ∧ val = value
      · obtain ⟨hk,hval⟩ := hk
        subst k; subst val
        simp only [and_self, ↓reduceIte]
        by_cases hn : sender ∈ (s.nodes actor).volatile.tally e value
        · simpa [hn] using h.tally_nodup actor e value
        · simp only [hn, ↓reduceIte, List.map_cons, List.nodup_cons]
          refine ⟨?_, h.tally_nodup actor e value⟩
          intro hm
          obtain ⟨w, hw, eq⟩ := List.mem_map.mp hm
          have weq : w = sender := Subtype.ext eq
          exact hn (weq ▸ hw)
      · simpa [hk] using h.tally_nodup actor k val
    · intro k val voter hv honest
      by_cases hk : k = e ∧ val = value
      · obtain ⟨hk,hval⟩ := hk
        subst k; subst val
        simp only [and_self, ↓reduceIte] at hv
        by_cases hn : sender ∈ (s.nodes actor).volatile.tally e value
        · simp only [ite_eq_left hn] at hv
          exact mono.1 _ _ _ (h.tally_honest_valid actor e value voter hv honest)
        · simp only [ite_eq_right hn] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact mono.1 _ _ _ (grant honest)
          · exact mono.1 _ _ _ (h.tally_honest_valid actor e value voter hv honest)
      · simp only [ite_eq_right hk] at hv
        exact mono.1 _ _ _ (h.tally_honest_valid actor k val voter hv honest)
    · intro k leader val he; exact certified_mono mono (h.qc_has_quorum.2 actor k leader val he)
    · intro x hx; simp [allocate] at hx
  | @recvCommitQC e leader val sender l authentic guard =>
    obtain ⟨x, hx, he⟩ := incoming ⟨sender,actor,l,.commitQC e leader val⟩ rfl
    have cert : BFTCertified c f faulty s e leader val := by
      apply h.qc_has_quorum.1 x hx e leader val
      simp [he]
    have cm : ∀ k pair, (s.nodes actor).durable.committed k = some pair →
        (if k = e then some (leader,val) else (s.nodes actor).durable.committed k) = some pair := by
      intro k pair he
      by_cases hk : k = e
      · subst k; rw [guard] at he; cases he
      · simp [hk, he]
    have mono := mono_of (fun _ _ he => he) cm
    apply finish (fun _ _ he => he) cm (h.tally_nodup actor)
    · intro k value voter hv honest; exact mono.1 _ _ _ (h.tally_honest_valid actor k value voter hv honest)
    · intro k lead value he
      by_cases hk : k = e
      · subst k; simp only at he
        rcases he with ⟨rfl, rfl⟩; exact certified_mono mono cert
      · simp only [ite_eq_right hk] at he
        exact certified_mono mono (h.qc_has_quorum.2 actor k lead value he)
    · intro x hx; simp [allocate] at hx

omit [DecidableEq N] [DecidableEq Val] in
/-- Faults can erase tallies and permute/copy/remove existing envelopes only. -/
theorem fault_preserved {c : Config N} {f : Nat} {faulty : List (Member c)} {s t : BFTState c Val}
    (h : BFTCommitInv c f faulty s)
    (votes : ∀ m, (t.nodes m).durable.votedFor = (s.nodes m).durable.votedFor)
    (commits : ∀ m, (t.nodes m).durable.committed = (s.nodes m).durable.committed)
    (tallies : ∀ m e val, (t.nodes m).volatile.tally e val = (s.nodes m).volatile.tally e val ∨
      (t.nodes m).volatile.tally e val = [])
    (pending : ∀ x ∈ t.pending, ∃ y ∈ s.pending, x.envelope = y.envelope) : BFTCommitInv c f faulty t := by
  have mono : DurableExtends s t :=
    ⟨fun m e cand he => by simpa [votes m] using he,
     fun m e pair he => by simpa [commits m] using he⟩
  apply rebuild h mono
  · intro m e val
    rcases tallies m e val with same | empty
    · rw [same]; exact h.tally_nodup m e val
    · simp [empty]
  · intro m e val voter hv honest
    rcases tallies m e val with same | empty
    · rw [same] at hv; exact mono.1 _ _ _ (h.tally_honest_valid m e val voter hv honest)
    · simp [empty] at hv
  · intro m e leader val he
    rw [commits m] at he
    exact certified_mono mono (h.qc_has_quorum.2 m e leader val he)
  · intro x hx
    obtain ⟨y, hy, he⟩ := pending x hx
    apply Or.inr
    constructor
    · intro e cand val hp honest
      rw [he] at hp ⊢
      exact mono.1 _ _ _ (h.vote_in_flight_honest y hy e cand val hp (by simpa [he] using honest))
    · intro e leader val hp
      rw [he] at hp
      exact certified_mono mono (h.qc_has_quorum.1 y hy e leader val hp)

theorem bftCommitInv_preserved (c : Config N) (f : Nat) (faulty : List (Member c)) (fp : FaultProfile)
    {s t : BFTState c Val} {a : BFTLabel c Val} (h : BFTCommitInv c f faulty s)
    (step : Distributed.Step c (bftCommitProtocol (Val := Val) c f faulty) fp s a t) : BFTCommitInv c f faulty t := by
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
    apply fault_preserved (t := ⟨s.nodes, rest, s.next⟩) h (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => Or.inl rfl)
    intro x hx
    exact ⟨x, take.mem_iff.mpr (by simp [hx]), rfl⟩
  | @duplicate e result allowed present copy =>
    apply fault_preserved (t := ⟨s.nodes, result, s.next+1⟩) h (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => Or.inl rfl)
    intro x hx
    rcases List.mem_cons.mp (copy.mem_iff.mp hx) with rfl | old
    · exact ⟨_, present, rfl⟩
    · exact ⟨x, old, rfl⟩
  | @crash actor allowed running =>
    apply fault_preserved h
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m e val; by_cases hm : m = actor
      · right; simp [setNode, hm, bftCommitProtocol]
      · left; simp [setNode, hm]
    · intro x hx; exact ⟨x, hx, rfl⟩
  | @recover actor allowed crashed =>
    apply fault_preserved h
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m e val; by_cases hm : m = actor
      · right; simp [setNode, hm, bftCommitProtocol]
      · left; simp [setNode, hm]
    · intro x hx; exact ⟨x, hx, rfl⟩

theorem reachable_bftCommitInv (c : Config N) (f : Nat) (faulty : List (Member c)) (fp : FaultProfile)
    {s : BFTState c Val} (hr : Foundation.Reachable (sys c f faulty fp) s) : BFTCommitInv c f faulty s := by
  apply Foundation.invariant (bftCommitInv_initial c f faulty fp) ?_ s hr
  intro s a o t hi hs
  exact bftCommitInv_preserved c f faulty fp hi hs.1

variable {c : Config N} {f e : Nat} {faulty : List (Member c)} {s t : BFTState c Val}
variable {m₁ m₂ leader₁ leader₂ n₁ n₂ : Member c} {val₁ val₂ : Val}

omit [DecidableEq Val] in
theorem bft_quorum_candidates_unique
    (hf : FaultyBounded c f faulty)
    {Q₁ Q₂ : List (Member c)} (hq₁ : IsBFTQuorum c f Q₁) (hq₂ : IsBFTQuorum c f Q₂)
    (hv₁ : ∀ voter ∈ Q₁, voter ∉ faulty → (s.nodes voter).durable.votedFor e = some (leader₁,val₁))
    (hv₂ : ∀ voter ∈ Q₂, voter ∉ faulty → (s.nodes voter).durable.votedFor e = some (leader₂,val₂)) :
    leader₁ = leader₂ ∧ val₁ = val₂ := by
  obtain ⟨v,h₁,h₂,honest⟩ := bft_quorum_honest_voter c f faulty Q₁ Q₂ hq₁ hq₂ hf
  exact Prod.mk.inj (Option.some.inj ((hv₁ v h₁ honest).symm.trans (hv₂ v h₂ honest)))

omit [DecidableEq Val] in
theorem bft_qc_unique (hf : FaultyBounded c f faulty)
    (h₁ : BFTCertified c f faulty s e leader₁ val₁)
    (h₂ : BFTCertified c f faulty s e leader₂ val₂) : leader₁ = leader₂ ∧ val₁ = val₂ := by
  obtain ⟨_,Q₁,hq₁,hv₁⟩ := h₁
  obtain ⟨_,Q₂,hq₂,hv₂⟩ := h₂
  exact bft_quorum_candidates_unique hf hq₁ hq₂ hv₁ hv₂

theorem bft_commit_safety (c : Config N) (f : Nat) (faulty : List (Member c))
    (hf : FaultyBounded c f faulty) (fp : FaultProfile)
    {s : BFTState c Val} {e : Nat} {n₁ n₂ leader₁ leader₂ : Member c} {val₁ val₂ : Val}
    (hr : Foundation.Reachable (sys c f faulty fp) s)
    (h₁ : (s.nodes n₁).durable.committed e = some (leader₁,val₁))
    (h₂ : (s.nodes n₂).durable.committed e = some (leader₂,val₂)) :
    leader₁ = leader₂ ∧ val₁ = val₂ := by
  have hi := reachable_bftCommitInv c f faulty fp hr
  exact bft_qc_unique hf (hi.qc_has_quorum.2 _ _ _ _ h₁) (hi.qc_has_quorum.2 _ _ _ _ h₂)

abbrev SeqBFTState (c : Config N) (Val : Type) := Nat → Option (Member c × Val)

inductive SeqBFTObs (c : Config N) (Val : Type) where
  | silent
  | committed (e : Nat) (leader : Member c) (val : Val)

def obsMap : BFTLabel c Val → SeqBFTObs c Val
  | .process actor (.local (.formQCAndCommit e val _)) _ => .committed e actor val
  | _ => .silent

inductive SeqBFTStep (c : Config N) (Val : Type) :
    SeqBFTState c Val → SeqBFTObs c Val → SeqBFTState c Val → Prop where
  | idle (b) : SeqBFTStep c Val b .silent b
  | commit (b) (e) (leader) (val) (guard : b e = none) :
      SeqBFTStep c Val b (.committed e leader val)
        (fun e' => if e' = e then some (leader,val) else b e')

def sequentialBFTSpec (c : Config N) (Val : Type) :
    Foundation.TransitionSystem (SeqBFTState c Val) (SeqBFTObs c Val) (SeqBFTObs c Val) where
  init b := b = fun _ => none
  step b a o b' := SeqBFTStep c Val b a b' ∧ o = a

def BFTSimRel (c : Config N) (f : Nat) (faulty : List (Member c)) (s : BFTState c Val)
    (b : SeqBFTState c Val) : Prop :=
  BFTCommitInv c f faulty s ∧ (∀ e leader val,
    b e = some (leader,val) ↔ (s.nodes leader).durable.committed e = some (leader,val))

omit [DecidableEq Val] in
theorem formQC_view_empty (hf : FaultyBounded c f faulty) (h : BFTSimRel c f faulty s b)
    (hq : IsBFTQuorum c f ((s.nodes actor).volatile.tally E value))
    (hg : (s.nodes actor).durable.committed E = none) : b E = none := by
  cases hb : b E with
  | none => rfl
  | some pair =>
    obtain ⟨leader,val⟩ := pair
    have hc := (h.2 E leader val).mp hb
    obtain ⟨hl, Q, hQ, hv⟩ := h.1.qc_has_quorum.2 leader E leader val hc
    have he : actor = leader := (bft_quorum_candidates_unique hf hq hQ
      (h.1.tally_honest_valid actor E value) hv).1
    subst leader
    rw [hg] at hl
    contradiction

omit [DecidableEq Val] in
theorem self_records_frame (s : BFTState c Val) (actor : Member c)
    (d : BFTDurable c Val) (v : BFTVolatile c Val) (status : Status)
    (hc : d.committed = (s.nodes actor).durable.committed) :
    ∀ e leader val,
      (setNode s.nodes actor ⟨d,v,status⟩ leader).durable.committed e = some (leader,val) ↔
      (s.nodes leader).durable.committed e = some (leader,val) := by
  intro e leader val
  by_cases he : leader = actor
  · subst leader; simp [setNode, hc]
  · simp [setNode, he]

omit [DecidableEq Val] in
theorem self_records_follower (s : BFTState c Val) (actor leader : Member c)
    (E : Nat) (value : Val) (v : BFTVolatile c Val)
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

omit [DecidableEq Val] in
theorem sim_commit_update (h : BFTSimRel c f faulty s b) (actor : Member c) (E : Nat)
    (value : Val) (v : BFTVolatile c Val) (hb : b E = none) :
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

theorem bft_commit_refines_spec (c : Config N) (f : Nat) (faulty : List (Member c)) (hf : FaultyBounded c f faulty) (fp : FaultProfile) :
    Foundation.ForwardSimulation
      (Distributed.system c (bftCommitProtocol (Val := Val) c f faulty) fp)
      (sequentialBFTSpec c Val) (BFTSimRel c f faulty) obsMap := by
  constructor
  · intro s hi
    refine ⟨fun _ => none, rfl, bftCommitInv_initial c f faulty fp s hi, ?_⟩
    intro e leader val
    have hc := (hi.2.2 leader).2.2.1
    simp [hc]
  · intro s a o t b hr hs
    obtain ⟨step, he⟩ := hs
    subst o
    have ht := bftCommitInv_preserved c f faulty fp hr.1 step
    have idle : ∀ (eqobs : obsMap a = SeqBFTObs.silent),
        (∀ e leader val, (t.nodes leader).durable.committed e = some (leader,val) ↔
          (s.nodes leader).durable.committed e = some (leader,val)) →
        ∃ ba b', (sequentialBFTSpec c Val).step b ba (obsMap a) b' ∧ BFTSimRel c f faulty t b' := by
      intro eqobs hframe
      refine ⟨.silent, b, ⟨SeqBFTStep.idle b, eqobs⟩, ht, ?_⟩
      intro e leader val
      exact (hr.2 e leader val).trans (hframe e leader val).symm
    cases step with
    | @process actor stimulus d v outs result running reaction publish =>
      cases reaction with
      | byzantineEquivocate isFaulty =>
        apply idle rfl
        exact self_records_frame s actor _ _ _ rfl
      | castHonestVote guard =>
        apply idle rfl
        exact self_records_frame s actor _ _ _ rfl
      | @formQCAndCommit E value followers quorum guard =>
        have hb := formQC_view_empty hf hr quorum guard
        refine ⟨.committed E actor value,
          fun k => if k = E then some (actor,value) else b k,
          ⟨SeqBFTStep.commit b E actor value hb, rfl⟩, ht, ?_⟩
        exact sim_commit_update hr actor E value _ hb
    | @deliver msg rest d v outs result running take reaction publish =>
      rcases msg with ⟨tid, sender, actor, l, payload⟩
      cases reaction with
      | recvVote guard =>
        apply idle rfl
        exact self_records_frame s _ _ _ _ rfl
      | recvCommitQC authentic guard =>
        rename_i E leader value
        have hc := hr.1.qc_msg_authentic ⟨tid,⟨sender,actor,l,.commitQC E leader value⟩⟩
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
theorem bft_safety_via_refinement (c : Config N) (f : Nat) (faulty : List (Member c)) (hf : FaultyBounded c f faulty) (fp : FaultProfile)
    {s : BFTState c Val} (hr : Foundation.Reachable (sys c f faulty fp) s) :
    ∀ e (n₁ n₂ leader₁ leader₂ : Member c) (val₁ val₂ : Val),
      (s.nodes n₁).durable.committed e = some (leader₁,val₁) →
      (s.nodes n₂).durable.committed e = some (leader₂,val₂) →
      leader₁ = leader₂ ∧ val₁ = val₂ := by
  apply (bft_commit_refines_spec c f faulty hf fp).transfer_invariant
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
    have hc₁ := (rel.1.qc_has_quorum.2 n₁ e leader₁ val₁ h₁).1
    have hc₂ := (rel.1.qc_has_quorum.2 n₂ e leader₂ val₂ h₂).1
    exact safe e leader₁ leader₂ val₁ val₂
      ((rel.2 e leader₁ val₁).mpr hc₁) ((rel.2 e leader₂ val₂).mpr hc₂)
  · exact hr

end Harmonia.VerifiedProtocols.BFTQuorumCommit
