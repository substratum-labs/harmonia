import Harmonia.Core.Refinement
import Harmonia.Distributed
import Harmonia.Theorems.Quorum

namespace Harmonia.VerifiedProtocols.TwoPhaseCommit
open Distributed
variable {N : Type} [DecidableEq N]

structure TwoPCDurable (c : Config N) where
  voted : Nat → Option Bool
  coordDecision : Nat → Option Bool
  outcome : Nat → Option Bool

structure TwoPCVolatile (c : Config N) where
  yesVoters : Nat → List (Member c)

inductive TwoPCMsg (c : Config N) where
  | voteYes (tx : Nat)
  | voteNo (tx : Nat)
  | decide (tx : Nat) (commit : Bool)
  deriving DecidableEq

inductive TwoPCCmd (c : Config N) where
  | castVoteYes (tx : Nat)
  | castVoteNo (tx : Nat)
  | coordCommit (tx : Nat) (participants : List (Member c))
  | coordAbort (tx : Nat) (participants : List (Member c))
  deriving DecidableEq

def IsAllMembers (c : Config N) (voters : List (Member c)) : Prop :=
  (voters.map Subtype.val).Nodup ∧ c.members.length ≤ (voters.map Subtype.val).length

omit [DecidableEq N] in
theorem mapped_members (c : Config N) (Q : List (Member c)) :
    ∀ x ∈ Q.map Subtype.val, x ∈ c.members := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact v.property

theorem all_members_of_unanimous (c : Config N) (voters : List (Member c))
    (hu : IsAllMembers c voters) (m : Member c) : m ∈ voters := by
  by_cases hm : m.val ∈ voters.map Subtype.val
  · obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
    exact Subtype.ext heq ▸ hv
  · have hsub : ∀ x ∈ voters.map Subtype.val, x ∈ Harmonia.Quorum.diff c.members [m.val] := by
      intro x hx
      apply List.mem_filter.mpr
      refine ⟨mapped_members c voters x hx, ?_⟩
      have hne : x ≠ m.val := fun he => hm (he ▸ hx)
      simpa [Harmonia.Quorum.diff] using hne
    have hlen := Harmonia.Quorum.subset_length_le (voters.map Subtype.val)
      (Harmonia.Quorum.diff c.members [m.val]) hu.1 hsub
    have hpart := Harmonia.Quorum.partition_length c.members [m.val]
    have hpos : 0 < (Harmonia.Quorum.inter c.members [m.val]).length :=
      List.length_pos_iff_exists_mem.mpr ⟨m.val, List.mem_filter.mpr ⟨m.property, by simp⟩⟩
    have hge := hu.2
    omega

inductive TwoPCReact (c : Config N) (coord : Member c) : Member c → TwoPCDurable c →
    TwoPCVolatile c → Input (Member c) Nat (TwoPCMsg c) (TwoPCCmd c) Empty →
    TwoPCDurable c → TwoPCVolatile c → List (Outgoing (Member c) Nat (TwoPCMsg c)) → Prop where
  | castVoteYes {actor d v tx}
      (guardVoted : d.voted tx = none) (guardOut : d.outcome tx = none) :
      TwoPCReact c coord actor d v (.scheduled (.local (.castVoteYes tx)))
        { d with voted := fun k => if k = tx then some true else d.voted k }
        v [⟨coord, tx, .voteYes tx⟩]
  | castVoteNo {actor d v tx}
      (notCoord : actor ≠ coord)
      (guardVoted : d.voted tx = none) (guardOut : d.outcome tx = none) :
      TwoPCReact c coord actor d v (.scheduled (.local (.castVoteNo tx)))
        { d with
            voted := fun k => if k = tx then some false else d.voted k,
            outcome := fun k => if k = tx then some false else d.outcome k }
        v [⟨coord, tx, .voteNo tx⟩]
  | coordCommit {actor d v tx participants}
      (isCoord : actor = coord)
      (unanimous : IsAllMembers c (v.yesVoters tx))
      (guardDec : d.coordDecision tx = none) (guardOut : d.outcome tx = none) :
      TwoPCReact c coord actor d v (.scheduled (.local (.coordCommit tx participants)))
        { d with
            coordDecision := fun k => if k = tx then some true else d.coordDecision k,
            outcome := fun k => if k = tx then some true else d.outcome k }
        v (participants.map fun peer => ⟨peer, tx, .decide tx true⟩)
  | coordAbort {actor d v tx participants}
      (isCoord : actor = coord)
      (guardDec : d.coordDecision tx = none) (guardOut : d.outcome tx = none) :
      TwoPCReact c coord actor d v (.scheduled (.local (.coordAbort tx participants)))
        { d with
            coordDecision := fun k => if k = tx then some false else d.coordDecision k,
            outcome := fun k => if k = tx then some false else d.outcome k }
        v (participants.map fun peer => ⟨peer, tx, .decide tx false⟩)
  | recvVoteYes {actor d v tx sender l} (isCoord : actor = coord) :
      TwoPCReact c coord actor d v (.message ⟨sender, actor, l, .voteYes tx⟩) d
        ⟨fun k => if k = tx then
          (if sender ∈ v.yesVoters tx then v.yesVoters tx else sender :: v.yesVoters tx)
          else v.yesVoters k⟩ []
  | recvVoteNo {actor d v tx sender l}
      (isCoord : actor = coord)
      (guardDec : d.coordDecision tx = none) (guardOut : d.outcome tx = none) :
      TwoPCReact c coord actor d v (.message ⟨sender, actor, l, .voteNo tx⟩)
        { d with
            coordDecision := fun k => if k = tx then some false else d.coordDecision k,
            outcome := fun k => if k = tx then some false else d.outcome k }
        v (c.members.attach.map fun peer => ⟨peer, tx, .decide tx false⟩)
  | recvDecide {actor d v tx commit sender l}
      (authentic : sender = coord) (guardOut : d.outcome tx = none) :
      TwoPCReact c coord actor d v (.message ⟨sender, actor, l, .decide tx commit⟩)
        { d with outcome := fun k => if k = tx then some commit else d.outcome k } v []

def twoPCProtocol (c : Config N) (coord : Member c) :
    Protocol (Member c) (TwoPCDurable c) (TwoPCVolatile c) Nat (TwoPCMsg c) (TwoPCCmd c) Empty where
  initial _ d v := d.voted = (fun _ => none) ∧ d.coordDecision = (fun _ => none) ∧
    d.outcome = (fun _ => none) ∧ v.yesVoters = (fun _ => [])
  react := TwoPCReact c coord
  crashReset _ _ := ⟨fun _ => []⟩
  recover _ := ⟨fun _ => []⟩

abbrev TwoPCState (c : Config N) :=
  State (Member c) (TwoPCDurable c) (TwoPCVolatile c) Nat (TwoPCMsg c)
abbrev TwoPCLabel (c : Config N) :=
  Label (Member c) Nat (TwoPCMsg c) (TwoPCCmd c) Empty

def sys (c : Config N) (coord : Member c) (fp : FaultProfile) :=
  Distributed.system c (twoPCProtocol c coord) fp

def CommitCertified (c : Config N) (coord : Member c) (s : TwoPCState c) (tx : Nat) : Prop :=
  (s.nodes coord).durable.coordDecision tx = some true ∧
  ∀ m : Member c, (s.nodes m).durable.voted tx = some true

structure TwoPCInv (c : Config N) (coord : Member c) (s : TwoPCState c) : Prop where
  yes_voters_nodup : ∀ m tx, (((s.nodes m).volatile.yesVoters tx).map Subtype.val).Nodup
  vote_yes_in_flight : ∀ t ∈ s.pending, ∀ tx,
    t.envelope.payload = .voteYes tx → (s.nodes t.envelope.sender).durable.voted tx = some true
  vote_no_in_flight : ∀ t ∈ s.pending, ∀ tx,
    t.envelope.payload = .voteNo tx → (s.nodes t.envelope.sender).durable.voted tx = some false
  collected_yes_valid : ∀ m tx voter, voter ∈ (s.nodes m).volatile.yesVoters tx →
    (s.nodes voter).durable.voted tx = some true
  decide_msg_authentic : ∀ t ∈ s.pending, ∀ tx commit,
    t.envelope.payload = .decide tx commit →
      (s.nodes coord).durable.coordDecision tx = some commit
  coord_commit_all_yes : ∀ tx,
    (s.nodes coord).durable.coordDecision tx = some true → CommitCertified c coord s tx
  outcome_true_certified : ∀ n tx,
    (s.nodes n).durable.outcome tx = some true → CommitCertified c coord s tx
  outcome_false_justified : ∀ n tx,
    (s.nodes n).durable.outcome tx = some false →
      (s.nodes n).durable.voted tx = some false ∨
      (s.nodes coord).durable.coordDecision tx = some false
  coord_decision_matches_outcome : ∀ tx dec,
    (s.nodes coord).durable.coordDecision tx = some dec →
      (s.nodes coord).durable.outcome tx = some dec


variable {c : Config N} {coord : Member c} {s t : TwoPCState c} {tx : Nat}

def DurableExtends (s t : TwoPCState c) : Prop :=
  (∀ m k b, (s.nodes m).durable.voted k = some b → (t.nodes m).durable.voted k = some b) ∧
  (∀ m k b, (s.nodes m).durable.coordDecision k = some b → (t.nodes m).durable.coordDecision k = some b) ∧
  (∀ m k b, (s.nodes m).durable.outcome k = some b → (t.nodes m).durable.outcome k = some b)

omit [DecidableEq N] in
theorem certified_mono (h : DurableExtends s t) (hc : CommitCertified c coord s tx) :
    CommitCertified c coord t tx := ⟨h.2.1 _ _ _ hc.1, fun m => h.1 _ _ _ (hc.2 m)⟩

theorem twoPCInv_initial (c : Config N) (coord : Member c) (fp : FaultProfile)
    (s : TwoPCState c) (h : (sys c coord fp).init s) : TwoPCInv c coord s := by
  obtain ⟨hp, _, hn⟩ := h
  have hd : ∀ m, (s.nodes m).durable.coordDecision = fun _ => none := fun m => (hn m).2.2.1
  have ho : ∀ m, (s.nodes m).durable.outcome = fun _ => none := fun m => (hn m).2.2.2.1
  have ht : ∀ m, (s.nodes m).volatile.yesVoters = fun _ => [] := fun m => (hn m).2.2.2.2
  constructor
  · intro m k; simp [ht]
  · simp [hp]
  · simp [hp]
  · intro m k voter hv; simp [ht] at hv
  · simp [hp]
  · intro k he; simp [hd] at he
  · intro m k he; simp [ho] at he
  · intro m k he; simp [ho] at he
  · intro k b he; simp [hd] at he

omit [DecidableEq N] in
/-- Reassemble the invariant after a local write and atomic publication. -/
theorem rebuild (h : TwoPCInv c coord s) (mono : DurableExtends s t)
    (nd : ∀ m k, (((t.nodes m).volatile.yesVoters k).map Subtype.val).Nodup)
    (cv : ∀ m k voter, voter ∈ (t.nodes m).volatile.yesVoters k →
      (t.nodes voter).durable.voted k = some true)
    (dc : ∀ k, (t.nodes coord).durable.coordDecision k = some true → CommitCertified c coord t k)
    (oc : ∀ m k, (t.nodes m).durable.outcome k = some true → CommitCertified c coord t k)
    (oa : ∀ m k, (t.nodes m).durable.outcome k = some false →
      (t.nodes m).durable.voted k = some false ∨ (t.nodes coord).durable.coordDecision k = some false)
    (dm : ∀ k b, (t.nodes coord).durable.coordDecision k = some b →
      (t.nodes coord).durable.outcome k = some b)
    (pending : ∀ x ∈ t.pending, ∃ y, y ∈ s.pending ∧ x.envelope = y.envelope ∨
      ((∀ k, x.envelope.payload = .voteYes k → (t.nodes x.envelope.sender).durable.voted k = some true) ∧
       (∀ k, x.envelope.payload = .voteNo k → (t.nodes x.envelope.sender).durable.voted k = some false) ∧
       (∀ k b, x.envelope.payload = .decide k b → (t.nodes coord).durable.coordDecision k = some b))) :
    TwoPCInv c coord t := by
  refine ⟨nd, ?_, ?_, cv, ?_, dc, oc, oa, dm⟩
  · intro x hx k he
    obtain ⟨y, old | fresh⟩ := pending x hx
    · have hv := mono.1 _ _ _ (h.vote_yes_in_flight y old.1 k (by simpa [old.2] using he))
      simpa [old.2] using hv
    · exact fresh.1 k he
  · intro x hx k he
    obtain ⟨y, old | fresh⟩ := pending x hx
    · have hv := mono.1 _ _ _ (h.vote_no_in_flight y old.1 k (by simpa [old.2] using he))
      simpa [old.2] using hv
    · exact fresh.2.1 k he
  · intro x hx k b he
    obtain ⟨y, old | fresh⟩ := pending x hx
    · exact mono.2.1 _ _ _ (h.decide_msg_authentic y old.1 k b (by simpa [old.2] using he))
    · exact fresh.2.2 k b he

theorem option_write_mono {old : Nat → Option α} (guard : old k = none) (value : α) :
    ∀ j b, old j = some b → (if j = k then some value else old j) = some b := by
  intro j b he
  by_cases hj : j = k
  · subst j; rw [guard] at he; cases he
  · simp [hj,he]

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

theorem reaction_preserved {c : Config N} {coord : Member c} {s : TwoPCState c}
    (h : TwoPCInv c coord s) {actor : Member c} {input d v outs result}
    (reaction : TwoPCReact c coord actor (s.nodes actor).durable (s.nodes actor).volatile input d v outs)
    (incoming : ∀ env, input = .message env → ∃ x ∈ s.pending, x.envelope = env)
    (publication : ∀ x ∈ result, x ∈ s.pending ∨ x ∈ allocate actor s.next outs) :
    TwoPCInv c coord ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩ := by
  let t : TwoPCState c := ⟨setNode s.nodes actor ⟨d,v,.running⟩,result,s.next + outs.length⟩
  have mono_of
      (vm : ∀ k b, (s.nodes actor).durable.voted k = some b → d.voted k = some b)
      (dm : ∀ k b, (s.nodes actor).durable.coordDecision k = some b → d.coordDecision k = some b)
      (om : ∀ k b, (s.nodes actor).durable.outcome k = some b → d.outcome k = some b) : DurableExtends s t := by
    refine ⟨?_,?_,?_⟩ <;> intro m k b he <;> by_cases hm : m = actor
    · subst m; simpa [t] using vm k b he
    · simpa [t,setNode,hm] using he
    · subst m; simpa [t] using dm k b he
    · simpa [t,setNode,hm] using he
    · subst m; simpa [t] using om k b he
    · simpa [t,setNode,hm] using he
  have finish (mono : DurableExtends s t)
      (nd : ∀ k, ((v.yesVoters k).map Subtype.val).Nodup)
      (cv : ∀ k voter, voter ∈ v.yesVoters k → (t.nodes voter).durable.voted k = some true)
      (dc : ∀ k, (t.nodes coord).durable.coordDecision k = some true → CommitCertified c coord t k)
      (oc : ∀ k, d.outcome k = some true → CommitCertified c coord t k)
      (oa : ∀ k, d.outcome k = some false → d.voted k = some false ∨
        (t.nodes coord).durable.coordDecision k = some false)
      (dm : ∀ k b, (t.nodes coord).durable.coordDecision k = some b →
        (t.nodes coord).durable.outcome k = some b)
      (og : ∀ x ∈ allocate actor s.next outs,
        (∀ k, x.envelope.payload = .voteYes k → (t.nodes x.envelope.sender).durable.voted k = some true) ∧
        (∀ k, x.envelope.payload = .voteNo k → (t.nodes x.envelope.sender).durable.voted k = some false) ∧
        (∀ k b, x.envelope.payload = .decide k b → (t.nodes coord).durable.coordDecision k = some b)) : TwoPCInv c coord t := by
    apply rebuild h mono
    · intro m k; by_cases hm : m = actor
      · subst m; simpa [t] using nd k
      · simpa [t,setNode,hm] using h.yes_voters_nodup m k
    · intro m k voter hv; by_cases hm : m = actor
      · subst m; exact cv k voter (by simpa [t] using hv)
      · exact mono.1 _ _ _ (h.collected_yes_valid m k voter (by simpa [t,setNode,hm] using hv))
    · exact dc
    · intro m k hv; by_cases hm : m = actor
      · subst m; exact oc k (by simpa [t] using hv)
      · exact certified_mono mono (h.outcome_true_certified m k (by simpa [t,setNode,hm] using hv))
    · intro m k hv; by_cases hm : m = actor
      · subst m; simpa [t] using oa k (by simpa [t] using hv)
      · rcases h.outcome_false_justified m k (by simpa [t,setNode,hm] using hv) with no | abort
        · exact Or.inl (mono.1 _ _ _ no)
        · exact Or.inr (mono.2.1 _ _ _ abort)
    · exact dm
    · intro x hx
      rcases publication x hx with old | fresh
      · exact ⟨x,Or.inl ⟨old,rfl⟩⟩
      · exact ⟨x,Or.inr (og x fresh)⟩
  have old_cv (mono : DurableExtends s t) : ∀ k voter,
      voter ∈ (s.nodes actor).volatile.yesVoters k → (t.nodes voter).durable.voted k = some true :=
    fun k voter hv => mono.1 _ _ _ (h.collected_yes_valid actor k voter hv)
  have old_oa (mono : DurableExtends s t) : ∀ k, (s.nodes actor).durable.outcome k = some false →
      (t.nodes actor).durable.voted k = some false ∨ (t.nodes coord).durable.coordDecision k = some false := by
    intro k he
    rcases h.outcome_false_justified actor k he with no | abort
    · exact Or.inl (mono.1 _ _ _ no)
    · exact Or.inr (mono.2.1 _ _ _ abort)
  have frame_dc (mono : DurableExtends s t)
      (eq : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision) :
      ∀ k, (t.nodes coord).durable.coordDecision k = some true → CommitCertified c coord t k := by
    intro k he; exact certified_mono mono (h.coord_commit_all_yes k (by simpa [eq] using he))
  have frame_dm (mono : DurableExtends s t)
      (eq : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision) :
      ∀ k b, (t.nodes coord).durable.coordDecision k = some b → (t.nodes coord).durable.outcome k = some b := by
    intro k b he; exact mono.2.2 _ _ _ (h.coord_decision_matches_outcome k b (by simpa [eq] using he))
  have decision (E : Nat) (value : Bool) (ha : actor = coord)
      (gd : (s.nodes actor).durable.coordDecision E = none)
      (go : (s.nodes actor).durable.outcome E = none)
      (dv : d.voted = (s.nodes actor).durable.voted)
      (dd : d.coordDecision = fun k => if k = E then some value else (s.nodes actor).durable.coordDecision k)
      (do' : d.outcome = fun k => if k = E then some value else (s.nodes actor).durable.outcome k)
      (vv : v = (s.nodes actor).volatile)
      (yes : value = true → ∀ m, (s.nodes m).durable.voted E = some true)
      (payload : ∀ x ∈ allocate actor s.next outs, x.envelope.payload = .decide E value) : TwoPCInv c coord t := by
    have mono := mono_of (by rw [dv]; exact fun _ _ he => he)
      (by rw [dd]; exact option_write_mono gd value)
      (by rw [do']; exact option_write_mono go value)
    have fresh : value = true → CommitCertified c coord t E := by
      intro he
      refine ⟨?_, fun m => mono.1 _ _ _ (yes he m)⟩
      simp [t, setNode, ← ha, dd, he]
    apply finish mono
    · simpa [vv] using h.yes_voters_nodup actor
    · simpa [vv] using old_cv mono
    · intro k he
      by_cases hk : k = E
      · subst k
        have eq : value = true := by simpa [t,setNode,← ha,dd] using he
        exact fresh eq
      · apply certified_mono mono (h.coord_commit_all_yes k ?_)
        simpa [t,setNode,← ha,dd,hk] using he
    · intro k he
      by_cases hk : k = E
      · subst k; exact fresh (by simpa [do'] using he)
      · exact certified_mono mono (h.outcome_true_certified actor k (by simpa [do',hk] using he))
    · intro k he
      by_cases hk : k = E
      · subst k
        have eq : value = false := by simpa [do'] using he
        right; simp [t,setNode,← ha,dd,eq]
      · have old := old_oa mono k (by simpa [do',hk] using he)
        simpa [t] using old
    · intro k b he
      by_cases hk : k = E
      · subst k
        have eq : value = b := by simpa [t,setNode,← ha,dd] using he
        simp [t,setNode,← ha,do',eq]
      · have old : (s.nodes coord).durable.coordDecision k = some b := by
          simpa [t,setNode,← ha,dd,hk] using he
        exact mono.2.2 _ _ _ (h.coord_decision_matches_outcome k b old)
    · intro x hx
      have hp := payload x hx
      refine ⟨?_,?_,?_⟩
      · intro k he; rw [hp] at he; cases he
      · intro k he; rw [hp] at he; cases he
      · intro k b he; rw [hp] at he; cases he
        simp [t,setNode,← ha,dd]
  cases reaction with
  | @castVoteYes E gv go =>
    have mono := mono_of (option_write_mono gv true) (fun _ _ he => he) (fun _ _ he => he)
    have eq : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision := by
      by_cases ha : coord = actor <;> simp [t,setNode,ha]
    apply finish mono (h.yes_voters_nodup actor) (old_cv mono) (frame_dc mono eq)
    · intro k he; exact certified_mono mono (h.outcome_true_certified actor k he)
    · intro k he; simpa [t] using old_oa mono k he
    · exact frame_dm mono eq
    · intro x hx
      simp only [allocate,List.mem_cons,List.not_mem_nil,or_false] at hx
      subst x
      refine ⟨?_,?_,?_⟩
      · intro k he; cases he; simp [t,setNode]
      · intro k he; cases he
      · intro k b he; cases he
  | @castVoteNo E ha gv go =>
    have mono := mono_of (option_write_mono gv false) (fun _ _ he => he) (option_write_mono go false)
    have eq : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision := by
      simp [t,setNode,Ne.symm ha]
    apply finish mono (h.yes_voters_nodup actor) (old_cv mono) (frame_dc mono eq)
    · intro k he
      by_cases hk : k = E
      · simp [hk] at he
      · exact certified_mono mono (h.outcome_true_certified actor k (by simpa [hk] using he))
    · intro k he
      by_cases hk : k = E
      · subst k; left; simp
      · simpa [t] using old_oa mono k (by simpa [hk] using he)
    · exact frame_dm mono eq
    · intro x hx
      simp only [allocate,List.mem_cons,List.not_mem_nil,or_false] at hx
      subst x
      refine ⟨?_,?_,?_⟩
      · intro k he; cases he
      · intro k he; cases he; simp [t,setNode]
      · intro k b he; cases he
  | @coordCommit E participants ha quorum gd go =>
    apply decision E true ha gd go rfl rfl rfl rfl
    · intro _ m
      exact h.collected_yes_valid actor E m (all_members_of_unanimous c _ quorum m)
    · intro x hx
      obtain ⟨out,ho,hp⟩ := allocate_payload actor s.next _ x hx
      obtain ⟨peer,_,rfl⟩ := List.mem_map.mp ho
      exact hp
  | @coordAbort E participants ha gd go =>
    apply decision E false ha gd go rfl rfl rfl rfl
    · intro he; cases he
    · intro x hx
      obtain ⟨out,ho,hp⟩ := allocate_payload actor s.next _ x hx
      obtain ⟨peer,_,rfl⟩ := List.mem_map.mp ho
      exact hp
  | @recvVoteNo E sender l ha gd go =>
    apply decision E false ha gd go rfl rfl rfl rfl
    · intro he; cases he
    · intro x hx
      obtain ⟨out,ho,hp⟩ := allocate_payload actor s.next _ x hx
      obtain ⟨peer,_,rfl⟩ := List.mem_map.mp ho
      exact hp
  | @recvVoteYes E sender l ha =>
    obtain ⟨x,hx,he⟩ := incoming ⟨sender,actor,l,.voteYes E⟩ rfl
    have grant : (s.nodes sender).durable.voted E = some true := by
      have hv := h.vote_yes_in_flight x hx E (by simp [he])
      simpa [he] using hv
    have mono := mono_of (fun _ _ he => he) (fun _ _ he => he) (fun _ _ he => he)
    have eq : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision := by
      by_cases he : coord = actor <;> simp [t,setNode,he]
    apply finish mono
    · intro k
      by_cases hk : k = E
      · subst k
        by_cases hn : sender ∈ (s.nodes actor).volatile.yesVoters E
        · simpa [hn] using h.yes_voters_nodup actor E
        · simp only [↓reduceIte,hn,List.map_cons,List.nodup_cons]
          refine ⟨?_,h.yes_voters_nodup actor E⟩
          intro hm
          obtain ⟨w,hw,he⟩ := List.mem_map.mp hm
          exact hn (Subtype.ext he ▸ hw)
      · simpa [hk] using h.yes_voters_nodup actor k
    · intro k voter hv
      by_cases hk : k = E
      · subst k
        by_cases hn : sender ∈ (s.nodes actor).volatile.yesVoters E
        · simp only [↓reduceIte,hn] at hv
          exact mono.1 _ _ _ (h.collected_yes_valid actor E voter hv)
        · simp only [↓reduceIte,hn] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact mono.1 _ _ _ grant
          · exact mono.1 _ _ _ (h.collected_yes_valid actor E voter hv)
      · simp only [ite_eq_right hk] at hv
        exact mono.1 _ _ _ (h.collected_yes_valid actor k voter hv)
    · exact frame_dc mono eq
    · intro k he; exact certified_mono mono (h.outcome_true_certified actor k he)
    · intro k he; simpa [t] using old_oa mono k he
    · exact frame_dm mono eq
    · intro x hx; simp [allocate] at hx
  | @recvDecide E value sender l authentic go =>
    obtain ⟨x,hx,he⟩ := incoming ⟨sender,actor,l,.decide E value⟩ rfl
    have dec := h.decide_msg_authentic x hx E value (by simp [he])
    have mono := mono_of (fun _ _ he => he) (fun _ _ he => he) (option_write_mono go value)
    have eq : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision := by
      by_cases ha : coord = actor <;> simp [t,setNode,ha]
    apply finish mono (h.yes_voters_nodup actor) (old_cv mono) (frame_dc mono eq)
    · intro k hv
      by_cases hk : k = E
      · subst k
        have hv : value = true := by simpa using hv
        exact certified_mono mono (h.coord_commit_all_yes E (hv ▸ dec))
      · exact certified_mono mono (h.outcome_true_certified actor k (by simpa [hk] using hv))
    · intro k hv
      by_cases hk : k = E
      · subst k
        have hv : value = false := by simpa using hv
        right; exact mono.2.1 _ _ _ (hv ▸ dec)
      · simpa [t] using old_oa mono k (by simpa [hk] using hv)
    · exact frame_dm mono eq
    · intro x hx; simp [allocate] at hx

omit [DecidableEq N] in
theorem fault_preserved (h : TwoPCInv c coord s)
    (durable : ∀ m, (t.nodes m).durable = (s.nodes m).durable)
    (tallies : ∀ m k, (t.nodes m).volatile.yesVoters k = (s.nodes m).volatile.yesVoters k ∨
      (t.nodes m).volatile.yesVoters k = [])
    (pending : ∀ x ∈ t.pending, ∃ y ∈ s.pending, x.envelope = y.envelope) : TwoPCInv c coord t := by
  have mono : DurableExtends s t := by
    refine ⟨?_,?_,?_⟩ <;> intro m k b he <;> simpa [durable m] using he
  apply rebuild h mono
  · intro m k
    rcases tallies m k with same | empty
    · rw [same]; exact h.yes_voters_nodup m k
    · simp [empty]
  · intro m k voter hv
    rcases tallies m k with same | empty
    · rw [same] at hv; exact mono.1 _ _ _ (h.collected_yes_valid m k voter hv)
    · simp [empty] at hv
  · intro k he; exact certified_mono mono (h.coord_commit_all_yes k (by simpa [durable] using he))
  · intro m k he; exact certified_mono mono (h.outcome_true_certified m k (by simpa [durable] using he))
  · intro m k he
    simpa [durable] using h.outcome_false_justified m k (by simpa [durable] using he)
  · intro k b he
    simpa [durable] using h.coord_decision_matches_outcome k b (by simpa [durable] using he)
  · intro x hx
    obtain ⟨y,hy,he⟩ := pending x hx
    exact ⟨y,Or.inl ⟨hy,he⟩⟩

theorem twoPCInv_preserved (c : Config N) (coord : Member c) (fp : FaultProfile)
    {s t : TwoPCState c} {a : TwoPCLabel c} (h : TwoPCInv c coord s)
    (step : Distributed.Step c (twoPCProtocol c coord) fp s a t) : TwoPCInv c coord t := by
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
    apply fault_preserved (t := ⟨s.nodes, rest, s.next⟩) h (fun _ => rfl) (fun _ _ => Or.inl rfl)
    intro x hx
    exact ⟨x, take.mem_iff.mpr (by simp [hx]), rfl⟩
  | @duplicate e result allowed present copy =>
    apply fault_preserved (t := ⟨s.nodes, result, s.next+1⟩) h (fun _ => rfl) (fun _ _ => Or.inl rfl)
    intro x hx
    rcases List.mem_cons.mp (copy.mem_iff.mp hx) with rfl | old
    · exact ⟨_, present, rfl⟩
    · exact ⟨x, old, rfl⟩
  | @crash actor allowed running =>
    apply fault_preserved h
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m e; by_cases hm : m = actor
      · right; simp [setNode, hm, twoPCProtocol]
      · left; simp [setNode, hm]
    · intro x hx; exact ⟨x, hx, rfl⟩
  | @recover actor allowed crashed =>
    apply fault_preserved h
    · intro m; by_cases hm : m = actor <;> simp [setNode, hm]
    · intro m e; by_cases hm : m = actor
      · right; simp [setNode, hm, twoPCProtocol]
      · left; simp [setNode, hm]
    · intro x hx; exact ⟨x, hx, rfl⟩

theorem reachable_twoPCInv (c : Config N) (coord : Member c) (fp : FaultProfile)
    {s : TwoPCState c} (hr : Foundation.Reachable (sys c coord fp) s) : TwoPCInv c coord s := by
  apply Foundation.invariant (twoPCInv_initial c coord fp) ?_ s hr
  intro s a o t hi hs
  exact twoPCInv_preserved c coord fp hi hs.1


omit [DecidableEq N] in
theorem agreement_of_inv (h : TwoPCInv c coord s)
    (h₁ : (s.nodes n₁).durable.outcome tx = some true)
    (h₂ : (s.nodes n₂).durable.outcome tx = some false) : False := by
  have cert := h.outcome_true_certified n₁ tx h₁
  rcases h.outcome_false_justified n₂ tx h₂ with no | abort
  · have he := (cert.2 n₂).symm.trans no; cases he
  · have he := cert.1.symm.trans abort; cases he

theorem twoPC_atomic_agreement (c : Config N) (coord : Member c) (fp : FaultProfile)
    {s : TwoPCState c} (hr : Foundation.Reachable (sys c coord fp) s)
    {n₁ n₂ : Member c} {tx : Nat} {b₁ b₂ : Bool}
    (h₁ : (s.nodes n₁).durable.outcome tx = some b₁)
    (h₂ : (s.nodes n₂).durable.outcome tx = some b₂) : b₁ = b₂ := by
  have hi := reachable_twoPCInv c coord fp hr
  cases b₁ <;> cases b₂
  · rfl
  · exact False.elim (agreement_of_inv hi h₂ h₁)
  · exact False.elim (agreement_of_inv hi h₁ h₂)
  · rfl

theorem twoPC_commit_validity (c : Config N) (coord : Member c) (fp : FaultProfile)
    {s : TwoPCState c} (hr : Foundation.Reachable (sys c coord fp) s)
    {n : Member c} {tx : Nat} (he : (s.nodes n).durable.outcome tx = some true) :
    ∀ m, (s.nodes m).durable.voted tx = some true :=
  ((reachable_twoPCInv c coord fp hr).outcome_true_certified n tx he).2

theorem twoPC_prepared_no_abort_without_coord (c : Config N) (coord : Member c) (fp : FaultProfile)
    {s : TwoPCState c} (hr : Foundation.Reachable (sys c coord fp) s)
    {n : Member c} {tx : Nat} (hv : (s.nodes n).durable.voted tx = some true)
    (ho : (s.nodes n).durable.outcome tx = some false) :
    (s.nodes coord).durable.coordDecision tx = some false := by
  rcases (reachable_twoPCInv c coord fp hr).outcome_false_justified n tx ho with no | abort
  · have he := hv.symm.trans no; cases he
  · exact abort

abbrev SeqTwoPCState := Nat → Option Bool

inductive SeqTwoPCObs where
  | silent
  | decided (tx : Nat) (commit : Bool)
  deriving DecidableEq

def obsMap {c : Config N} : TwoPCLabel c → SeqTwoPCObs
  | .process _ (.local (.coordCommit tx _)) _ => .decided tx true
  | .process _ (.local (.coordAbort tx _)) _ => .decided tx false
  | .deliver ⟨_, _, _, _, .voteNo tx⟩ _ => .decided tx false
  | _ => .silent

inductive SeqTwoPCStep : SeqTwoPCState → SeqTwoPCObs → SeqTwoPCState → Prop where
  | idle (b) : SeqTwoPCStep b .silent b
  | decide (b) (tx : Nat) (commit : Bool) (guard : b tx = none) :
      SeqTwoPCStep b (.decided tx commit)
        (fun k => if k = tx then some commit else b k)

def sequentialTwoPCSpec :
    Foundation.TransitionSystem SeqTwoPCState SeqTwoPCObs SeqTwoPCObs where
  init b := b = fun _ => none
  step b a o b' := SeqTwoPCStep b a b' ∧ o = a

def TwoPCSimRel (c : Config N) (coord : Member c) (s : TwoPCState c)
    (b : SeqTwoPCState) : Prop :=
  TwoPCInv c coord s ∧ (∀ tx dec,
    b tx = some dec ↔ (s.nodes coord).durable.coordDecision tx = some dec)

omit [DecidableEq N] in
theorem decision_empty (h : TwoPCSimRel c coord s b)
    (hg : (s.nodes coord).durable.coordDecision E = none) : b E = none := by
  cases hb : b E with
  | none => rfl
  | some value =>
    have he := (h.2 E value).mp hb
    rw [hg] at he; cases he

theorem decision_frame (s : TwoPCState c) (actor coord : Member c)
    (d : TwoPCDurable c) (v : TwoPCVolatile c) (status : Status)
    (hd : d.coordDecision = (s.nodes actor).durable.coordDecision) :
    (setNode s.nodes actor ⟨d,v,status⟩ coord).durable.coordDecision =
      (s.nodes coord).durable.coordDecision := by
  by_cases ha : coord = actor <;> simp [setNode,ha,hd]

theorem sim_decision_update (h : TwoPCSimRel c coord s b) (E : Nat) (value : Bool)
    (d : TwoPCDurable c) (v : TwoPCVolatile c)
    (hd : d.coordDecision = fun k => if k = E then some value else (s.nodes coord).durable.coordDecision k) :
    ∀ k dec, (if k = E then some value else b k) = some dec ↔
      (setNode s.nodes coord ⟨d,v,.running⟩ coord).durable.coordDecision k = some dec := by
  intro k dec
  by_cases hk : k = E
  · simp [hk,hd]
  · simpa [hk,hd] using h.2 k dec

theorem twoPC_refines_spec (c : Config N) (coord : Member c) (fp : FaultProfile) :
    Foundation.ForwardSimulation (sys c coord fp) sequentialTwoPCSpec
      (TwoPCSimRel c coord) obsMap := by
  constructor
  · intro s hi
    refine ⟨fun _ => none,rfl,twoPCInv_initial c coord fp s hi,?_⟩
    intro k dec
    have hd := (hi.2.2 coord).2.2.1
    simp [hd]
  · intro s a o t b hr hs
    obtain ⟨step,he⟩ := hs
    subst o
    have ht := twoPCInv_preserved c coord fp hr.1 step
    have idle (eqobs : obsMap a = .silent)
        (frame : (t.nodes coord).durable.coordDecision = (s.nodes coord).durable.coordDecision) :
        ∃ ba b', sequentialTwoPCSpec.step b ba (obsMap a) b' ∧ TwoPCSimRel c coord t b' := by
      refine ⟨.silent,b,⟨SeqTwoPCStep.idle b,eqobs⟩,ht,?_⟩
      intro k dec; simpa [frame] using hr.2 k dec
    cases step with
    | @process actor stimulus d v outs result running reaction publish =>
      cases reaction with
      | castVoteYes gv go =>
        exact idle rfl (decision_frame s actor coord _ _ _ rfl)
      | castVoteNo ha gv go =>
        exact idle rfl (decision_frame s actor coord _ _ _ rfl)
      | @coordCommit E participants ha quorum gd go =>
        subst actor
        have hb := decision_empty hr gd
        refine ⟨.decided E true,fun k => if k = E then some true else b k,
          ⟨SeqTwoPCStep.decide b E true hb,rfl⟩,ht,?_⟩
        exact sim_decision_update hr E true _ _ rfl
      | @coordAbort E participants ha gd go =>
        subst actor
        have hb := decision_empty hr gd
        refine ⟨.decided E false,fun k => if k = E then some false else b k,
          ⟨SeqTwoPCStep.decide b E false hb,rfl⟩,ht,?_⟩
        exact sim_decision_update hr E false _ _ rfl
    | @deliver msg rest d v outs result running take reaction publish =>
      rcases msg with ⟨tid,sender,actor,l,payload⟩
      cases reaction with
      | recvVoteYes ha =>
        exact idle rfl (decision_frame s actor coord _ _ _ rfl)
      | recvDecide authentic go =>
        exact idle rfl (decision_frame s actor coord _ _ _ rfl)
      | @recvVoteNo E _ _ ha gd go =>
        change actor = coord at ha
        subst actor
        have hb := decision_empty hr gd
        refine ⟨.decided E false,fun k => if k = E then some false else b k,
          ⟨SeqTwoPCStep.decide b E false hb,rfl⟩,ht,?_⟩
        exact sim_decision_update hr E false _ _ rfl
    | drop allowed take => exact idle rfl rfl
    | duplicate allowed present copy => exact idle rfl rfl
    | crash allowed running => exact idle rfl (decision_frame s _ coord _ _ _ rfl)
    | recover allowed crashed => exact idle rfl (decision_frame s _ coord _ _ _ rfl)

/-- Transport uniqueness of recorded coordinator decisions through the simulation. -/
theorem twoPC_safety_via_refinement (c : Config N) (coord : Member c) (fp : FaultProfile)
    {s : TwoPCState c} (hr : Foundation.Reachable (sys c coord fp) s) :
    ∀ k b₁ b₂, (s.nodes coord).durable.coordDecision k = some b₁ →
      (s.nodes coord).durable.coordDecision k = some b₂ → b₁ = b₂ := by
  apply (twoPC_refines_spec c coord fp).transfer_invariant
    (I := fun b => ∀ k b₁ b₂, b k = some b₁ → b k = some b₂ → b₁ = b₂)
    (J := fun s => ∀ k b₁ b₂, (s.nodes coord).durable.coordDecision k = some b₁ →
      (s.nodes coord).durable.coordDecision k = some b₂ → b₁ = b₂) (c := s)
  · intro b _ k b₁ b₂ h₁ h₂; exact Option.some.inj (h₁.symm.trans h₂)
  · intro s b rel safe k b₁ b₂ h₁ h₂
    exact safe k b₁ b₂ ((rel.2 k b₁).mpr h₁) ((rel.2 k b₂).mpr h₂)
  · exact hr

end Harmonia.VerifiedProtocols.TwoPhaseCommit
