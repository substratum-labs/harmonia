import Init.Data.List.Perm
namespace Harmonia.Distributed
universe u
structure Config (N : Type u) where
  members : List N
  distinct : members.Nodup

def Config.checked [DecidableEq N] (xs : List N) : Option (Config N) :=
  if h : xs.Nodup then some ⟨xs, h⟩ else none
abbrev Member (c : Config N) := { n : N // n ∈ c.members }
def Config.member? [DecidableEq N] (c : Config N) (n : N) : Option (Member c) :=
  if h : n ∈ c.members then some ⟨n, h⟩ else none

theorem Config.checked_rejects [DecidableEq N] (xs : List N) :
    Config.checked xs = none ↔ ¬ xs.Nodup := by
  unfold Config.checked
  split <;> simp_all

theorem Config.checked_preserves [DecidableEq N] {xs : List N} {c : Config N}
    (h : Config.checked xs = some c) : c.members = xs := by
  unfold Config.checked at h
  split at h
  · cases h; rfl
  · cases h

theorem member_configured (m : Member c) : m.val ∈ c.members := m.property
end Harmonia.Distributed
