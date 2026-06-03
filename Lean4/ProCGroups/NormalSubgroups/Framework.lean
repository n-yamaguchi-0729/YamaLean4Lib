import ProCGroups.FreeProC.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/NormalSubgroups/Framework.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Closed normal subgroups

Develops the normal-subgroup predicates used by the later compactness and algebraic comparison
arguments.
-/

noncomputable section

namespace ProCGroups

universe u

/-- A group is noncommutative when its abstract commutator subgroup is nontrivial. -/
def IsNoncommutativeGroup (G : Type u) [Group G] : Prop :=
  commutator G ≠ ⊥

namespace NormalSubgroups

/-- The closed normal closure of a subset as a universal closed normal subgroup. -/
def IsClosedNormalClosure {G : Type u} [Group G] [TopologicalSpace G]
    (S : Set G) (N : Subgroup G) : Prop :=
  N.Normal ∧ IsClosed (N : Set G) ∧ S ⊆ N ∧
    ∀ M : Subgroup G, M.Normal → IsClosed (M : Set G) → S ⊆ M → N ≤ M

/-- A subgroup is perfect when it is equal to its abstract commutator subgroup. -/
def IsPerfectSubgroup {G : Type u} [Group G] (K : Subgroup G) : Prop :=
  ⁅K, K⁆ = K

end NormalSubgroups
end ProCGroups
