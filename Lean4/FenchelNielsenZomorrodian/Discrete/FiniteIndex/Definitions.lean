import FenchelNielsenZomorrodian.Discrete.GroupTheory.DerivedSeries

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/FiniteIndex/Definitions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-index torsion-free subgroup data

Abstract finite-index and smooth quotient data, kernel transfer, normal core, and derived-length predicates for discrete Fuchsian groups.
-/

namespace FenchelNielsen

def SubgroupQuotientHasDerivedLengthAtMost {G : Type*} [Group G]
    (H : Subgroup G) (m : ℕ) : Prop :=
  derivedSeries G m ≤ H

def HasFiniteIndexTorsionFreeNormalSubgroupWithDerivedLengthAtMost
    (G : Type*) [Group G] (m : ℕ) : Prop :=
  ∃ H : Subgroup G,
    H.FiniteIndex ∧ H.Normal ∧ IsTorsionFreeGroup H ∧
      SubgroupQuotientHasDerivedLengthAtMost H m

def HasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost
    (G : Type*) [Group G] (m : ℕ) : Prop :=
  ∃ H : Subgroup G,
    H.FiniteIndex ∧ IsTorsionFreeGroup H ∧
      SubgroupQuotientHasDerivedLengthAtMost H m

theorem subgroupQuotientHasDerivedLengthAtMost_mono
    {G : Type*} [Group G] {H : Subgroup G} {m n : ℕ}
    (hmn : m ≤ n)
    (h : SubgroupQuotientHasDerivedLengthAtMost H m) :
    SubgroupQuotientHasDerivedLengthAtMost H n := by
  intro g hg
  exact h ((derivedSeries_antitone G hmn) hg)

theorem hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
    {G : Type*} [Group G] {m n : ℕ} (hmn : m ≤ n)
    (h : HasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost G m) :
    HasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost G n := by
  rcases h with ⟨H, hHFiniteIndex, hHTF, hHQuot⟩
  exact ⟨H, hHFiniteIndex, hHTF,
    subgroupQuotientHasDerivedLengthAtMost_mono hmn hHQuot⟩

end FenchelNielsen
