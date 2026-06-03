import ProCGroups.NormalSubgroups.Framework

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/NormalSubgroups/MaximalIntersectionsAndSimpleRanks.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Closed normal subgroups and simple quotients

Develops normal-subgroup frameworks, maximal intersections, simple quotient ranks, compactness arguments, and algebraic comparison theorems.
-/

noncomputable section

open scoped Cardinal

namespace ProCGroups.NormalSubgroups

universe u

/-- A maximal normal subgroup gives a simple quotient. -/
theorem maximal_normal_intersection_simple_quotient
    {G : Type u} [Group G] (M : Subgroup G) [M.Normal]
    (hproper : M ≠ ⊤)
    (hmax : ∀ N : Subgroup G, N.Normal → M < N → N = ⊤) :
    IsSimpleGroup (G ⧸ M) := by
  have hnotTopLe : ¬ (⊤ : Subgroup G) ≤ M := by
    intro hle
    exact hproper (le_antisymm le_top hle)
  rcases SetLike.not_le_iff_exists.mp hnotTopLe with ⟨g, _hgTop, hgM⟩
  refine
    { exists_pair_ne := ⟨QuotientGroup.mk' M g, 1, ?_⟩
      eq_bot_or_eq_top_of_normal := ?_ }
  · intro hg
    exact hgM ((QuotientGroup.eq_one_iff g).mp (by simpa using hg))
  · intro H hH
    let N : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) H
    have hMN : M ≤ N := by
      dsimp [N]
      exact QuotientGroup.le_comap_mk' M H
    have hNnormal : N.Normal := by
      dsimp [N]
      infer_instance
    by_cases hNM : N = M
    · left
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      dsimp [N] at hNM
      rw [hNM]
      ext x
      simp only [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    · right
      have hMNlt : M < N := lt_of_le_of_ne hMN (by
        intro hMN'
        exact hNM hMN'.symm)
      have hNtop : N = ⊤ := hmax N hNnormal hMNlt
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      dsimp [N] at hNtop
      rw [hNtop, Subgroup.comap_top]

end ProCGroups.NormalSubgroups
