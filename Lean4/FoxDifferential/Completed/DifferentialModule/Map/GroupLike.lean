import FoxDifferential.Completed.DifferentialModule.Map.Limit

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/Map/GroupLike.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed differential modules

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for primePowerCompletedGroupAlgebraMap_of. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_of
    (ψ : ContinuousMonoidHom G H) (g : G) :
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := G) g) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := H) (ψ g) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
      (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := G) g)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := H) (ψ g))
  rw [primePowerCompletedGroupAlgebraProjection_map,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraMapStage_of,
    primePowerCompletedGroupAlgebraProjection_of]
  rfl


end

end FoxDifferential
