import FoxDifferential.Completed.DifferentialModule.TargetQuotient.Fundamental

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/TargetQuotient/MulProjection.lean
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

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]

/-- 素冪係数で定めた 標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_mul_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (x y : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i (x * y)) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := FreeGroup X)
          (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
            (ℓ := ℓ) (X := X) N hfinite j.1)
          (primePowerCompletedGroupAlgebraAugmentation
            (ℓ := ℓ) (G := FreeGroup X) y) •
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i x) +
      primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraMap
            (ℓ := ℓ) (G := FreeGroup X)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) x) *
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i y) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection,
    primePowerCompletedGroupAlgebraProjection_mul]
  change
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ j.1) i
          ((primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
              (ℓ := ℓ) (X := X) N hfinite j.1) x) *
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1) y))) =
      _
  rw [finiteFoxStageGroupAlgebraDerivative_mul]
  rw [map_add, map_mul]
  rw [show
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
          (finiteFoxStageTargetQuotient (X := X) N) j.2
          (finiteFoxCommutatorPowerGroupAlgebraMap
            (F := FreeGroup X) N (ℓ ^ j.1)
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1) x)) =
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraMap
            (ℓ := ℓ) (G := FreeGroup X)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) x) by
      rw [primePowerCompletedGAProj_map_targetQuotient_eq_freeDerivativeSource]]
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection]
  rw [finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_projection_eq_completed
    (ℓ := ℓ) (X := X) N hfinite y j.1]
  rw [Algebra.smul_def, map_mul, modNCompletedGroupAlgebraStageMap_algebraMap,
    ← Algebra.smul_def]


end

end FoxDifferential
