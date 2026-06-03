import FoxDifferential.Completed.DifferentialModule.TargetQuotient.StageMap
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/TargetQuotient/Fundamental.lean
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

/-- 素冪係数で定めた 群元から得られる group-like 元の写像が関手的写像が有限段階射影と両立することを述べる。 -/
theorem ppCompletedGAFoxDerivToTarget_of_fundFormula_map
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) - 1 =
      ∑ i : X,
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) *
          (primePowerCompletedGroupAlgebraMap
            (ℓ := ℓ) (G := FreeGroup X)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
              (FreeGroup.of i)) - 1) := by
  rw [primePowerCompletedGroupAlgebraMap_targetQuotient_of]
  simp_rw [primePowerCompletedGroupAlgebraMap_targetQuotient_of]
  exact ppCompletedGAFoxDerivToTarget_of_fundFormula
    (ℓ := ℓ) (X := X) N hfinite w

/-- 素冪係数で定めた 群元から得られる group-like 元の写像が関手的写像が有限段階射影と両立することを述べる。 -/
theorem ppCompletedGAFoxDerivToTarget_of_mul_product_map
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (u v : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u *
          primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) +
        primePowerCompletedGroupAlgebraMap
          (ℓ := ℓ) (G := FreeGroup X)
          (H := finiteFoxStageTargetQuotient (X := X) N)
          (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) *
          primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul_product,
    primePowerCompletedGroupAlgebraMap_targetQuotient_of]


end

end FoxDifferential
