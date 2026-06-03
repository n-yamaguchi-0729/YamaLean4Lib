import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.SpecialValues

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/Source/Mul.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


omit [Fact (0 < ℓ)] in
/-- Product rule for the completed source Fox derivative on group-like source elements. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_of_mul
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (u v : FreeGroup X) :
      primePowerCompletedGroupAlgebraFreeFoxDerivative
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) (u * v)) =
      primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) +
        finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N u *
          primePowerCompletedGroupAlgebraFreeFoxDerivative
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative_of,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_of,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_of]
  simpa only [finiteFoxStagePrimePowerDerivativeLimitAddHom_apply] using
    (finiteFoxStagePrimePowerDerivativeLimit_sourceOf_mul
      (ℓ := ℓ) (X := X) N i u v)

omit [Fact (0 < ℓ)] in
/-- Product rule for the completed source Fox derivative when the source product is written in
the completed group algebra. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_of_mul_product
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (u v : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivative
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u *
          primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) =
      primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) +
        finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N u *
          primePowerCompletedGroupAlgebraFreeFoxDerivative
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) := by
  rw [← primePowerCompletedGroupAlgebraOf_mul (ell := ℓ) (H := FreeGroup X) u v]
  exact primePowerCompletedGroupAlgebraFreeFoxDerivative_of_mul
    (ℓ := ℓ) (X := X) N hfinite i u v

omit [Fact (0 < ℓ)] in
/-- Product rule for the completed-target Fox derivative on group-like source elements. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul
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
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) (u * v)) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) +
        primePowerCompletedGroupAlgebraOf (ell := ℓ)
          (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u) *
          primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) := by
  repeat rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget]
  simp only [AddMonoidHom.comp_apply]
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative_of_mul]
  rw [map_add, finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_mul,
    finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_targetOf]

omit [Fact (0 < ℓ)] in
/-- Product rule for the completed-target Fox derivative when the source product is written in
the completed group algebra. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul_product
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
        primePowerCompletedGroupAlgebraOf (ell := ℓ)
          (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u) *
          primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) := by
  rw [← primePowerCompletedGroupAlgebraOf_mul (ell := ℓ) (H := FreeGroup X) u v]
  exact primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul
    (ℓ := ℓ) (X := X) N hfinite i u v



end

end FoxDifferential
