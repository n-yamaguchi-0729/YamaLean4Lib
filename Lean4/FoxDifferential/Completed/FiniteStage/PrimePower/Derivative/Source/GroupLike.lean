import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Representatives
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedSource
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedTarget
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Limit
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Vector

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/Source/GroupLike.lean
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

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The completed source Fox derivative on a group-like element agrees with the prime-power
finite-stage derivative limit of the same word. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivative
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      finiteFoxStagePrimePowerDerivativeLimit
        (ℓ := ℓ) (X := X) N i
        (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w) := by
  simp only [primePowerCompletedGroupAlgebraFreeFoxDerivative, AddMonoidHom.coe_comp, Function.comp_apply,
  primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_of,
  finiteFoxStagePrimePowerDerivativeLimitAddHom_apply]

/-- Projection formula for the derivative limit of a group-like finite-stage source element. -/
@[simp]
theorem finiteFoxStagePrimePowerDerivativeLimit_sourceOf_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) (w : FreeGroup X) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
          (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)) =
      finiteFoxStageDerivative (X := X) N (ℓ ^ a) i w := by
  rw [finiteFoxStagePrimePowerDerivativeLimit_projection,
    finiteFoxStagePrimePowerSourceOf_projection,
    finiteFoxStageGroupAlgebraDerivative_of]

/-- Fundamental formula for a group-like finite-stage source element at one prime-power stage. -/
theorem finiteFoxStagePrimePowerDerivativeLimit_sourceOf_fundamental_formula
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1 =
      ∑ i : X,
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
              (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w))) *
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rw [finiteFoxStageDerivative_fundamental_formula (X := X) (N := N) (n := ℓ ^ a) w]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteFoxStagePrimePowerDerivativeLimit_sourceOf_projection]

/-- Projection formula for the completed source Fox derivative evaluated on a group-like element. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)) =
      finiteFoxStageDerivative (X := X) N (ℓ ^ a) i w := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative_of,
    finiteFoxStagePrimePowerDerivativeLimit_sourceOf_projection]

/-- The completed-target derivative of a group-like source element is the image of the
prime-power derivative limit in the completed target group algebra. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (finiteFoxStagePrimePowerDerivativeLimit
          (ℓ := ℓ) (X := X) N i
          (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget,
    AddMonoidHom.comp_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_of]

/-- Projection formula for the completed-target derivative evaluated on a group-like source
element. -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X)
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxStageDerivative (X := X) N (ℓ ^ j.1) i w) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget,
    AddMonoidHom.comp_apply,
    finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection]



end

end FoxDifferential
