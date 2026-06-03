import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.LimitMap
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Limit

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/CompletedSource.lean
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


/-- The completed source Fox derivative with values in the prime-power finite-stage target
limit. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivative
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N :=
  (finiteFoxStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i).comp
    (primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
      (ℓ := ℓ) (X := X) N hfinite)

/-- Projection formula for the completed source Fox derivative into the prime-power target
limit. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i z) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite a) z) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative,
    AddMonoidHom.comp_apply,
    finiteFoxStagePrimePowerDerivativeLimitAddHom_apply,
    finiteFoxStagePrimePowerDerivativeLimit_projection,
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_projection]

/-- The prime-power completed Fox derivative is uniquely determined by all finite-stage
projection formulas. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X)
    (f : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (hf : ∀ z a,
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (f z) =
        finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite a) z)) :
    f = primePowerCompletedGroupAlgebraFreeFoxDerivative
      (ℓ := ℓ) (X := X) N hfinite i := by
  apply AddMonoidHom.ext
  intro z
  apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a (f z) =
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i z)
  rw [hf, primePowerCompletedGroupAlgebraFreeFoxDerivative_projection]

/-- The finite-stage fundamental formula for the completed source Fox derivative after projection
to a prime-power stage. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_fundamental_formula_projection
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ a)
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite a) z) -
        algebraMap (ModNCompletedCoeff (ℓ ^ a))
          (finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N (ℓ ^ a)
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
                N hfinite a) z)) =
      ∑ i : X,
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (primePowerCompletedGroupAlgebraFreeFoxDerivative
              (ℓ := ℓ) (X := X) N hfinite i z)) *
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa [primePowerCompletedGroupAlgebraFreeFoxDerivative_projection,
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_projection] using
    (finiteFoxStagePrimePowerDerivativeLimit_fundamental_formula_projection
      (ℓ := ℓ) (X := X) N
      (primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite z) a)



end

end FoxDifferential
