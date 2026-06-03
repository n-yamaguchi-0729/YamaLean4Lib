import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Boundary
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Quotient/Fundamental.lean
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

/-- Finite-stage Fox fundamental formula on the finite source quotient. -/
theorem finiteFoxStageQuotientDerivative_fundamental_formula
    [Fintype X]
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageQuotientCoefficient (X := X) N n q - 1 =
      ∑ i : X,
        finiteFoxStageQuotientDerivative (X := X) N n i q *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rcases QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [finiteFoxStageQuotientCoefficient_mk]
  simp_rw [finiteFoxStageQuotientDerivative_mk]
  exact finiteFoxStageDerivative_fundamental_formula (X := X) N n w

/-- Boundary-map form of the finite-stage Fox fundamental formula on the finite source quotient. -/
theorem finiteFoxStageFoxBoundary_quotientDerivativeVector
    [Fintype X]
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageFoxBoundary (X := X) N n
        (finiteFoxStageQuotientDerivativeVector (X := X) N n q) =
      finiteFoxStageQuotientCoefficient (X := X) N n q - 1 := by
  rw [finiteFoxStageFoxBoundary_apply]
  simpa [finiteFoxStageQuotientDerivative] using
    (finiteFoxStageQuotientDerivative_fundamental_formula (X := X) N n q).symm

/-- Conditional finite-stage Fox boundary formula on the source quotient.  Any quotient-level
crossed differential with standard quotient-generator values satisfies the Fox boundary formula. -/
theorem finiteFoxStageFoxBoundary_quotient_of_crossedDifferential
    [Fintype X]
    (delta :
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →
        finiteFoxStageCoordinateVector (X := X) N n)
    (hdelta :
      IsCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) delta)
    (hbasis :
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageFoxBoundary (X := X) N n (delta q) =
      finiteFoxStageQuotientCoefficient (X := X) N n q - 1 := by
  have hdelta_eq :
      delta = finiteFoxStageQuotientDerivativeVector (X := X) N n :=
    finiteFoxStageQuotientDerivativeVector_unique (X := X) N n delta hdelta hbasis
  rw [hdelta_eq]
  exact finiteFoxStageFoxBoundary_quotientDerivativeVector (X := X) N n q

/-- Conditional finite-stage Fox fundamental formula on the source quotient. -/
theorem finiteFoxStageQuotientDerivative_fundamental_formula_of_crossedDifferential
    [Fintype X]
    (delta :
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →
        finiteFoxStageCoordinateVector (X := X) N n)
    (hdelta :
      IsCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) delta)
    (hbasis :
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageQuotientCoefficient (X := X) N n q - 1 =
      ∑ i : X,
        delta q i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa [finiteFoxStageFoxBoundary_apply] using
    (finiteFoxStageFoxBoundary_quotient_of_crossedDifferential
      (X := X) N n delta hdelta hbasis q).symm



end

end FoxDifferential
