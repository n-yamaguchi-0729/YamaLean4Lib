import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Quotient/Universal.lean
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

/-- Universal representation theorem for descended finite-stage crossed differentials on the
finite source quotient.

Crossed differentials on `F/[N,N]N^n` with coefficient `finiteFoxStageQuotientCoefficient` are
represented by linear maps out of the universal crossed-differential module for that quotient
coefficient. -/
def finiteFoxStageQuotientCrossedDifferentialEquivLinearMap :
    {delta :
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →
          finiteFoxStageCoordinateVector (X := X) N n //
      IsCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) delta} ≃
      (CrossedDifferentialModule (finiteFoxStageQuotientCoefficient (X := X) N n) →ₗ[
        finiteFoxStageTargetGroupAlgebra (X := X) N n]
        finiteFoxStageCoordinateVector (X := X) N n) :=
  crossedDifferentialModuleEquivLinearMap
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageQuotientCoefficient (X := X) N n)

/-- The linear map from the quotient universal crossed-differential module representing the
descended finite-stage Fox derivative vector. -/
def finiteFoxStageQuotientDerivativeVectorLinearMap :
    CrossedDifferentialModule (finiteFoxStageQuotientCoefficient (X := X) N n) →ₗ[
      finiteFoxStageTargetGroupAlgebra (X := X) N n]
      finiteFoxStageCoordinateVector (X := X) N n :=
  crossedDifferentialModuleLift
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageQuotientCoefficient (X := X) N n)
    (finiteFoxStageQuotientDerivativeVector (X := X) N n)
    (finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n)

/-- The quotient derivative-vector linear map evaluates on the universal differential as the
descended finite-stage Fox derivative vector. -/
@[simp]
theorem finiteFoxStageQuotientDerivativeVectorLinearMap_universal
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageQuotientDerivativeVectorLinearMap (X := X) N n
        (universalCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) q) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q := by
  exact crossedDifferentialModuleLift_universal
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageQuotientCoefficient (X := X) N n)
    (finiteFoxStageQuotientDerivativeVector (X := X) N n)
    (finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n) q

/-- Existence and uniqueness of the linear map representing the descended finite-stage Fox
derivative vector on the finite source quotient. -/
theorem existsUnique_finiteFoxStageQuotientDerivativeVectorLinearMap :
    ∃! f :
        CrossedDifferentialModule (finiteFoxStageQuotientCoefficient (X := X) N n) →ₗ[
          finiteFoxStageTargetGroupAlgebra (X := X) N n]
          finiteFoxStageCoordinateVector (X := X) N n,
      ∀ q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n,
        f (universalCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) q) =
          finiteFoxStageQuotientDerivativeVector (X := X) N n q := by
  exact existsUnique_crossedDifferentialModuleLift
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageQuotientCoefficient (X := X) N n)
    (finiteFoxStageQuotientDerivativeVector (X := X) N n)
    (finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n)



end

end FoxDifferential
