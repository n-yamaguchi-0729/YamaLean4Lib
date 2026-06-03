import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Lift
import FoxDifferential.Completed.Residue.FreeGroup.Coordinates

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Rules.lean
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

/-- The finite-stage derivative vector sends the identity word to zero. -/
@[simp]
theorem finiteFoxStageDerivativeVector_one :
    finiteFoxStageDerivativeVector (X := X) N n (1 : FreeGroup X) = 0 := by
  simp only [finiteFoxStageDerivativeVector, finiteFoxStageLift, QuotientGroup.mk'_apply, map_one,
  FiniteFoxStageSemidirect.one_left]

/-- Component form of the identity rule for the finite-stage derivative. -/
@[simp]
theorem finiteFoxStageDerivative_one (i : X) :
    finiteFoxStageDerivative (X := X) N n i (1 : FreeGroup X) = 0 := by
  simp only [finiteFoxStageDerivative, finiteFoxStageDerivativeVector_one, Pi.zero_apply]

/-- The finite-stage derivative vector sends a free generator to the corresponding coordinate
basis vector. -/
@[simp]
theorem finiteFoxStageDerivativeVector_of (x : X) :
    finiteFoxStageDerivativeVector (X := X) N n (FreeGroup.of x) =
      Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) := by
  simp only [finiteFoxStageDerivativeVector, finiteFoxStageLift, QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of]

/-- Product rule for the finite-stage Fox derivative vector. -/
theorem finiteFoxStageDerivativeVector_mul (u v : FreeGroup X) :
    finiteFoxStageDerivativeVector (X := X) N n (u * v) =
      finiteFoxStageDerivativeVector (X := X) N n u +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u)) •
          finiteFoxStageDerivativeVector (X := X) N n v := by
  simp only [finiteFoxStageDerivativeVector, map_mul, FiniteFoxStageSemidirect.mul_left,
  finiteFoxStageLift_right, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply]

/-- Component form of the finite-stage Fox product rule. -/
theorem finiteFoxStageDerivative_mul (i : X) (u v : FreeGroup X) :
    finiteFoxStageDerivative (X := X) N n i (u * v) =
      finiteFoxStageDerivative (X := X) N n i u +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u)) *
          finiteFoxStageDerivative (X := X) N n i v := by
  simpa [finiteFoxStageDerivative, Pi.smul_apply] using
    congrFun (finiteFoxStageDerivativeVector_mul (X := X) N n u v) i

/-- The finite-stage Fox derivative vector is a crossed differential. -/
theorem finiteFoxStageDerivativeVector_isCrossedDifferential :
    IsCrossedDifferential
      (finiteFoxStageCoefficient (X := X) N n)
      (finiteFoxStageDerivativeVector (X := X) N n) := by
  intro u v
  exact finiteFoxStageDerivativeVector_mul (X := X) N n u v

/-- Uniqueness of the finite-stage Fox derivative vector among crossed differentials with the
standard coordinate values on free generators. -/
theorem finiteFoxStageDerivativeVector_unique
    (delta : FreeGroup X → finiteFoxStageCoordinateVector (X := X) N n)
    (hdelta :
      IsCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n)) :
    delta = finiteFoxStageDerivativeVector (X := X) N n := by
  have hdelta_free :=
    freeCrossedDifferentialWithCoeff_unique
      (A := finiteFoxStageCoordinateVector (X := X) N n)
      (finiteFoxStageCoefficient (X := X) N n)
      (fun x => Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
      delta hdelta hbasis
  have hstage_free :=
    freeCrossedDifferentialWithCoeff_unique
      (A := finiteFoxStageCoordinateVector (X := X) N n)
      (finiteFoxStageCoefficient (X := X) N n)
      (fun x => Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
      (finiteFoxStageDerivativeVector (X := X) N n)
      (finiteFoxStageDerivativeVector_isCrossedDifferential (X := X) N n)
      (finiteFoxStageDerivativeVector_of (X := X) N n)
  exact hdelta_free.trans hstage_free.symm

/-- Existence and uniqueness theorem for the finite-stage Fox derivative vector. -/
theorem existsUnique_finiteFoxStageDerivativeVector :
    ∃! delta : FreeGroup X → finiteFoxStageCoordinateVector (X := X) N n,
      IsCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) delta ∧
        ∀ x : X, delta (FreeGroup.of x) =
          Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) := by
  refine ⟨finiteFoxStageDerivativeVector (X := X) N n, ?_, ?_⟩
  · exact ⟨finiteFoxStageDerivativeVector_isCrossedDifferential (X := X) N n,
      finiteFoxStageDerivativeVector_of (X := X) N n⟩
  · intro delta hdelta
    exact finiteFoxStageDerivativeVector_unique (X := X) N n delta hdelta.1 hdelta.2

/-- Universal representation theorem for finite-stage crossed differentials on the free group.

Finite-stage crossed differentials with coefficient `finiteFoxStageCoefficient` are represented
by linear maps out of the universal crossed-differential module for that coefficient. -/
def finiteFoxStageCrossedDifferentialEquivLinearMap :
    {delta : FreeGroup X → finiteFoxStageCoordinateVector (X := X) N n //
      IsCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) delta} ≃
      (CrossedDifferentialModule (finiteFoxStageCoefficient (X := X) N n) →ₗ[
        finiteFoxStageTargetGroupAlgebra (X := X) N n]
        finiteFoxStageCoordinateVector (X := X) N n) :=
  crossedDifferentialModuleEquivLinearMap
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageCoefficient (X := X) N n)

/-- The linear map from the finite-stage universal crossed-differential module representing the
finite-stage Fox derivative vector. -/
def finiteFoxStageDerivativeVectorLinearMap :
    CrossedDifferentialModule (finiteFoxStageCoefficient (X := X) N n) →ₗ[
      finiteFoxStageTargetGroupAlgebra (X := X) N n]
      finiteFoxStageCoordinateVector (X := X) N n :=
  crossedDifferentialModuleLift
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageCoefficient (X := X) N n)
    (finiteFoxStageDerivativeVector (X := X) N n)
    (finiteFoxStageDerivativeVector_isCrossedDifferential (X := X) N n)

/-- The finite-stage derivative-vector linear map evaluates on the universal differential as the
finite-stage Fox derivative vector. -/
@[simp]
theorem finiteFoxStageDerivativeVectorLinearMap_universal (w : FreeGroup X) :
    finiteFoxStageDerivativeVectorLinearMap (X := X) N n
        (universalCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) w) =
      finiteFoxStageDerivativeVector (X := X) N n w := by
  exact crossedDifferentialModuleLift_universal
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageCoefficient (X := X) N n)
    (finiteFoxStageDerivativeVector (X := X) N n)
    (finiteFoxStageDerivativeVector_isCrossedDifferential (X := X) N n) w

/-- Existence and uniqueness of the linear map representing the finite-stage Fox derivative
vector. -/
theorem existsUnique_finiteFoxStageDerivativeVectorLinearMap :
    ∃! f :
        CrossedDifferentialModule (finiteFoxStageCoefficient (X := X) N n) →ₗ[
          finiteFoxStageTargetGroupAlgebra (X := X) N n]
          finiteFoxStageCoordinateVector (X := X) N n,
      ∀ w : FreeGroup X,
        f (universalCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) w) =
          finiteFoxStageDerivativeVector (X := X) N n w := by
  exact existsUnique_crossedDifferentialModuleLift
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageCoefficient (X := X) N n)
    (finiteFoxStageDerivativeVector (X := X) N n)
    (finiteFoxStageDerivativeVector_isCrossedDifferential (X := X) N n)

/-- The finite-stage Fox derivative vector is the free crossed differential with coordinate
basis values. -/
theorem finiteFoxStageDerivativeVector_eq_freeCrossedDifferentialWithCoeff :
    finiteFoxStageDerivativeVector (X := X) N n =
      freeCrossedDifferentialWithCoeff
        (A := finiteFoxStageCoordinateVector (X := X) N n)
        (finiteFoxStageCoefficient (X := X) N n)
        (fun x => Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n)) := by
  exact freeCrossedDifferentialWithCoeff_unique
    (A := finiteFoxStageCoordinateVector (X := X) N n)
    (finiteFoxStageCoefficient (X := X) N n)
    (fun x => Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
    (finiteFoxStageDerivativeVector (X := X) N n)
    (finiteFoxStageDerivativeVector_isCrossedDifferential (X := X) N n)
    (finiteFoxStageDerivativeVector_of (X := X) N n)

/-- The finite-stage derivative is exactly the residue free Fox derivative for the quotient map
`FreeGroup X -> F/N`. -/
theorem finiteFoxStageDerivativeVector_eq_residueFreeGroupFoxDerivativeVector :
    finiteFoxStageDerivativeVector (X := X) N n =
      residueFreeGroupFoxDerivativeVector n (QuotientGroup.mk' N) := by
  rw [finiteFoxStageDerivativeVector_eq_freeCrossedDifferentialWithCoeff]
  rfl

/-- For a finite free basis, finite-stage derivative-vector zero is the same as zero of the
residue universal differential. -/
theorem finiteFoxStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
    [Fintype X] (w : FreeGroup X) :
    finiteFoxStageDerivativeVector (X := X) N n w = 0 ↔
      residueUniversalDifferential n (QuotientGroup.mk' N) w = 0 := by
  rw [finiteFoxStageDerivativeVector_eq_residueFreeGroupFoxDerivativeVector]
  constructor
  · intro h
    rw [← residueFreeFoxCoordinatesLinearMap_derivativeVector
      n (QuotientGroup.mk' N) w, h, map_zero]
  · intro h
    rw [← residueDifferentialToFreeFoxCoordinates_universal
      n (QuotientGroup.mk' N) w, h, map_zero]

end

end FoxDifferential
