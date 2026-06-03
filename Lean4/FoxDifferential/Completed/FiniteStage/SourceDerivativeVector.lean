import FoxDifferential.Completed.FiniteStage.SourceBoundary

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/SourceDerivativeVector.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Source-valued finite Fox derivative vectors

This file separates the source-coordinate Fox calculus from the target-coordinate finite stage.
The source quotient `F / ([N,N]N^n)` has its own group-algebra coefficients.  The derivative
vector with these coefficients has boundary exactly `s - 1`; applying the source-to-target
coordinate map recovers the already existing target-valued finite derivative.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Source-valued derivative vector of a source quotient element. -/
def finiteFoxStageSourceDerivativeVector
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceCoordinateVector (X := X) N n :=
  fun i =>
    finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)

omit [N.Normal] in
@[simp]
theorem finiteFoxStageSourceDerivativeVector_apply
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (i : X) :
    finiteFoxStageSourceDerivativeVector (X := X) N n q i =
      finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) :=
  rfl

/-- Source-valued derivative vector of an arbitrary source group-algebra element. -/
def finiteFoxStageSourceGroupAlgebraDerivativeVector :
    finiteFoxStageSourceGroupAlgebra (X := X) N n →ₗ[ModNCompletedCoeff n]
      finiteFoxStageSourceCoordinateVector (X := X) N n where
  toFun x := fun i => finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x
  map_add' := by
    intro x y
    funext i
    simp only [map_add, Pi.add_apply]
  map_smul' := by
    intro a x
    funext i
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply]

omit [N.Normal] in
@[simp]
theorem finiteFoxStageSourceGroupAlgebraDerivativeVector_apply
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) (i : X) :
    finiteFoxStageSourceGroupAlgebraDerivativeVector (X := X) N n x i =
      finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x :=
  rfl

omit [N.Normal] in
/-- The source boundary of the source-valued derivative of a source quotient element is `q - 1`. -/
theorem finiteFoxStageSourceFoxBoundary_sourceDerivativeVector
    [Fintype X]
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceFoxBoundary (X := X) N n
        (finiteFoxStageSourceDerivativeVector (X := X) N n q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1 := by
  rw [finiteFoxStageSourceFoxBoundary_apply]
  exact (finiteFoxStageSourceGroupAlgebraDerivative_of_quotient_fundamental_formula
    (X := X) (N := N) (n := n) q).symm

omit [N.Normal] in
/-- The source boundary of the source-valued derivative of a group-algebra element is the usual
source augmentation formula. -/
theorem finiteFoxStageSourceFoxBoundary_sourceGroupAlgebraDerivativeVector
    [Fintype X]
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) :
    finiteFoxStageSourceFoxBoundary (X := X) N n
        (finiteFoxStageSourceGroupAlgebraDerivativeVector (X := X) N n x) =
      x -
        algebraMap (ModNCompletedCoeff n)
          (finiteFoxStageSourceGroupAlgebra (X := X) N n)
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) := by
  rw [finiteFoxStageSourceFoxBoundary_apply]
  exact (finiteFoxStageSourceGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    (X := X) (N := N) (n := n) x).symm

omit [DecidableEq X] in
/-- The source-to-target coordinate map commutes with source scalar multiplication. -/
theorem finiteFoxStageCoordinateSourceToTarget_smul_source
    (a : finiteFoxStageSourceGroupAlgebra (X := X) N n)
    (v : finiteFoxStageSourceCoordinateVector (X := X) N n) :
    finiteFoxStageCoordinateSourceToTarget (X := X) N n (a • v) =
      finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a •
        finiteFoxStageCoordinateSourceToTarget (X := X) N n v := by
  funext i
  rw [finiteFoxStageCoordinateSourceToTarget_apply]
  simp only [Pi.smul_apply, finiteFoxStageCoordinateSourceToTarget_apply]
  change
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a * v i) =
      finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a *
        finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (v i)
  rw [RingHom.map_mul]

/-- Applying source-to-target coordinates to a source derivative vector gives the target-valued
finite derivative vector. -/
theorem finiteFoxStageCoordinateSourceToTarget_sourceDerivativeVector
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageCoordinateSourceToTarget (X := X) N n
        (finiteFoxStageSourceDerivativeVector (X := X) N n q) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q := by
  funext i
  rw [finiteFoxStageCoordinateSourceToTarget_apply,
    finiteFoxStageSourceDerivativeVector_apply]
  rw [finiteFoxStageSourceGroupAlgebraDerivative_map_of_quotient,
    finiteFoxStageGroupAlgebraDerivative_of_quotient]
  rfl

/-- Applying source-to-target coordinates to the group-algebra source derivative vector gives the
coordinatewise target group-algebra derivative. -/
theorem finiteFoxStageCoordinateSourceToTarget_sourceGroupAlgebraDerivativeVector
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) :
    finiteFoxStageCoordinateSourceToTarget (X := X) N n
        (finiteFoxStageSourceGroupAlgebraDerivativeVector (X := X) N n x) =
      fun i => finiteFoxStageGroupAlgebraDerivative (X := X) N n i x := by
  funext i
  rw [finiteFoxStageCoordinateSourceToTarget_apply,
    finiteFoxStageSourceGroupAlgebraDerivativeVector_apply]
  exact finiteFoxStageSourceGroupAlgebraDerivative_map
    (X := X) (N := N) (n := n) i x

end

end FoxDifferential
