import FoxDifferential.Completed.FiniteStage.TargetMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Bifiltered/Transition.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bifiltered finite Fox stage transitions

A finite Fox stage varies in two directions: the normal quotient `F/N` and the coefficient
modulus.  This file packages the combined transition

`(Z/mZ)[F/N]^X ⋊ F/N  ⟶  (Z/nZ)[F/M]^X ⋊ F/M`

for `N ≤ M` and `n ∣ m`.  This is the finite-stage interface needed for cofinal systems of
simultaneous target refinements and prime-power coefficient reductions.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)

/-- Combined coefficient/target transition on finite target group algebras. -/
def finiteFoxStageBifilteredTargetGroupAlgebraMap :
    finiteFoxStageTargetGroupAlgebra (X := X) N m →+*
      finiteFoxStageTargetGroupAlgebra (X := X) M n :=
  (finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n).comp
    (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
@[simp]
theorem finiteFoxStageBifilteredTargetGroupAlgebraMap_apply
    (x : finiteFoxStageTargetGroupAlgebra (X := X) N m) :
    finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm x =
      finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm x) :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- Evaluation of the bifiltered target-group-algebra transition on a represented word. -/
@[simp]
theorem finiteFoxStageBifilteredTargetGroupAlgebraMap_of
    (w : FreeGroup X) :
    finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) M) (QuotientGroup.mk' M w) := by
  rw [finiteFoxStageBifilteredTargetGroupAlgebraMap_apply]
  rw [finiteFoxStageTargetGroupAlgebraCoeffMap_of]
  rw [finiteFoxStageTargetGroupAlgebraMap_of]

/-- Combined coefficient/target transition on finite Fox coordinate vectors. -/
def finiteFoxStageBifilteredCoordinateVectorMap
    (v : finiteFoxStageCoordinateVector (X := X) N m) :
    finiteFoxStageCoordinateVector (X := X) M n :=
  fun i : X => finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm (v i)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- Combined coefficient/target transition commutes with the finite-stage Fox boundary. -/
theorem finiteFoxStageFoxBoundary_bifilteredMap
    [Fintype X]
    (v : finiteFoxStageCoordinateVector (X := X) N m) :
    finiteFoxStageFoxBoundary (X := X) M n
        (finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm v) =
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (finiteFoxStageFoxBoundary (X := X) N m v) := by
  calc
    finiteFoxStageFoxBoundary (X := X) M n
        (finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm v) =
      finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageFoxBoundary (X := X) N n
          (fun i : X => finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i))) := by
        exact finiteFoxStageFoxBoundary_targetMap (X := X) hNM n
          (fun i : X => finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i))
    _ = finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (finiteFoxStageFoxBoundary (X := X) N m v) := by
        rw [← finiteFoxStageFoxBoundary_coeffMap (X := X) N hnm v]
        rfl

/-- Combined coefficient/target transition on finite-stage semidirect Fox targets. -/
def finiteFoxStageBifilteredSemidirectMap :
    FiniteFoxStageSemidirect (X := X) N m →*
      FiniteFoxStageSemidirect (X := X) M n :=
  (finiteFoxStageSemidirectMap (X := X) hNM n).comp
    (finiteFoxStageSemidirectCoeffMap (X := X) N hnm)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
@[simp]
theorem finiteFoxStageBifilteredSemidirectMap_left
    (y : FiniteFoxStageSemidirect (X := X) N m) :
    (finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm y).left =
      finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm y.left :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
@[simp]
theorem finiteFoxStageBifilteredSemidirectMap_right
    (y : FiniteFoxStageSemidirect (X := X) N m) :
    (finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm y).right =
      finiteFoxStageTargetQuotientMap (X := X) hNM y.right :=
  rfl

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The combined transition sends kernel-word points to kernel-word points. -/
theorem finiteFoxStageBifilteredSemidirectMap_kernelWordPoint
    (w : FreeGroup X) :
    finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm
        (finiteFoxStageSemidirectKernelWordPoint (X := X) N m w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) M n w := by
  change finiteFoxStageSemidirectMap (X := X) hNM n
      (finiteFoxStageSemidirectCoeffMap (X := X) N hnm
        (finiteFoxStageSemidirectKernelWordPoint (X := X) N m w)) =
    finiteFoxStageSemidirectKernelWordPoint (X := X) M n w
  rw [finiteFoxStageSemidirectCoeffMap_kernelWordPoint]
  exact finiteFoxStageSemidirectMap_kernelWordPoint (X := X) hNM n w

end

end FoxDifferential
