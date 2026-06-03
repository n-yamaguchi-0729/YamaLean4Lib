import FoxDifferential.Completed.FiniteStage.CoeffMap.BoundaryCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/TargetMap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Target-quotient refinement for finite-stage Fox boundary cycles

This file packages the functoriality in the normal subgroup variable of a finite Fox stage.
If `N ≤ M`, the quotient map `F/N → F/M` carries finite Fox boundary cycles and relation-word
points at the `N`-stage to the corresponding objects at the `M`-stage.  This is the finite target
refinement layer needed before taking cofinal systems of finite quotients.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M) (n : ℕ)

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageSemidirectMap_left
    (y : FiniteFoxStageSemidirect (X := X) N n) :
    (finiteFoxStageSemidirectMap (X := X) hNM n y).left =
      fun i : X => finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n (y.left i) :=
  rfl

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageSemidirectMap_right
    (y : FiniteFoxStageSemidirect (X := X) N n) :
    (finiteFoxStageSemidirectMap (X := X) hNM n y).right =
      finiteFoxStageTargetQuotientMap (X := X) hNM y.right :=
  rfl

  omit [DecidableEq X] in
/-- Target-quotient refinement commutes with the finite-stage Fox boundary. -/
  theorem finiteFoxStageFoxBoundary_targetMap
    [Fintype X]
    (v : finiteFoxStageCoordinateVector (X := X) N n) :
    finiteFoxStageFoxBoundary (X := X) M n
        (fun i : X => finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n (v i)) =
      finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageFoxBoundary (X := X) N n v) := by
  rw [finiteFoxStageFoxBoundary_apply, finiteFoxStageFoxBoundary_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_sub, finiteFoxStageTargetGroupAlgebraMap_of, map_one]

omit [DecidableEq X] in
/-- Target-quotient refinement sends finite boundary cycles to finite boundary cycles. -/
theorem finiteFoxStageBoundaryCycleSubmodule_targetMap_mem
    [Fintype X]
    {v : finiteFoxStageCoordinateVector (X := X) N n}
    (hv : v ∈ finiteFoxStageBoundaryCycleSubmodule (X := X) N n) :
    (fun i : X => finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n (v i)) ∈
      finiteFoxStageBoundaryCycleSubmodule (X := X) M n := by
  rw [mem_finiteFoxStageBoundaryCycleSubmodule]
  rw [finiteFoxStageFoxBoundary_targetMap (X := X) hNM n v]
  rw [mem_finiteFoxStageBoundaryCycleSubmodule] at hv
  rw [hv]
  exact map_zero _

omit [DecidableEq X] in
/-- Target-quotient refinement sends semidirect boundary-cycle points to boundary-cycle points. -/
theorem finiteFoxStageSemidirectMap_mem_boundaryCycleSet
    [Fintype X]
    {y : FiniteFoxStageSemidirect (X := X) N n}
    (hy : y ∈ finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n) :
    finiteFoxStageSemidirectMap (X := X) hNM n y ∈
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) M n := by
  rcases hy with ⟨hyright, hyboundary⟩
  constructor
  · rw [finiteFoxStageSemidirectMap_right]
    rw [hyright]
    exact map_one (finiteFoxStageTargetQuotientMap (X := X) hNM)
  · rw [finiteFoxStageSemidirectMap_left]
    exact finiteFoxStageBoundaryCycleSubmodule_targetMap_mem (X := X) hNM n hyboundary

/-- Target-quotient refinement sends finite kernel-word points to finite kernel-word points. -/
theorem finiteFoxStageSemidirectMap_kernelWordPoint
    (w : FreeGroup X) :
    finiteFoxStageSemidirectMap (X := X) hNM n
        (finiteFoxStageSemidirectKernelWordPoint (X := X) N n w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) M n w := by
  apply FiniteFoxStageSemidirect.ext
  · funext i
    change finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageDerivative (X := X) N n i w) =
      finiteFoxStageDerivative (X := X) M n i w
    exact finiteFoxStageDerivative_natural (X := X) hNM n i w
  · rw [finiteFoxStageSemidirectMap_right]
    simp only [finiteFoxStageSemidirectKernelWordPoint, map_one]

/-- Target-quotient refinement sends finite source-kernel semidirect points to source-kernel
semidirect points. -/
theorem finiteFoxStageSemidirectMap_sourceKernelPoint
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSemidirectMap (X := X) hNM n
        (finiteFoxStageSemidirectSourceKernelPoint (X := X) N n q) =
      finiteFoxStageSemidirectSourceKernelPoint (X := X) M n
        (finiteFoxStageSourceQuotientMap (X := X) hNM n q) := by
  rcases QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  apply FiniteFoxStageSemidirect.ext
  · funext i
    change finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageQuotientDerivativeVector (X := X) N n
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) i) =
      finiteFoxStageQuotientDerivativeVector (X := X) M n
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n) w) i
    rw [finiteFoxStageQuotientDerivativeVector_mk, finiteFoxStageQuotientDerivativeVector_mk]
    exact finiteFoxStageDerivative_natural (X := X) hNM n i w
  · simp only [finiteFoxStageSemidirectSourceKernelPoint, QuotientGroup.mk'_apply,
  finiteFoxStageSemidirectMap_right, map_one]

/-- Target refinement sends the finite semidirect kernel-word derivative set into the refined one. -/
theorem finiteFoxStageSemidirectMap_kernelWordDerivativeSet_subset :
    (fun y : FiniteFoxStageSemidirect (X := X) N n =>
        finiteFoxStageSemidirectMap (X := X) hNM n y) ''
      finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N n ⊆
        finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) M n := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨w, hwN, hzw⟩
  refine ⟨w, hNM hwN, ?_⟩
  rw [← hzw]
  exact (finiteFoxStageSemidirectMap_kernelWordPoint (X := X) hNM n w).symm

/-- Target refinement sends source-kernel derivative points into source-kernel derivative points. -/
theorem finiteFoxStageSemidirectMap_sourceKernelDerivativeSet_subset :
    (fun y : FiniteFoxStageSemidirect (X := X) N n =>
        finiteFoxStageSemidirectMap (X := X) hNM n y) ''
      finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n ⊆
        finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) M n := by
  rw [finiteFoxStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet (X := X) N n,
    finiteFoxStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet (X := X) M n]
  exact finiteFoxStageSemidirectMap_kernelWordDerivativeSet_subset (X := X) hNM n

end

end FoxDifferential
