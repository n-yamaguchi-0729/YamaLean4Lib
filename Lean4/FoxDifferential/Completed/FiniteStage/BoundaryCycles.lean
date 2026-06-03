import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Fundamental

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/BoundaryCycles.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage Fox boundary cycles

This file packages the finite quotient algebra that sits below the completed density frontier.
For a normal subgroup `N ≤ FreeGroup X` and modulus `n`, the source quotient
`F / ([N,N] N^n)` carries a descended Fox derivative.  Its kernel over `F/N` gives a concrete
finite-stage relation-cycle subgroup inside the kernel of the finite Fox boundary
`∂ : R[F/N]^X → R[F/N]`.

The point of this file is to make the finite-stage exactness target explicit.  The completed
Crowell density step should be attacked by proving that every completed boundary cycle is detected
at finite stages and then approximated by these finite source-kernel derivatives.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite-stage Fox boundary-cycle submodule `ker ∂`. -/
def finiteFoxStageBoundaryCycleSubmodule [Fintype X] :
    Submodule (finiteFoxStageTargetGroupAlgebra (X := X) N n)
      (finiteFoxStageCoordinateVector (X := X) N n) :=
  LinearMap.ker (finiteFoxStageFoxBoundary (X := X) N n)

omit [DecidableEq X] in
@[simp]
theorem mem_finiteFoxStageBoundaryCycleSubmodule [Fintype X]
    {v : finiteFoxStageCoordinateVector (X := X) N n} :
    v ∈ finiteFoxStageBoundaryCycleSubmodule (X := X) N n ↔
      finiteFoxStageFoxBoundary (X := X) N n v = 0 :=
  Iff.rfl

/-- Quotient-level source-kernel derivatives in the finite stage.  These are the finite-stage
relation cycles coming from the kernel of `F/[N,N]N^n → F/N`. -/
def finiteFoxStageSourceKernelDerivativeSet :
    Set (finiteFoxStageCoordinateVector (X := X) N n) :=
  { v | ∃ q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n,
      finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q = 1 ∧
        finiteFoxStageQuotientDerivativeVector (X := X) N n q = v }

/-- Word-level kernel derivatives in the finite stage.  This is the algebraic form obtained from
actual relation words `w ∈ N`. -/
def finiteFoxStageKernelWordDerivativeSet :
    Set (finiteFoxStageCoordinateVector (X := X) N n) :=
  { v | ∃ w : FreeGroup X,
      w ∈ N ∧ finiteFoxStageDerivativeVector (X := X) N n w = v }

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageCoefficient_eq_one_of_mem
    {w : FreeGroup X} (hw : w ∈ N) :
    finiteFoxStageCoefficient (X := X) N n w = 1 := by
  rw [finiteFoxStageCoefficient_apply]
  have hq : QuotientGroup.mk' N w = 1 :=
    (QuotientGroup.eq_one_iff (N := N) w).2 hw
  rw [hq]
  rfl

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageQuotientCoefficient_eq_one_of_kernel
    {q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n}
    (hq : finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q = 1) :
    finiteFoxStageQuotientCoefficient (X := X) N n q = 1 := by
  rw [finiteFoxStageQuotientCoefficient_apply, hq]
  rfl

/-- Source-kernel derivatives form an additive subgroup of the finite coordinate module. -/
def finiteFoxStageSourceKernelDerivativeAddSubgroup :
    AddSubgroup (finiteFoxStageCoordinateVector (X := X) N n) where
  carrier := finiteFoxStageSourceKernelDerivativeSet (X := X) N n
  zero_mem' := by
    refine ⟨1, ?_, ?_⟩
    · simp only [map_one]
    · simp only [finiteFoxStageQuotientDerivativeVector_one]
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨q, hq, hqa⟩
    rcases hb with ⟨r, hr, hrb⟩
    refine ⟨q * r, ?_, ?_⟩
    · rw [map_mul, hq, hr, one_mul]
    · rw [finiteFoxStageQuotientDerivativeVector_mul]
      rw [finiteFoxStageQuotientCoefficient_eq_one_of_kernel (X := X) N n hq]
      simp only [hqa, hrb, one_smul]
  neg_mem' := by
    intro a ha
    rcases ha with ⟨q, hq, hqa⟩
    refine ⟨q⁻¹, ?_, ?_⟩
    · rw [map_inv, hq]
      simp only [inv_one]
    · rw [IsCrossedDifferential.inv
          (finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n)]
      have hcoeff :
          finiteFoxStageQuotientCoefficient (X := X) N n q⁻¹ = 1 := by
        apply finiteFoxStageQuotientCoefficient_eq_one_of_kernel (X := X) N n
        rw [map_inv, hq]
        simp only [inv_one]
      rw [hcoeff]
      simp only [hqa, one_smul]

@[simp]
theorem finiteFoxStageSourceKernelDerivativeAddSubgroup_coe :
    ((finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n :
        AddSubgroup (finiteFoxStageCoordinateVector (X := X) N n)) :
          Set (finiteFoxStageCoordinateVector (X := X) N n)) =
      finiteFoxStageSourceKernelDerivativeSet (X := X) N n :=
  rfl

/-- The quotient-level and word-level descriptions of finite-stage source-kernel derivatives
coincide. -/
theorem finiteFoxStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet :
    finiteFoxStageSourceKernelDerivativeSet (X := X) N n =
      finiteFoxStageKernelWordDerivativeSet (X := X) N n := by
  ext v
  constructor
  · rintro ⟨q, hq, hv⟩
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
    have hwN : w ∈ N := by
      have hwq : QuotientGroup.mk' N w = 1 := by
        simpa only [finiteFoxCommutatorPowerQuotientMapToNormalQuotient_mk] using hq
      exact (QuotientGroup.eq_one_iff (N := N) w).1 hwq
    refine ⟨w, hwN, ?_⟩
    simpa using hv
  · rintro ⟨w, hwN, hv⟩
    refine ⟨QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w, ?_, ?_⟩
    · rw [finiteFoxCommutatorPowerQuotientMapToNormalQuotient_mk]
      exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN
    · simpa [finiteFoxStageQuotientDerivativeVector_mk] using hv

/-- Word-level kernel derivatives form an additive subgroup, transported from the quotient-level
source-kernel subgroup. -/
def finiteFoxStageKernelWordDerivativeAddSubgroup :
    AddSubgroup (finiteFoxStageCoordinateVector (X := X) N n) :=
  finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n

@[simp]
theorem finiteFoxStageKernelWordDerivativeAddSubgroup_coe :
    ((finiteFoxStageKernelWordDerivativeAddSubgroup (X := X) N n :
        AddSubgroup (finiteFoxStageCoordinateVector (X := X) N n)) :
          Set (finiteFoxStageCoordinateVector (X := X) N n)) =
      finiteFoxStageKernelWordDerivativeSet (X := X) N n := by
  rw [finiteFoxStageKernelWordDerivativeAddSubgroup,
    finiteFoxStageSourceKernelDerivativeAddSubgroup_coe,
    finiteFoxStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet]

/-- Every finite-stage source-kernel derivative is a finite Fox boundary cycle. -/
theorem finiteFoxStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule
    [Fintype X] :
    finiteFoxStageSourceKernelDerivativeSet (X := X) N n ⊆
      (finiteFoxStageBoundaryCycleSubmodule (X := X) N n :
        Set (finiteFoxStageCoordinateVector (X := X) N n)) := by
  intro v hv
  rcases hv with ⟨q, hq, rfl⟩
  change finiteFoxStageFoxBoundary (X := X) N n
      (finiteFoxStageQuotientDerivativeVector (X := X) N n q) = 0
  rw [finiteFoxStageFoxBoundary_quotientDerivativeVector]
  rw [finiteFoxStageQuotientCoefficient_eq_one_of_kernel (X := X) N n hq]
  simp only [sub_self]

/-- The finite-stage exactness target: every finite Fox boundary cycle is represented by a
source-kernel derivative in `F/[N,N]N^n`. -/
def finiteFoxStageBoundaryCyclesCoveredBySourceKernel [Fintype X] : Prop :=
  (finiteFoxStageBoundaryCycleSubmodule (X := X) N n :
      Set (finiteFoxStageCoordinateVector (X := X) N n)) ⊆
    finiteFoxStageSourceKernelDerivativeSet (X := X) N n

/-- The finite-stage exactness target may equivalently be read using honest kernel words. -/
theorem finiteFoxStageBoundaryCyclesCoveredBySourceKernel_iff_words
    [Fintype X] :
    finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n ↔
      (finiteFoxStageBoundaryCycleSubmodule (X := X) N n :
          Set (finiteFoxStageCoordinateVector (X := X) N n)) ⊆
        finiteFoxStageKernelWordDerivativeSet (X := X) N n := by
  rw [finiteFoxStageBoundaryCyclesCoveredBySourceKernel,
    finiteFoxStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet]

/-- The finite-stage source-kernel derivative set is equal to `ker ∂` exactly when the reverse
coverage inclusion holds. -/
theorem finiteFoxStageSourceKernelDerivativeSet_eq_boundaryCycleSubmodule_iff
    [Fintype X] :
    finiteFoxStageSourceKernelDerivativeSet (X := X) N n =
        (finiteFoxStageBoundaryCycleSubmodule (X := X) N n :
          Set (finiteFoxStageCoordinateVector (X := X) N n)) ↔
      finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro h v hv
    rw [h]
    exact hv
  · intro h
    apply le_antisymm
    · exact finiteFoxStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule (X := X) N n
    · exact h

end

end FoxDifferential
