import FoxDifferential.Completed.FiniteStage.SemidirectCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/BoundarySubgroups.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage semidirect cycle subgroups

The completed density argument is formulated inside a semidirect product.  This file upgrades the
finite-stage semidirect cycle sets from raw sets to actual subgroups, so the finite approximation
step can be expressed as subgroup inclusion and quotient-kernel data.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Finite semidirect boundary cycles form a subgroup. -/
def finiteFoxStageSemidirectBoundaryCycleSubgroup [Fintype X] :
    Subgroup (FiniteFoxStageSemidirect (X := X) N n) where
  carrier := finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n
  one_mem' := by
    constructor
    · simp only [FiniteFoxStageSemidirect.one_right]
    · exact (finiteFoxStageBoundaryCycleSubmodule (X := X) N n).zero_mem
  mul_mem' := by
    intro y z hy hz
    rcases hy with ⟨hyright, hyleft⟩
    rcases hz with ⟨hzright, hzleft⟩
    constructor
    · simp only [FiniteFoxStageSemidirect.mul_right, hyright, hzright, mul_one]
    · rw [FiniteFoxStageSemidirect.mul_left, hyright]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) 1 :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.one_def]
      rw [hone, one_smul]
      exact (finiteFoxStageBoundaryCycleSubmodule (X := X) N n).add_mem hyleft hzleft
  inv_mem' := by
    intro y hy
    rcases hy with ⟨hyright, hyleft⟩
    constructor
    · simp only [FiniteFoxStageSemidirect.inv_right, hyright, inv_one]
    · rw [FiniteFoxStageSemidirect.inv_left, hyright, inv_one]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) 1 :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.one_def]
      rw [hone, one_smul]
      exact (finiteFoxStageBoundaryCycleSubmodule (X := X) N n).neg_mem hyleft

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageSemidirectBoundaryCycleSubgroup_coe [Fintype X] :
    ((finiteFoxStageSemidirectBoundaryCycleSubgroup (X := X) N n :
        Subgroup (FiniteFoxStageSemidirect (X := X) N n)) :
          Set (FiniteFoxStageSemidirect (X := X) N n)) =
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n :=
  rfl

/-- Source-kernel semidirect points are exactly points with right component `1` and left
component in the source-kernel derivative subgroup. -/
theorem finiteFoxStageSemidirectSourceKernelDerivativeSet_iff
    {y : FiniteFoxStageSemidirect (X := X) N n} :
    y ∈ finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n ↔
      y.right = 1 ∧
        y.left ∈ finiteFoxStageSourceKernelDerivativeSet (X := X) N n := by
  constructor
  · rintro ⟨q, hq, hqy⟩
    rw [← hqy]
    exact ⟨rfl, ⟨q, hq, rfl⟩⟩
  · rintro ⟨hyright, q, hq, hqleft⟩
    refine ⟨q, hq, ?_⟩
    apply FiniteFoxStageSemidirect.ext
    · exact hqleft
    · simpa [finiteFoxStageSemidirectSourceKernelPoint] using hyright.symm

/-- Finite source-kernel derivative semidirect points form a subgroup. -/
def finiteFoxStageSemidirectSourceKernelDerivativeSubgroup :
    Subgroup (FiniteFoxStageSemidirect (X := X) N n) where
  carrier :=
    { y | y.right = 1 ∧
        y.left ∈ finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n }
  one_mem' := by
    exact ⟨rfl, (finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n).zero_mem⟩
  mul_mem' := by
    intro y z hy hz
    rcases hy with ⟨hyright, hyleft⟩
    rcases hz with ⟨hzright, hzleft⟩
    constructor
    · simp only [FiniteFoxStageSemidirect.mul_right, hyright, hzright, mul_one]
    · rw [FiniteFoxStageSemidirect.mul_left, hyright]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) 1 :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.one_def]
      rw [hone, one_smul]
      exact
        (finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n).add_mem hyleft hzleft
  inv_mem' := by
    intro y hy
    rcases hy with ⟨hyright, hyleft⟩
    constructor
    · simp only [FiniteFoxStageSemidirect.inv_right, hyright, inv_one]
    · rw [FiniteFoxStageSemidirect.inv_left, hyright, inv_one]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) 1 :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.one_def]
      rw [hone, one_smul]
      exact (finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n).neg_mem hyleft

@[simp]
theorem finiteFoxStageSemidirectSourceKernelDerivativeSubgroup_coe :
    ((finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
        Subgroup (FiniteFoxStageSemidirect (X := X) N n)) :
          Set (FiniteFoxStageSemidirect (X := X) N n)) =
      finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n :=
  by
    ext y
    change
      (y.right = 1 ∧
          y.left ∈ finiteFoxStageSourceKernelDerivativeSet (X := X) N n) ↔
        y ∈ finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n
    exact (finiteFoxStageSemidirectSourceKernelDerivativeSet_iff (X := X) N n).symm

/-- The finite source-kernel derivative subgroup lies inside finite semidirect boundary cycles. -/
theorem finiteFoxStageSemidirectSourceKernelDerivativeSubgroup_le_boundaryCycleSubgroup
    [Fintype X] :
    finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n ≤
      finiteFoxStageSemidirectBoundaryCycleSubgroup (X := X) N n := by
  intro y hy
  have hyset :
      y ∈ finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n := by
    have hy' :
        y ∈ ((finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
          Subgroup (FiniteFoxStageSemidirect (X := X) N n)) :
            Set (FiniteFoxStageSemidirect (X := X) N n)) := hy
    rw [finiteFoxStageSemidirectSourceKernelDerivativeSubgroup_coe (X := X) N n] at hy'
    exact hy'
  exact finiteFoxStageSemidirectSourceKernelDerivativeSet_subset_boundaryCycleSet
    (X := X) N n hyset

/-- Semidirect finite-stage coverage is equivalently subgroup inclusion. -/
theorem finiteFoxStageSemiBoundaryCycleSubgroup_le_sourceKernelDerivSubgroup_iff_coord
    [Fintype X] :
    finiteFoxStageSemidirectBoundaryCycleSubgroup (X := X) N n ≤
        finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n ↔
      finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro hsub
    exact
      (finiteFoxStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff (X := X) N n).1
        (by
          intro y hy
          have hy' : y ∈ finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :=
            hsub hy
          have hyset :
              y ∈ ((finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
                Subgroup (FiniteFoxStageSemidirect (X := X) N n)) :
                  Set (FiniteFoxStageSemidirect (X := X) N n)) := hy'
          rw [finiteFoxStageSemidirectSourceKernelDerivativeSubgroup_coe (X := X) N n] at hyset
          exact hyset)
  · intro hcoord y hy
    have hyset :
        y ∈ finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n :=
      (finiteFoxStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff (X := X) N n).2
        hcoord hy
    change
      y ∈ ((finiteFoxStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
        Subgroup (FiniteFoxStageSemidirect (X := X) N n)) :
          Set (FiniteFoxStageSemidirect (X := X) N n))
    rw [finiteFoxStageSemidirectSourceKernelDerivativeSubgroup_coe (X := X) N n]
    exact hyset

end

end FoxDifferential
