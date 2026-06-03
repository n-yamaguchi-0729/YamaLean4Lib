import FoxDifferential.Completed.FiniteStage.BoundaryCycleHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/SemidirectCycles.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage semidirect boundary cycles

The completed density argument takes place in a semidirect product.  This file supplies the
matching finite-stage semidirect cycle sets and connects them to the coordinate statement
`ker ∂ = im D` from `BoundaryCycles.lean`.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite semidirect point `(Dq,1)` attached to a source-quotient element. -/
def finiteFoxStageSemidirectSourceKernelPoint
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    FiniteFoxStageSemidirect (X := X) N n :=
  { left := finiteFoxStageQuotientDerivativeVector (X := X) N n q,
    right := 1 }

@[simp]
theorem finiteFoxStageSemidirectSourceKernelPoint_left
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    (finiteFoxStageSemidirectSourceKernelPoint (X := X) N n q).left =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q :=
  rfl

@[simp]
theorem finiteFoxStageSemidirectSourceKernelPoint_right
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    (finiteFoxStageSemidirectSourceKernelPoint (X := X) N n q).right = 1 :=
  rfl

/-- The finite semidirect point `(Dw,1)` attached to a word. -/
def finiteFoxStageSemidirectKernelWordPoint (w : FreeGroup X) :
    FiniteFoxStageSemidirect (X := X) N n :=
  { left := finiteFoxStageDerivativeVector (X := X) N n w,
    right := 1 }

@[simp]
theorem finiteFoxStageSemidirectKernelWordPoint_left (w : FreeGroup X) :
    (finiteFoxStageSemidirectKernelWordPoint (X := X) N n w).left =
      finiteFoxStageDerivativeVector (X := X) N n w :=
  rfl

@[simp]
theorem finiteFoxStageSemidirectKernelWordPoint_right (w : FreeGroup X) :
    (finiteFoxStageSemidirectKernelWordPoint (X := X) N n w).right = 1 :=
  rfl

/-- Finite-stage boundary cycles as semidirect points `(v,1)` with `∂v = 0`. -/
def finiteFoxStageSemidirectBoundaryCycleSet [Fintype X] :
    Set (FiniteFoxStageSemidirect (X := X) N n) :=
  { y | y.right = 1 ∧
      y.left ∈ finiteFoxStageBoundaryCycleSubmodule (X := X) N n }

omit [DecidableEq X] in
@[simp]
theorem mem_finiteFoxStageSemidirectBoundaryCycleSet [Fintype X]
    {y : FiniteFoxStageSemidirect (X := X) N n} :
    y ∈ finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n ↔
      y.right = 1 ∧ y.left ∈ finiteFoxStageBoundaryCycleSubmodule (X := X) N n :=
  Iff.rfl

/-- Semidirect source-kernel derivative points in the finite stage. -/
def finiteFoxStageSemidirectSourceKernelDerivativeSet :
    Set (FiniteFoxStageSemidirect (X := X) N n) :=
  { y | ∃ q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n,
      finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q = 1 ∧
        finiteFoxStageSemidirectSourceKernelPoint (X := X) N n q = y }

/-- Semidirect kernel-word derivative points in the finite stage. -/
def finiteFoxStageSemidirectKernelWordDerivativeSet :
    Set (FiniteFoxStageSemidirect (X := X) N n) :=
  { y | ∃ w : FreeGroup X,
      w ∈ N ∧ finiteFoxStageSemidirectKernelWordPoint (X := X) N n w = y }

/-- Source-kernel semidirect points and honest kernel-word semidirect points coincide. -/
theorem finiteFoxStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet :
    finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n =
      finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N n := by
  ext y
  constructor
  · rintro ⟨q, hq, hy⟩
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
    have hwN : w ∈ N := by
      have hwq : QuotientGroup.mk' N w = 1 := by
        simpa only [finiteFoxCommutatorPowerQuotientMapToNormalQuotient_mk] using hq
      exact (QuotientGroup.eq_one_iff (N := N) w).1 hwq
    refine ⟨w, hwN, ?_⟩
    rw [← hy]
    apply FiniteFoxStageSemidirect.ext
    · exact (finiteFoxStageQuotientDerivativeVector_mk (X := X) N n w).symm
    · simp only [finiteFoxStageSemidirectKernelWordPoint, finiteFoxStageSemidirectSourceKernelPoint,
  QuotientGroup.mk'_apply]
  · rintro ⟨w, hwN, hy⟩
    refine ⟨QuotientGroup.mk'
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w, ?_, ?_⟩
    · rw [finiteFoxCommutatorPowerQuotientMapToNormalQuotient_mk]
      exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN
    · rw [← hy]
      apply FiniteFoxStageSemidirect.ext
      · exact finiteFoxStageQuotientDerivativeVector_mk (X := X) N n w
      · simp only [finiteFoxStageSemidirectSourceKernelPoint, QuotientGroup.mk'_apply,
  finiteFoxStageSemidirectKernelWordPoint]

/-- Every finite semidirect source-kernel derivative point is a semidirect boundary cycle. -/
theorem finiteFoxStageSemidirectSourceKernelDerivativeSet_subset_boundaryCycleSet
    [Fintype X] :
    finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n ⊆
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n := by
  intro y hy
  rcases hy with ⟨q, hq, hy⟩
  rw [← hy]
  constructor
  · simp only [finiteFoxStageSemidirectSourceKernelPoint]
  · exact finiteFoxStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule
      (X := X) N n ⟨q, hq, rfl⟩

/-- Every finite semidirect kernel-word derivative point is a semidirect boundary cycle. -/
theorem finiteFoxStageSemidirectKernelWordDerivativeSet_subset_boundaryCycleSet
    [Fintype X] :
    finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N n ⊆
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n := by
  rw [← finiteFoxStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet
    (X := X) N n]
  exact finiteFoxStageSemidirectSourceKernelDerivativeSet_subset_boundaryCycleSet
    (X := X) N n

/-- Semidirect finite-stage coverage: every semidirect boundary cycle is represented by a
source-kernel derivative point. -/
def finiteFoxStageSemidirectBoundaryCyclesCoveredBySourceKernel [Fintype X] : Prop :=
  finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n ⊆
    finiteFoxStageSemidirectSourceKernelDerivativeSet (X := X) N n

/-- The semidirect finite-stage coverage target is equivalent to the coordinate coverage target. -/
theorem finiteFoxStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
    [Fintype X] :
    finiteFoxStageSemidirectBoundaryCyclesCoveredBySourceKernel (X := X) N n ↔
      finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro hcover v hv
    have hy :
        ({ left := v, right := (1 : finiteFoxStageTargetQuotient (X := X) N) } :
          FiniteFoxStageSemidirect (X := X) N n) ∈
          finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n := by
      exact ⟨rfl, hv⟩
    rcases hcover hy with ⟨q, hq, hqy⟩
    refine ⟨q, hq, ?_⟩
    have hleft := congrArg (fun z : FiniteFoxStageSemidirect (X := X) N n => z.left) hqy
    simpa [finiteFoxStageSemidirectSourceKernelPoint] using hleft
  · intro hcover y hy
    rcases hy with ⟨hyright, hyleft⟩
    rcases hcover hyleft with ⟨q, hq, hqleft⟩
    refine ⟨q, hq, ?_⟩
    apply FiniteFoxStageSemidirect.ext
    · simpa [finiteFoxStageSemidirectSourceKernelPoint] using hqleft
    · simpa [finiteFoxStageSemidirectSourceKernelPoint] using hyright.symm

/-- Finite-stage coverage may equivalently be read with honest kernel words. -/
theorem finiteFoxStageSemidirectBoundaryCyclesCoveredByKernelWords_iff
    [Fintype X] :
    finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n ⊆
        finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N n ↔
      finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  rw [← finiteFoxStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet
    (X := X) N n]
  exact finiteFoxStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff (X := X) N n

end

end FoxDifferential
