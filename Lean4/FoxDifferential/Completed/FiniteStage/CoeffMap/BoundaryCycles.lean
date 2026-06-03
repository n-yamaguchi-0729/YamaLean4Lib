import FoxDifferential.Completed.FiniteStage.CoeffMap.Semidirect
import FoxDifferential.Completed.FiniteStage.CoeffMap.Boundary
import FoxDifferential.Completed.FiniteStage.SemidirectCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/CoeffMap/BoundaryCycles.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Coefficient reduction on finite semidirect boundary cycles

The completed-to-finite density route needs finite transition maps to preserve both sides of the
finite semidirect exactness statement.  This file packages that compatibility for coefficient
reduction: boundary-cycle points remain boundary-cycle points, and kernel-word points reduce to
the corresponding kernel-word points at the smaller modulus.
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

variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
@[simp]
theorem finiteFoxStageSemidirectCoeffMap_left
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (y : FiniteFoxStageSemidirect (X := X) N m₀) :
    (finiteFoxStageSemidirectCoeffMap (X := X) N hnm y).left =
      fun i : X => finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm (y.left i) :=
  rfl

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
@[simp]
theorem finiteFoxStageSemidirectCoeffMap_right
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (y : FiniteFoxStageSemidirect (X := X) N m₀) :
    (finiteFoxStageSemidirectCoeffMap (X := X) N hnm y).right = y.right :=
  rfl

omit [Fact (0 < m₀)] [DecidableEq X] [Fact (0 < n₀)] in
/-- Coefficient reduction by `dvd_rfl` is the identity on finite-stage semidirect targets. -/
@[simp]
theorem finiteFoxStageSemidirectCoeffMap_rfl
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    finiteFoxStageSemidirectCoeffMap
        (X := X) (n₀ := n₀) (m₀ := n₀) N dvd_rfl =
      MonoidHom.id (FiniteFoxStageSemidirect (X := X) N n₀) := by
  apply MonoidHom.ext
  intro y
  apply FiniteFoxStageSemidirect.ext
  · funext i
    change finiteFoxStageTargetGroupAlgebraCoeffMap
        (X := X) (n₀ := n₀) (m₀ := n₀) N dvd_rfl (y.left i) = y.left i
    rw [finiteFoxStageTargetGroupAlgebraCoeffMap_rfl]
    rfl
  · rfl

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Coefficient reductions compose on finite-stage semidirect targets. -/
@[simp]
theorem finiteFoxStageSemidirectCoeffMap_comp
    {k₀ : ℕ} [Fact (0 < k₀)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hnm : n₀ ∣ m₀) (hmk : m₀ ∣ k₀) :
    (finiteFoxStageSemidirectCoeffMap (X := X) N hnm).comp
        (finiteFoxStageSemidirectCoeffMap (X := X) N hmk) =
      finiteFoxStageSemidirectCoeffMap (X := X) N (dvd_trans hnm hmk) := by
  apply MonoidHom.ext
  intro y
  apply FiniteFoxStageSemidirect.ext
  · funext i
    change finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hmk (y.left i)) =
      finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N (dvd_trans hnm hmk) (y.left i)
    exact congrFun
      (congrArg DFunLike.coe
        (finiteFoxStageTargetGroupAlgebraCoeffMap_comp (X := X) N hnm hmk))
      (y.left i)
  · rfl

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Coefficient reduction carries finite semidirect boundary cycles to finite semidirect boundary
cycles. -/
theorem finiteFoxStageSemidirectCoeffMap_mem_boundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    {y : FiniteFoxStageSemidirect (X := X) N m₀}
    (hy : y ∈ finiteFoxStageSemidirectBoundaryCycleSet (X := X) N m₀) :
    finiteFoxStageSemidirectCoeffMap (X := X) N hnm y ∈
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n₀ := by
  rcases hy with ⟨hyright, hyboundary⟩
  constructor
  · simpa [finiteFoxStageSemidirectCoeffMap_right] using hyright
  · simpa [finiteFoxStageSemidirectCoeffMap_left] using
      finiteFoxStageBoundaryCycleSubmodule_coeffMap_mem
        (X := X) N hnm hyboundary

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Coefficient reduction sends the finite semidirect kernel-word point at modulus `m` to the
corresponding point at modulus `n`. -/
theorem finiteFoxStageSemidirectCoeffMap_kernelWordPoint
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (w : FreeGroup X) :
    finiteFoxStageSemidirectCoeffMap (X := X) N hnm
        (finiteFoxStageSemidirectKernelWordPoint (X := X) N m₀ w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) N n₀ w := by
  apply FiniteFoxStageSemidirect.ext
  · funext i
    change finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (finiteFoxStageDerivative (X := X) N m₀ i w) =
      finiteFoxStageDerivative (X := X) N n₀ i w
    exact finiteFoxStageDerivative_coeffMap (X := X) N hnm i w
  · rfl

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Coefficient reduction sends the finite semidirect kernel-word derivative set at modulus `m`
into the corresponding set at modulus `n`. -/
theorem finiteFoxStageSemidirectCoeffMap_kernelWordDerivativeSet_subset
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    (fun y : FiniteFoxStageSemidirect (X := X) N m₀ =>
        finiteFoxStageSemidirectCoeffMap (X := X) N hnm y) ''
      finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N m₀ ⊆
        finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N n₀ := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨w, hwN, hzw⟩
  refine ⟨w, hwN, ?_⟩
  rw [← hzw]
  exact (finiteFoxStageSemidirectCoeffMap_kernelWordPoint (X := X) N hnm w).symm

end

end FoxDifferential
