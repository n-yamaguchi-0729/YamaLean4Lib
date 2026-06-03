import FoxDifferential.Completed.FiniteStage.CoeffMap.Target
import FoxDifferential.Completed.FiniteStage.BoundaryCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/CoeffMap/Boundary.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Coefficient reduction and finite-stage Fox boundaries

This file records the finite-stage boundary compatibility that is needed when completed Fox
cycles are projected to finite coefficient stages.  It is the finite algebraic formula behind
`∂_n(π_n v) = π_n(∂_m v)`.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
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
/-- Coefficient reduction commutes with the finite-stage Fox boundary map. -/
theorem finiteFoxStageFoxBoundary_coeffMap
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (v : finiteFoxStageCoordinateVector (X := X) N m₀) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (finiteFoxStageFoxBoundary (X := X) N m₀ v) =
      finiteFoxStageFoxBoundary (X := X) N n₀
        (fun i : X =>
          finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i)) := by
  rw [finiteFoxStageFoxBoundary_apply, finiteFoxStageFoxBoundary_apply]
  simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, map_sum, map_mul, map_sub,
  finiteFoxStageTargetGroupAlgebraCoeffMap_single_apply, map_one]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- A vector is a boundary cycle after coefficient reduction whenever it was one before reduction. -/
theorem finiteFoxStageBoundaryCycleSubmodule_coeffMap_mem
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    {v : finiteFoxStageCoordinateVector (X := X) N m₀}
    (hv : v ∈ finiteFoxStageBoundaryCycleSubmodule (X := X) N m₀) :
    (fun i : X =>
        finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i)) ∈
      finiteFoxStageBoundaryCycleSubmodule (X := X) N n₀ := by
  rw [mem_finiteFoxStageBoundaryCycleSubmodule]
  rw [← finiteFoxStageFoxBoundary_coeffMap (X := X) N hnm v]
  rw [mem_finiteFoxStageBoundaryCycleSubmodule] at hv
  rw [hv]
  exact map_zero _

end

end FoxDifferential
