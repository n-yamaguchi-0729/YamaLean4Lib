import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedTarget

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/Vector.lean
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

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The vector of all completed-target Fox derivatives, indexed by free generators. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      (X → PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N)) where
  toFun z i :=
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite i z
  map_zero' := by
    funext i
    exact map_zero
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i)
  map_add' z z' := by
    funext i
    exact map_add
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i) z z'

/-- Evaluation of the completed-target derivative vector at a coordinate. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (i : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite z i =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i z := rfl



end

end FoxDifferential
