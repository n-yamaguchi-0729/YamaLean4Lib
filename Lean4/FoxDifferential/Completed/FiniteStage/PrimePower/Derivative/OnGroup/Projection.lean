import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.SpecialValues

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/OnGroup/Projection.lean
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


omit [Fact (0 < ℓ)] in
/-- Generator-value projection formula for the completed source Fox derivative. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_generator_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i j : X) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
            (FreeGroup.of j))) =
      ((Pi.single j (1 : finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
        X → finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection]
  change finiteFoxStageDerivativeVector (X := X) N (ℓ ^ a) (FreeGroup.of j) i =
    ((Pi.single j (1 : finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
      X → finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i
  rw [finiteFoxStageDerivativeVector_of]




end

end FoxDifferential
