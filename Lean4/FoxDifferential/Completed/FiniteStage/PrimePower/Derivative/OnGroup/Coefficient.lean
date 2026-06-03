import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.SpecialValues

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/OnGroup/Coefficient.lean
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


/-- The completed target coefficient homomorphism associated to the quotient
`FreeGroup X → finiteFoxStageTargetQuotient N`.

It sends a word to the corresponding group-like element of the prime-power completed group
algebra of the target quotient. -/
def finiteFoxStageTargetPrimePowerCompletedCoefficientHom
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)] :
    FreeGroup X →*
      PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N) where
  toFun w :=
    primePowerCompletedGroupAlgebraOf (ell := ℓ)
      (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)
  map_one' := by
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one, primePowerCompletedGroupAlgebraOf_one]
  map_mul' u v := by
    rw [← primePowerCompletedGroupAlgebraOf_mul (ell := ℓ)
      (H := finiteFoxStageTargetQuotient (X := X) N)]
    rfl

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation formula for the completed target coefficient homomorphism. -/
@[simp]
theorem finiteFoxStageTargetPrimePowerCompletedCoefficientHom_apply
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)] (w : FreeGroup X) :
    finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N w =
      primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := rfl




end

end FoxDifferential
