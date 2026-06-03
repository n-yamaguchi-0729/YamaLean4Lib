import FoxDifferential.Completed.FiniteStage.Stage.Semidirect

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Lift.lean
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

/-- Semidirect-product lift defining the finite-stage Fox derivative. -/
def finiteFoxStageLift :
    FreeGroup X →* FiniteFoxStageSemidirect (X := X) N n :=
  FreeGroup.lift fun x =>
    { left := Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n)
      right := QuotientGroup.mk' N (FreeGroup.of x) }

/-- The right component of the finite-stage lift is the quotient class in `F/N`. -/
@[simp]
theorem finiteFoxStageLift_right (w : FreeGroup X) :
    (finiteFoxStageLift (X := X) N n w).right =
      QuotientGroup.mk' N w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [finiteFoxStageLift, QuotientGroup.mk'_apply, map_one, FiniteFoxStageSemidirect.one_right]
  | of x =>
      simp only [finiteFoxStageLift, QuotientGroup.mk'_apply, FreeGroup.lift_apply_of]
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, FiniteFoxStageSemidirect.mul_right, hx, QuotientGroup.mk'_apply, hy]

/-- Finite-stage Fox derivative vector of a free-group word. -/
def finiteFoxStageDerivativeVector (w : FreeGroup X) :
    finiteFoxStageCoordinateVector (X := X) N n :=
  (finiteFoxStageLift (X := X) N n w).left

/-- A coordinate of the finite-stage Fox derivative vector. -/
def finiteFoxStageDerivative (i : X) (w : FreeGroup X) :
    finiteFoxStageTargetGroupAlgebra (X := X) N n :=
  finiteFoxStageDerivativeVector (X := X) N n w i

/-- The coefficient map for the finite-stage Fox crossed differential. -/
def finiteFoxStageCoefficient :
    FreeGroup X →* finiteFoxStageTargetGroupAlgebra (X := X) N n :=
  (MonoidAlgebra.of (ModNCompletedCoeff n)
    (finiteFoxStageTargetQuotient (X := X) N)).comp (QuotientGroup.mk' N)

omit [DecidableEq X] in
/-- Evaluation formula for the finite-stage coefficient homomorphism. -/
@[simp]
theorem finiteFoxStageCoefficient_apply (w : FreeGroup X) :
    finiteFoxStageCoefficient (X := X) N n w =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) :=
  rfl


end

end FoxDifferential
