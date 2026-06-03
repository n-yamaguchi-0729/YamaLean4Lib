import FoxDifferential.Completed.ProCIntegerCoefficients.FreeGroup.Coordinates

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/ProCIntegerCoefficients/FreeGroup/Fundamental.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebra coefficients

This module gives the free-group formulas for pro-\(C\) integer coefficients, used to compare completed Fox derivatives with ordinary finite-stage derivatives.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable (C : ProCGroups.FiniteGroupClass.{v})
variable {X : Type u} [DecidableEq X]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section FiniteBasis

variable [Fintype X]

/-- Boundary-map form of the completed Fox fundamental formula. -/
theorem zcFreeGroupFoxBoundary_derivativeVector
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcFreeGroupFoxBoundary C ψ (zcFreeGroupFoxDerivativeVector C ψ w) =
      zcCompletedGroupAlgebraBoundary C ψ w := by
  let beta : FreeGroup X → ZCCompletedGroupAlgebra C H :=
    fun w => zcFreeGroupFoxBoundary C ψ (zcFreeGroupFoxDerivativeVector C ψ w)
  have hbeta :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) beta :=
    IsCrossedDifferential.map_linear
      (zcFreeGroupFoxDerivativeVector_isCrossedDifferential C ψ)
      (zcFreeGroupFoxBoundary C ψ)
  have hbasis :
      ∀ x : X, beta (FreeGroup.of x) =
        zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x) := by
    intro x
    simp only [zcFreeGroupFoxDerivativeVector_of, zcFreeGroupFoxBoundary_single, beta]
  have hbeta_eq :
      beta =
        freeCrossedDifferentialWithCoeff
          (A := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraScalar C ψ)
          (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x)) := by
    exact freeCrossedDifferentialWithCoeff_unique
      (A := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)
      (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x))
      beta hbeta hbasis
  have hboundary_eq :
      zcCompletedGroupAlgebraBoundary C ψ =
        freeCrossedDifferentialWithCoeff
          (A := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraScalar C ψ)
          (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x)) := by
    exact freeCrossedDifferentialWithCoeff_unique
      (A := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)
      (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x))
      (zcCompletedGroupAlgebraBoundary C ψ)
      (zcCompletedGroupAlgebraBoundary_isCrossedDifferential C ψ)
      (by intro x; rfl)
  exact congrFun (hbeta_eq.trans hboundary_eq.symm) w

/-- Conditional completed Fox boundary formula.  Any completed crossed differential on a free
group with the standard basis values satisfies the completed Fox boundary formula. -/
theorem zcFreeGroupFoxBoundary_of_crossedDifferential
    (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcFreeGroupFoxBoundary C ψ (delta w) =
      zcCompletedGroupAlgebraBoundary C ψ w := by
  have hdelta_eq :
      delta = zcFreeGroupFoxDerivativeVector C ψ :=
    zcFreeGroupFoxDerivativeVector_unique C ψ delta hdelta hbasis
  rw [hdelta_eq]
  exact zcFreeGroupFoxBoundary_derivativeVector C ψ w

/-- Conditional completed Fox fundamental formula.  The finite Fox-Euler sum computed from any
completed crossed differential with standard basis values is `[ψ(w)] - 1`. -/
theorem zcFreeGroupFoxDerivative_fundamental_formula_of_crossedDifferential
    (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcCompletedGroupAlgebraBoundary C ψ w =
      ∑ i : X,
        delta w i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  simpa [zcFreeGroupFoxBoundary_apply] using
    (zcFreeGroupFoxBoundary_of_crossedDifferential C ψ delta hdelta hbasis w).symm

/-- Explicit `[ψ(w)] - 1` form of the conditional completed Fox-Euler formula. -/
theorem zcFreeGroupFoxDerivative_euler_formula_of_crossedDifferential
    (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcGroupLike C H (ψ w) - 1 =
      ∑ i : X,
        delta w i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  simpa [zcCompletedGroupAlgebraBoundary] using
    zcFreeGroupFoxDerivative_fundamental_formula_of_crossedDifferential
      C ψ delta hdelta hbasis w

/-- Completed Fox fundamental formula, also known as the completed Fox-Euler formula:
`[ψ(w)] - 1 = ∑ i, (∂w/∂x_i) ([ψ(x_i)] - 1)`. -/
theorem zcFreeGroupFoxDerivative_fundamental_formula
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcCompletedGroupAlgebraBoundary C ψ w =
      ∑ i : X,
        zcFreeGroupFoxDerivative C ψ i w *
          (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  simpa [zcFreeGroupFoxBoundary_apply, zcFreeGroupFoxDerivative] using
    (zcFreeGroupFoxBoundary_derivativeVector C ψ w).symm

/-- Explicit `[ψ(w)] - 1` form of the completed Fox-Euler formula. -/
theorem zcFreeGroupFoxDerivative_euler_formula
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcGroupLike C H (ψ w) - 1 =
      ∑ i : X,
        zcFreeGroupFoxDerivative C ψ i w *
          (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  simpa [zcCompletedGroupAlgebraBoundary] using
    zcFreeGroupFoxDerivative_fundamental_formula C ψ w


end FiniteBasis


end

end FoxDifferential
