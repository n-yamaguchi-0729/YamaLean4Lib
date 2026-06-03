import FoxDifferential.Completed.Residue.FreeGroup.Boundary

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Residue/FreeGroup/Fundamental.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Residue coefficient stages

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable {X : Type u} {H : Type v} [Group H] [DecidableEq X]

section FiniteBasis

variable [Fintype X]

/-- Boundary-map form of the residue Fox fundamental formula. -/
theorem residueFreeGroupFoxBoundary_derivativeVector
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueFreeGroupFoxBoundary n ψ
        (residueFreeGroupFoxDerivativeVector n ψ w) =
      residueGroupRingBoundary n ψ w := by
  let beta : FreeGroup X → ResidueGroupRing n H :=
    fun w => residueFreeGroupFoxBoundary n ψ (residueFreeGroupFoxDerivativeVector n ψ w)
  have hbeta :
      IsCrossedDifferential (residueGroupRingScalar n ψ) beta :=
    IsCrossedDifferential.map_linear
      (residueFreeGroupFoxDerivativeVector_isCrossedDifferential n ψ)
      (residueFreeGroupFoxBoundary n ψ)
  have hbasis :
      ∀ x : X, beta (FreeGroup.of x) =
        residueGroupRingBoundary n ψ (FreeGroup.of x) := by
    intro x
    simp only [residueFreeGroupFoxDerivativeVector_of, residueFreeGroupFoxBoundary_single, beta]
  have hbeta_eq :
      beta =
        freeCrossedDifferentialWithCoeff
          (A := ResidueGroupRing n H)
          (residueGroupRingScalar n ψ)
          (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x)) := by
    exact freeCrossedDifferentialWithCoeff_unique
      (A := ResidueGroupRing n H)
      (residueGroupRingScalar n ψ)
      (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x))
      beta hbeta hbasis
  have hboundary_eq :
      residueGroupRingBoundary n ψ =
        freeCrossedDifferentialWithCoeff
          (A := ResidueGroupRing n H)
          (residueGroupRingScalar n ψ)
          (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x)) := by
    exact freeCrossedDifferentialWithCoeff_unique
      (A := ResidueGroupRing n H)
      (residueGroupRingScalar n ψ)
      (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x))
      (residueGroupRingBoundary n ψ)
      (residueGroupRingBoundary_isCrossedDifferential n ψ)
      (by intro x; rfl)
  exact congrFun (hbeta_eq.trans hboundary_eq.symm) w

/-- Conditional residue Fox boundary formula.  Any residue crossed differential on a free group
with the standard basis values satisfies the residue Fox boundary formula. -/
theorem residueFreeGroupFoxBoundary_of_crossedDifferential
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ResidueFreeFoxCoordinates n H X)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H))
    (w : FreeGroup X) :
    residueFreeGroupFoxBoundary n ψ (delta w) =
      residueGroupRingBoundary n ψ w := by
  have hdelta_eq :
      delta = residueFreeGroupFoxDerivativeVector n ψ :=
    residueFreeGroupFoxDerivativeVector_unique n ψ delta hdelta hbasis
  rw [hdelta_eq]
  exact residueFreeGroupFoxBoundary_derivativeVector n ψ w

/-- Conditional residue Fox fundamental formula.  The residue Fox-Euler sum computed from any
residue crossed differential with standard basis values is `[ψ(w)] - 1`. -/
theorem residueFreeGroupFoxDerivative_fundamental_formula_of_crossedDifferential
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ResidueFreeFoxCoordinates n H X)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H))
    (w : FreeGroup X) :
    residueGroupRingBoundary n ψ w =
      ∑ i : X,
        delta w i *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  simpa [residueFreeGroupFoxBoundary_apply] using
    (residueFreeGroupFoxBoundary_of_crossedDifferential n ψ delta hdelta hbasis w).symm

/-- Explicit `[ψ(w)] - 1` form of the conditional residue Fox-Euler formula. -/
theorem residueFreeGroupFoxDerivative_euler_formula_of_crossedDifferential
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ResidueFreeFoxCoordinates n H X)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H))
    (w : FreeGroup X) :
    (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ w) : ResidueGroupRing n H) - 1 =
      ∑ i : X,
        delta w i *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  simpa [residueGroupRingBoundary] using
    residueFreeGroupFoxDerivative_fundamental_formula_of_crossedDifferential
      n ψ delta hdelta hbasis w

/-- Residue Fox fundamental formula, also known as the residue Fox-Euler formula:
`[ψ(w)] - 1 = ∑ i, (∂w/∂x_i) ([ψ(x_i)] - 1)`. -/
theorem residueFreeGroupFoxDerivative_fundamental_formula
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueGroupRingBoundary n ψ w =
      ∑ i : X,
        residueFreeGroupFoxDerivative n ψ i w *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  simpa [residueFreeGroupFoxBoundary_apply, residueFreeGroupFoxDerivative] using
    (residueFreeGroupFoxBoundary_derivativeVector n ψ w).symm

/-- Explicit `[ψ(w)] - 1` form of the residue Fox-Euler formula. -/
theorem residueFreeGroupFoxDerivative_euler_formula
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ w) : ResidueGroupRing n H) - 1 =
      ∑ i : X,
        residueFreeGroupFoxDerivative n ψ i w *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  simpa [residueGroupRingBoundary] using
    residueFreeGroupFoxDerivative_fundamental_formula n ψ w

end FiniteBasis


end

end FoxDifferential
