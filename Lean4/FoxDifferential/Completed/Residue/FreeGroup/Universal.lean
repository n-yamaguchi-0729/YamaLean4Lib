import FoxDifferential.Completed.Residue.FreeGroup.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Residue/FreeGroup/Universal.lean
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

/-- Universal representation theorem for residue crossed differentials on a free group. -/
def residueFreeCrossedDifferentialEquivLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    {delta : FreeGroup X → ResidueFreeFoxCoordinates n H X //
      IsCrossedDifferential (residueGroupRingScalar n ψ) delta} ≃
      (ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
        ResidueFreeFoxCoordinates n H X) :=
  residueCrossedDifferentialEquivLinearMap
    (A := ResidueFreeFoxCoordinates n H X) n ψ

/-- The linear map from the residue universal module representing the residue derivative
vector. -/
def residueFreeGroupFoxDerivativeVectorLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
      ResidueFreeFoxCoordinates n H X :=
  residueDifferentialModuleLift
    (A := ResidueFreeFoxCoordinates n H X) n ψ
    (residueFreeGroupFoxDerivativeVector n ψ)
    (residueFreeGroupFoxDerivativeVector_isCrossedDifferential n ψ)

/-- The representing linear map evaluates on the universal differential as the residue
derivative vector. -/
@[simp]
theorem residueFreeGroupFoxDerivativeVectorLinearMap_universal
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueFreeGroupFoxDerivativeVectorLinearMap n ψ
        (residueUniversalDifferential n ψ w) =
      residueFreeGroupFoxDerivativeVector n ψ w := by
  exact residueDifferentialModuleLift_universal
    (A := ResidueFreeFoxCoordinates n H X) n ψ
    (residueFreeGroupFoxDerivativeVector n ψ)
    (residueFreeGroupFoxDerivativeVector_isCrossedDifferential n ψ) w

/-- Existence and uniqueness of the linear map representing the residue derivative vector. -/
theorem existsUnique_residueFreeGroupFoxDerivativeVectorLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ∃! f :
        ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
          ResidueFreeFoxCoordinates n H X,
      ∀ w : FreeGroup X,
        f (residueUniversalDifferential n ψ w) =
          residueFreeGroupFoxDerivativeVector n ψ w := by
  exact existsUnique_residueDifferentialModuleLift
    (A := ResidueFreeFoxCoordinates n H X) n ψ
    (residueFreeGroupFoxDerivativeVector n ψ)
    (residueFreeGroupFoxDerivativeVector_isCrossedDifferential n ψ)

end

end FoxDifferential
