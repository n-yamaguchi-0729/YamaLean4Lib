import FoxDifferential.Common.FreeCrossedDifferential
import FoxDifferential.Completed.Residue.Core

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Residue/FreeGroup/Basic.lean
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

/-- Residue Fox-coordinate vectors with coefficients in `(Z/nZ)[H]`. -/
abbrev ResidueFreeFoxCoordinates (n : ℕ) (H : Type v) (X : Type u) : Type (max u v) :=
  X → ResidueGroupRing n H

/-- Residue free-group Fox derivative vector, with coefficients pushed forward along
`ψ : FreeGroup X ->* H`. -/
def residueFreeGroupFoxDerivativeVector (n : ℕ) (ψ : FreeGroup X →* H)
    (w : FreeGroup X) :
    ResidueFreeFoxCoordinates n H X :=
  freeCrossedDifferentialWithCoeff
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H))
    w

/-- A coordinate of the residue free-group Fox derivative. -/
def residueFreeGroupFoxDerivative (n : ℕ) (ψ : FreeGroup X →* H) (i : X)
    (w : FreeGroup X) : ResidueGroupRing n H :=
  residueFreeGroupFoxDerivativeVector n ψ w i

/-- The residue free-group derivative vector sends the identity word to zero. -/
@[simp]
theorem residueFreeGroupFoxDerivativeVector_one (n : ℕ) (ψ : FreeGroup X →* H) :
    residueFreeGroupFoxDerivativeVector n ψ (1 : FreeGroup X) = 0 := by
  simp only [residueFreeGroupFoxDerivativeVector, freeCrossedDifferentialWithCoeff_one]

/-- Component form of the identity rule for the residue free-group derivative. -/
@[simp]
theorem residueFreeGroupFoxDerivative_one (n : ℕ) (ψ : FreeGroup X →* H) (i : X) :
    residueFreeGroupFoxDerivative n ψ i (1 : FreeGroup X) = 0 := by
  simp only [residueFreeGroupFoxDerivative, residueFreeGroupFoxDerivativeVector_one, Pi.zero_apply]

/-- The residue free-group derivative vector sends a free generator to the corresponding
coordinate basis vector. -/
@[simp]
theorem residueFreeGroupFoxDerivativeVector_of (n : ℕ) (ψ : FreeGroup X →* H) (x : X) :
    residueFreeGroupFoxDerivativeVector n ψ (FreeGroup.of x) =
      Pi.single x (1 : ResidueGroupRing n H) := by
  simp only [residueFreeGroupFoxDerivativeVector, freeCrossedDifferentialWithCoeff_of]

/-- Component form of the residue generator value. -/
@[simp]
theorem residueFreeGroupFoxDerivative_of (n : ℕ) (ψ : FreeGroup X →* H) (i x : X) :
    residueFreeGroupFoxDerivative n ψ i (FreeGroup.of x) =
      (Pi.single x (1 : ResidueGroupRing n H) :
        ResidueFreeFoxCoordinates n H X) i := by
  rw [residueFreeGroupFoxDerivative, residueFreeGroupFoxDerivativeVector_of]

/-- The residue free-group derivative vector is a crossed differential. -/
theorem residueFreeGroupFoxDerivativeVector_isCrossedDifferential
    (n : ℕ) (ψ : FreeGroup X →* H) :
    IsCrossedDifferential
      (residueGroupRingScalar n ψ) (residueFreeGroupFoxDerivativeVector n ψ) := by
  exact freeCrossedDifferentialWithCoeff_isCrossedDifferential
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H))

/-- Uniqueness of the residue free-group derivative vector among crossed differentials with
standard coordinate values on free generators. -/
theorem residueFreeGroupFoxDerivativeVector_unique
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ResidueFreeFoxCoordinates n H X)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H)) :
    delta = residueFreeGroupFoxDerivativeVector n ψ := by
  exact freeCrossedDifferentialWithCoeff_unique
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H))
    delta hdelta hbasis

/-- Existence and uniqueness theorem for the residue free-group derivative vector. -/
theorem existsUnique_residueFreeGroupFoxDerivativeVector
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ∃! delta : FreeGroup X → ResidueFreeFoxCoordinates n H X,
      IsCrossedDifferential (residueGroupRingScalar n ψ) delta ∧
        ∀ x : X, delta (FreeGroup.of x) =
          Pi.single x (1 : ResidueGroupRing n H) := by
  exact existsUnique_freeCrossedDifferentialWithCoeff
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H))


end

end FoxDifferential
