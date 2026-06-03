import FoxDifferential.Common.FoxBoundary
import FoxDifferential.Completed.Residue.FreeGroup.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Residue/FreeGroup/Boundary.lean
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

/-- The residue Fox boundary/Euler map
`v ↦ ∑ i, v_i * ([ψ x_i] - 1)`. -/
def residueFreeGroupFoxBoundary (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueFreeFoxCoordinates n H X →ₗ[ResidueGroupRing n H] ResidueGroupRing n H where
  toFun v :=
    ∑ i : X,
      v i *
        (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, MonoidAlgebra.of_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, MonoidAlgebra.of_apply, mul_assoc, RingHom.id_apply, Finset.mul_sum]

omit [DecidableEq X] in
/-- Evaluation formula for the residue Fox boundary/Euler map. -/
theorem residueFreeGroupFoxBoundary_apply
    (n : ℕ) (ψ : FreeGroup X →* H) (v : ResidueFreeFoxCoordinates n H X) :
    residueFreeGroupFoxBoundary n ψ v =
      ∑ i : X,
        v i *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) :=
  rfl

/-- The residue Fox boundary sends a coordinate basis vector to the corresponding augmentation
generator. -/
@[simp]
theorem residueFreeGroupFoxBoundary_single (n : ℕ) (ψ : FreeGroup X →* H) (i : X) :
    residueFreeGroupFoxBoundary n ψ
        (Pi.single i (1 : ResidueGroupRing n H)) =
      residueGroupRingBoundary n ψ (FreeGroup.of i) := by
  rw [residueFreeGroupFoxBoundary_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, MonoidAlgebra.of_apply, one_mul, residueGroupRingBoundary]
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, MonoidAlgebra.of_apply, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, MonoidAlgebra.of_apply, one_mul,
  IsEmpty.forall_iff]

end FiniteBasis


end

end FoxDifferential
