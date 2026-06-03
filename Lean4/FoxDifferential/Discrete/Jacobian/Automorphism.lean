import FoxDifferential.Discrete.Jacobian.ChainRule

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/Jacobian/Automorphism.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete group-ring Fox calculus

Ordinary Fox derivatives over group rings are developed through augmentation, relative differential modules, coordinates, Jacobians, and chain rules.
-/
namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators

universe u v w z t

variable {H : Type w} [Group H]
variable {X : Type u} {Y : Type v}
/-- The Fox Jacobian of a free-group automorphism has a left inverse, with the expected
coefficient push-forward. -/
theorem freeGroupAutomorphismFoxJacobian_left_inverse_apply
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X)
    (x z : X) :
    (∑ y : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.toMonoidHom)
          e.symm.toMonoidHom x y *
          freeGroupHomFoxJacobian (H := H) ψ e.toMonoidHom y z) =
      (Pi.single x (1 : GroupRing H) : X → GroupRing H) z := by
  have h :=
    freeGroupHomFoxJacobian_comp_apply (H := H)
      (X := X) (Y := X) (Z := X) ψ e.toMonoidHom e.symm.toMonoidHom x z
  have hid :
      e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (FreeGroup X) := by
    ext w
    simp only [MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm, MonoidHom.id_apply]
  rw [hid, freeGroupHomFoxJacobian_id] at h
  simpa using h.symm

/-- The Fox Jacobian of a free-group automorphism has a right inverse, with the expected
coefficient push-forward. -/
theorem freeGroupAutomorphismFoxJacobian_right_inverse_apply
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X)
    (x z : X) :
    (∑ y : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.symm.toMonoidHom)
          e.toMonoidHom x y *
          freeGroupHomFoxJacobian (H := H) ψ e.symm.toMonoidHom y z) =
      (Pi.single x (1 : GroupRing H) : X → GroupRing H) z := by
  have h :=
    freeGroupHomFoxJacobian_comp_apply (H := H)
      (X := X) (Y := X) (Z := X) ψ e.symm.toMonoidHom e.toMonoidHom x z
  have hid :
      e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id (FreeGroup X) := by
    ext w
    simp only [MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom, MonoidHom.id_apply]
  rw [hid, freeGroupHomFoxJacobian_id] at h
  simpa using h.symm

/-- The Jacobian matrix of a free-group automorphism has the expected left inverse. -/
theorem freeGroupAutomorphismFoxJacobianMatrix_left_inverse
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp e.toMonoidHom)
        e.symm.toMonoidHom *
      freeGroupHomFoxJacobianMatrix (H := H) ψ e.toMonoidHom =
      (1 : Matrix X X (GroupRing H)) := by
  apply Matrix.ext
  intro x z
  rw [Matrix.mul_apply]
  change
    (∑ j : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.toMonoidHom)
          e.symm.toMonoidHom x j *
          freeGroupHomFoxJacobian (H := H) ψ e.toMonoidHom j z) =
      (1 : Matrix X X (GroupRing H)) x z
  rw [show
      (∑ j : X,
          freeGroupHomFoxJacobian (H := H) (ψ.comp e.toMonoidHom)
            e.symm.toMonoidHom x j *
            freeGroupHomFoxJacobian (H := H) ψ e.toMonoidHom j z) =
        (Pi.single x (1 : GroupRing H) : X → GroupRing H) z from
      freeGroupAutomorphismFoxJacobian_left_inverse_apply (H := H) ψ e x z]
  by_cases hxz : x = z
  · subst z
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [ne_eq, hxz, not_false_eq_true, Pi.single_eq_of_ne', Matrix.one_apply_ne]

/-- The Jacobian matrix of a free-group automorphism has the expected right inverse. -/
theorem freeGroupAutomorphismFoxJacobianMatrix_right_inverse
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp e.symm.toMonoidHom)
        e.toMonoidHom *
      freeGroupHomFoxJacobianMatrix (H := H) ψ e.symm.toMonoidHom =
      (1 : Matrix X X (GroupRing H)) := by
  apply Matrix.ext
  intro x z
  rw [Matrix.mul_apply]
  change
    (∑ j : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.symm.toMonoidHom)
          e.toMonoidHom x j *
          freeGroupHomFoxJacobian (H := H) ψ e.symm.toMonoidHom j z) =
      (1 : Matrix X X (GroupRing H)) x z
  rw [show
      (∑ j : X,
          freeGroupHomFoxJacobian (H := H) (ψ.comp e.symm.toMonoidHom)
            e.toMonoidHom x j *
            freeGroupHomFoxJacobian (H := H) ψ e.symm.toMonoidHom j z) =
        (Pi.single x (1 : GroupRing H) : X → GroupRing H) z from
      freeGroupAutomorphismFoxJacobian_right_inverse_apply (H := H) ψ e x z]
  by_cases hxz : x = z
  · subst z
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [ne_eq, hxz, not_false_eq_true, Pi.single_eq_of_ne', Matrix.one_apply_ne]

/-- The named inverse matrix for the Fox Jacobian of a free-group automorphism.

For `J_ψ(e)`, the inverse is the Jacobian of `e.symm` with coefficients pushed forward
by `ψ.comp e.toMonoidHom`. -/
def freeGroupAutomorphismFoxJacobianMatrixInverse
    [DecidableEq X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    Matrix X X (GroupRing H) :=
  freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp e.toMonoidHom) e.symm.toMonoidHom

/-- The named inverse matrix is a left inverse for the Fox Jacobian of a free-group automorphism. -/
theorem freeGroupAutomorphismFoxJacobianMatrixInverse_mul
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupAutomorphismFoxJacobianMatrixInverse (H := H) ψ e *
        freeGroupHomFoxJacobianMatrix (H := H) ψ e.toMonoidHom =
      (1 : Matrix X X (GroupRing H)) := by
  simpa [freeGroupAutomorphismFoxJacobianMatrixInverse] using
    freeGroupAutomorphismFoxJacobianMatrix_left_inverse (H := H) ψ e

/-- The named inverse matrix is a right inverse for the Fox Jacobian of a free-group automorphism. -/
theorem freeGroupAutomorphismFoxJacobianMatrix_mul_inverse
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ e.toMonoidHom *
        freeGroupAutomorphismFoxJacobianMatrixInverse (H := H) ψ e =
      (1 : Matrix X X (GroupRing H)) := by
  have h :=
    freeGroupAutomorphismFoxJacobianMatrix_right_inverse (H := H)
      (ψ.comp e.toMonoidHom) e
  have hcomp :
      (ψ.comp e.toMonoidHom).comp e.symm.toMonoidHom = ψ := by
    ext w
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
  MulEquiv.apply_symm_apply]
  rw [hcomp] at h
  simpa [freeGroupAutomorphismFoxJacobianMatrixInverse] using h


end FoxCalculus

end

end FoxDifferential
