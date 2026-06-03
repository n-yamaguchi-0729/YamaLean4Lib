import FoxDifferential.Discrete.FoxCalculus.Derivative

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/FoxCalculus/Universal.lean
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

universe u v


variable {H : Type v} [Group H]
variable (X : Type u)

variable [DecidableEq X]
variable (ψ : FreeGroup X →* H)

/-- The universal map `A_ψ → ℤ[H]^X` induced by the relative Fox derivative. -/
def relativeDifferentialToFreeFoxCoordinates :
    DifferentialModule ψ →ₗ[GroupRing H] RelativeFreeFoxCoordinates (H := H) X :=
  lift
    (A := RelativeFreeFoxCoordinates (H := H) X)
    ψ
    (relativeFreeGroupFoxDerivative (H := H) X ψ)
    (relativeFreeGroupFoxDerivative_isDifferentialMap (H := H) X ψ)

/-- The coordinate map out of the universal differential module sends `universalDifferential w` to the Fox derivative
of `w`. -/
@[simp]
theorem relativeDifferentialToFreeFoxCoordinates_d (w : FreeGroup X) :
    relativeDifferentialToFreeFoxCoordinates (H := H) X ψ (universalDifferential ψ w) =
      relativeFreeGroupFoxDerivative (H := H) X ψ w := by
  simpa [relativeDifferentialToFreeFoxCoordinates] using
    lift_d
      (A := RelativeFreeFoxCoordinates (H := H) X)
      ψ
      (relativeFreeGroupFoxDerivative (H := H) X ψ)
      (relativeFreeGroupFoxDerivative_isDifferentialMap (H := H) X ψ)
      w

variable [Fintype X]

/-- The linear map from pushed-forward Fox-coordinate vectors to `A_ψ`, sending the coordinate
basis vector at `x` to `universalDifferentialψ(x)`. -/
def relativeFreeFoxCoordinatesLinearMap :
    RelativeFreeFoxCoordinates (H := H) X →ₗ[GroupRing H] DifferentialModule ψ :=
  { toFun := fun a =>
      ∑ x : X, a x • universalDifferential ψ (FreeGroup.of x)
    map_add' := by
      intro a b
      simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, Pi.add_apply, add_smul,
  Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, Pi.smul_apply, smul_eq_mul,
  RingHom.id_apply, Finset.smul_sum, smul_smul]}

/-- The coordinate-to-differential map sends a coordinate basis vector to the corresponding
universal generator differential. -/
@[simp]
theorem relativeFreeFoxCoordinatesLinearMap_single (x : X) :
    relativeFreeFoxCoordinatesLinearMap (H := H) X ψ
        (Pi.single x (1 : GroupRing H)) =
      universalDifferential ψ (FreeGroup.of x) := by
  change (∑ y : X,
      ((Pi.single x (1 : GroupRing H) : RelativeFreeFoxCoordinates (H := H) X) y) •
        universalDifferential ψ (FreeGroup.of y)) =
    universalDifferential ψ (FreeGroup.of x)
  rw [Finset.sum_eq_single x]
  · simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, Pi.single_eq_same, one_smul]
  · intro y _ hy
    simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, Pi.single_eq_of_ne hy, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, relationSubmodule_eq_crossedDifferentialRelationSubmodule,
  Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

omit [DecidableEq X] [Fintype X] in
/-- The universal relative differential on a free group satisfies the inverse rule. -/
theorem relativeFreeGroupDifferential_inv (w : FreeGroup X) :
    universalDifferential ψ w⁻¹ =
      -((MonoidAlgebra.of ℤ H (ψ w⁻¹) : GroupRing H) • universalDifferential ψ w) := by
  have h := universalDifferential_mul_inv_right ψ w⁻¹
  rw [eq_neg_iff_add_eq_zero]
  simpa using h

/-- The relative Fox-coordinate formula recovers the universal differential in `A_ψ`. -/
theorem relativeFreeFoxCoordinatesLinearMap_derivative (w : FreeGroup X) :
    relativeFreeFoxCoordinatesLinearMap (H := H) X ψ
        (relativeFreeGroupFoxDerivative (H := H) X ψ w) =
      universalDifferential ψ w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, relativeFreeGroupFoxDerivative_one,
  map_zero, universalDifferential_one]
  | of x =>
      simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, relativeFreeGroupFoxDerivative_of,
  relativeFreeFoxCoordinatesLinearMap_single]
  | inv_of x hx =>
      rw [relativeFreeGroupFoxDerivative_inv, map_neg, map_smul, hx]
      exact (relativeFreeGroupDifferential_inv (H := H) X ψ (FreeGroup.of x)).symm
  | mul x y hx hy =>
      rw [relativeFreeGroupFoxDerivative_mul, map_add, map_smul, hx, hy]
      simpa using (universalDifferential_mul ψ x y).symm

end FoxCalculus

end

end FoxDifferential
