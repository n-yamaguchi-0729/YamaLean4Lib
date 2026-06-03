import FoxDifferential.RightDerivative.IntegerPower
import Mathlib.Tactic.NoncommRing

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/RightDerivative/CommutatorFormula.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Right Fox derivatives

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

/-- The paper commutator convention `u⁻¹ * v⁻¹ * u * v`, kept local to Fox calculus so that
metabelian applications depend on `FoxDifferential`, not conversely. -/
def paperComm {G : Type*} [Group G] (u v : G) : G :=
  u⁻¹ * v⁻¹ * u * v

namespace RightDerivation

variable {G : Type*} [Group G]

theorem map_conjugated_groupElement (D : RightDerivation G) (u v : G) :
    D (MonoidAlgebra.of ℤ G (v⁻¹ * u * v) : FoxDifferential.GroupRing G) =
      D (MonoidAlgebra.of ℤ G v : FoxDifferential.GroupRing G) *
          (1 - MonoidAlgebra.of ℤ G (v⁻¹ * u * v)) +
        D (MonoidAlgebra.of ℤ G u : FoxDifferential.GroupRing G) *
          MonoidAlgebra.of ℤ G v := by
  have hmul :
      (MonoidAlgebra.of ℤ G (v⁻¹ * u * v) : FoxDifferential.GroupRing G) =
        ((MonoidAlgebra.of ℤ G v⁻¹ : FoxDifferential.GroupRing G) *
          MonoidAlgebra.of ℤ G u) * MonoidAlgebra.of ℤ G v := by
    simp only [mul_assoc, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
  rw [hmul]
  rw [map_mul, map_mul, map_inv_groupElement]
  simp only [MonoidAlgebra.of_apply, neg_mul, mul_assoc, MonoidAlgebra.single_mul_single, mul_one, augmentation,
  augmentationAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply,
  one_smul, sub_eq_add_neg]
  rw [add_mul, neg_mul]
  simp only [mul_assoc, MonoidAlgebra.single_mul_single, mul_one]
  noncomm_ring

theorem map_paperComm_groupElement (D : RightDerivation G) (u v : G) :
    D (MonoidAlgebra.of ℤ G (paperComm u v) : FoxDifferential.GroupRing G) =
      D (MonoidAlgebra.of ℤ G u : FoxDifferential.GroupRing G) *
          (MonoidAlgebra.of ℤ G v - MonoidAlgebra.of ℤ G (paperComm u v)) +
        D (MonoidAlgebra.of ℤ G v : FoxDifferential.GroupRing G) *
          (1 - MonoidAlgebra.of ℤ G (v⁻¹ * u * v)) := by
  have hmul :
      (MonoidAlgebra.of ℤ G (paperComm u v) : FoxDifferential.GroupRing G) =
        (((MonoidAlgebra.of ℤ G u⁻¹ : FoxDifferential.GroupRing G) *
          MonoidAlgebra.of ℤ G v⁻¹) * MonoidAlgebra.of ℤ G u) * MonoidAlgebra.of ℤ G v := by
    simp only [paperComm, mul_assoc, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
  rw [hmul]
  rw [map_mul, map_mul, map_mul, map_inv_groupElement, map_inv_groupElement]
  simp only [MonoidAlgebra.of_apply, neg_mul, mul_assoc, MonoidAlgebra.single_mul_single, mul_one, augmentation,
  augmentationAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply,
  smul_neg, one_smul, add_mul, sub_eq_add_neg]
  noncomm_ring

end RightDerivation

end

end FoxDifferential
