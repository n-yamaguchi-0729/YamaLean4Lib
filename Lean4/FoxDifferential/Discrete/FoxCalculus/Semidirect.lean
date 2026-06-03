import FoxDifferential.Discrete.DifferentialModule.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/FoxCalculus/Semidirect.lean
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

/-- Fox-coordinate vectors for a homomorphism from a free group to a target group `H`.

The coefficients are already pushed forward to `ℤ[H]`; this is the coordinate module which will
identify `A_ψ` with `ℤ[H]^X` for `ψ : FreeGroup X →* H`. -/
abbrev RelativeFreeFoxCoordinates : Type _ := X → GroupRing H

/-- The semidirect product encoding Fox crossed homomorphisms with coefficients pushed forward
along a homomorphism `ψ : FreeGroup X →* H`. -/
structure RelativeFoxSemidirect where
  /-- The additive Fox-coordinate component. -/
  left : RelativeFreeFoxCoordinates (H := H) X
  /-- The target-group component. -/
  right : H

namespace RelativeFoxSemidirect

/-- Identity element of the relative Fox semidirect product. -/
instance instOneRelativeFoxSemidirect : One (RelativeFoxSemidirect (H := H) X) where
  one := ⟨0, 1⟩

/-- Multiplication in the relative Fox semidirect product. -/
instance instMulRelativeFoxSemidirect : Mul (RelativeFoxSemidirect (H := H) X) where
  mul a b :=
    ⟨a.left + (MonoidAlgebra.of ℤ H a.right : GroupRing H) • b.left, a.right * b.right⟩

/-- Inversion in the relative Fox semidirect product. -/
instance instInvRelativeFoxSemidirect : Inv (RelativeFoxSemidirect (H := H) X) where
  inv a :=
    ⟨-((MonoidAlgebra.of ℤ H a.right⁻¹ : GroupRing H) • a.left), a.right⁻¹⟩

omit [Group H] in
/-- Extensionality for the relative Fox semidirect product. -/
@[ext]
theorem ext {a b : RelativeFoxSemidirect (H := H) X}
    (hleft : a.left = b.left) (hright : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

/-- The left component of the identity semidirect element is zero. -/
@[simp]
theorem one_left : (1 : RelativeFoxSemidirect (H := H) X).left = 0 :=
  rfl

/-- The right component of the identity semidirect element is the group identity. -/
@[simp]
theorem one_right : (1 : RelativeFoxSemidirect (H := H) X).right = 1 :=
  rfl

/-- The left component of semidirect multiplication. -/
@[simp]
theorem mul_left (a b : RelativeFoxSemidirect (H := H) X) :
    (a * b).left = a.left + (MonoidAlgebra.of ℤ H a.right : GroupRing H) • b.left :=
  rfl

/-- The right component of semidirect multiplication. -/
@[simp]
theorem mul_right (a b : RelativeFoxSemidirect (H := H) X) :
    (a * b).right = a.right * b.right :=
  rfl

/-- The left component of semidirect inversion. -/
@[simp]
theorem inv_left (a : RelativeFoxSemidirect (H := H) X) :
    a⁻¹.left = -((MonoidAlgebra.of ℤ H a.right⁻¹ : GroupRing H) • a.left) :=
  rfl

/-- The right component of semidirect inversion. -/
@[simp]
theorem inv_right (a : RelativeFoxSemidirect (H := H) X) :
    a⁻¹.right = a.right⁻¹ :=
  rfl

/-- Group structure on the relative Fox semidirect product. -/
instance instGroupRelativeFoxSemidirect : Group (RelativeFoxSemidirect (H := H) X) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    ext
    · simp only [mul_left, MonoidAlgebra.of_apply, mul_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc,
  MonoidAlgebra.coe_add, MonoidAlgebra.single_mul_apply, one_mul, mul_inv_rev, mul_assoc, smul_add, smul_smul,
  MonoidAlgebra.single_mul_single, mul_one]
    · simp only [mul_right, mul_assoc]
  one_mul a := by
    ext
    · simp only [mul_left, one_left, one_right, map_one, one_smul, zero_add]
    · simp only [mul_right, one_right, one_mul]
  mul_one a := by
    ext
    · simp only [mul_left, one_left, smul_zero, add_zero]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel a := by
    ext
    · simp only [mul_left, inv_left, inv_right, neg_add_cancel, one_left]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

end RelativeFoxSemidirect

end FoxCalculus

end

end FoxDifferential
