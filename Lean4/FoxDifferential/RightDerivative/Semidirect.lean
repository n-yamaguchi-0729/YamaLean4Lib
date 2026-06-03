import FoxDifferential.RightDerivative.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/RightDerivative/Semidirect.lean
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

structure RightFoxSemidirect (G : Type*) [Group G] where
  left : FoxDifferential.GroupRing G
  right : G

namespace RightFoxSemidirect

variable {G : Type*} [Group G]

@[ext]
theorem ext {x y : RightFoxSemidirect G}
    (hleft : x.left = y.left) (hright : x.right = y.right) : x = y := by
  cases x
  cases y
  simp_all

instance instOneRightFoxSemidirect : One (RightFoxSemidirect G) where
  one := ⟨0, 1⟩

instance instMulRightFoxSemidirect : Mul (RightFoxSemidirect G) where
  mul x y :=
    ⟨x.left * MonoidAlgebra.of ℤ G y.right + y.left, x.right * y.right⟩

instance instInvRightFoxSemidirect : Inv (RightFoxSemidirect G) where
  inv x :=
    ⟨-x.left * MonoidAlgebra.of ℤ G x.right⁻¹, x.right⁻¹⟩

@[simp]
theorem one_left : (1 : RightFoxSemidirect G).left = 0 :=
  rfl

@[simp]
theorem one_right : (1 : RightFoxSemidirect G).right = 1 :=
  rfl

@[simp]
theorem mul_left (x y : RightFoxSemidirect G) :
    (x * y).left = x.left * MonoidAlgebra.of ℤ G y.right + y.left :=
  rfl

@[simp]
theorem mul_right (x y : RightFoxSemidirect G) :
    (x * y).right = x.right * y.right :=
  rfl

@[simp]
theorem inv_left (x : RightFoxSemidirect G) :
    x⁻¹.left = -x.left * MonoidAlgebra.of ℤ G x.right⁻¹ :=
  rfl

@[simp]
theorem inv_right (x : RightFoxSemidirect G) :
    x⁻¹.right = x.right⁻¹ :=
  rfl

instance instGroupRightFoxSemidirect : Group (RightFoxSemidirect G) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc x y z := by
    ext
    · simp only [mul_left, MonoidAlgebra.of_apply, MonoidAlgebra.coe_add, Pi.add_apply,
        MonoidAlgebra.mul_single_apply, mul_one, mul_right, mul_inv_rev, mul_assoc,
        add_assoc]
    · simp only [mul_right, mul_assoc]
  one_mul x := by
    ext
    · simp only [mul_left, one_left, MonoidAlgebra.of_apply, zero_mul, zero_add]
    · simp only [mul_right, one_right, one_mul]
  mul_one x := by
    ext
    · simp only [mul_left, one_right, MonoidAlgebra.of_apply, one_left, add_zero,
        MonoidAlgebra.mul_single_apply, inv_one, mul_one]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel x := by
    ext
    · simp only [mul_left, inv_left, MonoidAlgebra.of_apply, neg_mul, MonoidAlgebra.coe_add,
        Pi.add_apply, MonoidAlgebra.neg_apply, MonoidAlgebra.mul_single_apply, inv_inv,
        inv_mul_cancel_right, mul_one, neg_add_cancel, one_left, Finsupp.coe_zero,
        Pi.zero_apply]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

def rightHom : RightFoxSemidirect G →* G where
  toFun x := x.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem rightHom_apply (x : RightFoxSemidirect G) :
    rightHom x = x.right :=
  rfl

end RightFoxSemidirect

end

end FoxDifferential
