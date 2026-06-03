import FoxDifferential.Common.CrossedDifferential
import FoxDifferential.Common.Jacobian
import Mathlib.GroupTheory.FreeGroup.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Common/FreeCrossedDifferential.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Universal Fox calculus

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

variable {R : Type*} [Semiring R]
variable {A : Type*} [AddCommGroup A] [Module R A]
variable {X : Type u}

/-- The semidirect product used to construct a free crossed differential with coefficients
`coeff : FreeGroup X →* R`.  The right component remembers the free-group word, while the left
component accumulates the crossed differential value. -/
structure FreeCrossedDifferentialSemidirect
    (coeff : FreeGroup X →* R) (A : Type*) [AddCommGroup A] [Module R A] where
  /-- Additive component carrying the crossed differential value. -/
  left : A
  /-- Free-group component carrying the source word. -/
  right : FreeGroup X

namespace FreeCrossedDifferentialSemidirect

variable (coeff : FreeGroup X →* R)

/-- Identity element in the semidirect product used for free crossed differentials. -/
instance instOneFreeCrossedDifferentialSemidirect :
    One (FreeCrossedDifferentialSemidirect (X := X) coeff A) where
  one := ⟨0, 1⟩

/-- Multiplication in the semidirect product used for free crossed differentials. -/
instance instMulFreeCrossedDifferentialSemidirect :
    Mul (FreeCrossedDifferentialSemidirect (X := X) coeff A) where
  mul x y := ⟨x.left + coeff x.right • y.left, x.right * y.right⟩

/-- Inversion in the semidirect product used for free crossed differentials. -/
instance instInvFreeCrossedDifferentialSemidirect :
    Inv (FreeCrossedDifferentialSemidirect (X := X) coeff A) where
  inv x := ⟨-(coeff x.right⁻¹ • x.left), x.right⁻¹⟩

/-- Extensionality for the free crossed-differential semidirect product. -/
@[ext]
theorem ext {x y : FreeCrossedDifferentialSemidirect (X := X) coeff A}
    (hleft : x.left = y.left) (hright : x.right = y.right) : x = y := by
  cases x
  cases y
  simp_all

/-- The additive component of the identity semidirect element is zero. -/
@[simp]
theorem one_left :
    (1 : FreeCrossedDifferentialSemidirect (X := X) coeff A).left = 0 :=
  rfl

/-- The free-group component of the identity semidirect element is the identity word. -/
@[simp]
theorem one_right :
    (1 : FreeCrossedDifferentialSemidirect (X := X) coeff A).right = 1 :=
  rfl

/-- The additive component of semidirect multiplication. -/
@[simp]
theorem mul_left (x y : FreeCrossedDifferentialSemidirect (X := X) coeff A) :
    (x * y).left = x.left + coeff x.right • y.left :=
  rfl

/-- The free-group component of semidirect multiplication. -/
@[simp]
theorem mul_right (x y : FreeCrossedDifferentialSemidirect (X := X) coeff A) :
    (x * y).right = x.right * y.right :=
  rfl

/-- The additive component of semidirect inversion. -/
@[simp]
theorem inv_left (x : FreeCrossedDifferentialSemidirect (X := X) coeff A) :
    x⁻¹.left = -(coeff x.right⁻¹ • x.left) :=
  rfl

/-- The free-group component of semidirect inversion. -/
@[simp]
theorem inv_right (x : FreeCrossedDifferentialSemidirect (X := X) coeff A) :
    x⁻¹.right = x.right⁻¹ :=
  rfl

/-- Group structure on the semidirect product used for free crossed differentials. -/
instance instGroupFreeCrossedDifferentialSemidirect :
    Group (FreeCrossedDifferentialSemidirect (X := X) coeff A) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc x y z := by
    ext
    · simp only [mul_left, mul_right, map_mul, add_assoc, smul_add, smul_smul]
    · simp only [mul_right, mul_assoc]
  one_mul x := by
    ext
    · simp only [mul_left, one_left, one_right, map_one, one_smul, zero_add]
    · simp only [mul_right, one_right, one_mul]
  mul_one x := by
    ext
    · simp only [mul_left, one_left, smul_zero, add_zero]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel x := by
    ext
    · simp only [mul_left, inv_left, inv_right, neg_add_cancel, one_left]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

end FreeCrossedDifferentialSemidirect

variable (coeff : FreeGroup X →* R) (basisValue : X → A)

/-- The semidirect lift whose left component is the free crossed differential with prescribed
generator values. -/
def freeCrossedDifferentialWithCoeffLift :
    FreeGroup X →* FreeCrossedDifferentialSemidirect (X := X) coeff A :=
  FreeGroup.lift fun x => ⟨basisValue x, FreeGroup.of x⟩

/-- The free crossed differential with coefficient homomorphism `coeff` and prescribed generator
values `basisValue`. -/
def freeCrossedDifferentialWithCoeff (w : FreeGroup X) : A :=
  (freeCrossedDifferentialWithCoeffLift (A := A) coeff basisValue w).left

/-- The right component of the free crossed-differential lift is the identity on the free group. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffLift_right (w : FreeGroup X) :
    (freeCrossedDifferentialWithCoeffLift (A := A) coeff basisValue w).right = w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [freeCrossedDifferentialWithCoeffLift, map_one, FreeCrossedDifferentialSemidirect.one_right]
  | of x =>
      simp only [freeCrossedDifferentialWithCoeffLift, FreeGroup.lift_apply_of]
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, FreeCrossedDifferentialSemidirect.mul_right, hx, hy]

/-- The free crossed differential sends the identity word to zero. -/
@[simp]
theorem freeCrossedDifferentialWithCoeff_one :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue 1 = 0 := by
  simp only [freeCrossedDifferentialWithCoeff, freeCrossedDifferentialWithCoeffLift, map_one,
  FreeCrossedDifferentialSemidirect.one_left]

/-- The free crossed differential sends a free generator to its prescribed value. -/
@[simp]
theorem freeCrossedDifferentialWithCoeff_of (x : X) :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue (FreeGroup.of x) =
      basisValue x := by
  simp only [freeCrossedDifferentialWithCoeff, freeCrossedDifferentialWithCoeffLift, FreeGroup.lift_apply_of]

/-- Product rule for the free crossed differential with arbitrary coefficients. -/
theorem freeCrossedDifferentialWithCoeff_mul (u v : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue (u * v) =
      freeCrossedDifferentialWithCoeff (A := A) coeff basisValue u +
        coeff u • freeCrossedDifferentialWithCoeff (A := A) coeff basisValue v := by
  simp only [freeCrossedDifferentialWithCoeff, map_mul, FreeCrossedDifferentialSemidirect.mul_left,
  freeCrossedDifferentialWithCoeffLift_right]

/-- Inverse rule for the free crossed differential with arbitrary coefficients. -/
theorem freeCrossedDifferentialWithCoeff_inv (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue w⁻¹ =
      -(coeff w⁻¹ • freeCrossedDifferentialWithCoeff (A := A) coeff basisValue w) := by
  simp only [freeCrossedDifferentialWithCoeff, map_inv, FreeCrossedDifferentialSemidirect.inv_left,
  freeCrossedDifferentialWithCoeffLift_right]

/-- The free crossed differential with arbitrary coefficients satisfies the Fox Leibniz rule. -/
theorem freeCrossedDifferentialWithCoeff_isCrossedDifferential :
    IsCrossedDifferential coeff
      (freeCrossedDifferentialWithCoeff (A := A) coeff basisValue) := by
  intro u v
  simpa using freeCrossedDifferentialWithCoeff_mul (A := A) coeff basisValue u v

/-- Uniqueness of crossed differentials on a free group from their generator values, for an
arbitrary coefficient homomorphism. -/
theorem freeCrossedDifferentialWithCoeff_unique
    (delta : FreeGroup X → A)
    (hdelta : IsCrossedDifferential coeff delta)
    (hbasis : ∀ x : X, delta (FreeGroup.of x) = basisValue x) :
    delta = freeCrossedDifferentialWithCoeff (A := A) coeff basisValue := by
  funext w
  induction w using FreeGroup.induction_on with
  | C1 =>
      rw [IsCrossedDifferential.one hdelta, freeCrossedDifferentialWithCoeff_one]
  | of x =>
      rw [hbasis x, freeCrossedDifferentialWithCoeff_of]
  | inv_of x hx =>
      rw [IsCrossedDifferential.inv hdelta,
        freeCrossedDifferentialWithCoeff_inv, hx]
  | mul u v hu hv =>
      rw [hdelta u v, freeCrossedDifferentialWithCoeff_mul, hu, hv]

/-- Existence and uniqueness of crossed differentials on a free group from arbitrary generator
values and an arbitrary coefficient homomorphism. -/
theorem existsUnique_freeCrossedDifferentialWithCoeff :
    ∃! delta : FreeGroup X → A,
      IsCrossedDifferential coeff delta ∧
        ∀ x : X, delta (FreeGroup.of x) = basisValue x := by
  refine ⟨freeCrossedDifferentialWithCoeff (A := A) coeff basisValue, ?_, ?_⟩
  · exact ⟨freeCrossedDifferentialWithCoeff_isCrossedDifferential (A := A) coeff basisValue,
      freeCrossedDifferentialWithCoeff_of (A := A) coeff basisValue⟩
  · intro delta hdelta
    exact freeCrossedDifferentialWithCoeff_unique (A := A) coeff basisValue
      delta hdelta.1 hdelta.2

/-- Crossed differentials on a free group are equivalent to assignments of values on the free
generators. -/
def crossedDifferentialEquivGeneratorValues :
    {delta : FreeGroup X → A // IsCrossedDifferential coeff delta} ≃ (X → A) where
  toFun delta := fun x => delta.1 (FreeGroup.of x)
  invFun basisValue :=
    ⟨freeCrossedDifferentialWithCoeff (A := A) coeff basisValue,
      freeCrossedDifferentialWithCoeff_isCrossedDifferential (A := A) coeff basisValue⟩
  left_inv delta := by
    apply Subtype.ext
    exact (freeCrossedDifferentialWithCoeff_unique (A := A) coeff
      (fun x => delta.1 (FreeGroup.of x)) delta.1 delta.2 (by intro x; rfl)).symm
  right_inv basisValue := by
    funext x
    simp only [freeCrossedDifferentialWithCoeff_of]

section Coordinates

variable {S : Type*} [Ring S]
variable {B : Type*} [AddCommGroup B] [Module S B]
variable {Y : Type v}
variable [DecidableEq X]

/-- The universal Fox-coordinate crossed differential for an arbitrary coefficient homomorphism
to a ring. -/
def freeCrossedDifferentialWithCoeffCoordinates
    (coeff : FreeGroup X →* S) (w : FreeGroup X) : X → S :=
  freeCrossedDifferentialWithCoeff
    (A := X → S) coeff (fun x => Pi.single x (1 : S)) w

/-- The coordinate crossed differential sends the identity word to zero. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffCoordinates_one
    (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff (1 : FreeGroup X) = 0 := by
  simp only [freeCrossedDifferentialWithCoeffCoordinates, freeCrossedDifferentialWithCoeff_one]

/-- The coordinate crossed differential sends a generator to the standard coordinate vector. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffCoordinates_of
    (coeff : FreeGroup X →* S) (x : X) :
    freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff (FreeGroup.of x) =
      Pi.single x (1 : S) := by
  simp only [freeCrossedDifferentialWithCoeffCoordinates, freeCrossedDifferentialWithCoeff_of]

/-- The coordinate crossed differential is a crossed differential. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_isCrossedDifferential
    (coeff : FreeGroup X →* S) :
    IsCrossedDifferential coeff
      (freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff) := by
  exact freeCrossedDifferentialWithCoeff_isCrossedDifferential
    (A := X → S) coeff (fun x => Pi.single x (1 : S))

/-- The finite linear map evaluating a coordinate vector on prescribed generator values. -/
def freeCrossedDifferentialWithCoeffExpansionLinearMap
    [Fintype X] (basisValue : X → B) : (X → S) →ₗ[S] B where
  toFun v := ∑ x : X, v x • basisValue x
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

omit [DecidableEq X] in
/-- Evaluation formula for the finite expansion linear map. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffExpansionLinearMap_apply
    [Fintype X] (basisValue : X → B) (v : X → S) :
    freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue v =
      ∑ x : X, v x • basisValue x :=
  rfl

/-- The expansion linear map sends a standard coordinate vector to the corresponding value. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffExpansionLinearMap_single
    [Fintype X] (basisValue : X → B) (x : X) :
    freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue
        (Pi.single x (1 : S)) =
      basisValue x := by
  rw [freeCrossedDifferentialWithCoeffExpansionLinearMap_apply]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_smul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

/-- The Fox-coordinate expansion determined by arbitrary coefficient coordinates. -/
def freeCrossedDifferentialWithCoeffExpansion
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B)
    (w : FreeGroup X) : B :=
  freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue
    (freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff w)

/-- The coefficient-coordinate expansion is a crossed differential. -/
theorem freeCrossedDifferentialWithCoeffExpansion_isCrossedDifferential
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) :
    IsCrossedDifferential coeff
      (freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue) := by
  exact IsCrossedDifferential.map_linear
    (freeCrossedDifferentialWithCoeffCoordinates_isCrossedDifferential (X := X) coeff)
    (freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue)

/-- The coefficient-coordinate expansion sends each generator to its prescribed value. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffExpansion_of
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) (x : X) :
    freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue (FreeGroup.of x) =
      basisValue x := by
  rw [freeCrossedDifferentialWithCoeffExpansion,
    freeCrossedDifferentialWithCoeffCoordinates_of,
    freeCrossedDifferentialWithCoeffExpansionLinearMap_single]

/-- A free crossed differential is its coefficient-coordinate expansion. -/
theorem freeCrossedDifferentialWithCoeff_eq_expansion
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := B) coeff basisValue w =
      freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue w := by
  have h :=
    freeCrossedDifferentialWithCoeff_unique
      (A := B) coeff basisValue
      (freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue)
      (freeCrossedDifferentialWithCoeffExpansion_isCrossedDifferential
        (X := X) coeff basisValue)
      (freeCrossedDifferentialWithCoeffExpansion_of (X := X) coeff basisValue)
  exact congrFun h.symm w

/-- Abstract Fox chain rule: composing a crossed differential with a free-group homomorphism is
the coordinate expansion using the pulled-back coefficient homomorphism. -/
theorem freeCrossedDifferentialWithCoeff_comp_expansion
    [Fintype X]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (delta : FreeGroup Y → B) (hdelta : IsCrossedDifferential coeff delta)
    (w : FreeGroup X) :
    delta (φ w) =
      freeCrossedDifferentialWithCoeffExpansion
        (X := X) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) w := by
  let pulled : FreeGroup X → B := fun w => delta (φ w)
  have hpulled : IsCrossedDifferential (coeff.comp φ) pulled :=
    hdelta.comp_monoidHom φ
  have hunique :
      pulled =
        freeCrossedDifferentialWithCoeff
          (A := B) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) :=
    freeCrossedDifferentialWithCoeff_unique
      (A := B) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x)))
      pulled hpulled (by intro x; rfl)
  calc
    delta (φ w) = pulled w := rfl
    _ =
        freeCrossedDifferentialWithCoeff
          (A := B) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) w := by
          exact congrFun hunique w
    _ =
        freeCrossedDifferentialWithCoeffExpansion
          (X := X) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) w := by
          exact freeCrossedDifferentialWithCoeff_eq_expansion
            (X := X) (B := B) (coeff.comp φ)
            (fun x : X => delta (φ (FreeGroup.of x))) w

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian of a homomorphism of free sources, with coefficients in `S`. -/
def freeCrossedDifferentialWithCoeffJacobian
    [DecidableEq Y] (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) :
    X → Y → S :=
  fun x => freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ (FreeGroup.of x))

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian of a free-source homomorphism as a matrix. -/
def freeCrossedDifferentialWithCoeffJacobianMatrix
    [DecidableEq Y] (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) :
    Matrix X Y S :=
  foxJacobianMatrix (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ)

omit [DecidableEq X] in
/-- Evaluation of the abstract Fox-Jacobian matrix. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianMatrix_apply
    [DecidableEq Y] (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (x : X) (y : Y) :
    freeCrossedDifferentialWithCoeffJacobianMatrix (X := X) coeff φ x y =
      freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x y :=
  rfl

omit [DecidableEq X] in
/-- The finite linear map encoded by the abstract Fox-Jacobian. -/
def freeCrossedDifferentialWithCoeffJacobianLinearMap
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) :
    (X → S) →ₗ[S] (Y → S) :=
  foxJacobianLinearMap (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ)

omit [DecidableEq X] in
/-- Evaluation formula for the finite linear map encoded by the abstract Fox-Jacobian. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_apply
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (v : X → S) (y : Y) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ v y =
      ∑ x : X, v x * freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x y :=
  rfl

/-- The abstract Fox-Jacobian linear map sends a source basis vector to the corresponding row. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_single
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) (x : X) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ
        (Pi.single x (1 : S)) =
      freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x := by
  exact foxJacobianLinearMap_single
    (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ) x

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian linear map is row-vector multiplication by its matrix. -/
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_eq_vecMul
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) (v : X → S) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ v =
      Matrix.vecMul v
        (freeCrossedDifferentialWithCoeffJacobianMatrix (X := X) coeff φ) := by
  exact foxJacobianLinearMap_eq_vecMul
    (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ) v

/-- The abstract Fox-Jacobian of the identity homomorphism is the identity family. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobian_id (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffJacobian
        (X := X) (Y := X) coeff (MonoidHom.id (FreeGroup X)) =
      foxJacobianId (R := S) (X := X) := by
  funext x y
  simp only [freeCrossedDifferentialWithCoeffJacobian, MonoidHom.id_apply,
  freeCrossedDifferentialWithCoeffCoordinates_of, foxJacobianId]

/-- The abstract Fox-Jacobian matrix of the identity homomorphism is the identity matrix. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianMatrix_id (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffJacobianMatrix
        (X := X) (Y := X) coeff (MonoidHom.id (FreeGroup X)) =
      (1 : Matrix X X S) := by
  rw [freeCrossedDifferentialWithCoeffJacobianMatrix,
    freeCrossedDifferentialWithCoeffJacobian_id]
  simp only [foxJacobianMatrix_id]

/-- The abstract Fox-Jacobian linear map of the identity homomorphism is the identity. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_id
    [Fintype X] (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap
        (X := X) (Y := X) coeff (MonoidHom.id (FreeGroup X)) =
      (LinearMap.id : (X → S) →ₗ[S] (X → S)) := by
  rw [freeCrossedDifferentialWithCoeffJacobianLinearMap,
    freeCrossedDifferentialWithCoeffJacobian_id]
  simp only [foxJacobianLinearMap_id]

/-- Abstract Fox chain rule, vector form. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) =
      freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ
        (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w) := by
  have h :=
    freeCrossedDifferentialWithCoeff_comp_expansion
      (X := X) (Y := Y) (B := Y → S) coeff φ
      (freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff)
      (freeCrossedDifferentialWithCoeffCoordinates_isCrossedDifferential (X := Y) coeff) w
  calc
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) =
        freeCrossedDifferentialWithCoeffExpansion
          (X := X) (coeff.comp φ)
          (fun x : X =>
            freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff
              (φ (FreeGroup.of x))) w := h
    _ =
        freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ
          (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w) := by
          funext y
          simp only [freeCrossedDifferentialWithCoeffExpansion, freeCrossedDifferentialWithCoeffExpansionLinearMap,
  LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
  freeCrossedDifferentialWithCoeffJacobianLinearMap, foxJacobianLinearMap_apply,
  freeCrossedDifferentialWithCoeffJacobian]

/-- Abstract Fox chain rule, component form. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_comp_apply
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) (y : Y) :
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) y =
      ∑ x : X,
        freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w x *
          freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x y := by
  exact congrFun
    (freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap
      (X := X) (Y := Y) coeff φ w) y

/-- Abstract Fox chain rule, matrix form. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_comp_matrix
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) =
      Matrix.vecMul
        (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w)
        (freeCrossedDifferentialWithCoeffJacobianMatrix (X := X) coeff φ) := by
  rw [freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap]
  exact freeCrossedDifferentialWithCoeffJacobianLinearMap_eq_vecMul
    (X := X) coeff φ
    (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w)

omit [DecidableEq X] in
/-- Abstract Fox-Jacobian chain rule, component form. -/
theorem freeCrossedDifferentialWithCoeffJacobian_comp_apply
    {Z : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y)
    (x : X) (z : Z) :
    freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Z) coeff (φ.comp χ) x z =
      ∑ y : Y,
        freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (coeff.comp φ) χ x y *
          freeCrossedDifferentialWithCoeffJacobian (X := Y) (Y := Z) coeff φ y z := by
  simpa [freeCrossedDifferentialWithCoeffJacobian] using
    freeCrossedDifferentialWithCoeffCoordinates_comp_apply
      (X := Y) (Y := Z) coeff φ (χ (FreeGroup.of x)) z

omit [DecidableEq X] in
/-- Abstract Fox-Jacobian chain rule, family form. -/
theorem freeCrossedDifferentialWithCoeffJacobian_comp
    {Z : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Z) coeff (φ.comp χ) =
      fun x z =>
        ∑ y : Y,
          freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (coeff.comp φ) χ x y *
            freeCrossedDifferentialWithCoeffJacobian (X := Y) (Y := Z) coeff φ y z := by
  funext x z
  exact freeCrossedDifferentialWithCoeffJacobian_comp_apply
    (X := X) (Y := Y) coeff φ χ x z

omit [DecidableEq X] in
/-- Abstract Fox-Jacobian chain rule, linear-map form. -/
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_comp
    {Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    (freeCrossedDifferentialWithCoeffJacobianLinearMap (X := Y) (Y := Z) coeff φ).comp
        (freeCrossedDifferentialWithCoeffJacobianLinearMap
          (X := X) (Y := Y) (coeff.comp φ) χ) =
      freeCrossedDifferentialWithCoeffJacobianLinearMap
        (X := X) (Y := Z) coeff (φ.comp χ) := by
  change
    (foxJacobianLinearMap
        (freeCrossedDifferentialWithCoeffJacobian (X := Y) (Y := Z) coeff φ)).comp
      (foxJacobianLinearMap
        (freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (coeff.comp φ) χ)) =
    foxJacobianLinearMap
      (freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Z) coeff (φ.comp χ))
  rw [foxJacobianLinearMap_comp]
  congr
  funext x z
  exact (freeCrossedDifferentialWithCoeffJacobian_comp_apply
    (X := X) (Y := Y) coeff φ χ x z).symm

omit [DecidableEq X] in
/-- Abstract Fox-Jacobian chain rule, matrix form. -/
theorem freeCrossedDifferentialWithCoeffJacobianMatrix_comp
    {Z : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeCrossedDifferentialWithCoeffJacobianMatrix
        (X := X) (Y := Z) coeff (φ.comp χ) =
      freeCrossedDifferentialWithCoeffJacobianMatrix
          (X := X) (Y := Y) (coeff.comp φ) χ *
        freeCrossedDifferentialWithCoeffJacobianMatrix
          (X := Y) (Y := Z) coeff φ := by
  apply Matrix.ext
  intro x z
  simp only [freeCrossedDifferentialWithCoeffJacobianMatrix, foxJacobianMatrix_apply,
  freeCrossedDifferentialWithCoeffJacobian_comp_apply, Matrix.mul_apply]

end Coordinates

end

end FoxDifferential
