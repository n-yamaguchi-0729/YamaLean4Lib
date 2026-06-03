import FoxDifferential.Common.FreeCrossedDifferential
import FoxDifferential.Completed.ProCIntegerCoefficients.Core

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/ProCIntegerCoefficients/FreeGroup/Derivative.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebra coefficients

This module gives the free-group formulas for pro-\(C\) integer coefficients, used to compare completed Fox derivatives with ordinary finite-stage derivatives.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable (C : ProCGroups.FiniteGroupClass.{v})
variable {X : Type u} [DecidableEq X]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [DecidableEq X] in
/-- Completed Fox-coordinate vectors with coefficients in `Z_C[[H]]`. -/
abbrev ZCFreeFoxCoordinates : Type (max u v) :=
  X → ZCCompletedGroupAlgebra C H

/-- Completed free-group Fox derivative vector, with coefficients pushed forward along
`ψ : FreeGroup X ->* H`. -/
def zcFreeGroupFoxDerivativeVector (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    ZCFreeFoxCoordinates C (X := X) (H := H) :=
  freeCrossedDifferentialWithCoeff
    (A := ZCFreeFoxCoordinates C (X := X) (H := H))
    (zcCompletedGroupAlgebraScalar C ψ)
    (fun x => Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    w

/-- A coordinate of the completed free-group Fox derivative. -/
def zcFreeGroupFoxDerivative (ψ : FreeGroup X →* H) (i : X)
    (w : FreeGroup X) : ZCCompletedGroupAlgebra C H :=
  zcFreeGroupFoxDerivativeVector C ψ w i

/-- The completed free-group derivative vector sends the identity word to zero. -/
@[simp]
theorem zcFreeGroupFoxDerivativeVector_one (ψ : FreeGroup X →* H) :
    zcFreeGroupFoxDerivativeVector C ψ (1 : FreeGroup X) = 0 := by
  simp only [zcFreeGroupFoxDerivativeVector, freeCrossedDifferentialWithCoeff_one]

/-- The completed free-group derivative vector sends a free generator to the corresponding
coordinate basis vector. -/
@[simp]
theorem zcFreeGroupFoxDerivativeVector_of (ψ : FreeGroup X →* H) (x : X) :
    zcFreeGroupFoxDerivativeVector C ψ (FreeGroup.of x) =
      Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
  simp only [zcFreeGroupFoxDerivativeVector, freeCrossedDifferentialWithCoeff_of]

/-- Product rule for the completed free-group derivative vector. -/
theorem zcFreeGroupFoxDerivativeVector_mul
    (ψ : FreeGroup X →* H) (u v : FreeGroup X) :
    zcFreeGroupFoxDerivativeVector C ψ (u * v) =
      zcFreeGroupFoxDerivativeVector C ψ u +
        zcCompletedGroupAlgebraScalar C ψ u • zcFreeGroupFoxDerivativeVector C ψ v := by
  exact freeCrossedDifferentialWithCoeff_mul
    (A := ZCFreeFoxCoordinates C (X := X) (H := H))
    (zcCompletedGroupAlgebraScalar C ψ)
    (fun x => Pi.single x (1 : ZCCompletedGroupAlgebra C H)) u v

/-- The completed free-group derivative vector is a crossed differential. -/
theorem zcFreeGroupFoxDerivativeVector_isCrossedDifferential
    (ψ : FreeGroup X →* H) :
    IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar C ψ) (zcFreeGroupFoxDerivativeVector C ψ) := by
  exact freeCrossedDifferentialWithCoeff_isCrossedDifferential
    (A := ZCFreeFoxCoordinates C (X := X) (H := H))
    (zcCompletedGroupAlgebraScalar C ψ)
    (fun x => Pi.single x (1 : ZCCompletedGroupAlgebra C H))

/-- The coefficient-generic coordinate crossed differential specializes to the completed
free-group Fox derivative vector. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_eq_zcFreeGroupFoxDerivativeVector
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeffCoordinates
        (X := X) (zcCompletedGroupAlgebraScalar C ψ) w =
      zcFreeGroupFoxDerivativeVector C ψ w :=
  rfl

section AbstractChainRule

variable {Y : Type u}
variable {A : Type*} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
variable [Fintype X]

/-- Completed `Z_C[[H]]` abstract Fox chain rule for an arbitrary crossed differential. -/
theorem zcCrossedDifferential_comp_zcFreeGroupFoxDerivative
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (delta : FreeGroup Y → A)
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (w : FreeGroup X) :
    delta (φ w) =
      ∑ x : X,
        zcFreeGroupFoxDerivative C (ψ.comp φ) x w •
          delta (φ (FreeGroup.of x)) := by
  calc
    delta (φ w) =
        freeCrossedDifferentialWithCoeffExpansion
          (X := X) (zcCompletedGroupAlgebraScalar C (ψ.comp φ))
          (fun x : X => delta (φ (FreeGroup.of x))) w := by
          exact freeCrossedDifferentialWithCoeff_comp_expansion
            (X := X) (Y := Y) (B := A)
            (zcCompletedGroupAlgebraScalar C ψ) φ delta hdelta w
    _ =
        ∑ x : X,
          zcFreeGroupFoxDerivative C (ψ.comp φ) x w •
            delta (φ (FreeGroup.of x)) := by
          rw [freeCrossedDifferentialWithCoeffExpansion,
            freeCrossedDifferentialWithCoeffExpansionLinearMap_apply,
            freeCrossedDifferentialWithCoeffCoordinates_eq_zcFreeGroupFoxDerivativeVector
              C (ψ.comp φ) w]
          rfl

end AbstractChainRule

section Jacobian

variable {Y : Type u} [DecidableEq Y]

/-- Completed `Z_C[[H]]` Fox-Jacobian of a homomorphism of free groups. -/
def zcFreeGroupHomFoxJacobian
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    X → Y → ZCCompletedGroupAlgebra C H :=
  freeCrossedDifferentialWithCoeffJacobian
    (X := X) (Y := Y) (zcCompletedGroupAlgebraScalar C ψ) φ

omit [DecidableEq X] in
/-- Evaluation of the completed `Z_C[[H]]` Fox-Jacobian. -/
@[simp]
theorem zcFreeGroupHomFoxJacobian_apply
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (x : X) (y : Y) :
    zcFreeGroupHomFoxJacobian C ψ φ x y =
      zcFreeGroupFoxDerivative C ψ y (φ (FreeGroup.of x)) :=
  rfl

/-- The completed `Z_C[[H]]` Fox-Jacobian as a matrix. -/
def zcFreeGroupHomFoxJacobianMatrix
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    Matrix X Y (ZCCompletedGroupAlgebra C H) :=
  freeCrossedDifferentialWithCoeffJacobianMatrix
    (X := X) (Y := Y) (zcCompletedGroupAlgebraScalar C ψ) φ

omit [DecidableEq X] in
/-- Matrix evaluation is componentwise the completed `Z_C[[H]]` Fox-Jacobian. -/
@[simp]
theorem zcFreeGroupHomFoxJacobianMatrix_apply
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (x : X) (y : Y) :
    zcFreeGroupHomFoxJacobianMatrix C ψ φ x y =
      zcFreeGroupHomFoxJacobian C ψ φ x y :=
  rfl

/-- The completed `Z_C[[H]]` Fox-Jacobian as a finite linear map on coordinate vectors. -/
def zcFreeGroupHomFoxJacobianLinearMap
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C (X := Y) (H := H) :=
  freeCrossedDifferentialWithCoeffJacobianLinearMap
    (X := X) (Y := Y) (zcCompletedGroupAlgebraScalar C ψ) φ

omit [DecidableEq X] in
/-- Evaluation formula for the completed `Z_C[[H]]` Fox-Jacobian linear map. -/
@[simp]
theorem zcFreeGroupHomFoxJacobianLinearMap_apply
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) (y : Y) :
    zcFreeGroupHomFoxJacobianLinearMap C ψ φ v y =
      ∑ x : X, v x * zcFreeGroupHomFoxJacobian C ψ φ x y :=
  rfl

omit [DecidableEq X] in
/-- The completed `Z_C[[H]]` Fox-Jacobian linear map is row-vector multiplication by its
matrix. -/
theorem zcFreeGroupHomFoxJacobianLinearMap_eq_vecMul
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcFreeGroupHomFoxJacobianLinearMap C ψ φ v =
      Matrix.vecMul v (zcFreeGroupHomFoxJacobianMatrix C ψ φ) := by
  exact freeCrossedDifferentialWithCoeffJacobianLinearMap_eq_vecMul
    (X := X) (Y := Y) (zcCompletedGroupAlgebraScalar C ψ) φ v

/-- The completed `Z_C[[H]]` Fox-Jacobian of the identity homomorphism is the identity
family. -/
@[simp]
theorem zcFreeGroupHomFoxJacobian_id (ψ : FreeGroup X →* H) :
    zcFreeGroupHomFoxJacobian C ψ (MonoidHom.id (FreeGroup X)) =
      foxJacobianId (R := ZCCompletedGroupAlgebra C H) (X := X) := by
  simp only [zcFreeGroupHomFoxJacobian,
  freeCrossedDifferentialWithCoeffJacobian_id (X := X) (S := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)]

/-- The completed `Z_C[[H]]` Fox-Jacobian matrix of the identity homomorphism is the identity
matrix. -/
@[simp]
theorem zcFreeGroupHomFoxJacobianMatrix_id (ψ : FreeGroup X →* H) :
    zcFreeGroupHomFoxJacobianMatrix C ψ (MonoidHom.id (FreeGroup X)) =
      (1 : Matrix X X (ZCCompletedGroupAlgebra C H)) := by
  simp only [zcFreeGroupHomFoxJacobianMatrix,
  freeCrossedDifferentialWithCoeffJacobianMatrix_id (X := X) (S := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)]

/-- The completed `Z_C[[H]]` Fox-Jacobian linear map of the identity homomorphism is the
identity. -/
@[simp]
theorem zcFreeGroupHomFoxJacobianLinearMap_id
    [Fintype X] (ψ : FreeGroup X →* H) :
    zcFreeGroupHomFoxJacobianLinearMap C ψ (MonoidHom.id (FreeGroup X)) =
      (LinearMap.id :
        ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
          ZCFreeFoxCoordinates C (X := X) (H := H)) := by
  simp only [zcFreeGroupHomFoxJacobianLinearMap,
  freeCrossedDifferentialWithCoeffJacobianLinearMap_id (X := X) (S := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)]

/-- Completed `Z_C[[H]]` Fox chain rule, vector form. -/
theorem zcFreeGroupFoxDerivativeVector_comp_linearMap
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    zcFreeGroupFoxDerivativeVector C ψ (φ w) =
      zcFreeGroupHomFoxJacobianLinearMap C ψ φ
        (zcFreeGroupFoxDerivativeVector C (ψ.comp φ) w) := by
  simpa [zcFreeGroupFoxDerivativeVector, zcFreeGroupHomFoxJacobianLinearMap,
    zcFreeGroupHomFoxJacobian] using
    freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap
      (X := X) (Y := Y) (zcCompletedGroupAlgebraScalar C ψ) φ w

/-- Completed `Z_C[[H]]` Fox chain rule, component form. -/
theorem zcFreeGroupFoxDerivativeVector_comp_apply
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) (y : Y) :
    zcFreeGroupFoxDerivativeVector C ψ (φ w) y =
      ∑ x : X,
        zcFreeGroupFoxDerivativeVector C (ψ.comp φ) w x *
          zcFreeGroupHomFoxJacobian C ψ φ x y := by
  exact congrFun (zcFreeGroupFoxDerivativeVector_comp_linearMap C ψ φ w) y

/-- Completed `Z_C[[H]]` Fox chain rule, component form for named derivative coordinates. -/
theorem zcFreeGroupFoxDerivative_comp
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) (y : Y) :
    zcFreeGroupFoxDerivative C ψ y (φ w) =
      ∑ x : X,
        zcFreeGroupFoxDerivative C (ψ.comp φ) x w *
          zcFreeGroupHomFoxJacobian C ψ φ x y := by
  exact zcFreeGroupFoxDerivativeVector_comp_apply C ψ φ w y

/-- Completed `Z_C[[H]]` Fox chain rule, matrix form. -/
theorem zcFreeGroupFoxDerivativeVector_comp_matrix
    [Fintype X]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    zcFreeGroupFoxDerivativeVector C ψ (φ w) =
      Matrix.vecMul
        (zcFreeGroupFoxDerivativeVector C (ψ.comp φ) w)
        (zcFreeGroupHomFoxJacobianMatrix C ψ φ) := by
  rw [zcFreeGroupFoxDerivativeVector_comp_linearMap]
  exact zcFreeGroupHomFoxJacobianLinearMap_eq_vecMul C ψ φ
    (zcFreeGroupFoxDerivativeVector C (ψ.comp φ) w)

variable {Z : Type u} [DecidableEq Z]

omit [DecidableEq X] in
/-- Completed `Z_C[[H]]` Fox-Jacobian chain rule, component form. -/
theorem zcFreeGroupHomFoxJacobian_comp_apply
    [Fintype Y]
    (ψ : FreeGroup Z →* H)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y)
    (x : X) (z : Z) :
    zcFreeGroupHomFoxJacobian C ψ (φ.comp χ) x z =
      ∑ y : Y,
        zcFreeGroupHomFoxJacobian C (ψ.comp φ) χ x y *
          zcFreeGroupHomFoxJacobian C ψ φ y z := by
  simpa [zcFreeGroupHomFoxJacobian] using
    freeCrossedDifferentialWithCoeffJacobian_comp_apply
      (X := X) (Y := Y) (Z := Z) (zcCompletedGroupAlgebraScalar C ψ) φ χ x z

omit [DecidableEq X] in
/-- Completed `Z_C[[H]]` Fox-Jacobian chain rule, linear-map form. -/
theorem zcFreeGroupHomFoxJacobianLinearMap_comp
    [Fintype X] [Fintype Y]
    (ψ : FreeGroup Z →* H)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    (zcFreeGroupHomFoxJacobianLinearMap C ψ φ).comp
        (zcFreeGroupHomFoxJacobianLinearMap C (ψ.comp φ) χ) =
      zcFreeGroupHomFoxJacobianLinearMap C ψ (φ.comp χ) := by
  simpa [zcFreeGroupHomFoxJacobianLinearMap] using
    freeCrossedDifferentialWithCoeffJacobianLinearMap_comp
      (X := X) (Y := Y) (Z := Z) (zcCompletedGroupAlgebraScalar C ψ) φ χ

omit [DecidableEq X] in
/-- Completed `Z_C[[H]]` Fox-Jacobian chain rule, matrix form. -/
theorem zcFreeGroupHomFoxJacobianMatrix_comp
    [Fintype Y]
    (ψ : FreeGroup Z →* H)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    zcFreeGroupHomFoxJacobianMatrix C ψ (φ.comp χ) =
      zcFreeGroupHomFoxJacobianMatrix C (ψ.comp φ) χ *
        zcFreeGroupHomFoxJacobianMatrix C ψ φ := by
  apply Matrix.ext
  intro x z
  exact zcFreeGroupHomFoxJacobian_comp_apply C ψ φ χ x z

end Jacobian

/-- Uniqueness of the completed free-group derivative vector among crossed differentials with
standard coordinate values on free generators. -/
theorem zcFreeGroupFoxDerivativeVector_unique
    (ψ : FreeGroup X →* H)
    (delta : FreeGroup X → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    delta = zcFreeGroupFoxDerivativeVector C ψ := by
  exact freeCrossedDifferentialWithCoeff_unique
    (A := ZCFreeFoxCoordinates C (X := X) (H := H))
    (zcCompletedGroupAlgebraScalar C ψ)
    (fun x => Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    delta hdelta hbasis

/-- Existence and uniqueness theorem for the completed free-group derivative vector. -/
theorem existsUnique_zcFreeGroupFoxDerivativeVector
    (ψ : FreeGroup X →* H) :
    ∃! delta : FreeGroup X → ZCFreeFoxCoordinates C (X := X) (H := H),
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta ∧
        ∀ x : X, delta (FreeGroup.of x) =
          Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
  exact existsUnique_freeCrossedDifferentialWithCoeff
    (A := ZCFreeFoxCoordinates C (X := X) (H := H))
    (zcCompletedGroupAlgebraScalar C ψ)
    (fun x => Pi.single x (1 : ZCCompletedGroupAlgebra C H))

/-- Universal representation theorem for completed crossed differentials on a free group. -/
def zcFreeCrossedDifferentialEquivLinearMap
    (ψ : FreeGroup X →* H) :
    {delta : FreeGroup X → ZCFreeFoxCoordinates C (X := X) (H := H) //
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta} ≃
      (ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H)) :=
  zcCompletedCrossedDifferentialEquivLinearMap
    (A := ZCFreeFoxCoordinates C (X := X) (H := H)) C ψ

/-- The linear map from the completed universal module representing the completed derivative
vector. -/
def zcFreeGroupFoxDerivativeVectorLinearMap
    (ψ : FreeGroup X →* H) :
    ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C (X := X) (H := H) :=
  zcCompletedDifferentialModuleLift
    (A := ZCFreeFoxCoordinates C (X := X) (H := H)) C ψ
    (zcFreeGroupFoxDerivativeVector C ψ)
    (zcFreeGroupFoxDerivativeVector_isCrossedDifferential C ψ)

/-- The representing linear map evaluates on the universal differential as the completed
derivative vector. -/
@[simp]
theorem zcFreeGroupFoxDerivativeVectorLinearMap_universal
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcFreeGroupFoxDerivativeVectorLinearMap C ψ
        (zcUniversalDifferential C ψ w) =
      zcFreeGroupFoxDerivativeVector C ψ w := by
  exact zcCompletedDifferentialModuleLift_universal
    (A := ZCFreeFoxCoordinates C (X := X) (H := H)) C ψ
    (zcFreeGroupFoxDerivativeVector C ψ)
    (zcFreeGroupFoxDerivativeVector_isCrossedDifferential C ψ) w

/-- If the universal completed differential of a word vanishes, then its completed free Fox
derivative vector vanishes. -/
theorem zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
    (ψ : FreeGroup X →* H) {w : FreeGroup X}
    (hw : zcUniversalDifferential C ψ w = 0) :
    zcFreeGroupFoxDerivativeVector C ψ w = 0 := by
  have h :=
    congrArg (zcFreeGroupFoxDerivativeVectorLinearMap C ψ) hw
  simpa using h

/-- Component form of
`zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero`. -/
theorem zcFreeGroupFoxDerivative_eq_zero_of_zcUniversalDifferential_eq_zero
    (ψ : FreeGroup X →* H) (i : X) {w : FreeGroup X}
    (hw : zcUniversalDifferential C ψ w = 0) :
    zcFreeGroupFoxDerivative C ψ i w = 0 := by
  have hvec :=
    zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := C) ψ hw
  simpa [zcFreeGroupFoxDerivative] using congrFun hvec i

/-- Existence and uniqueness of the linear map representing the completed derivative vector. -/
theorem existsUnique_zcFreeGroupFoxDerivativeVectorLinearMap
    (ψ : FreeGroup X →* H) :
    ∃! f :
        ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
          ZCFreeFoxCoordinates C (X := X) (H := H),
      ∀ w : FreeGroup X,
        f (zcUniversalDifferential C ψ w) =
          zcFreeGroupFoxDerivativeVector C ψ w := by
  exact existsUnique_zcCompletedDifferentialModuleLift
    (A := ZCFreeFoxCoordinates C (X := X) (H := H)) C ψ
    (zcFreeGroupFoxDerivativeVector C ψ)
    (zcFreeGroupFoxDerivativeVector_isCrossedDifferential C ψ)



end

end FoxDifferential
