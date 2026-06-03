import FoxDifferential.Discrete.FoxCalculus.Semidirect
import FoxDifferential.Discrete.DifferentialModule.Universal
import FoxDifferential.Common.FreeCrossedDifferential

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/FoxCalculus/Derivative.lean
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

/-- The semidirect-product lift whose left component is the Fox derivative pushed forward by
`ψ`, and whose right component is `ψ` itself. -/
def relativeFreeGroupFoxLift : FreeGroup X →* RelativeFoxSemidirect (H := H) X :=
  FreeGroup.lift fun x =>
    { left := Pi.single x (1 : GroupRing H)
      right := ψ (FreeGroup.of x) }

/-- The Fox derivative of a free-group word, with coefficients pushed forward to `ℤ[H]` by
`ψ`. -/
def relativeFreeGroupFoxDerivative (w : FreeGroup X) :
    RelativeFreeFoxCoordinates (H := H) X :=
  (relativeFreeGroupFoxLift (H := H) X ψ w).left

/-- The right component of the relative Fox lift is the target homomorphism `ψ`. -/
@[simp]
theorem relativeFreeGroupFoxLift_right (w : FreeGroup X) :
    (relativeFreeGroupFoxLift (H := H) X ψ w).right = ψ w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [relativeFreeGroupFoxLift, map_one, RelativeFoxSemidirect.one_right]
  | of x =>
      simp only [relativeFreeGroupFoxLift, FreeGroup.lift_apply_of]
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, RelativeFoxSemidirect.mul_right, hx, hy]

/-- The relative Fox derivative of the identity word is zero. -/
@[simp]
theorem relativeFreeGroupFoxDerivative_one :
    relativeFreeGroupFoxDerivative (H := H) X ψ (1 : FreeGroup X) = 0 := by
  simp only [relativeFreeGroupFoxDerivative, relativeFreeGroupFoxLift, map_one, RelativeFoxSemidirect.one_left]

/-- The relative Fox derivative of a free generator is the corresponding coordinate vector. -/
@[simp]
theorem relativeFreeGroupFoxDerivative_of (x : X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (FreeGroup.of x) =
      Pi.single x (1 : GroupRing H) := by
  simp only [relativeFreeGroupFoxDerivative, relativeFreeGroupFoxLift, FreeGroup.lift_apply_of]

/-- Relative Fox product rule. -/
theorem relativeFreeGroupFoxDerivative_mul (w₁ w₂ : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (w₁ * w₂) =
      relativeFreeGroupFoxDerivative (H := H) X ψ w₁ +
        (MonoidAlgebra.of ℤ H (ψ w₁) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ w₂ := by
  simp only [relativeFreeGroupFoxDerivative, map_mul, RelativeFoxSemidirect.mul_left,
  relativeFreeGroupFoxLift_right, MonoidAlgebra.of_apply]

/-- Relative Fox inverse rule. -/
theorem relativeFreeGroupFoxDerivative_inv (w : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ w⁻¹ =
      -((MonoidAlgebra.of ℤ H (ψ w⁻¹) : GroupRing H) •
        relativeFreeGroupFoxDerivative (H := H) X ψ w) := by
  simp only [relativeFreeGroupFoxDerivative, map_inv, RelativeFoxSemidirect.inv_left,
  relativeFreeGroupFoxLift_right, MonoidAlgebra.of_apply]

/-- The relative free-group Fox derivative is a differential map for `ψ`. -/
theorem relativeFreeGroupFoxDerivative_isDifferentialMap :
    IsDifferentialMap
      (A := RelativeFreeFoxCoordinates (H := H) X)
      ψ
      (relativeFreeGroupFoxDerivative (H := H) X ψ) := by
  intro w₁ w₂
  simpa using relativeFreeGroupFoxDerivative_mul (H := H) X ψ w₁ w₂

/-- Uniqueness of the relative free-group Fox derivative among differential maps with standard
coordinate values on free generators. -/
theorem relativeFreeGroupFoxDerivative_unique
    (delta : FreeGroup X → RelativeFreeFoxCoordinates (H := H) X)
    (hdelta : IsDifferentialMap (A := RelativeFreeFoxCoordinates (H := H) X) ψ delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : GroupRing H)) :
    delta = relativeFreeGroupFoxDerivative (H := H) X ψ := by
  have hdelta_free :
      delta =
        freeCrossedDifferentialWithCoeff
          (A := RelativeFreeFoxCoordinates (H := H) X) (groupRingScalar ψ)
          (fun x : X => Pi.single x (1 : GroupRing H)) :=
    freeCrossedDifferentialWithCoeff_unique
      (A := RelativeFreeFoxCoordinates (H := H) X) (groupRingScalar ψ)
      (fun x : X => Pi.single x (1 : GroupRing H))
      delta hdelta hbasis
  have hrelative_free :
      relativeFreeGroupFoxDerivative (H := H) X ψ =
        freeCrossedDifferentialWithCoeff
          (A := RelativeFreeFoxCoordinates (H := H) X) (groupRingScalar ψ)
          (fun x : X => Pi.single x (1 : GroupRing H)) :=
    freeCrossedDifferentialWithCoeff_unique
      (A := RelativeFreeFoxCoordinates (H := H) X) (groupRingScalar ψ)
      (fun x : X => Pi.single x (1 : GroupRing H))
      (relativeFreeGroupFoxDerivative (H := H) X ψ)
      (relativeFreeGroupFoxDerivative_isDifferentialMap (H := H) X ψ)
      (relativeFreeGroupFoxDerivative_of (H := H) X ψ)
  exact hdelta_free.trans hrelative_free.symm

/-- Relative Fox derivative of a positive power. -/
theorem relativeFreeGroupFoxDerivative_pow (w : FreeGroup X) (n : ℕ) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (w ^ n) =
      (Finset.range n).sum (fun k =>
        (MonoidAlgebra.of ℤ H (ψ (w ^ k)) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ w) := by
  simpa [groupRingScalar] using
    IsCrossedDifferential.pow
      (relativeFreeGroupFoxDerivative_isDifferentialMap (H := H) X ψ) w n

/-- Relative Fox derivative of a conjugate. -/
theorem relativeFreeGroupFoxDerivative_conj (g h : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (g * h * g⁻¹) =
      relativeFreeGroupFoxDerivative (H := H) X ψ g +
        (MonoidAlgebra.of ℤ H (ψ g) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ h -
        (MonoidAlgebra.of ℤ H (ψ (g * h * g⁻¹)) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ g := by
  simpa [groupRingScalar] using
    IsCrossedDifferential.conj
      (relativeFreeGroupFoxDerivative_isDifferentialMap (H := H) X ψ) g h

/-- Relative Fox derivative of a commutator. -/
theorem relativeFreeGroupFoxDerivative_commutator (g h : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ ⁅g, h⁆ =
      relativeFreeGroupFoxDerivative (H := H) X ψ g +
        (MonoidAlgebra.of ℤ H (ψ g) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ h -
        (MonoidAlgebra.of ℤ H (ψ (g * h * g⁻¹)) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ g -
        (MonoidAlgebra.of ℤ H (ψ ⁅g, h⁆) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ h := by
  simpa [groupRingScalar] using
    IsCrossedDifferential.commutator
      (relativeFreeGroupFoxDerivative_isDifferentialMap (H := H) X ψ) g h

end FoxCalculus

end

end FoxDifferential
