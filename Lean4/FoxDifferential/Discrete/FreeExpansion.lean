import FoxDifferential.Discrete.FoxCalculus.Universal

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/FreeExpansion.lean
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

universe u v w

variable {H : Type v} [Group H]
variable {A : Type*} [AddCommGroup A] [Module (GroupRing H) A]
variable {X : Type u} [DecidableEq X] [Fintype X]
variable (ψ : FreeGroup X →* H) (basisValue : X → A)

/-- The Fox-coordinate expansion determined by prescribed values on the free generators. -/
def freeCrossedDifferentialExpansion (w : FreeGroup X) : A :=
  ∑ x : X,
    relativeFreeGroupFoxDerivative (H := H) X ψ w x • basisValue x

/-- The Fox-coordinate expansion of the identity word is zero. -/
@[simp]
theorem freeCrossedDifferentialExpansion_one :
    freeCrossedDifferentialExpansion (H := H) (A := A) ψ basisValue 1 = 0 := by
  simp only [freeCrossedDifferentialExpansion, relativeFreeGroupFoxDerivative_one, Pi.zero_apply, zero_smul,
  Finset.sum_const_zero]

/-- The Fox-coordinate expansion of a free generator returns its prescribed basis value. -/
@[simp]
theorem freeCrossedDifferentialExpansion_of (x : X) :
    freeCrossedDifferentialExpansion (H := H) (A := A) ψ basisValue (FreeGroup.of x) =
      basisValue x := by
  rw [freeCrossedDifferentialExpansion]
  rw [relativeFreeGroupFoxDerivative_of]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_smul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

/-- The Fox-coordinate expansion is a crossed differential. -/
theorem freeCrossedDifferentialExpansion_isDifferentialMap :
    IsDifferentialMap (A := A) ψ
      (freeCrossedDifferentialExpansion (H := H) (A := A) ψ basisValue) := by
  intro u v
  rw [freeCrossedDifferentialExpansion, freeCrossedDifferentialExpansion]
  change
    (∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X ψ (u * v) x • basisValue x) =
      (∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X ψ u x • basisValue x) +
        (MonoidAlgebra.of ℤ H (ψ u) : GroupRing H) •
          (∑ x : X,
            relativeFreeGroupFoxDerivative (H := H) X ψ v x • basisValue x)
  rw [relativeFreeGroupFoxDerivative_mul]
  simp only [MonoidAlgebra.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
  Finset.smul_sum, smul_smul]

/-- The coefficient-generic free crossed differential over a group ring is the Fox-coordinate
expansion of its generator values. -/
theorem freeCrossedDifferentialWithCoeff_groupRingScalar_eq_expansion (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := A) (groupRingScalar ψ) basisValue w =
      freeCrossedDifferentialExpansion (H := H) (A := A) ψ basisValue w := by
  have h :=
    freeCrossedDifferentialWithCoeff_unique (A := A) (groupRingScalar ψ) basisValue
      (freeCrossedDifferentialExpansion (H := H) (A := A) ψ basisValue)
      (freeCrossedDifferentialExpansion_isDifferentialMap (H := H) (A := A) ψ basisValue)
      (freeCrossedDifferentialExpansion_of (H := H) (A := A) ψ basisValue)
  exact congrFun h.symm w

omit [Fintype X] in
/-- The coefficient-generic coordinate crossed differential specializes to the usual relative
Fox derivative over a group ring. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_eq_relativeFreeGroupFoxDerivative
    (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeffCoordinates
        (X := X) (groupRingScalar ψ) w =
      relativeFreeGroupFoxDerivative (H := H) X ψ w := by
  exact congrFun (relativeFreeGroupFoxDerivative_unique (H := H) X ψ
    (freeCrossedDifferentialWithCoeffCoordinates (X := X) (groupRingScalar ψ))
    (freeCrossedDifferentialWithCoeffCoordinates_isCrossedDifferential
      (X := X) (groupRingScalar ψ))
    (freeCrossedDifferentialWithCoeffCoordinates_of
      (X := X) (groupRingScalar ψ))) w

variable {Y : Type w}

/-- Abstract Fox chain rule for an arbitrary crossed differential. -/
theorem crossedDifferential_comp_relativeFreeGroupFoxDerivative
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (delta : FreeGroup Y → A) (hdelta : IsDifferentialMap (A := A) ψ delta)
    (w : FreeGroup X) :
    delta (φ w) =
      ∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X (ψ.comp φ) w x •
          delta (φ (FreeGroup.of x)) := by
  calc
    delta (φ w) =
        freeCrossedDifferentialWithCoeffExpansion
          (X := X) (groupRingScalar (ψ.comp φ))
          (fun x : X => delta (φ (FreeGroup.of x))) w := by
          exact freeCrossedDifferentialWithCoeff_comp_expansion
            (X := X) (Y := Y) (B := A)
            (groupRingScalar ψ) φ delta hdelta w
    _ =
        ∑ x : X,
          relativeFreeGroupFoxDerivative (H := H) X (ψ.comp φ) w x •
            delta (φ (FreeGroup.of x)) := by
          rw [freeCrossedDifferentialWithCoeffExpansion,
            freeCrossedDifferentialWithCoeffExpansionLinearMap_apply,
            freeCrossedDifferentialWithCoeffCoordinates_eq_relativeFreeGroupFoxDerivative
              (H := H) (X := X) (ψ.comp φ) w]

end FoxCalculus

end

end FoxDifferential
