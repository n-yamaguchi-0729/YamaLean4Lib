import FoxDifferential.Common.FoxBoundary
import FoxDifferential.Discrete.DifferentialModule.Boundary
import FoxDifferential.Discrete.FoxCalculus.Universal

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/FoxCalculus/Boundary.lean
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

variable [Fintype X]

/-- The pushed-forward Fox boundary
`a ↦ ∑ x, a_x (ψ x - 1)`. -/
def relativeFreeGroupFoxBoundary :
    RelativeFreeFoxCoordinates (H := H) X →ₗ[GroupRing H] GroupRing H :=
  { toFun := fun a =>
      ∑ x : X, a x * augmentationGenerator H (ψ (FreeGroup.of x))
    map_add' := by
      intro a b
      simp only [Pi.add_apply, augmentationGenerator_eq_groupRingBoundary, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      simp only [Pi.smul_apply, smul_eq_mul, augmentationGenerator_eq_groupRingBoundary, mul_assoc,
  RingHom.id_apply, Finset.mul_sum]}

omit [DecidableEq X] in
/-- Evaluation formula for the relative Fox boundary map. -/
theorem relativeFreeGroupFoxBoundary_apply
    (a : RelativeFreeFoxCoordinates (H := H) X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ a =
      ∑ x : X, a x * augmentationGenerator H (ψ (FreeGroup.of x)) :=
  rfl

/-- The relative Fox boundary sends a coordinate basis vector to the corresponding
augmentation generator. -/
@[simp]
theorem relativeFreeGroupFoxBoundary_single (x : X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ
        (Pi.single x (1 : GroupRing H)) =
      augmentationGenerator H (ψ (FreeGroup.of x)) := by
  rw [relativeFreeGroupFoxBoundary_apply]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, augmentationGenerator_eq_groupRingBoundary, one_mul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, augmentationGenerator_eq_groupRingBoundary, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, augmentationGenerator_eq_groupRingBoundary,
  one_mul, IsEmpty.forall_iff]

omit [DecidableEq X] in
/-- The universal boundary composed with the coordinate-to-differential map is the pushed-forward
Fox boundary. -/
theorem toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap :
    (toGroupRing ψ).comp
        (relativeFreeFoxCoordinatesLinearMap (H := H) X ψ) =
      relativeFreeGroupFoxBoundary (H := H) X ψ := by
  apply LinearMap.ext
  intro a
  simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, relativeFreeFoxCoordinatesLinearMap,
  LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_sum, map_smul, toGroupRing_d,
  groupRingBoundary, MonoidAlgebra.of_apply, smul_eq_mul, relativeFreeGroupFoxBoundary, augmentationGenerator]

/-- Relative Fox fundamental formula, also known as the Fox--Euler formula:
`ψ(w) - 1 = ∑ x, (∂w/∂x) (ψ x - 1)`. -/
theorem relativeFreeGroupFoxDerivative_fundamental_formula (w : FreeGroup X) :
    groupRingBoundary ψ w =
      ∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X ψ w x *
          augmentationGenerator H (ψ (FreeGroup.of x)) := by
  have h :=
    LinearMap.congr_fun
      (toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap (H := H) X ψ)
      (relativeFreeGroupFoxDerivative (H := H) X ψ w)
  rw [LinearMap.comp_apply, relativeFreeFoxCoordinatesLinearMap_derivative,
    toGroupRing_d] at h
  simpa [relativeFreeGroupFoxBoundary] using h

/-- Fox boundary form of the relative Fox fundamental formula. -/
theorem relativeFreeGroupFoxBoundary_derivative (w : FreeGroup X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ
        (relativeFreeGroupFoxDerivative (H := H) X ψ w) =
      groupRingBoundary ψ w := by
  simpa [relativeFreeGroupFoxBoundary_apply] using
    (relativeFreeGroupFoxDerivative_fundamental_formula (H := H) X ψ w).symm

/-- Conditional relative Fox boundary formula.  Any differential map on a free group with the
standard coordinate values satisfies the relative Fox boundary formula. -/
theorem relativeFreeGroupFoxBoundary_of_differentialMap
    (delta : FreeGroup X → RelativeFreeFoxCoordinates (H := H) X)
    (hdelta : IsDifferentialMap (A := RelativeFreeFoxCoordinates (H := H) X) ψ delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : GroupRing H))
    (w : FreeGroup X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ (delta w) =
      groupRingBoundary ψ w := by
  have hdelta_eq :
      delta = relativeFreeGroupFoxDerivative (H := H) X ψ :=
    relativeFreeGroupFoxDerivative_unique (H := H) X ψ delta hdelta hbasis
  rw [hdelta_eq]
  exact relativeFreeGroupFoxBoundary_derivative (H := H) X ψ w

/-- Conditional relative Fox fundamental formula.  The Fox-Euler sum computed from any
differential map with standard coordinate values is `[ψ(w)] - 1`. -/
theorem relativeFreeGroupFoxDerivative_fundamental_formula_of_differentialMap
    (delta : FreeGroup X → RelativeFreeFoxCoordinates (H := H) X)
    (hdelta : IsDifferentialMap (A := RelativeFreeFoxCoordinates (H := H) X) ψ delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : GroupRing H))
    (w : FreeGroup X) :
    groupRingBoundary ψ w =
      ∑ x : X,
        delta w x * augmentationGenerator H (ψ (FreeGroup.of x)) := by
  simpa [relativeFreeGroupFoxBoundary_apply] using
    (relativeFreeGroupFoxBoundary_of_differentialMap
      (H := H) X ψ delta hdelta hbasis w).symm

/-- Explicit `ψ(w) - 1` version of the conditional relative Fox-Euler formula. -/
theorem relativeFreeGroupFoxDerivative_euler_formula_of_differentialMap
    (delta : FreeGroup X → RelativeFreeFoxCoordinates (H := H) X)
    (hdelta : IsDifferentialMap (A := RelativeFreeFoxCoordinates (H := H) X) ψ delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : GroupRing H))
    (w : FreeGroup X) :
    (MonoidAlgebra.of ℤ H (ψ w) : GroupRing H) - 1 =
      ∑ x : X,
        delta w x * augmentationGenerator H (ψ (FreeGroup.of x)) := by
  simpa [groupRingBoundary] using
    relativeFreeGroupFoxDerivative_fundamental_formula_of_differentialMap
      (H := H) X ψ delta hdelta hbasis w

/-- Explicit `ψ(w) - 1` version of the relative Fox--Euler formula. -/
theorem relativeFreeGroupFoxDerivative_euler_formula (w : FreeGroup X) :
    (MonoidAlgebra.of ℤ H (ψ w) : GroupRing H) - 1 =
      ∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X ψ w x *
          augmentationGenerator H (ψ (FreeGroup.of x)) := by
  simpa [groupRingBoundary] using
    relativeFreeGroupFoxDerivative_fundamental_formula (H := H) X ψ w

end FoxCalculus

end

end FoxDifferential
