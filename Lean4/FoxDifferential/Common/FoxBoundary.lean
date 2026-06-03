import FoxDifferential.Common.FreeCrossedDifferential

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Common/FoxBoundary.lean
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

section CoefficientBoundary

variable {R : Type u} [Ring R]
variable {G : Type v} [Group G]

/-- The Fox boundary crossed differential attached to a coefficient homomorphism:
`g ↦ coeff g - 1`. -/
def coefficientFoxBoundary (coeff : G →* R) (g : G) : R :=
  coeff g - 1

/-- The coefficient Fox boundary sends the identity to zero. -/
@[simp]
theorem coefficientFoxBoundary_one (coeff : G →* R) :
    coefficientFoxBoundary coeff 1 = 0 := by
  simp only [coefficientFoxBoundary, map_one, sub_self]

/-- Product rule for the coefficient Fox boundary `g ↦ coeff g - 1`. -/
theorem coefficientFoxBoundary_mul (coeff : G →* R) (g h : G) :
    coefficientFoxBoundary coeff (g * h) =
      coefficientFoxBoundary coeff g + coeff g • coefficientFoxBoundary coeff h := by
  rw [coefficientFoxBoundary, coefficientFoxBoundary, coefficientFoxBoundary, map_mul]
  change coeff g * coeff h - 1 = coeff g - 1 + coeff g * (coeff h - 1)
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, mul_add, mul_neg, mul_one]
  rw [show coeff g + -1 + (coeff g * coeff h + -coeff g) =
      coeff g + -coeff g + (coeff g * coeff h + -1) by ac_rfl]
  simp only [add_neg_cancel, zero_add]

/-- The coefficient Fox boundary is a crossed differential. -/
theorem coefficientFoxBoundary_isCrossedDifferential (coeff : G →* R) :
    IsCrossedDifferential coeff (coefficientFoxBoundary coeff) := by
  intro g h
  exact coefficientFoxBoundary_mul coeff g h

end CoefficientBoundary

section BoundaryMap

variable {R : Type u} [Ring R]
variable {X : Type v} [Fintype X]

/-- The finite Fox boundary map with prescribed generator boundary values.

It sends a coordinate vector `v : X → R` to `∑ x, v x * generatorBoundary x`. -/
def foxBoundaryMap (generatorBoundary : X → R) : (X → R) →ₗ[R] R where
  toFun v := ∑ x : X, v x * generatorBoundary x
  map_add' v w := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, Finset.mul_sum]

/-- Evaluation formula for the finite Fox boundary map. -/
theorem foxBoundaryMap_apply (generatorBoundary : X → R) (v : X → R) :
    foxBoundaryMap generatorBoundary v =
      ∑ x : X, v x * generatorBoundary x :=
  rfl

variable [DecidableEq X]

/-- The finite Fox boundary map sends a coordinate basis vector to the corresponding
generator boundary. -/
@[simp]
theorem foxBoundaryMap_single (generatorBoundary : X → R) (x : X) :
    foxBoundaryMap generatorBoundary (Pi.single x (1 : R)) = generatorBoundary x := by
  rw [foxBoundaryMap_apply]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_mul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_mul, IsEmpty.forall_iff]

end BoundaryMap

section FreeGroup

variable {R : Type u} [Ring R]
variable {X : Type v} [Fintype X] [DecidableEq X]
variable (coeff : FreeGroup X →* R)
variable (generatorBoundary : X → R)

/-- Boundary-map form of the generic free-group Fox formula.

If `boundary` is the crossed differential with generator values `generatorBoundary`, then the
Fox boundary of the free crossed differential with standard coordinate values recovers
`boundary`. -/
theorem foxBoundaryMap_freeCrossedDifferentialWithCoeff
    (boundary : FreeGroup X → R)
    (hboundary : IsCrossedDifferential coeff boundary)
    (hgenerator :
      ∀ x : X, boundary (FreeGroup.of x) = generatorBoundary x)
    (w : FreeGroup X) :
    foxBoundaryMap generatorBoundary
        (freeCrossedDifferentialWithCoeff
          (A := X → R) coeff (fun x : X => Pi.single x (1 : R)) w) =
      boundary w := by
  let delta : FreeGroup X → R := fun w =>
    foxBoundaryMap generatorBoundary
      (freeCrossedDifferentialWithCoeff
        (A := X → R) coeff (fun x : X => Pi.single x (1 : R)) w)
  have hdelta : IsCrossedDifferential coeff delta :=
    IsCrossedDifferential.map_linear
      (freeCrossedDifferentialWithCoeff_isCrossedDifferential
        (A := X → R) coeff (fun x : X => Pi.single x (1 : R)))
      (foxBoundaryMap generatorBoundary)
  have hdelta_generator :
      ∀ x : X, delta (FreeGroup.of x) = generatorBoundary x := by
    intro x
    simp only [freeCrossedDifferentialWithCoeff_of, foxBoundaryMap_single, delta]
  have hdelta_eq :
      delta = freeCrossedDifferentialWithCoeff (A := R) coeff generatorBoundary :=
    freeCrossedDifferentialWithCoeff_unique
      (A := R) coeff generatorBoundary delta hdelta hdelta_generator
  have hboundary_eq :
      boundary = freeCrossedDifferentialWithCoeff (A := R) coeff generatorBoundary :=
    freeCrossedDifferentialWithCoeff_unique
      (A := R) coeff generatorBoundary boundary hboundary hgenerator
  change delta w = boundary w
  rw [hdelta_eq, hboundary_eq]

/-- Conditional boundary-map form of the generic free-group Fox formula.

Any crossed differential with standard coordinate values satisfies the same boundary formula as
the canonical free crossed differential. -/
theorem foxBoundaryMap_of_crossedDifferential
    (delta : FreeGroup X → X → R)
    (hdelta : IsCrossedDifferential coeff delta)
    (hdelta_generator :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : R))
    (boundary : FreeGroup X → R)
    (hboundary : IsCrossedDifferential coeff boundary)
    (hboundary_generator :
      ∀ x : X, boundary (FreeGroup.of x) = generatorBoundary x)
    (w : FreeGroup X) :
    foxBoundaryMap generatorBoundary (delta w) = boundary w := by
  have hdelta_eq :
      delta =
        freeCrossedDifferentialWithCoeff
          (A := X → R) coeff (fun x : X => Pi.single x (1 : R)) :=
    freeCrossedDifferentialWithCoeff_unique
      (A := X → R) coeff (fun x : X => Pi.single x (1 : R))
      delta hdelta hdelta_generator
  rw [hdelta_eq]
  exact foxBoundaryMap_freeCrossedDifferentialWithCoeff
    coeff generatorBoundary boundary hboundary hboundary_generator w

/-- Explicit finite-sum form of the generic Fox--Euler formula for any crossed differential with
standard coordinate values:
`coeff w - 1 = ∑ x, delta w x * (coeff x - 1)`. -/
theorem foxEulerFormula_of_crossedDifferential
    (delta : FreeGroup X → X → R)
    (hdelta : IsCrossedDifferential coeff delta)
    (hdelta_generator :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : R))
    (w : FreeGroup X) :
    coeff w - 1 =
      ∑ x : X, delta w x * (coeff (FreeGroup.of x) - 1) := by
  have hboundary :=
    foxBoundaryMap_of_crossedDifferential
      coeff
      (fun x : X => coefficientFoxBoundary coeff (FreeGroup.of x))
      delta hdelta hdelta_generator
      (coefficientFoxBoundary coeff)
      (coefficientFoxBoundary_isCrossedDifferential coeff)
      (by intro x; rfl)
      w
  simpa [coefficientFoxBoundary, foxBoundaryMap_apply] using hboundary.symm

end FreeGroup

end

end FoxDifferential
