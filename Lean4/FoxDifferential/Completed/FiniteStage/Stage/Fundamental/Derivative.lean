import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Boundary
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Relators
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Fundamental

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Fundamental/Derivative.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Linear extension of a descended finite-stage Fox derivative coordinate to the source group
algebra. -/
def finiteFoxStageGroupAlgebraDerivative (i : X) :
    MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →ₗ[
      ModNCompletedCoeff n]
      finiteFoxStageTargetGroupAlgebra (X := X) N n :=
  Finsupp.linearCombination (ModNCompletedCoeff n)
    (finiteFoxStageQuotientDerivative (X := X) N n i)

/-- Evaluation of the finite-stage group-algebra derivative on a quotient basis element. -/
@[simp]
theorem finiteFoxStageGroupAlgebraDerivative_of_quotient
    (i : X)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
      finiteFoxStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      finiteFoxStageQuotientDerivative (X := X) N n i q := by
  change
      (Finsupp.linearCombination (ModNCompletedCoeff n)
        (finiteFoxStageQuotientDerivative (X := X) N n i))
          (Finsupp.single q (1 : ModNCompletedCoeff n)) =
        finiteFoxStageQuotientDerivative (X := X) N n i q
  rw [Finsupp.linearCombination_single, one_smul]

/-- Evaluation of the finite-stage group-algebra derivative on a represented word. -/
@[simp]
theorem finiteFoxStageGroupAlgebraDerivative_of
    (i : X) (w : FreeGroup X) :
    finiteFoxStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w)) =
      finiteFoxStageDerivative (X := X) N n i w := by
  rw [finiteFoxStageGroupAlgebraDerivative_of_quotient,
    finiteFoxStageQuotientDerivative_mk]

/-- The finite-stage group-algebra derivative sends the unit to zero. -/
@[simp]
theorem finiteFoxStageGroupAlgebraDerivative_one (i : X) :
    finiteFoxStageGroupAlgebraDerivative (X := X) N n i
        (1 : MonoidAlgebra (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)) = 0 := by
  change finiteFoxStageGroupAlgebraDerivative (X := X) N n i
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (1 : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)) = 0
  rw [finiteFoxStageGroupAlgebraDerivative_of_quotient]
  change finiteFoxStageDerivative (X := X) N n i (1 : FreeGroup X) = 0
  simp only [finiteFoxStageDerivative_one]

/-- Product rule for the finite-stage group-algebra derivative on quotient basis elements. -/
theorem finiteFoxStageGroupAlgebraDerivative_of_quotient_mul
    (i : X)
    (q r : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (q * r)) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) +
        finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
          finiteFoxStageGroupAlgebraDerivative (X := X) N n i
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) r) := by
  rcases QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with
    ⟨u, rfl⟩
  rcases QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) r with
    ⟨v, rfl⟩
  change finiteFoxStageGroupAlgebraDerivative (X := X) N n i
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) (u * v))) =
    _
  rw [finiteFoxStageGroupAlgebraDerivative_of,
    finiteFoxStageGroupAlgebraDerivative_of,
    finiteFoxStageGroupAlgebraDerivative_of,
    finiteFoxCommutatorPowerGroupAlgebraMap_of,
    finiteFoxStageDerivative_mul]

/-- Product rule for the finite-stage group-algebra derivative on arbitrary source group-algebra
elements. -/
theorem finiteFoxStageGroupAlgebraDerivative_mul
    (i : X)
    (x y : MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    finiteFoxStageGroupAlgebraDerivative (X := X) N n i (x * y) =
      finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n y •
        finiteFoxStageGroupAlgebraDerivative (X := X) N n i x +
      finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x *
        finiteFoxStageGroupAlgebraDerivative (X := X) N n i y := by
  classical
  let Source :=
    MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
  let Target := finiteFoxStageTargetGroupAlgebra (X := X) N n
  let D : Source →ₗ[ModNCompletedCoeff n] Target :=
    finiteFoxStageGroupAlgebraDerivative (X := X) N n i
  let φ : Source →+* Target :=
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
  let ε : Source →ₐ[ModNCompletedCoeff n] ModNCompletedCoeff n :=
    finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation (F := FreeGroup X) N n
  have h_right_basis
      (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
      (x : Source) :
      D (x * MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
        D x +
          φ x * D (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) := by
    refine Finsupp.induction_linear x ?zero_right ?add_right ?single_right
    · simp only [MonoidAlgebra.of_apply, zero_mul, map_zero, add_zero, Source, D, φ]
    · intro x y hx hy
      rw [add_mul, map_add, hx, hy, map_add, map_add, add_mul]
      abel
    · intro q' a
      rw [← Finsupp.smul_single_one q' a]
      change
        D ((a • MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') *
          MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
          D (a • MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') +
            φ (a • MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') *
              D (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
      rw [smul_mul_assoc, map_smul, map_smul]
      have hprod :
          MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q' *
            MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q =
            MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (q' * q) := by
        simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
      rw [hprod]
      have hbasis :=
        finiteFoxStageGroupAlgebraDerivative_of_quotient_mul
          (X := X) (N := N) (n := n) i q' q
      change
          D (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (q' * q)) =
            D (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') +
              φ (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') *
                D (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) at hbasis
      rw [hbasis]
      have hφ_smul :
          φ (a • MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') =
            a • φ (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') := by
        dsimp [φ, finiteFoxCommutatorPowerGroupAlgebraMap, MonoidAlgebra.of,
          MonoidAlgebra.single]
        rw [Finsupp.smul_single_one]
        change
          MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
              (finiteFoxCommutatorPowerQuotientMapToNormalQuotient
                (F := FreeGroup X) N n)
              (Finsupp.single q' a) =
            a •
              MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
                (finiteFoxCommutatorPowerQuotientMapToNormalQuotient
                  (F := FreeGroup X) N n)
                (Finsupp.single q' (1 : ModNCompletedCoeff n))
        rw [MonoidAlgebra.mapDomainRingHom_apply,
          MonoidAlgebra.mapDomainRingHom_apply]
        change
          MonoidAlgebra.mapDomain
              (finiteFoxCommutatorPowerQuotientMapToNormalQuotient
                (F := FreeGroup X) N n)
              (MonoidAlgebra.single q' a) =
            a •
              MonoidAlgebra.mapDomain
                (finiteFoxCommutatorPowerQuotientMapToNormalQuotient
                  (F := FreeGroup X) N n)
                (MonoidAlgebra.single q' (1 : ModNCompletedCoeff n))
        rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single,
          Finsupp.smul_single_one]
      rw [hφ_smul]
      simp only [MonoidAlgebra.of_apply, smul_add, Algebra.smul_mul_assoc, D, φ]
  change
    D (x * (y : Source)) =
      ε (y : Source) • D x + φ x * D (y : Source)
  refine Finsupp.induction_linear y ?zero_y ?add_y ?single_y
  · simp only [mul_zero, map_zero, zero_smul, add_zero, Source, D, ε, φ]
  · intro y z hy hz
    let y0 : Source := y
    let z0 : Source := z
    change
      D (x * (y0 + z0)) =
        ε (y0 + z0) • D x + φ x * D (y0 + z0)
    rw [mul_add, map_add, hy, hz, map_add, map_add, left_distrib, add_smul]
    abel
  · intro q a
    rw [← Finsupp.smul_single_one q a]
    change
      D (x * (a • MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)) =
        ε (a • MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) •
          D x +
        φ x *
          D (a • MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
    rw [mul_smul_comm, map_smul, h_right_basis]
    have hε :
        ε (a • MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) = a := by
      rw [map_smul]
      have hq :=
        finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient
          (F := FreeGroup X) N n q
      change
          ε (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
            1 at hq
      rw [hq]
      simp only [smul_eq_mul, mul_one]
    have hD_smul :
        D (a • MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
          a • D (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) := by
      exact map_smul D a
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
    rw [hε, hD_smul, mul_smul_comm, smul_add]



end

end FoxDifferential
