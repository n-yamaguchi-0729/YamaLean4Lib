import FoxDifferential.Common.FoxBoundary
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules
import Mathlib.Tactic.NoncommRing

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Boundary.lean
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

/-- The finite-stage Fox boundary/Euler map
`v ↦ ∑ i, v_i * ([x_i] - 1)` on coordinate vectors. -/
def finiteFoxStageFoxBoundary [Fintype X] :
    finiteFoxStageCoordinateVector (X := X) N n →ₗ[
      finiteFoxStageTargetGroupAlgebra (X := X) N n]
      finiteFoxStageTargetGroupAlgebra (X := X) N n where
  toFun v :=
    ∑ i : X,
      v i *
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N (FreeGroup.of i)) - 1)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, mul_assoc,
  RingHom.id_apply, Finset.mul_sum]

omit [DecidableEq X] in
/-- Evaluation formula for the finite-stage Fox boundary/Euler map. -/
theorem finiteFoxStageFoxBoundary_apply [Fintype X]
    (v : finiteFoxStageCoordinateVector (X := X) N n) :
    finiteFoxStageFoxBoundary (X := X) N n v =
      ∑ i : X,
        v i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) :=
  rfl

/-- The finite-stage Fox boundary sends a coordinate basis vector to its augmentation generator. -/
@[simp]
theorem finiteFoxStageFoxBoundary_single [Fintype X] (i : X) :
    finiteFoxStageFoxBoundary (X := X) N n
        (Pi.single i (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N (FreeGroup.of i)) - 1 := by
  rw [finiteFoxStageFoxBoundary_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, one_mul]
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, QuotientGroup.mk'_apply,
  MonoidAlgebra.of_apply, one_mul, IsEmpty.forall_iff]

/-- Finite-stage Fox fundamental formula for a free-group word. -/
theorem finiteFoxStageDerivative_fundamental_formula
    [Fintype X] (w : FreeGroup X) :
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1 =
      ∑ i : X,
        finiteFoxStageDerivative (X := X) N n i w *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
  sub_self, finiteFoxStageDerivative, finiteFoxStageDerivativeVector, map_one, FiniteFoxStageSemidirect.one_left,
  Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  | of x =>
      simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, MonoidAlgebra.one_def, finiteFoxStageDerivative,
  finiteFoxStageDerivativeVector_of, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
  ↓reduceIte]
      have hone :
          (MonoidAlgebra.single
            (1 : finiteFoxStageTargetQuotient (X := X) N)
            (1 : ModNCompletedCoeff n) :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.one_def]
      rw [hone, one_mul]
  | inv_of x hx =>
      simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
  finiteFoxStageDerivative, finiteFoxStageDerivativeVector, finiteFoxStageLift, map_inv, FreeGroup.lift_apply_of,
  FiniteFoxStageSemidirect.inv_left, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
  MonoidAlgebra.single_mul_single, mul_one, mul_zero, neg_mul, ite_mul, zero_mul, Finset.sum_neg_distrib,
  Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      change
        MonoidAlgebra.single ((QuotientGroup.mk' N (FreeGroup.of x))⁻¹)
            (1 : ModNCompletedCoeff n) -
            MonoidAlgebra.single (1 : finiteFoxStageTargetQuotient (X := X) N)
              (1 : ModNCompletedCoeff n) =
          - (MonoidAlgebra.single ((QuotientGroup.mk' N (FreeGroup.of x))⁻¹)
              (1 : ModNCompletedCoeff n) *
              (MonoidAlgebra.single (QuotientGroup.mk' N (FreeGroup.of x))
                  (1 : ModNCompletedCoeff n) -
                MonoidAlgebra.single (1 : finiteFoxStageTargetQuotient (X := X) N)
                  (1 : ModNCompletedCoeff n)))
      have hone :
          (MonoidAlgebra.single
            (1 : finiteFoxStageTargetQuotient (X := X) N)
            (1 : ModNCompletedCoeff n) :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.one_def]
      have hmul :
          (MonoidAlgebra.single ((QuotientGroup.mk' N (FreeGroup.of x))⁻¹)
              (1 : ModNCompletedCoeff n) *
            MonoidAlgebra.single (QuotientGroup.mk' N (FreeGroup.of x))
              (1 : ModNCompletedCoeff n) :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [QuotientGroup.mk'_apply, MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one,
  MonoidAlgebra.one_def]
      rw [hone, mul_sub, hmul, mul_one]
      noncomm_ring
  | mul u v hu hv =>
      let gu : finiteFoxStageTargetGroupAlgebra (X := X) N n :=
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u)
      let gv : finiteFoxStageTargetGroupAlgebra (X := X) N n :=
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N v)
      have hmul :
          MonoidAlgebra.of (ModNCompletedCoeff n)
              (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N (u * v)) =
            gu * gv := by
        simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, MonoidAlgebra.of_apply,
  MonoidAlgebra.single_mul_single, mul_one, gu, gv]
      calc
        MonoidAlgebra.of (ModNCompletedCoeff n)
              (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N (u * v)) - 1
            = (gu - 1) + gu * (gv - 1) := by
                rw [hmul]
                noncomm_ring
        _ =
            (∑ i : X,
              finiteFoxStageDerivative (X := X) N n i u *
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (finiteFoxStageTargetQuotient (X := X) N)
                  (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) +
              gu * (∑ i : X,
                finiteFoxStageDerivative (X := X) N n i v *
                  (MonoidAlgebra.of (ModNCompletedCoeff n)
                    (finiteFoxStageTargetQuotient (X := X) N)
                    (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) := by
                rw [hu, hv]
        _ =
            ∑ i : X,
              (finiteFoxStageDerivative (X := X) N n i u +
                gu * finiteFoxStageDerivative (X := X) N n i v) *
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (finiteFoxStageTargetQuotient (X := X) N)
                  (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                noncomm_ring
        _ =
              ∑ i : X,
                finiteFoxStageDerivative (X := X) N n i (u * v) *
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (finiteFoxStageTargetQuotient (X := X) N)
                  (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [finiteFoxStageDerivative_mul]

/-- Boundary-map form of the finite-stage Fox fundamental formula. -/
theorem finiteFoxStageFoxBoundary_derivativeVector [Fintype X] (w : FreeGroup X) :
    finiteFoxStageFoxBoundary (X := X) N n
        (finiteFoxStageDerivativeVector (X := X) N n w) =
      finiteFoxStageCoefficient (X := X) N n w - 1 := by
  rw [finiteFoxStageFoxBoundary_apply, finiteFoxStageCoefficient_apply]
  simpa [finiteFoxStageDerivative] using
    (finiteFoxStageDerivative_fundamental_formula (X := X) N n w).symm

/-- Conditional finite-stage Fox boundary formula.  Any finite-stage crossed differential on the
free group with standard generator values satisfies the Fox boundary formula. -/
theorem finiteFoxStageFoxBoundary_of_crossedDifferential
    [Fintype X]
    (delta : FreeGroup X → finiteFoxStageCoordinateVector (X := X) N n)
    (hdelta :
      IsCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
    (w : FreeGroup X) :
    finiteFoxStageFoxBoundary (X := X) N n (delta w) =
      finiteFoxStageCoefficient (X := X) N n w - 1 := by
  have hdelta_eq :
      delta = finiteFoxStageDerivativeVector (X := X) N n :=
    finiteFoxStageDerivativeVector_unique (X := X) N n delta hdelta hbasis
  rw [hdelta_eq]
  exact finiteFoxStageFoxBoundary_derivativeVector (X := X) N n w

/-- Conditional finite-stage Fox fundamental formula.  The Fox-Euler sum computed from any
finite-stage crossed differential with standard generator values is `[w] - 1` in the target
group algebra. -/
theorem finiteFoxStageDerivative_fundamental_formula_of_crossedDifferential
    [Fintype X]
    (delta : FreeGroup X → finiteFoxStageCoordinateVector (X := X) N n)
    (hdelta :
      IsCrossedDifferential (finiteFoxStageCoefficient (X := X) N n) delta)
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n))
    (w : FreeGroup X) :
    finiteFoxStageCoefficient (X := X) N n w - 1 =
      ∑ i : X,
        delta w i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa [finiteFoxStageFoxBoundary_apply] using
    (finiteFoxStageFoxBoundary_of_crossedDifferential
      (X := X) N n delta hdelta hbasis w).symm


end

end FoxDifferential
