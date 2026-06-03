import FoxDifferential.Completed.FiniteStage.Stage.Fundamental.Derivative

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Fundamental/Formula.lean
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

/-- Finite-stage Fox fundamental formula on a source quotient basis element after mapping to the
target group algebra. -/
theorem finiteFoxStageGroupAlgebraDerivative_of_quotient_fundamental_formula
    [Fintype X]
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) - 1 =
      ∑ i : X,
        finiteFoxStageGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rcases QuotientGroup.mk'_surjective
    (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [finiteFoxCommutatorPowerGroupAlgebraMap_of]
  simp_rw [finiteFoxStageGroupAlgebraDerivative_of]
  exact finiteFoxStageDerivative_fundamental_formula (X := X) (N := N) (n := n) w

/-- Algebra-hom form of the finite-stage Fox fundamental formula on the source group algebra. -/
theorem finiteFoxStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula_algHom
    [Fintype X]
    (x : MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    finiteFoxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n x -
        algebraMap (ModNCompletedCoeff n)
          (finiteFoxStageTargetGroupAlgebra (X := X) N n)
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) =
      ∑ i : X,
        finiteFoxStageGroupAlgebraDerivative (X := X) N n i x *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  classical
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [map_zero, sub_self, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, zero_mul,
  Finset.sum_const_zero]
  · intro x y hx hy
    calc
      finiteFoxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n (x + y) -
          algebraMap (ModNCompletedCoeff n)
            (finiteFoxStageTargetGroupAlgebra (X := X) N n)
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (x + y)) =
          (finiteFoxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n x -
              algebraMap (ModNCompletedCoeff n)
                (finiteFoxStageTargetGroupAlgebra (X := X) N n)
                (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n x)) +
            (finiteFoxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n y -
              algebraMap (ModNCompletedCoeff n)
                (finiteFoxStageTargetGroupAlgebra (X := X) N n)
                (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n y)) := by
        rw [map_add, map_add, map_add]
        abel
      _ = (∑ i : X,
            finiteFoxStageGroupAlgebraDerivative (X := X) N n i x *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (finiteFoxStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) +
          (∑ i : X,
            finiteFoxStageGroupAlgebraDerivative (X := X) N n i y *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (finiteFoxStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) := by
        rw [hx, hy]
      _ = ∑ i : X,
            (finiteFoxStageGroupAlgebraDerivative (X := X) N n i x +
              finiteFoxStageGroupAlgebraDerivative (X := X) N n i y) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (finiteFoxStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_mul]
      _ = ∑ i : X,
            finiteFoxStageGroupAlgebraDerivative (X := X) N n i (x + y) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (finiteFoxStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_add]
  · intro q a
    have hq :=
      finiteFoxStageGroupAlgebraDerivative_of_quotient_fundamental_formula
        (X := X) (N := N) (n := n) q
    rw [← Finsupp.smul_single_one q a]
    calc
      finiteFoxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n
            (a • MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) -
          algebraMap (ModNCompletedCoeff n)
            (finiteFoxStageTargetGroupAlgebra (X := X) N n)
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n
              (a • MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)) =
          a • (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
              (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) - 1) := by
        rw [map_smul, map_smul]
        have haug :
            finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n
                (Finsupp.single q (1 : ModNCompletedCoeff n)) = 1 := by
          simpa [MonoidAlgebra.of, MonoidAlgebra.single] using
            finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient
              (F := FreeGroup X) N n q
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk,
  finiteFoxCommutatorPowerGroupAlgebraAlgHom_apply, finiteFoxCommutatorPowerGroupAlgebraMap_single_apply,
  MonoidAlgebra.smul_single, smul_eq_mul, mul_one, haug, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, smul_sub, sub_right_inj]
        rw [show (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) =
            Finsupp.single (1 : finiteFoxStageTargetQuotient (X := X) N)
              (1 : ModNCompletedCoeff n) by
          simp only [MonoidAlgebra.one_def]]
        rw [Finsupp.smul_single_one]
      _ = a • (∑ i : X,
            finiteFoxStageGroupAlgebraDerivative (X := X) N n i
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (finiteFoxStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) := by
        rw [hq]
      _ = ∑ i : X,
            finiteFoxStageGroupAlgebraDerivative (X := X) N n i
              (a • MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (finiteFoxStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, smul_mul_assoc]

/-- Ring-hom form of the finite-stage Fox fundamental formula on the source group algebra. -/
theorem finiteFoxStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    [Fintype X]
    (x : MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x -
        algebraMap (ModNCompletedCoeff n)
          (finiteFoxStageTargetGroupAlgebra (X := X) N n)
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) =
      ∑ i : X,
        finiteFoxStageGroupAlgebraDerivative (X := X) N n i x *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa using
    finiteFoxStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula_algHom
      (X := X) (N := N) (n := n) x



end

end FoxDifferential
