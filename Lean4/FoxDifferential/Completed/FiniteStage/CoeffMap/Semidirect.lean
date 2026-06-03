import FoxDifferential.Completed.FiniteStage.CoeffMap.Augmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/CoeffMap/Semidirect.lean
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


variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]

/-- Coefficient-reduction map on finite-stage semidirect Fox targets. -/
def finiteFoxStageSemidirectCoeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    FiniteFoxStageSemidirect (X := X) N m₀ →*
      FiniteFoxStageSemidirect (X := X) N n₀ where
  toFun a :=
    { left := fun i => finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm (a.left i)
      right := a.right }
  map_one' := by
    apply FiniteFoxStageSemidirect.ext
    · funext i
      simp only [FiniteFoxStageSemidirect.one_left, Pi.zero_apply, map_zero]
    · rfl
  map_mul' a b := by
    apply FiniteFoxStageSemidirect.ext
    · funext i
      have hright :
          finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
              (MonoidAlgebra.single a.right (1 : ModNCompletedCoeff m₀)) =
            MonoidAlgebra.single a.right (1 : ModNCompletedCoeff n₀) := by
        rcases QuotientGroup.mk'_surjective N a.right with ⟨w, hw⟩
        rw [← hw]
        simp only [MonoidAlgebra.single, QuotientGroup.mk'_apply,
  finiteFoxStageTargetGroupAlgebraCoeffMap_single_apply, map_one]
      simp only [FiniteFoxStageSemidirect.mul_left, MonoidAlgebra.of_apply, Pi.add_apply, Pi.smul_apply,
  smul_eq_mul, map_add, map_mul, hright]
    · simp only [FiniteFoxStageSemidirect.mul_right]

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- The finite-stage semidirect coefficient map carries the lift at modulus `m` to the lift at
modulus `n`. -/
theorem finiteFoxStageSemidirectCoeffMap_lift
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    finiteFoxStageSemidirectCoeffMap (X := X) N hnm
        (finiteFoxStageLift (X := X) N m₀ w) =
      finiteFoxStageLift (X := X) N n₀ w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [finiteFoxStageLift, QuotientGroup.mk'_apply, map_one]
  | of x =>
      apply FiniteFoxStageSemidirect.ext
      · funext i
        by_cases hix : i = x
        · subst hix
          simp only [finiteFoxStageSemidirectCoeffMap, finiteFoxStageLift, QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of, MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_same, map_one]
        · simp only [finiteFoxStageSemidirectCoeffMap, finiteFoxStageLift, QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of, MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_of_ne hix, map_zero]
      · rfl
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Finite-stage Fox derivative coordinates commute with coefficient reduction. -/
theorem finiteFoxStageDerivative_coeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (i : X) (w : FreeGroup X) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (finiteFoxStageDerivative (X := X) N m₀ i w) =
      finiteFoxStageDerivative (X := X) N n₀ i w := by
  have h :=
    congrArg FiniteFoxStageSemidirect.left
      (finiteFoxStageSemidirectCoeffMap_lift (X := X) N hnm w)
  simpa [finiteFoxStageDerivative, finiteFoxStageDerivativeVector,
    finiteFoxStageSemidirectCoeffMap] using congrFun h i

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Finite-stage group-algebra derivative coordinates commute with source transition and
coefficient reduction. -/
theorem finiteFoxStageGroupAlgebraDerivative_powerCoeff_natural
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (i : X)
    (x : MonoidAlgebra (ModNCompletedCoeff m₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (finiteFoxStageGroupAlgebraDerivative (X := X) N m₀ i x) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N n₀ i
        (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
          (finiteFoxStageGroupAlgebraDerivative (X := X) N m₀ i x) =
        finiteFoxStageGroupAlgebraDerivative (X := X) N n₀ i
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) q with ⟨w, rfl⟩
    rw [finiteFoxStageGroupAlgebraDerivative_of,
      finiteFoxStagePowerSourceGroupAlgebraMap_of,
      finiteFoxStageGroupAlgebraDerivative_of,
      finiteFoxStageDerivative_coeffMap]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    have htargetScalar :
        finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
            (MonoidAlgebra.single
              (1 : finiteFoxStageTargetQuotient (X := X) N) a) =
          MonoidAlgebra.single
            (1 : finiteFoxStageTargetQuotient (X := X) N)
            (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
      rcases ZMod.intCast_surjective a with ⟨z, rfl⟩
      letI : Algebra (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) :=
        ZMod.algebra' (R := ModNCompletedCoeff n₀) (m := n₀) (n := m₀) hnm
      simp only [finiteFoxStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap, MonoidAlgebra.of,
  MonoidAlgebra.single, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.smul_single, modNCompletedCoeffMap, map_intCast]
      ext q
      by_cases hq : q = 1
      · subst hq
        simp only [Finsupp.single_eq_same]
        rw [Algebra.smul_def]
        simp only [map_intCast, mul_one]
      · simp only [ne_eq, hq, not_false_eq_true, Finsupp.single_eq_of_ne]
    have hsourceScalar :
        finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm
            (MonoidAlgebra.single
              (1 : FreeGroup X ⧸
                finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) a) =
          MonoidAlgebra.single
            (1 : FreeGroup X ⧸
              finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
            (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
      rcases ZMod.intCast_surjective a with ⟨z, rfl⟩
      letI : Algebra (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) :=
        ZMod.algebra' (R := ModNCompletedCoeff n₀) (m := n₀) (n := m₀) hnm
      simp only [finiteFoxStagePowerSourceGroupAlgebraMap, finiteFoxStageSameSourceGroupAlgebraCoeffMap,
        modNCompletedGroupRingCoeffMap, MonoidAlgebra.of, MonoidAlgebra.single,
        AlgHom.toRingHom_eq_coe, MonoidAlgebra.mapDomainRingHom,
        finiteFoxStagePowerSourceQuotientMap, RingHom.coe_comp, RingHom.coe_coe,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
        Finsupp.mapDomain_single, map_one, MonoidAlgebra.lift_single, modNCompletedCoeffMap,
        map_intCast]
      rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single]
      congr 1
      rw [Algebra.smul_def]
      simp only [map_intCast, mul_one]
    calc
      finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
          (finiteFoxStageGroupAlgebraDerivative (X := X) N m₀ i (a • x))
        =
          finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
            (a • finiteFoxStageGroupAlgebraDerivative (X := X) N m₀ i x) := by
            rw [LinearMap.map_smul]
      _ =
          (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) •
            finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
              (finiteFoxStageGroupAlgebraDerivative (X := X) N m₀ i x) := by
            simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, htargetScalar]
      _ =
          (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) •
            finiteFoxStageGroupAlgebraDerivative (X := X) N n₀ i
              (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
            rw [hx]
      _ =
          finiteFoxStageGroupAlgebraDerivative (X := X) N n₀ i
            ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) •
              finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
            rw [LinearMap.map_smul]
      _ =
          finiteFoxStageGroupAlgebraDerivative (X := X) N n₀ i
            (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm (a • x)) := by
            congr 1
            simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, hsourceScalar]



end

end FoxDifferential
