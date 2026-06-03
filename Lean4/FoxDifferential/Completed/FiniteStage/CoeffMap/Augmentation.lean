import FoxDifferential.Completed.FiniteStage.CoeffMap.Source

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/CoeffMap/Augmentation.lean
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
omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Source augmentation commutes with finite-stage coefficient/source reduction. -/
theorem finiteFoxCommutatorPowerSourceGAAugmentation_powerSourceGAMap
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀)
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N m₀) :
    finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n₀
        (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x) =
      modNCompletedCoeffMap (n := n₀) (m := m₀) hnm
        (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N m₀ x) := by
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n₀
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x) =
        modNCompletedCoeffMap (n := n₀) (m := m₀) hnm
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N m₀ x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) q with ⟨w, rfl⟩
    rw [finiteFoxStagePowerSourceGroupAlgebraMap_of,
      finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient,
      finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient]
    exact (map_one (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm)).symm
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def]
    change
      ((finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n₀).toRingHom.comp
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm))
          (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x) =
        ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).comp
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N m₀).toRingHom)
          (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x)
    rw [RingHom.map_mul, RingHom.map_mul]
    have hx' :
        ((finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n₀).toRingHom.comp
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm)) x =
          ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).comp
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N m₀).toRingHom) x := by
      simpa [RingHom.comp_apply] using hx
    rw [hx']
    have hcoeff :
        ((finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n₀).toRingHom.comp
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm))
            (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) =
          ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).comp
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N m₀).toRingHom)
            (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) := by
      simp only [finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation, AlgHom.toRingHom_eq_coe,
  finiteFoxStagePowerSourceGroupAlgebraMap, finiteFoxStageSameSourceGroupAlgebraCoeffMap,
  modNCompletedGroupRingCoeffMap, MonoidAlgebra.mapDomainRingHom, finiteFoxStagePowerSourceQuotientMap, map_intCast,
  modNCompletedCoeffMap]
    rw [hcoeff]




end

end FoxDifferential
