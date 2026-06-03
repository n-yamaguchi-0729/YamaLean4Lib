import FoxDifferential.Completed.DifferentialModule.TargetQuotient.Basic
import FoxDifferential.Completed.DifferentialModule.Map.GroupLike

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/TargetQuotient/StageMap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed differential modules

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]

omit [DecidableEq X] in
/-- At a completed finite stage of `F/N`, the completed map induced by `F -> F/N` agrees
with first projecting to the completed free derivative source finite quotient and then using the
completed free derivative natural finite-stage group-algebra map. -/
theorem primePowerCompletedGroupAlgebraMapStage_targetQuotient_transition_source
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N))
    (x : PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
      (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
        (ℓ := ℓ) (X := X) N hfinite j.1)) :
    primePowerCompletedGroupAlgebraMapStage
        (ℓ := ℓ) (G := FreeGroup X)
        (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X)
          (show
            (j.1, completedGroupAlgebraComapIndex
              (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
              (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) ≤
              (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1) from
            ⟨le_rfl,
              finiteFoxStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
                (ℓ := ℓ) (X := X) N hfinite j⟩) x) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1) x) := by
  let hidx :
      (j.1, completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) ≤
        (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) :=
    ⟨le_rfl,
      finiteFoxStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
        (ℓ := ℓ) (X := X) N hfinite j⟩
  let leftMap :
      PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
          (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
            (ℓ := ℓ) (X := X) N hfinite j.1) →+*
        PrimePowerCompletedGroupAlgebraStage ℓ
          (finiteFoxStageTargetQuotient (X := X) N) j :=
    (primePowerCompletedGroupAlgebraMapStage
      (ℓ := ℓ) (G := FreeGroup X)
      (H := finiteFoxStageTargetQuotient (X := X) N)
      (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j).comp
      (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X) hidx)
  let rightMap :
      PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
          (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
            (ℓ := ℓ) (X := X) N hfinite j.1) →+*
        PrimePowerCompletedGroupAlgebraStage ℓ
          (finiteFoxStageTargetQuotient (X := X) N) j :=
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (finiteFoxStageTargetQuotient (X := X) N) j.2).comp
      (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1))
  change leftMap x = rightMap x
  have hmaps : leftMap = rightMap := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
      simp only [primePowerCompletedGroupAlgebraMapStage, MonoidAlgebra.mapDomainRingHom,
  primePowerCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMapInClass_rfl,
  modNCompletedGroupAlgebraTransition, RingHomCompTriple.comp_eq, RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk,
  OneHom.coe_mk, Function.comp_apply, Finsupp.mapDomain_single, map_one, modNCompletedGroupAlgebraStageMap,
  finiteFoxCommutatorPowerGroupAlgebraMap, leftMap, rightMap]
    · intro q
      rcases QuotientGroup.mk'_surjective
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) q with
        ⟨w, rfl⟩
      change
        leftMap
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
              (FreeGroup X ⧸
                finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1))
              (QuotientGroup.mk'
                (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w)) =
          rightMap
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
              (FreeGroup X ⧸
                finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1))
              (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w))
      dsimp [leftMap, rightMap]
      change
        primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := FreeGroup X)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j
            (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X)
              hidx
              (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
                (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                  (finiteFoxStagePrimePowerSourceCompletedIndex
                    (ℓ := ℓ) (X := X) N hfinite j.1))
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w))) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
            (finiteFoxStageTargetQuotient (X := X) N) j.2
            (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
              (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
                (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                  (finiteFoxStagePrimePowerSourceCompletedIndex
                    (ℓ := ℓ) (X := X) N hfinite j.1))
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w)))
      rw [primePowerCompletedGroupAlgebraTransition_of]
      change
        primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := FreeGroup X)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
              (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                (completedGroupAlgebraComapIndex
                  (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
                  (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2))
              ((OpenNormalSubgroupInClass.map
                (C := ProCGroups.FiniteGroupClass.allFinite) (G := FreeGroup X)
                (U := OrderDual.ofDual
                  (completedGroupAlgebraComapIndex
                    (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
                    (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2))
                (V := OrderDual.ofDual
                  (finiteFoxStagePrimePowerSourceCompletedIndex
                    (ℓ := ℓ) (X := X) N hfinite j.1))
                (finiteFoxStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
                  (ℓ := ℓ) (X := X) N hfinite j))
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w))) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
            (finiteFoxStageTargetQuotient (X := X) N) j.2
            (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
              (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
                (FreeGroup X ⧸
                  finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1))
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w)))
      rw [primePowerCompletedGroupAlgebraMapStage_of,
        finiteFoxCommutatorPowerGroupAlgebraMap_of,
        modNCompletedGroupAlgebraStageMap_of]
      rfl
  rw [hmaps]

omit [DecidableEq X] in
/-- The target finite-stage projection of the completed quotient map can be computed using
the completed free derivative source projection at the same prime-power exponent. -/
theorem primePowerCompletedGAProj_map_targetQuotient_eq_freeDerivativeSource
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraMap
          (ℓ := ℓ) (G := FreeGroup X)
          (H := finiteFoxStageTargetQuotient (X := X) N)
          (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) z) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
              (ℓ := ℓ) (X := X) N hfinite j.1) z)) := by
  let hidx :
      (j.1, completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) ≤
        (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) :=
    ⟨le_rfl,
      finiteFoxStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
        (ℓ := ℓ) (X := X) N hfinite j⟩
  rw [primePowerCompletedGroupAlgebraProjection_map]
  have hz := z.2
    (j.1, completedGroupAlgebraComapIndex
      (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
      (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2)
    (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
      (ℓ := ℓ) (X := X) N hfinite j.1) hidx
  change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X) hidx
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) z) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (j.1, completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) z at hz
  rw [← hz]
  exact
    primePowerCompletedGroupAlgebraMapStage_targetQuotient_transition_source
      (ℓ := ℓ) (X := X) N hfinite j
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (j.1, finiteFoxStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) z)

omit [DecidableEq X] in
/-- Evaluation formula for primePowerCompletedGroupAlgebraMap_targetQuotient_of. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_targetQuotient_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := by
  rw [primePowerCompletedGroupAlgebraMap_of]
  rfl


end

end FoxDifferential
