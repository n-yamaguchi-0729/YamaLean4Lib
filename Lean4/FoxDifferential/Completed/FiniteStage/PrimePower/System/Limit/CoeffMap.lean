import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Mul

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Limit/CoeffMap.lean
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

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


omit [DecidableEq X] in
/-- Compatibility of target stage maps with coefficient reduction in the completed target group
algebra. -/
theorem finiteFoxStagePrimePowerTargetStageMap_coeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    {a b : ℕ} (hab : a ≤ b)
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex (finiteFoxStageTargetQuotient (X := X) N))
    (x : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) :
    modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ a) (m := ℓ ^ b)
        (G := finiteFoxStageTargetQuotient (X := X) N) U
        (primePow_dvd_primePow (ℓ := ℓ) hab)
        (modNCompletedGroupAlgebraStageMap (ℓ ^ b)
          (finiteFoxStageTargetQuotient (X := X) N) U x) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ a)
        (finiteFoxStageTargetQuotient (X := X) N) U
        (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab x) := by
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ b)
          (G := finiteFoxStageTargetQuotient (X := X) N) U
          (primePow_dvd_primePow (ℓ := ℓ) hab)
          (modNCompletedGroupAlgebraStageMap (ℓ ^ b)
            (finiteFoxStageTargetQuotient (X := X) N) U x) =
        modNCompletedGroupAlgebraStageMap (ℓ ^ a)
          (finiteFoxStageTargetQuotient (X := X) N) U
          (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
    rw [modNCompletedGroupAlgebraStageMap_of]
    change modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ a) (m := ℓ ^ b)
        (G := finiteFoxStageTargetQuotient (X := X) N) U
        (primePow_dvd_primePow (ℓ := ℓ) hab)
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (finiteFoxStageTargetQuotient (X := X) N) U)
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite)
            (G := finiteFoxStageTargetQuotient (X := X) N) U
            (QuotientGroup.mk' N w))) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ a)
        (finiteFoxStageTargetQuotient (X := X) N) U
        (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
            (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)))
    rw [modNCompletedGroupAlgebraStageCoeffMap_of,
      finiteFoxStagePrimePowerTargetTransition_of,
      modNCompletedGroupAlgebraStageMap_of]
    simp only [MonoidAlgebra.of, MonoidAlgebra.single, QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hx]
    have ht :
        modNCompletedGroupAlgebraStageCoeffMap
            (n := ℓ ^ a) (m := ℓ ^ b)
            (G := finiteFoxStageTargetQuotient (X := X) N) U
            (primePow_dvd_primePow (ℓ := ℓ) hab)
            (modNCompletedGroupAlgebraStageMap (ℓ ^ b)
              (finiteFoxStageTargetQuotient (X := X) N) U
              ((algebraMap (ModNCompletedCoeff (ℓ ^ b))
                (finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b)) ↑t)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ a)
            (finiteFoxStageTargetQuotient (X := X) N) U
            (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
              ((algebraMap (ModNCompletedCoeff (ℓ ^ b))
                (finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b)) ↑t)) := by
      simp only [modNCompletedGroupAlgebraStageCoeffMap, modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
  modNCompletedGroupAlgebraStageMap, MonoidAlgebra.mapDomainRingHom, map_intCast,
  finiteFoxStagePrimePowerTargetTransition, finiteFoxStageTargetGroupAlgebraCoeffMap]
    rw [ht]
    exact (RingHom.map_mul
      (modNCompletedGroupAlgebraStageMap (ℓ ^ a)
        (finiteFoxStageTargetQuotient (X := X) N) U)
      (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
        ((algebraMap (ModNCompletedCoeff (ℓ ^ b))
          (finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b)) ↑t))
      (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab x)).symm




end

end FoxDifferential
