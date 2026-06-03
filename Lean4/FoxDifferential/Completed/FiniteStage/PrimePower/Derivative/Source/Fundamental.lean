import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/Source/Fundamental.lean
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


omit [Fact (0 < ℓ)] in
/-- The completed-target Fox fundamental formula for a group-like source element after projection
to one completed target stage. -/
theorem ppCompletedGAFoxDerivToTarget_of_fundFormula_proj
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X)
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraOf (ell := ℓ)
          (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := finiteFoxStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have hstage := congrArg
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (finiteFoxStageTargetQuotient (X := X) N) j.2)
    (finiteFoxStageDerivative_fundamental_formula
      (X := X) (N := N) (n := ℓ ^ j.1) w)
  simp_rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_projection,
    primePowerCompletedGroupAlgebraProjection_sub,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_one]
  have hmap (g : finiteFoxStageTargetQuotient (X := X) N) :
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
          (finiteFoxStageTargetQuotient (X := X) N) j.2
          (Finsupp.single g (1 : ModNCompletedCoeff (ℓ ^ j.1))) =
        Finsupp.single
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite)
            (G := finiteFoxStageTargetQuotient (X := X) N) j.2 g)
          (1 : ModNCompletedCoeff (ℓ ^ j.1)) := by
    simpa [MonoidAlgebra.of, MonoidAlgebra.single] using
      (modNCompletedGroupAlgebraStageMap_of
        (n := ℓ ^ j.1) (G := finiteFoxStageTargetQuotient (X := X) N)
        j.2 g)
  simpa [map_sub, map_sum, map_mul,
    modNCompletedGroupAlgebraStageMap_of, MonoidAlgebra.of, MonoidAlgebra.single, hmap]
    using hstage

omit [Fact (0 < ℓ)] in
/-- The completed-target Fox fundamental formula for a group-like source element. -/
theorem ppCompletedGAFoxDerivToTarget_of_fundFormula
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1 =
      ∑ i : X,
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) *
          (primePowerCompletedGroupAlgebraOf (ell := ℓ)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro j
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
      (primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
      (∑ i : X,
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) *
          (primePowerCompletedGroupAlgebraOf (ell := ℓ)
            (H := finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1))
  rw [ppCompletedGAFoxDerivToTarget_of_fundFormula_proj
    (ℓ := ℓ) (X := X) N hfinite w j]
  have hsum
      (f : X → PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N)) :
      primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (∑ i : X, f i) =
        ∑ i : X,
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j (f i) := by
    classical
    refine Finset.induction_on (s := Finset.univ) ?_ ?_
    · simp only [Finset.sum_empty, InverseSystem.projection_apply, coe_zero_primePowerCompletedGroupAlgebra,
  Pi.zero_apply]
    · intro a s has ih
      rw [Finset.sum_insert has, Finset.sum_insert has,
        primePowerCompletedGroupAlgebraProjection_add, ih]
  rw [hsum]
  rfl



end

end FoxDifferential
