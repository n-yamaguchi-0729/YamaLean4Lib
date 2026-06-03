import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedSource

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/CompletedTarget.lean
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


/-- The completed source Fox derivative, mapped from the finite-stage target limit into the
completed group algebra of the target quotient. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N) :=
  (finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
    ℓ (X := X) N).comp
    (primePowerCompletedGroupAlgebraFreeFoxDerivative
      (ℓ := ℓ) (X := X) N hfinite i)

omit [Fact (0 < ℓ)] in
/-- Projection formula for the completed-target Fox derivative. -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i z) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ j.1) i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget,
    AddMonoidHom.comp_apply,
    finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_projection]

omit [Fact (0 < ℓ)] in
/-- The completed-target prime-power Fox derivative is uniquely determined by all completed
target finite-stage projection formulas. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X)
    (f : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N))
    (hf : ∀ z
      (j : PrimePowerCompletedGroupAlgebraIndex (finiteFoxStageTargetQuotient (X := X) N)),
      primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j (f z) =
        modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
          (finiteFoxStageTargetQuotient (X := X) N) j.2
          (finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ j.1) i
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
                N hfinite j.1) z))) :
    f = primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite i := by
  apply AddMonoidHom.ext
  intro z
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro j
  change
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j (f z) =
      primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i z)
  rw [hf, primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection]

omit [Fact (0 < ℓ)] in
/-- The completed-target fundamental formula after projection to one completed target stage. -/
theorem ppCompletedGAFoxDerivToTarget_fundFormula_proj
    [Fintype X]
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
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z) -
          algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
            (finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ j.1))
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N (ℓ ^ j.1)
              (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
                (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
                  N hfinite j.1) z))) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i z) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := finiteFoxStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have hstage := congrArg
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (finiteFoxStageTargetQuotient (X := X) N) j.2)
    (primePowerCompletedGroupAlgebraFreeFoxDerivative_fundamental_formula_projection
      (ℓ := ℓ) (X := X) N hfinite z j.1)
  simp_rw [map_sub, map_sum, map_mul] at hstage
  rw [map_sub]
  rw [hstage]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [map_sub, modNCompletedGroupAlgebraStageMap_of, map_one,
    primePowerCompletedGroupAlgebraProjection_sub,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_one]
  simp only [MonoidAlgebra.single, QuotientGroup.mk'_apply, MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk,
  sub_left_inj]
  rfl

omit [Fact (0 < ℓ)] in
/-- The projected completed-target fundamental formula with the augmentation term written through
the target-stage algebra map. -/
theorem ppCompletedGAFoxDerivToTarget_fundFormula_proj_algebraMap
    [Fintype X]
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
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) -
      algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
        (PrimePowerCompletedGroupAlgebraStage ℓ
          (finiteFoxStageTargetQuotient (X := X) N) j)
        (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i z) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := finiteFoxStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have h :=
    ppCompletedGAFoxDerivToTarget_fundFormula_proj
      (ℓ := ℓ) (X := X) N hfinite z j
  rw [map_sub, modNCompletedGroupAlgebraStageMap_algebraMap] at h
  simpa using h

omit [Fact (0 < ℓ)] in
/-- The projected completed-target fundamental formula with the source augmentation read from the
completed group algebra. -/
theorem primePowerCompletedTarget_fundamentalFormula_projection_completedAugmentation
    [Fintype X]
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
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (finiteFoxStageTargetQuotient (X := X) N) j.2
        (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) -
      algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
        (PrimePowerCompletedGroupAlgebraStage ℓ
          (finiteFoxStageTargetQuotient (X := X) N) j)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := FreeGroup X)
          (j.1, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite j.1)
          (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := FreeGroup X) z)) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i z) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := finiteFoxStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa [finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_projection_eq_completed]
    using
      (ppCompletedGAFoxDerivToTarget_fundFormula_proj_algebraMap
        (ℓ := ℓ) (X := X) N hfinite z j)



end

end FoxDifferential
