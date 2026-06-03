import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/Source/SpecialValues.lean
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
/-- The completed-target Fox derivative sends the unit of the completed source group algebra to
zero. -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 0 := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro j
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) j
      (0 : PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N))
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection,
    primePowerCompletedGroupAlgebraProjection_zero,
    primePowerCompletedGroupAlgebraProjection_one]
  rw [finiteFoxStageGroupAlgebraDerivative_one]
  exact RingHom.map_zero
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (finiteFoxStageTargetQuotient (X := X) N) j.2)

omit [Fact (0 < ℓ)] in
/-- Subtracting the unit from a group-like source element does not change its completed-target
Fox derivative. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_sub_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w - 1) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) := by
  rw [map_sub, primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_one, sub_zero]

omit [Fact (0 < ℓ)] in
/-- Subtracting the unit from a group-like source element does not change its completed-target
Fox derivative vector. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_sub_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w - 1) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) := by
  funext i
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_sub_one]

omit [Fact (0 < ℓ)] in
/-- Family-level projection formula for the derivative limit of a group-like source element. -/
@[simp]
theorem finiteFoxStagePrimePowerDerivativeLimit_sourceOf_toFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) (w : FreeGroup X) (a : ℕ) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N
        (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
          (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)) a =
      finiteFoxStageDerivative (X := X) N (ℓ ^ a) i w := by
  exact finiteFoxStagePrimePowerDerivativeLimit_sourceOf_projection (ℓ := ℓ) (X := X) N i w a

omit [Fact (0 < ℓ)] in
/-- Product rule for the prime-power derivative limit on group-like source elements. -/
theorem finiteFoxStagePrimePowerDerivativeLimit_sourceOf_mul
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) (u v : FreeGroup X) :
    finiteFoxStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i
        (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (u * v)) =
      finiteFoxStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i
          (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N u) +
        finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N u *
          finiteFoxStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i
            (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N v) := by
  apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  simp only [finiteFoxStagePrimePowerDerivativeLimitAddHom_apply,
  finiteFoxStagePrimePowerDerivativeLimit_sourceOf_toFamily, finiteFoxStageDerivative_mul, QuotientGroup.mk'_apply,
  MonoidAlgebra.of_apply, finiteFoxStagePrimePowerTargetLimitToFamily_add,
  finiteFoxStagePrimePowerTargetLimitToFamily_mul, Pi.add_apply, Pi.mul_apply,
  finiteFoxStagePrimePowerTargetOf_toFamily]

omit [Fact (0 < ℓ)] in
/-- Generator-value projection formula for the prime-power derivative limit. -/
@[simp]
theorem finiteFoxStagePrimePowerDerivativeLimit_generator_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (i j : X) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
          (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (FreeGroup.of j))) =
      ((Pi.single j (1 : finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
        X → finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i := by
  rw [finiteFoxStagePrimePowerDerivativeLimit_sourceOf_projection]
  change finiteFoxStageDerivativeVector (X := X) N (ℓ ^ a) (FreeGroup.of j) i =
    ((Pi.single j (1 : finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
      X → finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i
  rw [finiteFoxStageDerivativeVector_of]

omit [Fact (0 < ℓ)] in
/-- Generator-value projection formula for the completed-target Fox derivative. -/
@[simp 900]
theorem ppCompletedGAFoxDerivToTarget_generator_proj
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i j : X)
    (k : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) k
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
            (FreeGroup.of j))) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ k.1)
        (finiteFoxStageTargetQuotient (X := X) N) k.2
        (((Pi.single j
          (1 : finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1))) :
            X → finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1)) i) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_projection]
  congr 1
  change finiteFoxStageDerivativeVector (X := X) N (ℓ ^ k.1) (FreeGroup.of j) i =
    ((Pi.single j (1 : finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1))) :
      X → finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1)) i
  rw [finiteFoxStageDerivativeVector_of]



end

end FoxDifferential
