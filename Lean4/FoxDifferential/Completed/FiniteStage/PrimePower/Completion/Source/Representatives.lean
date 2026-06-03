import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.LimitMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Completion/Source/Representatives.lean
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


/-- The compatible source-limit family represented by a free-group word. -/
def finiteFoxStagePrimePowerSourceOf
    (N : Subgroup (FreeGroup X)) (w : FreeGroup X) :
    FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N :=
  ⟨fun a =>
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
            (FreeGroup X ⧸
              finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b))
            (QuotientGroup.mk'
              (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b)) w)) =
        MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
          (FreeGroup X ⧸
            finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w)
      exact finiteFoxStagePrimePowerSourceTransition_of (ℓ := ℓ) (X := X) N hab w⟩

omit [DecidableEq X] in
/-- Projection formula for the source-limit element represented by a word. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceOf_projection
    (N : Subgroup (FreeGroup X)) (w : FreeGroup X) (a : ℕ) :
    (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) := rfl

omit [DecidableEq X] in
/-- Projecting a group-like free-group algebra element to a source stage agrees with the
corresponding source-limit projection. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceProjection_eq_sourceOf_projection
    (N : Subgroup (FreeGroup X)) (w : FreeGroup X) (a : ℕ) :
    finiteFoxStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X) w) =
      (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w) := by
  rw [finiteFoxStagePrimePowerSourceProjection_of,
    finiteFoxStagePrimePowerSourceOf_projection]

omit [DecidableEq X] in
/-- The completed-source-to-finite-stage-limit map sends a group-like completed element to the
source-limit element represented by the same word. -/
@[simp]
theorem primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w := by
  apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
    (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
      (finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    finiteFoxStagePrimePowerSourceOf_projection]
  rfl

omit [DecidableEq X] in
/-- The source-limit bridge sends the completed group-like boundary `[w]-1` to the
corresponding source-limit boundary. -/
@[simp]
theorem primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_sub_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w - 1) =
      finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w - 1 := by
  rw [map_sub,
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_of,
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_one]

/-- The compatible target-limit family represented by a free-group word. -/
def finiteFoxStagePrimePowerTargetOf
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) :
    FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N :=
  ⟨fun a =>
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (finiteFoxStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N w)) =
        MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
          (finiteFoxStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N w)
      exact finiteFoxStagePrimePowerTargetTransition_of (ℓ := ℓ) (X := X) N hab w⟩

omit [DecidableEq X] in
/-- Projection formula for the target-limit element represented by a word. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetOf_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (finiteFoxStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w) := rfl

omit [DecidableEq X] in
/-- The target-limit-to-completed-group-algebra map sends a represented word to the corresponding
group-like element in the completed target group algebra. -/
@[simp 900]
theorem finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_targetOf
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (w : FreeGroup X) :
    finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) i
      (finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w)) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w))
  rw [finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection,
    finiteFoxStagePrimePowerTargetOf_projection,
    modNCompletedGroupAlgebraStageMap_of,
    primePowerCompletedGroupAlgebraProjection_of]
  rfl

omit [DecidableEq X] in
/-- Family-level projection formula for the target-limit element represented by a word. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetOf_toFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N
        (finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w) a =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (finiteFoxStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w) := rfl

omit [DecidableEq X] in
/-- The source-limit element represented by the identity word is one. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceOf_one
    (N : Subgroup (FreeGroup X)) :
    finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (1 : FreeGroup X) = 1 := by
  apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (1 : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) =
    (1 : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a)
  simpa using
    (map_one (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))))

omit [DecidableEq X] in
/-- The source-limit representative of a product is the product of source-limit representatives. -/
theorem finiteFoxStagePrimePowerSourceOf_mul
    (N : Subgroup (FreeGroup X)) (u v : FreeGroup X) :
    finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (u * v) =
      finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N u *
        finiteFoxStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N v := by
  apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) (u * v)) =
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) u) *
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) v)
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, MonoidAlgebra.of_apply,
  MonoidAlgebra.single_mul_single, mul_one]

omit [DecidableEq X] in
/-- The target-limit element represented by the identity word is one. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetOf_one
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N (1 : FreeGroup X) = 1 := by
  apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (finiteFoxStageTargetQuotient (X := X) N)
      (1 : finiteFoxStageTargetQuotient (X := X) N) =
    (1 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a)
  simpa using
    (map_one (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (finiteFoxStageTargetQuotient (X := X) N)))

omit [DecidableEq X] in
/-- The target-limit representative of a product is the product of target-limit representatives. -/
theorem finiteFoxStagePrimePowerTargetOf_mul
    (N : Subgroup (FreeGroup X)) [N.Normal] (u v : FreeGroup X) :
    finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N (u * v) =
      finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N u *
        finiteFoxStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N v := by
  apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (finiteFoxStageTargetQuotient (X := X) N)
      (QuotientGroup.mk' N (u * v)) =
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u) *
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N v)
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, MonoidAlgebra.of_apply,
  MonoidAlgebra.single_mul_single, mul_one]




end

end FoxDifferential
