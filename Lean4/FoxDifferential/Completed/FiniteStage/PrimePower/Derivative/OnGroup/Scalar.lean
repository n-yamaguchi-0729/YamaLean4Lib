import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.OnGroup.Coefficient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/OnGroup/Scalar.lean
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


/-- The dense group-level form of the completed-target Fox derivative.

This is the completed-target derivative evaluated on group-like elements of the source
completed group algebra. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    FreeGroup X →
      PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N) :=
  fun w =>
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for the group-level completed-target Fox derivative. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_apply
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i w =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) := rfl

omit [Fact (0 < ℓ)] in
/-- The completed-target Fox derivative on group-like source elements satisfies the crossed
differential product rule over the completed target coefficient homomorphism. -/
theorem ppCompletedGAFoxDerivToTargetOnGroup_isCrossedDiff
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    IsCrossedDifferential
      (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i) := by
  intro u v
  simpa [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup]
    using primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul
      (ℓ := ℓ) (X := X) N hfinite i u v

omit [Fact (0 < ℓ)] in
/-- On a free generator, the group-level completed-target Fox derivative has the expected
Kronecker generator value. -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i j : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i (FreeGroup.of j) =
      ((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)) j := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro k
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_apply]
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) k
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
          (FreeGroup.of j))) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) k
      (((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)) j)
  rw [ppCompletedGAFoxDerivToTarget_generator_proj]
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same, map_one, InverseSystem.projection_apply,
  coe_one_primePowerCompletedGroupAlgebra, Pi.one_apply]
  · have hij : i ≠ j := by
      exact Ne.symm hji
    simp only [ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne, map_zero, hji, InverseSystem.projection_apply,
  coe_zero_primePowerCompletedGroupAlgebra, Pi.zero_apply]

omit [Fact (0 < ℓ)] in
/-- The group-level completed-target Fox derivative is the unique crossed differential with its
standard Kronecker values on free generators. -/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X)
    (delta : FreeGroup X →
      PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N))
    (hdelta : IsCrossedDifferential
      (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      delta)
    (hbasis : ∀ j : X, delta (FreeGroup.of j) =
      ((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)) j) :
    delta =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i := by
  let basisValue : X →
      PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N) :=
    fun j =>
      ((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)) j
  have hdelta_free := freeCrossedDifferentialWithCoeff_unique
    (A := PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N))
    (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    basisValue delta hdelta hbasis
  have hcompleted_free := freeCrossedDifferentialWithCoeff_unique
    (A := PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N))
    (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    basisValue
    (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
      (ℓ := ℓ) (X := X) N hfinite i)
    (ppCompletedGAFoxDerivToTargetOnGroup_isCrossedDiff
      (ℓ := ℓ) (X := X) N hfinite i)
    (by
      intro j
      exact primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of
        (ℓ := ℓ) (X := X) N hfinite i j)
  exact hdelta_free.trans hcompleted_free.symm

omit [Fact (0 < ℓ)] in
/-- Existence and uniqueness of the completed-target Fox derivative on group-like source
elements, characterized as a crossed differential with Kronecker values on the free generators. -/
theorem existsUnique_ppCompletedGAFoxDerivToTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    ∃! delta : FreeGroup X →
      PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N),
      IsCrossedDifferential
        (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
        delta ∧
        ∀ j : X, delta (FreeGroup.of j) =
          ((Pi.single i
            (1 : PrimePowerCompletedGroupAlgebra ℓ
              (finiteFoxStageTargetQuotient (X := X) N))) :
            X → PrimePowerCompletedGroupAlgebra ℓ
              (finiteFoxStageTargetQuotient (X := X) N)) j := by
  refine ⟨primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
    (ℓ := ℓ) (X := X) N hfinite i, ?_, ?_⟩
  · exact ⟨
      ppCompletedGAFoxDerivToTargetOnGroup_isCrossedDiff
        (ℓ := ℓ) (X := X) N hfinite i,
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of
        (ℓ := ℓ) (X := X) N hfinite i⟩
  · intro delta hdelta
    exact primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_unique
      (ℓ := ℓ) (X := X) N hfinite i delta hdelta.1 hdelta.2




end

end FoxDifferential
