import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.OnGroup.Scalar

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/OnGroup/Vector.lean
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


/-- The dense group-level completed-target Fox derivative vector.

It evaluates the completed-target derivative vector on group-like elements of the source completed
group algebra. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    FreeGroup X →
      (X → PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N)) :=
  fun w =>
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for the dense group-level completed-target Fox derivative vector. -/
@[simp]
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_apply
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) (i : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite w i =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i w := rfl

omit [Fact (0 < ℓ)] in
/-- The completed-target Fox derivative vector on group-like source elements is a crossed
differential over the completed target coefficient homomorphism. -/
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_isCrossedDiff
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    IsCrossedDifferential
      (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite) := by
  intro u v
  funext i
  simpa [primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_apply]
    using
      (ppCompletedGAFoxDerivToTargetOnGroup_isCrossedDiff
        (ℓ := ℓ) (X := X) N hfinite i u v)

omit [Fact (0 < ℓ)] in
/-- On a free generator, the completed-target derivative vector has the corresponding standard
basis vector as its value. -/
@[simp 900]
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (j : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite (FreeGroup.of j) =
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)) := by
  funext i
  rw [primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of]
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same]
  · have hij : i ≠ j := by
      exact Ne.symm hji
    simp only [ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, hij]

omit [Fact (0 < ℓ)] in
/-- The completed-target Fox derivative vector on group-like source elements is the unique crossed
differential with standard basis values on the free generators. -/
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (delta : FreeGroup X →
      (X → PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N)))
    (hdelta : IsCrossedDifferential
      (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      delta)
    (hbasis : ∀ j : X, delta (FreeGroup.of j) =
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N))) :
    delta =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite := by
  have hdelta_free := freeCrossedDifferentialWithCoeff_unique
    (A := X → PrimePowerCompletedGroupAlgebra ℓ
      (finiteFoxStageTargetQuotient (X := X) N))
    (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    (fun j : X =>
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)))
    delta hdelta hbasis
  have hcompleted_free := freeCrossedDifferentialWithCoeff_unique
    (A := X → PrimePowerCompletedGroupAlgebra ℓ
      (finiteFoxStageTargetQuotient (X := X) N))
    (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    (fun j : X =>
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (finiteFoxStageTargetQuotient (X := X) N)))
    (primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
      (ℓ := ℓ) (X := X) N hfinite)
    (primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_isCrossedDiff
      (ℓ := ℓ) (X := X) N hfinite)
    (primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of
      (ℓ := ℓ) (X := X) N hfinite)
  exact hdelta_free.trans hcompleted_free.symm

omit [Fact (0 < ℓ)] in
/-- Existence and uniqueness of the completed-target Fox derivative vector on group-like source
elements, characterized by the crossed-differential rule and the standard basis values. -/
theorem existsUnique_primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    ∃! delta : FreeGroup X →
      (X → PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N)),
      IsCrossedDifferential
        (finiteFoxStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
        delta ∧
        ∀ j : X, delta (FreeGroup.of j) =
          Pi.single j
            (1 : PrimePowerCompletedGroupAlgebra ℓ
              (finiteFoxStageTargetQuotient (X := X) N)) := by
  refine ⟨primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
    (ℓ := ℓ) (X := X) N hfinite, ?_, ?_⟩
  · exact ⟨
      primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_isCrossedDiff
        (ℓ := ℓ) (X := X) N hfinite,
      primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of
        (ℓ := ℓ) (X := X) N hfinite⟩
  · intro delta hdelta
    exact primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_unique
      (ℓ := ℓ) (X := X) N hfinite delta hdelta.1 hdelta.2




end

end FoxDifferential
