import FoxDifferential.Completed.DifferentialModule.TargetQuotient.StageMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/TargetQuotient/Surjective.lean
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

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]

omit [DecidableEq X] in
/-- The quotient homomorphism `FreeGroup X -> FreeGroup X / N` is surjective.

This specialized form is used to lift coefficients from `Z_ell[[F/N]]` to
`Z_ell[[F]]` in the completed Fox derivative construction. -/
theorem finiteFoxStageTargetQuotientContinuousMonoidHom_surjective
    [TopologicalSpace (FreeGroup X)] [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)] :
    Function.Surjective
      (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) := by
  intro q
  rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
  exact ⟨w, rfl⟩

omit [DecidableEq X] in
/-- The completed group-algebra map attached to `FreeGroup X -> FreeGroup X / N` is surjective.

This is the coefficient-lifting input for the surjectivity half of `K/KI -> L`. -/
theorem primePowerCompletedGroupAlgebraMap_targetQuotient_surjective
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)] :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)) := by
  exact
    primePowerCompletedGroupAlgebraMap_surjective
      (ℓ := ℓ) (G := FreeGroup X)
      (H := finiteFoxStageTargetQuotient (X := X) N)
      (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)
      (finiteFoxStageTargetQuotientContinuousMonoidHom_surjective (X := X) N)

/-- A noncomputable lift of a completed target-group-algebra coefficient to the source completed
group algebra.  The defining equation is `primePowerCompletedGroupAlgebraMap_targetQuotient_lift_spec`. -/
def primePowerCompletedGroupAlgebraMap_targetQuotient_lift
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (a : PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N)) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) :=
  Classical.choose
    (primePowerCompletedGroupAlgebraMap_targetQuotient_surjective
      (ℓ := ℓ) (X := X) N a)

omit [DecidableEq X] in
/-- The chosen coefficient lift maps back to the prescribed completed target coefficient. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_targetQuotient_lift_spec
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (a : PrimePowerCompletedGroupAlgebra ℓ (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N)
        (primePowerCompletedGroupAlgebraMap_targetQuotient_lift
          (ℓ := ℓ) (X := X) N a) = a :=
  Classical.choose_spec
    (primePowerCompletedGroupAlgebraMap_targetQuotient_surjective
      (ℓ := ℓ) (X := X) N a)


end

end FoxDifferential
