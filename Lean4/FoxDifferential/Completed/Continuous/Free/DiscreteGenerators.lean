import FoxDifferential.Completed.Continuous.Free.CanonicalFormula
import FoxDifferential.Completed.FreeProC.Uniqueness.Existence

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Free/DiscreteGenerators.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous crossed differentials

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u


variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {F : Type u}
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [TopologicalSpace X]

variable [DiscreteTopology X]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Continuous completed Fox semidirect homomorphisms from a free pro-`C` source are unique for
discrete generators, without a separate generator-continuity hypothesis. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLiftHom
    (ProC := ProC) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X H φ)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Componentwise continuous completed Fox semidirect homomorphisms from a free pro-`C` source
are unique for discrete generators, without a separate generator-continuity hypothesis. -/
theorem existsUnique_freeProCZCFoxSemiLiftHom_components_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      (∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
      ∀ x : X, (f (ι x)).right = φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_components
    (ProC := ProC) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X H φ)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Continuous completed Fox semidirect lifts from a free pro-`C` source are unique for discrete
generators, without a separate generator-continuity hypothesis. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLift_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H) :
    ∃! f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      Continuous f ∧
        ∀ x : X, f (ι x) =
          freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLift
    (ProC := ProC) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X H φ)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Componentwise continuous completed Fox semidirect lifts from a free pro-`C` source are unique
for discrete generators, without a separate generator-continuity hypothesis. -/
theorem existsUnique_freeProCZCFoxSemiLift_components_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H) :
    ∃! f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      Continuous f ∧
        (∀ x : X, (f (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
        ∀ x : X, (f (ι x)).right = φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLift_components
    (ProC := ProC) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X H φ)



end

end FoxDifferential
