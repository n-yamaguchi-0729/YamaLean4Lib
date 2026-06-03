import FoxDifferential.Completed.Continuous.Free.SourceFormula

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Free/CanonicalFormula.lean
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

section CanonicalSourceFormula

variable [Fintype X]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Boundary-map form of the source-shaped completed Fox formula for the canonical free pro-`C`
semidirect lift. -/
theorem freeProCZCCompletedFoxDerivativeVector_boundary
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetUnit :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H))
    (φ : X → H) (g : F) :
    freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass φ
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ) g) =
      zcCompletedGroupAlgebraBoundary ProC.finiteQuotientClass
        (freeProCZCCompletedFoxRightHom
          (ProC := ProC) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ)) g := by
  let hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X H φ
  simpa [freeProCZCCompletedFoxBoundary] using
    freeProCZCCompletedFoxBoundary_of_continuousCrossedDifferential
      (ProC := ProC) X H hι htargetUnit
      (freeProCZCCompletedFoxRightHom
        (ProC := ProC) hι htarget φ hφ)
      (freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) hι htarget φ hφ)
      (freeProCZCCompletedFoxDerivativeVector_isCrossedDifferential
        (ProC := ProC) hι htarget φ hφ)
      (continuous_freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) X H hι htarget φ hφ)
      (continuous_freeProCZCCompletedFoxRightHom
        (ProC := ProC) X H hι htarget φ hφ)
      (freeProCZCCompletedFoxDerivativeVector_generator
        (ProC := ProC) hι htarget φ hφ)
      g

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Source-shaped completed Fox fundamental formula for the canonical free pro-`C`
semidirect lift. -/
theorem freeProCZCCompletedFoxDerivative_fundamental_formula
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetUnit :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H))
    (φ : X → H) (g : F) :
    zcCompletedGroupAlgebraBoundary ProC.finiteQuotientClass
        (freeProCZCCompletedFoxRightHom
          (ProC := ProC) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ)) g =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (ProC := ProC) hι htarget φ
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
              (ProC := ProC) X H φ) g x *
          (zcGroupLike ProC.finiteQuotientClass H (φ x) - 1) := by
  simpa [freeProCZCCompletedFoxBoundary_apply] using
    (freeProCZCCompletedFoxDerivativeVector_boundary
      (ProC := ProC) X H hι htarget htargetUnit φ g).symm

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Explicit `[ρ g] - 1` form of the source-shaped completed Fox-Euler formula for the canonical
free pro-`C` semidirect lift. -/
theorem freeProCZCCompletedFoxDerivative_euler_formula
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetUnit :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H))
    (φ : X → H) (g : F) :
    zcGroupLike ProC.finiteQuotientClass H
        (freeProCZCCompletedFoxRightHom
          (ProC := ProC) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ) g) - 1 =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (ProC := ProC) hι htarget φ
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
              (ProC := ProC) X H φ) g x *
          (zcGroupLike ProC.finiteQuotientClass H (φ x) - 1) := by
  simpa [zcCompletedGroupAlgebraBoundary] using
    freeProCZCCompletedFoxDerivative_fundamental_formula
      (ProC := ProC) X H hι htarget htargetUnit φ g

end CanonicalSourceFormula



end

end FoxDifferential
