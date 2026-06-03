import FoxDifferential.Completed.Continuous.Free.Continuity

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Free/SourceFormula.lean
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

section SourceFormula

variable [Fintype X]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Source-shaped completed Fox boundary formula for continuous crossed differentials out of an
free pro-`C` source. -/
theorem freeProCZCCompletedFoxBoundary_of_continuousCrossedDifferential
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetUnit :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H))
    (ψ : F →* H)
    (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (g : F) :
    freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass (fun x : X => ψ (ι x))
        (delta g) =
      zcCompletedGroupAlgebraBoundary ProC.finiteQuotientClass ψ g := by
  let beta : F → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H :=
    fun g => freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass
      (fun x : X => ψ (ι x)) (delta g)
  have hbeta :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ)
        beta := by
    exact IsCrossedDifferential.map_linear hdelta
      (freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass (fun x : X => ψ (ι x)))
  let betaVec : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass
      (X := PUnit) (H := H) :=
    fun g _ => beta g
  have hbetaVec :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ)
        betaVec := by
    intro g h
    funext u
    exact hbeta g h
  let boundaryVec : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass
      (X := PUnit) (H := H) :=
    fun g _ => zcCompletedGroupAlgebraBoundary ProC.finiteQuotientClass ψ g
  have hboundaryVec :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ)
        boundaryVec := by
    intro g h
    funext u
    exact zcCompletedGroupAlgebraBoundary_isCrossedDifferential
      ProC.finiteQuotientClass ψ g h
  have hbeta_continuous : Continuous beta := by
    exact (continuous_freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass
      (fun x : X => ψ (ι x))).comp hdelta_continuous
  have hbetaVec_continuous : Continuous betaVec := by
    exact continuous_pi fun _ => hbeta_continuous
  have hboundary_continuous :
      Continuous (zcCompletedGroupAlgebraBoundary ProC.finiteQuotientClass ψ) :=
    continuous_zcCompletedGroupAlgebraBoundary
      (C := ProC.finiteQuotientClass) (G := H) ψ hψ_continuous
  have hboundaryVec_continuous : Continuous boundaryVec := by
    exact continuous_pi fun _ => hboundary_continuous
  let f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := PUnit) (F := F) (H := H) ψ betaVec hbetaVec
  let h : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := PUnit) (F := F) (H := H) ψ boundaryVec hboundaryVec
  have hf_continuous : Continuous f :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := PUnit) (F := F) (H := H)
      ψ betaVec hbetaVec hbetaVec_continuous hψ_continuous
  have hh_continuous : Continuous h :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := PUnit) (F := F) (H := H) ψ boundaryVec hboundaryVec
      hboundaryVec_continuous hψ_continuous
  have hgen : ∀ x : X, f (ι x) = h (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · funext u
      simp only [freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_left, hbasis x,
  freeProCZCCompletedFoxBoundary_single, zcCompletedGroupAlgebraBoundary, f, betaVec, beta, h, boundaryVec]
    · rfl
  have hfh : f = h := hι.hom_ext htargetUnit hf_continuous hh_continuous hgen
  have hleft := congrArg
    (fun q : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H =>
      (q g).left PUnit.unit) hfh
  simpa [f, h, betaVec, boundaryVec, beta] using hleft

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Source-shaped completed Fox fundamental formula for continuous crossed differentials out of
free pro-`C` source. -/
theorem freeProCZCCompletedFoxDerivative_fundFormula_of_continuousCrossedDiff
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetUnit :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H))
    (ψ : F →* H)
    (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (g : F) :
    zcCompletedGroupAlgebraBoundary ProC.finiteQuotientClass ψ g =
      ∑ x : X, delta g x *
        (zcGroupLike ProC.finiteQuotientClass H (ψ (ι x)) - 1) := by
  simpa [freeProCZCCompletedFoxBoundary_apply] using
    (freeProCZCCompletedFoxBoundary_of_continuousCrossedDifferential
      (ProC := ProC) X H hι htargetUnit ψ delta hdelta hdelta_continuous hψ_continuous
      hbasis g).symm

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Explicit `[ψ g] - 1` form of the source-shaped completed Fox-Euler formula for continuous
crossed differentials out of a free pro-`C` source. -/
theorem freeProCZCCompletedFoxDerivative_euler_formula_of_continuousCrossedDifferential
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetUnit :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass PUnit H))
    (ψ : F →* H)
    (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (g : F) :
    zcGroupLike ProC.finiteQuotientClass H (ψ g) - 1 =
      ∑ x : X, delta g x *
        (zcGroupLike ProC.finiteQuotientClass H (ψ (ι x)) - 1) := by
  simpa [zcCompletedGroupAlgebraBoundary] using
    freeProCZCCompletedFoxDerivative_fundFormula_of_continuousCrossedDiff
      (ProC := ProC) X H hι htargetUnit ψ delta hdelta hdelta_continuous hψ_continuous hbasis g

end SourceFormula



end

end FoxDifferential
