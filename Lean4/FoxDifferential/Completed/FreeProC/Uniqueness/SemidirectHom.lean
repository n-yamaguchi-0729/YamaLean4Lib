import FoxDifferential.Completed.FreeProC.SemidirectLift

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/Uniqueness/SemidirectHom.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C completed Fox calculus

Free pro-C sources are treated through completed Fox derivatives, stage projections, density arguments, and semidirect lift formulas.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.FreeProC

universe u


variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X F H : Type u}
variable [TopologicalSpace X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]

/-- A completed crossed differential and its coefficient homomorphism combine into a semidirect
homomorphism. -/
def freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
    (ψ : F →* H) (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta) :
    F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H where
  toFun g := { left := delta g, right := ψ g }
  map_one' := by
    apply ZCCompletedFoxSemidirect.ext
    · simpa using IsCrossedDifferential.one hdelta
    · simp only [map_one, ZCCompletedFoxSemidirect.one_right]
  map_mul' g h := by
    apply ZCCompletedFoxSemidirect.ext
    · simpa using hdelta g h
    · simp only [map_mul, ZCCompletedFoxSemidirect.mul_right]

omit [TopologicalSpace X] [TopologicalSpace F] [IsTopologicalGroup F] [DecidableEq X]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- The semidirect homomorphism attached to a crossed differential has `delta` as its left
component. -/
@[simp]
theorem freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_left
    (ψ : F →* H) (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (g : F) :
    (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta hdelta g).left = delta g :=
  rfl

omit [TopologicalSpace X] [TopologicalSpace F] [IsTopologicalGroup F] [DecidableEq X]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- The semidirect homomorphism attached to a crossed differential has `ψ` as its right
component. -/
@[simp]
theorem freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_right
    (ψ : F →* H) (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (g : F) :
    (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta hdelta g).right = ψ g :=
  rfl

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- If a crossed-differential semidirect homomorphism is continuous and has the standard
generator coordinates, then the corresponding semidirect generator map is continuous. -/
theorem continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (ψ : F →* H) (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hcontinuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta hdelta))
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) (fun x : X => ψ (ι x))) := by
  have hgenerator :
      (fun x : X =>
        freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
          (X := X) ψ delta hdelta (ι x)) =
        freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) (fun x : X => ψ (ι x)) := by
    funext x
    apply ZCCompletedFoxSemidirect.ext
    · exact hbasis x
    · rfl
  rw [← hgenerator]
  exact hcontinuous.comp hι.continuous_ι


end

end FoxDifferential
