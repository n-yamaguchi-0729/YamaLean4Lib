import FoxDifferential.Completed.FreeProC.Uniqueness.SemidirectHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/Uniqueness/Lift.lean
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

/-- Continuous completed Fox semidirect lifts from a free pro-`C` source are unique once their
generator values are prescribed. -/
theorem freeProCZCCompletedFoxSemidirectLift_unique
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (hf : Continuous f)
    (hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x) :
    f = freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ :=
  hι.lift_unique htarget (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)
    hφ hf hgenerator

/-- Componentwise uniqueness for continuous completed Fox semidirect lifts from a free pro-`C`
source. -/
theorem freeProCZCCompletedFoxSemidirectLift_unique_of_components
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (hf : Continuous f)
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    f = freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ := by
  apply freeProCZCCompletedFoxSemidirectLift_unique
    (ProC := ProC) hι htarget φ hφ f hf
  intro x
  apply ZCCompletedFoxSemidirect.ext
  · exact hleft x
  · exact hright x

/-- Continuous completed Fox semidirect homomorphisms from a free pro-`C` source are unique once
their generator values are prescribed. -/
theorem freeProCZCCompletedFoxSemidirectLiftHom_unique
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htarget φ hφ :=
  hι.liftHom_unique htarget (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)
    hφ hgenerator

/-- Componentwise uniqueness for continuous completed Fox semidirect homomorphisms from a free
pro-`C` source. -/
theorem freeProCZCCompletedFoxSemidirectLiftHom_unique_of_components
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htarget φ hφ := by
  apply freeProCZCCompletedFoxSemidirectLiftHom_unique
    (ProC := ProC) hι htarget φ hφ f
  intro x
  apply ZCCompletedFoxSemidirect.ext
  · exact hleft x
  · exact hright x

/-- Existence and uniqueness of the continuous completed Fox semidirect homomorphism from a free
pro-`C` source. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftHom
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htarget φ hφ, ?_, ?_⟩
  · exact freeProCZCCompletedFoxSemidirectLiftHom_generator
      (ProC := ProC) hι htarget φ hφ
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftHom_unique
      (ProC := ProC) hι htarget φ hφ f hf

/-- Componentwise existence and uniqueness of the continuous completed Fox semidirect
homomorphism from a free pro-`C` source. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_components
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      (∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
      ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htarget φ hφ, ?_, ?_⟩
  · exact ⟨
      freeProCZCCompletedFoxSemidirectLiftHom_left_generator
        (ProC := ProC) hι htarget φ hφ,
      freeProCZCCompletedFoxSemidirectLiftHom_right_generator
        (ProC := ProC) hι htarget φ hφ⟩
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftHom_unique_of_components
      (ProC := ProC) hι htarget φ hφ f hf.1 hf.2


end

end FoxDifferential
