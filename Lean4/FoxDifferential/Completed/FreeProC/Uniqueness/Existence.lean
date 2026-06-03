import FoxDifferential.Completed.FreeProC.Uniqueness.Lift
import FoxDifferential.Completed.FreeProC.Uniqueness.Morphism

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/Uniqueness/Existence.lean
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

/-- Existence and uniqueness of the free pro-`C` completed Fox derivative vector, formulated as
the left component of a continuous semidirect homomorphism with prescribed generator data. -/
theorem existsUnique_freeProCZCCompletedFoxDerivativeVector_of_semidirectLiftHom
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
      ∃ f : F →ₜ* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        (∀ g : F, delta g = (f g).left) ∧
        (∀ x : X, (f (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
        ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxDerivativeVector
    (ProC := ProC) hι htarget φ hφ, ?_, ?_⟩
  · refine ⟨freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htarget φ hφ, ?_, ?_, ?_⟩
    · intro g
      rfl
    · exact freeProCZCCompletedFoxSemidirectLiftHom_left_generator
        (ProC := ProC) hι htarget φ hφ
    · exact freeProCZCCompletedFoxSemidirectLiftHom_right_generator
        (ProC := ProC) hι htarget φ hφ
  · intro delta hdelta
    rcases hdelta with ⟨f, hdelta_left, hleft, hright⟩
    have hf_eq := freeProCZCCompletedFoxSemidirectLiftHom_unique_of_components
      (ProC := ProC) hι htarget φ hφ f hleft hright
    funext g
    calc
      delta g = (f g).left := hdelta_left g
      _ = (freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htarget φ hφ g).left := by
            rw [hf_eq]
      _ = freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι htarget φ hφ g := rfl

/-- Existence and uniqueness of the continuous completed Fox semidirect lift from a free pro-`C`
source. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLift
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      Continuous f ∧
        ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x :=
  hι.existsUnique_lift htarget (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) hφ

/-- Componentwise existence and uniqueness of the continuous completed Fox semidirect lift from a
free pro-`C` source. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLift_components
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
      Continuous f ∧
        (∀ x : X, (f (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
        ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ, ?_, ?_⟩
  · exact ⟨
      continuous_freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ,
      freeProCZCCompletedFoxSemidirectLift_left_generator
        (ProC := ProC) hι htarget φ hφ,
      freeProCZCCompletedFoxSemidirectLift_right_generator
        (ProC := ProC) hι htarget φ hφ⟩
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLift_unique_of_components
      (ProC := ProC) hι htarget φ hφ f hf.1 hf.2.1 hf.2.2


end

end FoxDifferential
