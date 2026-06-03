import FoxDifferential.Completed.FreeProC.SemidirectLift

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/Uniqueness/Morphism.lean
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

/-- Categorical completed Fox semidirect morphisms from a free pro-`C` source are unique once
their generator values are prescribed. -/
theorem freeProCZCCompletedFoxSemidirectLiftMorphism_unique
    [ProCGroups.ProC.ProCGroup ProC F]
    [ProCGroups.ProC.ProCGroup ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f :
      ProCGrp.of ProC F ⟶
        ProCGrp.of ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftMorphism
      (ProC := ProC) hι φ hφ :=
  hι.liftMorphism_unique
    (ProCGrp.of ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) hφ
    (f := f) hgenerator

/-- Componentwise uniqueness for categorical completed Fox semidirect morphisms from a free
pro-`C` source. -/
theorem freeProCZCCompletedFoxSemidirectLiftMorphism_unique_of_components
    [ProCGroups.ProC.ProCGroup ProC F]
    [ProCGroups.ProC.ProCGroup ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f :
      ProCGrp.of ProC F ⟶
        ProCGrp.of ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftMorphism
      (ProC := ProC) hι φ hφ := by
  apply freeProCZCCompletedFoxSemidirectLiftMorphism_unique
    (ProC := ProC) hι φ hφ f
  intro x
  apply ZCCompletedFoxSemidirect.ext
  · exact hleft x
  · exact hright x

/-- Existence and uniqueness of the categorical completed Fox semidirect morphism from a free
pro-`C` source. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftMorphism
    [ProCGroups.ProC.ProCGroup ProC F]
    [ProCGroups.ProC.ProCGroup ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! f :
      ProCGrp.of ProC F ⟶
        ProCGrp.of ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftMorphism
      (ProC := ProC) hι φ hφ, ?_, ?_⟩
  · exact freeProCZCCompletedFoxSemidirectLiftMorphism_generator
      (ProC := ProC) hι φ hφ
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftMorphism_unique
      (ProC := ProC) hι φ hφ f hf

/-- Componentwise existence and uniqueness of the categorical completed Fox semidirect morphism
from a free pro-`C` source. -/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftMorphism_components
    [ProCGroups.ProC.ProCGroup ProC F]
    [ProCGroups.ProC.ProCGroup ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! f :
      ProCGrp.of ProC F ⟶
        ProCGrp.of ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
      (∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
      ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftMorphism
      (ProC := ProC) hι φ hφ, ?_, ?_⟩
  · exact ⟨
      freeProCZCCompletedFoxSemidirectLiftMorphism_left_generator
        (ProC := ProC) hι φ hφ,
      freeProCZCCompletedFoxSemidirectLiftMorphism_right_generator
        (ProC := ProC) hι φ hφ⟩
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftMorphism_unique_of_components
      (ProC := ProC) hι φ hφ f hf.1 hf.2

/-- Existence and uniqueness of the free pro-`C` completed Fox derivative vector, formulated as
the left component of a categorical completed Fox semidirect morphism with prescribed generator
data. -/
theorem existsUnique_freeProCZCCompletedFoxDerivativeVector_of_semidirectMorphism
    [ProCGroups.ProC.ProCGroup ProC F]
    [ProCGroups.ProC.ProCGroup ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
      ∃ f :
        ProCGrp.of ProC F ⟶
          ProCGrp.of ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
        (∀ g : F, delta g = (f g).left) ∧
        (∀ x : X, (f (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
        ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxDerivativeVector
    (ProC := ProC) hι
      (inferInstanceAs
        (ProCGroups.ProC.ProCGroup ProC (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))).isProC
      φ hφ, ?_, ?_⟩
  · refine ⟨freeProCZCCompletedFoxSemidirectLiftMorphism
      (ProC := ProC) hι φ hφ, ?_, ?_, ?_⟩
    · intro g
      rfl
    · exact freeProCZCCompletedFoxSemidirectLiftMorphism_left_generator
        (ProC := ProC) hι φ hφ
    · exact freeProCZCCompletedFoxSemidirectLiftMorphism_right_generator
        (ProC := ProC) hι φ hφ
  · intro delta hdelta
    rcases hdelta with ⟨f, hdelta_left, hleft, hright⟩
    have hf_eq := freeProCZCCompletedFoxSemidirectLiftMorphism_unique_of_components
      (ProC := ProC) hι φ hφ f hleft hright
    funext g
    calc
      delta g = (f g).left := hdelta_left g
      _ = (freeProCZCCompletedFoxSemidirectLiftMorphism
      (ProC := ProC) hι φ hφ g).left := by
            rw [hf_eq]
      _ = freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι
            (inferInstanceAs
              (ProCGroups.ProC.ProCGroup ProC
                (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))).isProC
            φ hφ g := rfl


end

end FoxDifferential
