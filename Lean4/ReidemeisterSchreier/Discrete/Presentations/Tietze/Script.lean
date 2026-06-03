import ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorDeletion

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/Presentations/Tietze/Script.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Tietze transformations

Presentation-level Tietze moves for adding and deleting generators, replacing relators, comparing quotient presentations, and recording executable Tietze scripts.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

namespace TietzeScript

variable {X Y Z : Type*}

def replaceRelators
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeScript (Presentation.ofRelators R) (Presentation.ofRelators S) :=
  (Presented.replaceRelatorsTietzeEquiv hR_to_S hS_to_R).toScript

def replaceRelator
    {R : Set (FreeGroup X)} {oldRelator newRelator : FreeGroup X}
    (holdRelator :
      RelatorEquivalent (insert newRelator (R \ {oldRelator})) oldRelator 1)
    (hnewRelator : RelatorEquivalent R newRelator 1) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (insert newRelator (R \ {oldRelator}))) :=
  (Presented.replaceRelatorTietzeEquiv holdRelator hnewRelator).toScript

def addRedundantRelator
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure R) :
    TietzeScript (Presentation.ofRelators (insert r R))
      (Presentation.ofRelators R) :=
  (Presented.addRedundantRelatorTietzeEquiv hr).toScript

def addRedundantRelatorInverse
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure R) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (insert r R)) :=
  (Presented.addRedundantRelatorTietzeEquiv hr).symm.toScript

def removeRedundantRelator
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure (R \ {r})) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (R \ {r})) :=
  (Presented.removeRedundantRelatorTietzeEquiv hr).toScript

def addRedundantRelators
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    TietzeScript (Presentation.ofRelators (R ∪ S))
      (Presentation.ofRelators R) :=
  (Presented.addRedundantRelatorsTietzeEquiv hS).toScript

def addRedundantRelatorsRelatorEquivalent
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeScript (Presentation.ofRelators (R ∪ S))
      (Presentation.ofRelators R) :=
  (Presented.addRedundantRelatorsRelatorEquivalentTietzeEquiv hS).toScript

def addRedundantRelatorsInverse
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (R ∪ S)) :=
  (Presented.addRedundantRelatorsTietzeEquiv hS).symm.toScript

def addRedundantRelatorsRelatorEquivalentInverse
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (R ∪ S)) :=
  (Presented.addRedundantRelatorsRelatorEquivalentTietzeEquiv hS).symm.toScript

def removeRelatorSubset
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (R \ D)) :=
  (Presented.removeRelatorSubsetTietzeEquiv hD).toScript

def removeRelatorSubsetRelatorEquivalent
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (R \ D)) :=
  (Presented.removeRelatorSubsetRelatorEquivalentTietzeEquiv hD).toScript

def removeRelatorSubsetInverse
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    TietzeScript (Presentation.ofRelators (R \ D))
      (Presentation.ofRelators R) :=
  (Presented.removeRelatorSubsetTietzeEquiv hD).symm.toScript

def removeRelatorSubsetRelatorEquivalentInverse
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    TietzeScript (Presentation.ofRelators (R \ D))
      (Presentation.ofRelators R) :=
  (Presented.removeRelatorSubsetRelatorEquivalentTietzeEquiv hD).symm.toScript

def replaceRelatorSubset
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure ((R \ D) ∪ E))
    (hE : E ⊆ Subgroup.normalClosure R) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators ((R \ D) ∪ E)) :=
  (Presented.replaceRelatorSubsetTietzeEquiv hD hE).toScript

def replaceRelatorSubsetRelatorEquivalent
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → RelatorEquivalent ((R \ D) ∪ E) d 1)
    (hE : ∀ e ∈ E, RelatorEquivalent R e 1) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators ((R \ D) ∪ E)) :=
  (Presented.replaceRelatorSubsetRelatorEquivalentTietzeEquiv hD hE).toScript

def renameGenerators
    (R : Set (FreeGroup X)) (e : X ≃ Y) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (FreeGroup.freeGroupCongr e '' R)) :=
  (Presented.renameGeneratorsTietzeEquiv R e).toScript

def ofGeneratorMaps
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        FreeGroup.lift toGenerator r ∈ Subgroup.normalClosure S)
    (hS :
      ∀ s ∈ S,
        FreeGroup.lift invGenerator s ∈ Subgroup.normalClosure R)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeScript (Presentation.ofRelators R) (Presentation.ofRelators S) :=
  (TietzeEquiv.ofGeneratorMaps
    toGenerator invGenerator hR hS hinv_to hto_inv).toScript

def ofGeneratorMapsRelatorEquivalent
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ s ∈ S,
        RelatorEquivalent R (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeScript (Presentation.ofRelators R) (Presentation.ofRelators S) :=
  (TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    toGenerator invGenerator hR hS hinv_to hto_inv).toScript

def adjoinGenerators
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
    TietzeScript (Presentation.ofRelators R)
      (Presentation.ofRelators (Presented.adjoinGeneratorsRelators R word)) :=
  (Presented.adjoinGeneratorsTietzeEquiv R word).toScript

def substituteDefinedGenerators
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) :
    TietzeScript
      (Presentation.ofRelators (Presented.relatorsWithDefinedGenerators R word))
      (Presentation.ofRelators
        (Presented.relatorsAfterSubstitutingDefinedGenerators R word)) :=
  (Presented.substituteDefinedGeneratorsTietzeEquiv R word).toScript

def deleteTrivialGenerators
    (R : Set (FreeGroup (Sum X Y))) :
    TietzeScript
      (Presentation.ofRelators (Presented.relatorsWithTrivialGenerators R))
      (Presentation.ofRelators
        (Presented.relatorsAfterDeletingTrivialGenerators R)) :=
  (Presented.deleteTrivialGeneratorsTietzeEquiv R).toScript

def substituteDefinedGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    TietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithDefinedGeneratorsAlongEquiv R e word))
      (Presentation.ofRelators
        (Presented.relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv
          R e word)) :=
  (Presented.substituteDefinedGeneratorsAlongEquivTietzeEquiv R e word).toScript

def deleteTrivialGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    TietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithTrivialGeneratorsAlongEquiv R e))
      (Presentation.ofRelators
        (Presented.relatorsAfterDeletingTrivialGeneratorsAlongEquiv R e)) :=
  (Presented.deleteTrivialGeneratorsAlongEquivTietzeEquiv R e).toScript

def substituteDefinedGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete]
    (word :
      Presented.GeneratorPartition.Deleted delete →
        FreeGroup (Presented.GeneratorPartition.Kept delete)) :
    TietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithDefinedGeneratorsOfPredicate R delete word))
      (Presentation.ofRelators
        (Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
          R delete word)) :=
  (Presented.substituteDefinedGeneratorsOfPredicateTietzeEquiv R delete word).toScript

def deleteTrivialGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete] :
    TietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithTrivialGeneratorsOfPredicate R delete))
      (Presentation.ofRelators
        (Presented.relatorsAfterDeletingTrivialGeneratorsOfPredicate
          R delete)) :=
  (Presented.deleteTrivialGeneratorsOfPredicateTietzeEquiv R delete).toScript

end TietzeScript

end ReidemeisterSchreier.Discrete.Presentations
