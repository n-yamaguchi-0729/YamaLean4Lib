import ReidemeisterSchreier.Discrete.Presentations.Tietze.Core

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/Presentations/Tietze/RelatorReplacement.lean
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

namespace Presented

variable {X Y : Type*}

noncomputable def refl (R : Set (FreeGroup X)) :
    PresentedGroup R ≃* PresentedGroup R :=
  MulEquiv.refl (PresentedGroup R)

noncomputable def symm
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (e : PresentedGroup R ≃* PresentedGroup S) :
    PresentedGroup S ≃* PresentedGroup R :=
  e.symm

noncomputable def trans
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)} {Z : Type*}
    {T : Set (FreeGroup Z)}
    (e₁ : PresentedGroup R ≃* PresentedGroup S)
    (e₂ : PresentedGroup S ≃* PresentedGroup T) :
    PresentedGroup R ≃* PresentedGroup T :=
  e₁.trans e₂

noncomputable def ofMutualMapData
    (R : Set (FreeGroup X)) (S : Set (FreeGroup Y))
    (D : RelatorQuotientMutualMapData R S) :
    PresentedGroup R ≃* PresentedGroup S :=
  quotientEquivOfRelatorQuotientMutualMapData R S D

noncomputable def ofTietzeEquiv
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (D : TietzeEquiv R S) :
    PresentedGroup R ≃* PresentedGroup S :=
  D.presentedEquiv

noncomputable def ofNormalClosureEq
    {R S : Set (FreeGroup X)}
    (h : Subgroup.normalClosure R = Subgroup.normalClosure S) :
    PresentedGroup R ≃* PresentedGroup S :=
  QuotientGroup.congr
    (Subgroup.normalClosure R)
    (Subgroup.normalClosure S)
    (MulEquiv.refl (FreeGroup X))
    (by simpa using h)

noncomputable def ofGeneratorMaps
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
    PresentedGroup R ≃* PresentedGroup S :=
  (TietzeEquiv.ofGeneratorMaps
    toGenerator invGenerator hR hS hinv_to hto_inv).presentedEquiv

noncomputable def ofGeneratorMapsRelatorEquivalent
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
    PresentedGroup R ≃* PresentedGroup S :=
  (TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    toGenerator invGenerator hR hS hinv_to hto_inv).presentedEquiv

noncomputable def replaceRelators
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    PresentedGroup R ≃* PresentedGroup S :=
  ofNormalClosureEq (normalClosure_eq_of_relatorEquivalent hR_to_S hS_to_R)

def replaceRelatorsTietzeEquiv
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeEquiv R S :=
  TietzeEquiv.ofRelatorEquivalent hR_to_S hS_to_R

noncomputable def replaceRelator
    {R : Set (FreeGroup X)} {oldRelator newRelator : FreeGroup X}
    (holdRelator :
      RelatorEquivalent (insert newRelator (R \ {oldRelator})) oldRelator 1)
    (hnewRelator : RelatorEquivalent R newRelator 1) :
    PresentedGroup R ≃*
      PresentedGroup (insert newRelator (R \ {oldRelator})) :=
  replaceRelators
    (S := insert newRelator (R \ {oldRelator}))
    (by
      intro r hr
      by_cases hrold : r = oldRelator
      · simpa [hrold] using holdRelator
      · exact RelatorEquivalent.of_mem
          (R := insert newRelator (R \ {oldRelator}))
          (Or.inr ⟨hr, by simpa [Set.mem_singleton_iff] using hrold⟩))
    (by
      intro s hs
      rcases hs with rfl | hs
      · exact hnewRelator
      · exact RelatorEquivalent.of_mem (R := R) hs.1)

def replaceRelatorTietzeEquiv
    {R : Set (FreeGroup X)} {oldRelator newRelator : FreeGroup X}
    (holdRelator :
      RelatorEquivalent (insert newRelator (R \ {oldRelator})) oldRelator 1)
    (hnewRelator : RelatorEquivalent R newRelator 1) :
    TietzeEquiv R (insert newRelator (R \ {oldRelator})) :=
  replaceRelatorsTietzeEquiv
    (S := insert newRelator (R \ {oldRelator}))
    (by
      intro r hr
      by_cases hrold : r = oldRelator
      · simpa [hrold] using holdRelator
      · exact RelatorEquivalent.of_mem
          (R := insert newRelator (R \ {oldRelator}))
          (Or.inr ⟨hr, by simpa [Set.mem_singleton_iff] using hrold⟩))
    (by
      intro s hs
      rcases hs with rfl | hs
      · exact hnewRelator
      · exact RelatorEquivalent.of_mem (R := R) hs.1)

theorem normalClosure_union_eq_left_of_subset
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    Subgroup.normalClosure (R ∪ S) = Subgroup.normalClosure R := by
  apply normalClosure_eq_of_subset_normalClosure
  · intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_normalClosure hx
    · exact hS hx
  · intro x hx
    exact Subgroup.subset_normalClosure (Or.inl hx)

theorem normalClosure_sdiff_eq_of_subset
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    Subgroup.normalClosure R = Subgroup.normalClosure (R \ D) := by
  apply normalClosure_eq_of_subset_normalClosure
  · intro r hr
    by_cases hd : r ∈ D
    · exact hD r hd hr
    · exact Subgroup.subset_normalClosure ⟨hr, hd⟩
  · intro r hr
    exact Subgroup.subset_normalClosure hr.1

noncomputable def addRedundantRelators
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    PresentedGroup (R ∪ S) ≃* PresentedGroup R :=
  ofNormalClosureEq (normalClosure_union_eq_left_of_subset hS)

noncomputable def addRedundantRelatorsRelatorEquivalent
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    PresentedGroup (R ∪ S) ≃* PresentedGroup R :=
  addRedundantRelators
    (R := R) (S := S)
    (fun s hs => RelatorEquivalent.mem_normalClosure_of_eq_one (hS s hs))

def addRedundantRelatorsTietzeEquiv
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    TietzeEquiv (R ∪ S) R :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_union_eq_left_of_subset hS)

def addRedundantRelatorsRelatorEquivalentTietzeEquiv
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeEquiv (R ∪ S) R :=
  addRedundantRelatorsTietzeEquiv
    (R := R) (S := S)
    (fun s hs => RelatorEquivalent.mem_normalClosure_of_eq_one (hS s hs))

noncomputable def addRedundantRelatorsInverse
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    PresentedGroup R ≃* PresentedGroup (R ∪ S) :=
  (addRedundantRelators (R := R) (S := S) hS).symm

noncomputable def addRedundantRelatorsRelatorEquivalentInverse
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    PresentedGroup R ≃* PresentedGroup (R ∪ S) :=
  (addRedundantRelatorsRelatorEquivalent (R := R) (S := S) hS).symm

noncomputable def removeRelatorSubset
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    PresentedGroup R ≃* PresentedGroup (R \ D) :=
  ofNormalClosureEq (normalClosure_sdiff_eq_of_subset hD)

noncomputable def removeRelatorSubsetRelatorEquivalent
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    PresentedGroup R ≃* PresentedGroup (R \ D) :=
  removeRelatorSubset
    (R := R) (D := D)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))

def removeRelatorSubsetTietzeEquiv
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    TietzeEquiv R (R \ D) :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_sdiff_eq_of_subset hD)

def removeRelatorSubsetRelatorEquivalentTietzeEquiv
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    TietzeEquiv R (R \ D) :=
  removeRelatorSubsetTietzeEquiv
    (R := R) (D := D)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))

noncomputable def removeRelatorSubsetInverse
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    PresentedGroup (R \ D) ≃* PresentedGroup R :=
  (removeRelatorSubset (R := R) (D := D) hD).symm

noncomputable def removeRelatorSubsetRelatorEquivalentInverse
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    PresentedGroup (R \ D) ≃* PresentedGroup R :=
  (removeRelatorSubsetRelatorEquivalent (R := R) (D := D) hD).symm

/-- Replace a whole subfamily `D` of relators by a new family `E`.  Relators
outside `D` are kept unchanged. -/
noncomputable def replaceRelatorSubset
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure ((R \ D) ∪ E))
    (hE : E ⊆ Subgroup.normalClosure R) :
    PresentedGroup R ≃* PresentedGroup ((R \ D) ∪ E) :=
  replaceRelators
    (S := (R \ D) ∪ E)
    (by
      intro r hr
      by_cases hd : r ∈ D
      · exact RelatorEquivalent.of_mem_normalClosure (hD r hd hr)
      · exact RelatorEquivalent.of_mem (R := (R \ D) ∪ E)
          (Or.inl ⟨hr, hd⟩))
    (by
      intro s hs
      rcases hs with hs | hs
      · exact RelatorEquivalent.of_mem (R := R) hs.1
      · exact RelatorEquivalent.of_mem_normalClosure (hE hs))

noncomputable def replaceRelatorSubsetRelatorEquivalent
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → RelatorEquivalent ((R \ D) ∪ E) d 1)
    (hE : ∀ e ∈ E, RelatorEquivalent R e 1) :
    PresentedGroup R ≃* PresentedGroup ((R \ D) ∪ E) :=
  replaceRelatorSubset
    (R := R) (D := D) (E := E)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))
    (fun e he => RelatorEquivalent.mem_normalClosure_of_eq_one (hE e he))

def replaceRelatorSubsetTietzeEquiv
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure ((R \ D) ∪ E))
    (hE : E ⊆ Subgroup.normalClosure R) :
    TietzeEquiv R ((R \ D) ∪ E) :=
  replaceRelatorsTietzeEquiv
    (S := (R \ D) ∪ E)
    (by
      intro r hr
      by_cases hd : r ∈ D
      · exact RelatorEquivalent.of_mem_normalClosure (hD r hd hr)
      · exact RelatorEquivalent.of_mem (R := (R \ D) ∪ E)
          (Or.inl ⟨hr, hd⟩))
    (by
      intro s hs
      rcases hs with hs | hs
      · exact RelatorEquivalent.of_mem (R := R) hs.1
      · exact RelatorEquivalent.of_mem_normalClosure (hE hs))

def replaceRelatorSubsetRelatorEquivalentTietzeEquiv
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → RelatorEquivalent ((R \ D) ∪ E) d 1)
    (hE : ∀ e ∈ E, RelatorEquivalent R e 1) :
    TietzeEquiv R ((R \ D) ∪ E) :=
  replaceRelatorSubsetTietzeEquiv
    (R := R) (D := D) (E := E)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))
    (fun e he => RelatorEquivalent.mem_normalClosure_of_eq_one (hE e he))

noncomputable def addRedundantRelator
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure R) :
    PresentedGroup (insert r R) ≃* PresentedGroup R :=
  ofNormalClosureEq (normalClosure_insert_eq_of_mem (R := R) hr)

def addRedundantRelatorTietzeEquiv
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure R) :
    TietzeEquiv (insert r R) R :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_insert_eq_of_mem (R := R) hr)

noncomputable def removeRedundantRelator
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure (R \ {r})) :
    PresentedGroup R ≃* PresentedGroup (R \ {r}) :=
  ofNormalClosureEq (normalClosure_diff_singleton_eq_of_mem (R := R) hr)

def removeRedundantRelatorTietzeEquiv
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure (R \ {r})) :
    TietzeEquiv R (R \ {r}) :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_diff_singleton_eq_of_mem (R := R) hr)

noncomputable def renameGenerators
    (R : Set (FreeGroup X)) (e : X ≃ Y) :
    PresentedGroup R ≃*
      PresentedGroup (FreeGroup.freeGroupCongr e '' R) :=
  PresentedGroup.equivPresentedGroup R e

def renameGeneratorsTietzeEquiv
    (R : Set (FreeGroup X)) (e : X ≃ Y) :
    TietzeEquiv R (FreeGroup.freeGroupCongr e '' R) :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfRelatorImagesMemNormalClosure
      (FreeGroup.freeGroupCongr e)
      R (FreeGroup.freeGroupCongr e '' R)
      (by
        intro r hr
        exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩)
      (by
        intro s hs
        rcases hs with ⟨r, hr, rfl⟩
        have hback :
            (FreeGroup.freeGroupCongr e).symm
                ((FreeGroup.freeGroupCongr e) r) = r :=
          (FreeGroup.freeGroupCongr e).left_inv r
        rw [hback]
        exact Subgroup.subset_normalClosure hr))

end Presented

end ReidemeisterSchreier.Discrete.Presentations
