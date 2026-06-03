import ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Presentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/ReidemeisterSchreier/FiniteQuotient/TargetPresentation/Core.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite quotient Reidemeister-Schreier presentations

Specializes Reidemeister-Schreier rewriting to finite quotient targets, cleaned symbols, cleaned relators, target presentations, word certificates, and Tietze equivalences.
-/

namespace ReidemeisterSchreier.Discrete.ReidemeisterSchreier

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

/-- Finite quotient Schreier data whose section is prefix closed on its
representative words.  This is the convenient application-facing input for the raw
finite Reidemeister-Schreier presentation theorem. -/
structure PrefixClosedFiniteQuotientSchreierData
    (X Q : Type*) [Group Q] [Fintype Q] [DecidableEq X] where
  toFiniteQuotientSchreierData : FiniteQuotientSchreierData X Q
  isPrefixClosed :
    toFiniteQuotientSchreierData.IsPrefixClosedQuotientSection

/-- Common word-level data for a finite quotient section. -/
structure QuotientSectionWordCertificate
    (X Q : Type*) [Group Q] [Fintype Q] where
  quotientMap : FreeGroup X →* Q
  quotientSectionWord : Q → List (X × Bool)
  quotientMap_mk_quotientSectionWord :
    ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q

/-- A fully general word-level certificate for a prefix-closed finite quotient
section.  This extends the common quotient-section word data with the reduced
word and prefix-closedness proofs required by
`PrefixClosedFiniteQuotientSchreierData.ofPrefixClosedQuotientSectionWords` as a
reusable object. -/
structure PrefixClosedQuotientSectionWordCertificate
    (X Q : Type*) [Group Q] [Fintype Q] [DecidableEq X]
    extends QuotientSectionWordCertificate X Q where
  quotientSectionWord_one : quotientSectionWord 1 = []
  quotientSectionWord_reduced :
    ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q
  prefixClosed_quotientSectionWord :
    ∀ q : Q,
      (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
        quotientSectionWord quotientMap_mk_quotientSectionWord
        quotientSectionWord_one).prefixClosedQuotientSectionWordAlongList
          quotientSectionWord 1 (quotientSectionWord q)

namespace PrefixClosedQuotientSectionWordCertificate

variable [DecidableEq X]
variable (C : PrefixClosedQuotientSectionWordCertificate X Q)

def toFiniteQuotientSchreierData :
    FiniteQuotientSchreierData X Q :=
  FiniteQuotientSchreierData.ofQuotientSectionWords
    C.quotientMap C.quotientSectionWord
    C.quotientMap_mk_quotientSectionWord C.quotientSectionWord_one

def toPrefixClosedFiniteQuotientSchreierData :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData := C.toFiniteQuotientSchreierData
  isPrefixClosed :=
    FiniteQuotientSchreierData.isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
      C.toFiniteQuotientSchreierData
      (by intro q; rfl)
      C.quotientSectionWord_reduced
      (by
        intro q
        exact C.prefixClosed_quotientSectionWord q)

end PrefixClosedQuotientSectionWordCertificate

/-- A certificate for a positive prefix-closed quotient-section tree.  The word
for each quotient element is a positive word in the original generators, and
every prefix of such a word is itself the chosen word for the quotient element it
represents.  From this data the library builds the reduced-word and
prefix-closedness proofs needed by the finite Reidemeister-Schreier theorem. -/
structure PositivePrefixClosedQuotientSectionWordCertificate
    (X Q : Type*) [Group Q] [Fintype Q]
    extends QuotientSectionWordCertificate X Q where
  quotientSectionWord_positive :
    ∀ q : Q, ∀ xb ∈ quotientSectionWord q, xb.2 = true
  prefixState :
    ∀ q : Q, ∀ acc rest : List (X × Bool),
      acc ++ rest = quotientSectionWord q →
        quotientSectionWord (quotientMap (FreeGroup.mk acc)) = acc

namespace PositivePrefixClosedQuotientSectionWordCertificate

variable (C : PositivePrefixClosedQuotientSectionWordCertificate X Q)

theorem quotientSectionWord_one :
    C.quotientSectionWord 1 = [] := by
  have h := C.prefixState 1 [] (C.quotientSectionWord 1) (by simp only [List.nil_append])
  simpa [← FreeGroup.one_eq_mk] using h

theorem quotientSectionWord_reduced [DecidableEq X] (q : Q) :
    FreeGroup.reduce (C.quotientSectionWord q) = C.quotientSectionWord q :=
  FiniteQuotientSchreierData.reduce_eq_of_forall_snd_eq_true
    (C.quotientSectionWord_positive q)

def toFiniteQuotientSchreierData :
    FiniteQuotientSchreierData X Q :=
  FiniteQuotientSchreierData.ofQuotientSectionWords
    C.quotientMap C.quotientSectionWord
    C.quotientMap_mk_quotientSectionWord
    C.quotientSectionWord_one

def toPrefixClosedFiniteQuotientSchreierData [DecidableEq X] :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData := C.toFiniteQuotientSchreierData
  isPrefixClosed := by
    apply
      FiniteQuotientSchreierData.isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
        (D := C.toFiniteQuotientSchreierData)
    · intro q
      rfl
    · intro q
      exact C.quotientSectionWord_reduced q
    · intro q
      exact
        FiniteQuotientSchreierData.prefixClosedQuotientSectionWordAlongList_of_positive_prefixStates
          (D := C.toFiniteQuotientSchreierData)
          (by intro q; rfl)
          C.quotientSectionWord_positive
          (by
            intro target acc rest hcat
            simpa [toFiniteQuotientSchreierData,
              FiniteQuotientSchreierData.ofQuotientSectionWords] using
              C.prefixState target acc rest hcat)
          q

end PositivePrefixClosedQuotientSectionWordCertificate

namespace PrefixClosedFiniteQuotientSchreierData

variable [DecidableEq X]

def ofQuotientSectionWords
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (quotientSectionWord_reduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (prefixClosed_quotientSectionWord :
      ∀ q : Q,
        (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
          quotientSectionWord quotientMap_mk_quotientSectionWord
          quotientSectionWord_one).prefixClosedAlongList 1
            (quotientSectionWord q)) :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData :=
    FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
      quotientSectionWord quotientMap_mk_quotientSectionWord
      quotientSectionWord_one
  isPrefixClosed := by
    intro q
    simpa [FiniteQuotientSchreierData.ofQuotientSectionWords,
      FreeGroup.toWord_mk, quotientSectionWord_reduced q] using
      prefixClosed_quotientSectionWord q

def ofPrefixClosedQuotientSectionWords
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (quotientSectionWord_reduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (prefixClosed_quotientSectionWord :
      ∀ q : Q,
        FiniteQuotientSchreierData.prefixClosedQuotientSectionWordAlongList
          (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
            quotientSectionWord quotientMap_mk_quotientSectionWord
            quotientSectionWord_one)
          quotientSectionWord 1 (quotientSectionWord q)) :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData :=
    FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
      quotientSectionWord quotientMap_mk_quotientSectionWord
      quotientSectionWord_one
  isPrefixClosed :=
    FiniteQuotientSchreierData.isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
      (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
        quotientSectionWord quotientMap_mk_quotientSectionWord
        quotientSectionWord_one)
      (by intro q; rfl)
      quotientSectionWord_reduced
      prefixClosed_quotientSectionWord

@[simp 900]
theorem ofQuotientSectionWords_toFiniteQuotientSchreierData
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (quotientSectionWord_reduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (prefixClosed_quotientSectionWord :
      ∀ q : Q,
        (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
          quotientSectionWord quotientMap_mk_quotientSectionWord
          quotientSectionWord_one).prefixClosedAlongList 1
            (quotientSectionWord q)) :
    (ofQuotientSectionWords quotientMap quotientSectionWord
      quotientMap_mk_quotientSectionWord quotientSectionWord_one
      quotientSectionWord_reduced prefixClosed_quotientSectionWord).toFiniteQuotientSchreierData =
      FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
        quotientSectionWord quotientMap_mk_quotientSectionWord
        quotientSectionWord_one :=
  rfl

variable (D : PrefixClosedFiniteQuotientSchreierData X Q)

instance instCoePrefixClosedFiniteQuotientSchreierData :
    Coe (PrefixClosedFiniteQuotientSchreierData X Q)
    (FiniteQuotientSchreierData X Q) where
  coe D := D.toFiniteQuotientSchreierData

abbrev kernel : Subgroup (FreeGroup X) :=
  D.toFiniteQuotientSchreierData.kernel

abbrev presentationRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteQuotientSchreierData.FiniteSchreierSymbol X Q)) :=
  D.toFiniteQuotientSchreierData.presentationRelators R

abbrev relatorSubgroup (R : Set (FreeGroup X)) :
    Subgroup D.kernel :=
  D.toFiniteQuotientSchreierData.relatorSubgroup R

theorem quotientSectionRelators_redundant
    (R : Set (FreeGroup X)) (q : Q) :
    D.toFiniteQuotientSchreierData.tau 1
        (D.toFiniteQuotientSchreierData.quotientSection q) ∈
      Subgroup.normalClosure (presentationRelators D R) :=
  FiniteQuotientSchreierData.tau_quotientSection_mem_normalClosure_presentationRelators_of_isPrefixClosed
    D.toFiniteQuotientSchreierData R D.isPrefixClosed q

theorem normalClosure_augmentedPresentationRelators_eq
    (R : Set (FreeGroup X)) :
    Subgroup.normalClosure
        (D.toFiniteQuotientSchreierData.augmentedPresentationRelators R) =
      Subgroup.normalClosure (presentationRelators D R) :=
  FiniteQuotientSchreierData.normalClosure_augmentedPresentationRelators_eq_of_isPrefixClosed
    D.toFiniteQuotientSchreierData D.isPrefixClosed

/-- Raw finite Reidemeister-Schreier presentation theorem for a prefix-closed
finite quotient section. -/
noncomputable def presentationQuotientEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    FreeGroup (FiniteQuotientSchreierData.FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (presentationRelators D R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  (D.toFiniteQuotientSchreierData).presentationQuotientEquivOfIsPrefixClosedQuotientSection
    hR D.isPrefixClosed

noncomputable def presentationPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup (presentationRelators D R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  D.presentationQuotientEquiv hR

abbrev nondegenerateSchreierSymbol :
    Type _ :=
  D.toFiniteQuotientSchreierData.NondegenerateSchreierSymbol

abbrev presentationRelatorsAfterDeletingDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.nondegenerateSchreierSymbol) :=
  (D.toFiniteQuotientSchreierData).presentationRelatorsAfterDeletingDegenerateSchreierGenerators R

def deleteDegenerateSchreierGeneratorsTietzeEquiv
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    TietzeEquiv (presentationRelators D R)
      (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) :=
  by
    change TietzeEquiv
      (D.toFiniteQuotientSchreierData.presentationRelators R)
      ((D.toFiniteQuotientSchreierData).presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)
    exact
      D.toFiniteQuotientSchreierData.deleteDegenerateSchreierGeneratorsTietzeEquiv R

noncomputable def deleteDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    PresentedGroup (presentationRelators D R) ≃*
      PresentedGroup
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) :=
  (D.deleteDegenerateSchreierGeneratorsTietzeEquiv R).presentedEquiv

/-- Prefix-closed finite Reidemeister-Schreier theorem after deleting all
degenerate Schreier generators. -/
noncomputable def presentationAfterDeletingDegenerateSchreierGeneratorsPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  (D.deleteDegenerateSchreierGenerators R).symm.trans
    (D.presentationPresentedGroupEquiv hR)

abbrev cleanedTau
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup D.nondegenerateSchreierSymbol :=
  D.toFiniteQuotientSchreierData.cleanedTau q w

abbrev cleanedTauList
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup D.nondegenerateSchreierSymbol :=
  D.toFiniteQuotientSchreierData.cleanedTauList q xs

noncomputable def cleanedTauNormalWord
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    List (D.nondegenerateSchreierSymbol × Bool) :=
  D.toFiniteQuotientSchreierData.cleanedTauNormalWord q w

noncomputable def cleanedTauListNormalWord
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    List (D.nondegenerateSchreierSymbol × Bool) :=
  D.toFiniteQuotientSchreierData.cleanedTauListNormalWord q xs

theorem cleanedTau_mk
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    D.cleanedTau q (FreeGroup.mk xs) = D.cleanedTauList q xs :=
  D.toFiniteQuotientSchreierData.cleanedTau_mk q xs

theorem mk_cleanedTauNormalWord
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup.mk (D.cleanedTauNormalWord q w) = D.cleanedTau q w :=
  D.toFiniteQuotientSchreierData.mk_cleanedTauNormalWord q w

theorem cleanedTau_eq_mk_iff_cleanedTauNormalWord_eq_reduce
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X)
    (ys : List (D.nondegenerateSchreierSymbol × Bool)) :
    D.cleanedTau q w = FreeGroup.mk ys ↔
      D.cleanedTauNormalWord q w = FreeGroup.reduce ys :=
  (D.toFiniteQuotientSchreierData).cleanedTau_eq_mk_iff_cleanedTauNormalWord_eq_reduce q w ys

theorem targetLift_cleanedTau_eq_mk_of_substitutionWord_reduce_eq
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys) :
    FreeGroup.lift toTargetGenerator (D.cleanedTau q w) =
      FreeGroup.mk ys :=
  D.toFiniteQuotientSchreierData
    |>.targetLift_cleanedTau_eq_mk_of_substitutionWord_reduce_eq
      (toTargetGenerator := toTargetGenerator) q w h

theorem targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys)
    (hy : RelatorEquivalent S (FreeGroup.mk ys) 1) :
    RelatorEquivalent S
      (FreeGroup.lift toTargetGenerator (D.cleanedTau q w)) 1 :=
  D.toFiniteQuotientSchreierData
    |>.targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
      (toTargetGenerator := toTargetGenerator) q w h hy

theorem targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_mem
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys)
    (hy : FreeGroup.mk ys ∈ S) :
    RelatorEquivalent S
      (FreeGroup.lift toTargetGenerator (D.cleanedTau q w)) 1 :=
  D.toFiniteQuotientSchreierData
    |>.targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_mem
      (toTargetGenerator := toTargetGenerator) q w h hy

theorem mapsCleanedRelators_of_cleanedTauNormalWord_reduce
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y}
    (targetWord : Q → FreeGroup X → List (Y × Bool))
    (hword :
      ∀ q : Q, ∀ r ∈ R,
        FreeGroup.reduce
            (freeGroupSubstitutionWord toTargetGenerator
              (D.cleanedTauNormalWord q r)) =
          FreeGroup.reduce (targetWord q r))
    (hrel :
      ∀ q : Q, ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.mk (targetWord q r)) 1) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent S
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1 :=
  D.toFiniteQuotientSchreierData
    |>.mapsCleanedRelators_of_cleanedTauNormalWord_reduce
      (toTargetGenerator := toTargetGenerator) targetWord hword hrel

theorem mapsCleanedRelators_of_cleanedTauNormalWord_reduce_mem
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y}
    (targetWord : Q → FreeGroup X → List (Y × Bool))
    (hword :
      ∀ q : Q, ∀ r ∈ R,
        FreeGroup.reduce
            (freeGroupSubstitutionWord toTargetGenerator
              (D.cleanedTauNormalWord q r)) =
          FreeGroup.reduce (targetWord q r))
    (hmem :
      ∀ q : Q, ∀ r ∈ R, FreeGroup.mk (targetWord q r) ∈ S) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent S
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1 :=
  D.toFiniteQuotientSchreierData
    |>.mapsCleanedRelators_of_cleanedTauNormalWord_reduce_mem
      (toTargetGenerator := toTargetGenerator) targetWord hword hmem

theorem nondegenerateSymbolEvalHom_cleanedTau
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    D.toFiniteQuotientSchreierData.nondegenerateSymbolEvalHom
        (D.cleanedTau q w) =
      D.toFiniteQuotientSchreierData.quotientSection q * w *
        (D.toFiniteQuotientSchreierData.quotientSection
          (D.toFiniteQuotientSchreierData.quotientMap
            (D.toFiniteQuotientSchreierData.quotientSection q * w)))⁻¹ :=
  D.toFiniteQuotientSchreierData.nondegenerateSymbolEvalHom_cleanedTau q w

  abbrev cleanedSchreierRelators
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.nondegenerateSchreierSymbol) :=
  D.toFiniteQuotientSchreierData.cleanedSchreierRelators R

theorem presentationRelatorsAfterDeletingDegenerate_eq_cleaned
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
  D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R =
      D.cleanedSchreierRelators R :=
  (D.toFiniteQuotientSchreierData).presentationRelatorsAfterDeletingDegenerate_eq_cleaned R

/-- Prefix-closed finite Reidemeister-Schreier theorem stated directly with
cleaned relators, i.e. after deleting degenerate Schreier generators. -/
noncomputable def cleanedPresentationPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup (D.cleanedSchreierRelators R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  (Presented.ofNormalClosureEq
    (R := D.cleanedSchreierRelators R)
    (S := D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)
    (by
      rw [D.presentationRelatorsAfterDeletingDegenerate_eq_cleaned R])).trans
    (D.presentationAfterDeletingDegenerateSchreierGeneratorsPresentedGroupEquiv hR)

/-- Data proving that the cleaned finite Reidemeister-Schreier presentation is
Tietze equivalent to a chosen target presentation.  This is the general
application-facing form of "rewrite the raw Reidemeister-Schreier presentation and then clean it up". -/
structure CleanedReidemeisterSchreierTargetPresentationData
    (R : Set (FreeGroup X)) (Y : Type*)
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] where
  targetRelators : Set (FreeGroup Y)
  toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y
  fromTargetGenerator : Y → FreeGroup D.nondegenerateSchreierSymbol
  mapsCleanedRelators :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent targetRelators
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1
  mapsTargetRelators :
    ∀ s ∈ targetRelators,
      RelatorEquivalent (D.cleanedSchreierRelators R)
        (FreeGroup.lift fromTargetGenerator s) 1
  from_toTargetGenerator :
    ∀ z : D.nondegenerateSchreierSymbol,
      RelatorEquivalent (D.cleanedSchreierRelators R)
        (FreeGroup.lift fromTargetGenerator (toTargetGenerator z))
        (FreeGroup.of z)
  to_fromTargetGenerator :
    ∀ y : Y,
      RelatorEquivalent targetRelators
        (FreeGroup.lift toTargetGenerator (fromTargetGenerator y))
        (FreeGroup.of y)

namespace CleanedReidemeisterSchreierTargetPresentationData

variable {D}
variable {R : Set (FreeGroup X)} {Y : Type*}
variable [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]

def toTietzeEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y) :
    TietzeEquiv (D.cleanedSchreierRelators R) C.targetRelators :=
  TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    C.toTargetGenerator C.fromTargetGenerator
    (by
      intro z hz
      rcases hz with ⟨q, r, hr, rfl⟩
      exact C.mapsCleanedRelators q r hr)
    C.mapsTargetRelators
    C.from_toTargetGenerator
    C.to_fromTargetGenerator

noncomputable def presentedEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y) :
    PresentedGroup (D.cleanedSchreierRelators R) ≃*
      PresentedGroup C.targetRelators :=
  C.toTietzeEquiv.presentedEquiv

noncomputable def targetPresentedGroupEquivKernel
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y)
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup C.targetRelators ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  C.presentedEquiv.symm.trans (D.cleanedPresentationPresentedGroupEquiv hR)

def toTietzeScript
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y) :
    TietzeScript
      (Presentation.ofRelators (D.cleanedSchreierRelators R))
      (Presentation.ofRelators C.targetRelators) :=
  C.toTietzeEquiv.toScript

end CleanedReidemeisterSchreierTargetPresentationData

end PrefixClosedFiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete.ReidemeisterSchreier
