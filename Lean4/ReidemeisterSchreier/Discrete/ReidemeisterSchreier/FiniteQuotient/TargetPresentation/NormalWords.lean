import ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.TargetPresentation.Core

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/ReidemeisterSchreier/FiniteQuotient/TargetPresentation/NormalWords.lean
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

namespace PrefixClosedFiniteQuotientSchreierData

variable [DecidableEq X]
variable (D : PrefixClosedFiniteQuotientSchreierData X Q)

/-- A computation-facing variant of
`CleanedReidemeisterSchreierTargetPresentationData`.  Instead of asking
directly for
`FreeGroup.lift toTargetGenerator (cleanedTau q r) ≡ 1`, it asks for a concrete
target word and a proof that substituting the target-generator words into the
reduced `cleanedTauNormalWord q r` reduces to that target word. -/
structure CleanedReidemeisterSchreierTargetPresentationNormalWordData
    (R : Set (FreeGroup X)) (Y : Type*)
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol] [DecidableEq Y] where
  targetRelators : Set (FreeGroup Y)
  toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y
  fromTargetGenerator : Y → FreeGroup D.nondegenerateSchreierSymbol
  cleanedRelatorWord : Q → FreeGroup X → List (Y × Bool)
  cleanedRelatorWord_reduce :
    ∀ q : Q, ∀ r ∈ R,
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q r)) =
        FreeGroup.reduce (cleanedRelatorWord q r)
  mapsCleanedRelatorWords :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent targetRelators
        (FreeGroup.mk (cleanedRelatorWord q r)) 1
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

namespace CleanedReidemeisterSchreierTargetPresentationNormalWordData

variable {D}
variable {R : Set (FreeGroup X)} {Y : Type*}
variable [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
variable [DecidableEq D.nondegenerateSchreierSymbol] [DecidableEq Y]

def mapsCleanedRelators
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent C.targetRelators
        (FreeGroup.lift C.toTargetGenerator (D.cleanedTau q r)) 1 :=
  D.mapsCleanedRelators_of_cleanedTauNormalWord_reduce
    (toTargetGenerator := C.toTargetGenerator)
    C.cleanedRelatorWord C.cleanedRelatorWord_reduce
    C.mapsCleanedRelatorWords

def toTargetPresentationData
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    D.CleanedReidemeisterSchreierTargetPresentationData R Y where
  targetRelators := C.targetRelators
  toTargetGenerator := C.toTargetGenerator
  fromTargetGenerator := C.fromTargetGenerator
  mapsCleanedRelators := C.mapsCleanedRelators
  mapsTargetRelators := C.mapsTargetRelators
  from_toTargetGenerator := C.from_toTargetGenerator
  to_fromTargetGenerator := C.to_fromTargetGenerator

def toTietzeEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    TietzeEquiv (D.cleanedSchreierRelators R) C.targetRelators :=
  C.toTargetPresentationData.toTietzeEquiv

noncomputable def presentedEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    PresentedGroup (D.cleanedSchreierRelators R) ≃*
      PresentedGroup C.targetRelators :=
  C.toTietzeEquiv.presentedEquiv

noncomputable def targetPresentedGroupEquivKernel
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y)
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup C.targetRelators ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  C.presentedEquiv.symm.trans (D.cleanedPresentationPresentedGroupEquiv hR)

def toTietzeScript
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    TietzeScript
      (Presentation.ofRelators (D.cleanedSchreierRelators R))
      (Presentation.ofRelators C.targetRelators) :=
  C.toTietzeEquiv.toScript

end CleanedReidemeisterSchreierTargetPresentationNormalWordData

end PrefixClosedFiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete.ReidemeisterSchreier
