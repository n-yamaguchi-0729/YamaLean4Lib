import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.QuotientAndBasis
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.TargetSignatures

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/TargetMaps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Period-one cleanup step

Handles the cleanup of period-one target entries using quotient maps, kernel equivalences, low-cardinality dihedral cases, source subgroups, and relator proofs.
-/

open scoped BigOperators

namespace FenchelNielsen

noncomputable def oneHeadPeriodOneTargetToSchreierGeneratorImage
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    FuchsianGenerator target → FreeGroup ↥(schreierGeneratorSet hT) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  intro g
  cases g with
  | elliptic i =>
      exact
        match (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p).symm i with
        | .inl _ =>
            basis.symm
              (originalFirstReductionPeriodOneSecondPowerKernel
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)
        | .inr jk =>
            basis.symm
              (originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e jk.2 jk.1)
  | surfaceA _ => exact 1
  | surfaceB _ => exact 1

noncomputable def oneHeadPeriodOneTargetToSchreierHom
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    FreeGroup (FuchsianGenerator target) →* FreeGroup ↥(schreierGeneratorSet hT) :=
  FreeGroup.lift
    (oneHeadPeriodOneTargetToSchreierGeneratorImage
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e)

noncomputable def doublePeriodOneTargetToSchreierGeneratorImage
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    FuchsianGenerator target → FreeGroup ↥(schreierGeneratorSet hT) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  intro g
  cases g with
  | elliptic i =>
      let jk : Fin p × Fin tailLen :=
        finProdFinEquiv.symm i
      exact basis.symm
        (originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e jk.2 jk.1)
  | surfaceA _ => exact 1
  | surfaceB _ => exact 1

noncomputable def doublePeriodOneTargetToSchreierHom
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    FreeGroup (FuchsianGenerator target) →* FreeGroup ↥(schreierGeneratorSet hT) :=
  FreeGroup.lift
    (doublePeriodOneTargetToSchreierGeneratorImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e)

end FenchelNielsen
