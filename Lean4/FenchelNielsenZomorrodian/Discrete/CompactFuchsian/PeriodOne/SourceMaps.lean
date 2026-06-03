import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.TargetMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/SourceMaps.lean
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

noncomputable def oneHeadPeriodOneTargetTailBlockWord
    {tailLen p : ℕ}
    (m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j)
    (hTailLen : 0 < tailLen) :
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    Fin p → FreeGroup (FuchsianGenerator target) := by
  classical
  dsimp
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  intro k
  exact
    (List.ofFn (fun j : Fin tailLen =>
      xWord target (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))).prod

noncomputable def oneHeadPeriodOneSecondEdgeForwardWord
    {tailLen p : ℕ}
    (m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j)
    (hTailLen : 0 < tailLen) :
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    Fin p → FreeGroup (FuchsianGenerator target) := by
  classical
  dsimp
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let block := oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen
  intro k
  if h0 : k.val = 0 then
    exact block ⟨p - 1, by omega⟩
  else
    exact block ⟨k.val - 1, by omega⟩

noncomputable def doublePeriodOneTargetTailBlockWord
    {tailLen p : ℕ}
    (tail : Fin tailLen → ℕ)
    (htail : ∀ j, 2 ≤ tail j) (hHigh : 3 ≤ p * tailLen) :
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    Fin p → FreeGroup (FuchsianGenerator target) := by
  classical
  dsimp
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  intro k
  exact
    (List.ofFn (fun j : Fin tailLen =>
      xWord target (finProdFinEquiv (k, j)))).prod

noncomputable def doublePeriodOneSecondEdgeForwardWord
    {tailLen p : ℕ}
    (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (htail : ∀ j, 2 ≤ tail j)
    (hHigh : 3 ≤ p * tailLen) :
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    Fin p → FreeGroup (FuchsianGenerator target) := by
  classical
  dsimp
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let block := doublePeriodOneTargetTailBlockWord tail htail hHigh
  intro k
  if h0 : k.val = 0 then
    exact block ⟨p - 1, by omega⟩
  else
    exact block ⟨k.val - 1, by omega⟩

noncomputable def oneHeadPeriodOneSchreierToTargetGeneratorImage
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
    ↥(schreierGeneratorSet hT) → FreeGroup (FuchsianGenerator target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let secondWord :=
    oneHeadPeriodOneSecondEdgeForwardWord m₂' tail hp hm₂'ge htail hTailLen
  intro z
  if hFirst :
      (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e then
    exact 1
  else if hSecond :
      ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k then
    exact secondWord (Classical.choose hSecond)
  else if hTail :
      ∃ j : Fin tailLen, ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k then
    let j : Fin tailLen := Classical.choose hTail
    let hk : ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k :=
      Classical.choose_spec hTail
    let k : Fin p := Classical.choose hk
    exact
      (xWord target
        (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))⁻¹
  else
    exact 1

noncomputable def oneHeadPeriodOneSchreierToTargetHom
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
    FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup (FuchsianGenerator target) :=
  FreeGroup.lift
    (oneHeadPeriodOneSchreierToTargetGeneratorImage
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e)

noncomputable def doublePeriodOneSchreierToTargetGeneratorImage
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
    ↥(schreierGeneratorSet hT) → FreeGroup (FuchsianGenerator target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let secondWord :=
    doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh
  intro z
  if hFirst :
      (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e then
    exact 1
  else if hSecond :
      ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k then
    exact secondWord (Classical.choose hSecond)
  else if hTail :
      ∃ j : Fin tailLen, ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k then
    let j : Fin tailLen := Classical.choose hTail
    let hk : ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k :=
      Classical.choose_spec hTail
    let k : Fin p := Classical.choose hk
    exact (xWord target (finProdFinEquiv (k, j)))⁻¹
  else
    exact 1

noncomputable def doublePeriodOneSchreierToTargetHom
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
    FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup (FuchsianGenerator target) :=
  FreeGroup.lift
    (doublePeriodOneSchreierToTargetGeneratorImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e)

end FenchelNielsen
