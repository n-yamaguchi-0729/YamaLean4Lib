import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.RelatorProofs

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/KernelEquivalence.lean
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

def OriginalFirstReductionPeriodOneSchreierRelatorData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    {Y : Type} (targetRelators : Set (FreeGroup Y)) : Type :=
  (letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let ξ :=
      originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let f := ellipticQuotientGeneratorImage source ξ
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hx : FreeGroup.lift f (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simpa [f, x, ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
        originalFirstReductionPeriodOneFreeQuotientHom_head_zero
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    CyclicSchreierRelatorData
      (N := p) (rels := relators source) f x hx targetRelators)

def OriginalFirstReductionPeriodOneForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (τ : FuchsianSignature)
    (θ :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
      let hT :=
        originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
      FreeGroup (FuchsianGenerator τ) →* FreeGroup ↥(schreierGeneratorSet hT)) :
    Type :=
  (letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let ξ :=
      originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let f := ellipticQuotientGeneratorImage source ξ
    let T :=
      originalFirstReductionPeriodOneSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    ReidemeisterSchreier.Discrete.Presentations.RelatorQuotientForwardMapData
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T))
      (relators τ)
      θ)

noncomputable def doublePeriodOneForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1) (hm₂'one : m₂' = 1) :
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    OriginalFirstReductionPeriodOneForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e target
      (doublePeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  refine
    { toHom := η
      mapsRelators := ?_
      inv_toHom := ?_
      to_invHom := ?_ }
  · intro r hr
    simpa [source, target, ξ, f, T, basis, η] using
      doublePeriodOneSchreierToTarget_mapsRelators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he
        hm₁'one hm₂'one r hr
  · intro w
    simpa [source, target, ξ, f, T, hT, basis, θ, η] using
      doublePeriodOneSchreierToTarget_invComp_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he
        hm₁'one w
  · intro y
    simpa [source, target, θ, η] using
      doublePeriodOneSchreierToTarget_toInv_mem_normalClosure_of_generators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
        (doublePeriodOneSchreierToTarget_toInv_generators_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e) y

noncomputable def oneHeadPeriodOneForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1) :
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    OriginalFirstReductionPeriodOneForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e target
      (oneHeadPeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  refine
    { toHom := η
      mapsRelators := ?_
      inv_toHom := ?_
      to_invHom := ?_ }
  · intro r hr
    simpa [source, target, ξ, f, T, basis, η] using
      oneHeadPeriodOneSchreierToTarget_mapsRelators
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he
        hm₁'one r hr
  · intro w
    simpa [source, target, ξ, f, T, hT, basis, θ, η] using
      oneHeadPeriodOneSchreierToTarget_invComp_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he
        hm₁'one w
  · intro y
    simpa [source, target, θ, η] using
      oneHeadPeriodOneSchreierToTarget_toInv_mem_normalClosure_of_generators
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
        (oneHeadPeriodOneSchreierToTarget_toInv_generators_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e) y

noncomputable def oneHeadPeriodOneSchreierRelatorData_of_forwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1)
    (D :
      let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
      OriginalFirstReductionPeriodOneForwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e target
        (oneHeadPeriodOneTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e)) :
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    OriginalFirstReductionPeriodOneSchreierRelatorData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  have hTarget :
      ∀ s ∈ relators target, θ s ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [source, target, ξ, f, T, basis, θ] using
      oneHeadPeriodOneTargetToSchreier_mapsTargetRelators
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he hm₁'one
  simpa [OriginalFirstReductionPeriodOneSchreierRelatorData,
    OriginalFirstReductionPeriodOneForwardMapData, source, target, ξ, f, T, basis, θ] using
    (ReidemeisterSchreier.Discrete.Presentations.relatorQuotientMutualMapDataOfForwardMapData
      (R := ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T))
      (S := relators target)
      (invHom := θ)
      hTarget
      D)

noncomputable def doublePeriodOneSchreierRelatorData_of_forwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1) (hm₂'one : m₂' = 1)
    (D :
      let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
      OriginalFirstReductionPeriodOneForwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e target
        (doublePeriodOneTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e)) :
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    OriginalFirstReductionPeriodOneSchreierRelatorData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  have hTarget :
      ∀ s ∈ relators target, θ s ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [source, target, ξ, f, T, basis, θ] using
      doublePeriodOneTargetToSchreier_mapsTargetRelators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he
          hm₁'one hm₂'one
  simpa [OriginalFirstReductionPeriodOneSchreierRelatorData,
    OriginalFirstReductionPeriodOneForwardMapData, source, target, ξ, f, T, basis, θ] using
    (ReidemeisterSchreier.Discrete.Presentations.relatorQuotientMutualMapDataOfForwardMapData
      (R := ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T))
      (S := relators target)
      (invHom := θ)
      hTarget
      D)

noncomputable def originalFirstReductionPeriodOneKernelEquivOfRelatorData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (τ : FuchsianSignature)
    (D : OriginalFirstReductionPeriodOneSchreierRelatorData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e (relators τ)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let ξ :=
      originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hrels : ∀ r ∈ relators source,
        FreeGroup.lift (ellipticQuotientGeneratorImage source ξ) r = 1 := by
      simpa [ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
        originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
    (PresentedGroup.toGroup (rels := relators source)
      (f := ellipticQuotientGeneratorImage source ξ) hrels).ker ≃*
        FuchsianPresentedGroup τ := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hpow : ∀ i, ξ i ^ source.periods i = 1 :=
    originalFirstReductionPeriodOneQuotientImage_pow
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  let hprod : ∏ i : Fin source.numPeriods, ξ i = 1 :=
    originalFirstReductionPeriodOneQuotientImage_prod
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hrels : ∀ r ∈ relators source,
      FreeGroup.lift (ellipticQuotientGeneratorImage source ξ) r = 1 := by
    simpa [ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  let i₀ : Fin source.numPeriods := e (.inl (0 : Fin 2))
  have hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Fin.isValue, originalFirstReductionPeriodOneQuotientImage, Equiv.symm_apply_apply, ofAdd_neg,
  twoPeriods_zero, ξ, i₀]
  have hData :
      FuchsianEllipticCyclicSchreierRelatorData source τ ξ i₀ hi₀ := by
    simpa [FuchsianEllipticCyclicSchreierRelatorData,
      OriginalFirstReductionPeriodOneSchreierRelatorData,
      source, ξ, i₀, hi₀, originalFirstReductionPeriodOneFreeQuotientHom,
      originalFirstReductionPeriodOneDistinguishedGenerator] using D
  simpa [ellipticQuotientHom, source, ξ, hpow, hprod, hrels] using
    fuchsianEllipticCyclicKernelEquivOfRelatorData
      source τ ξ hpow hprod i₀ hi₀ hData

noncomputable def oneHeadPeriodOneKernelEquivOfForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1)
    (D :
      let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
      OriginalFirstReductionPeriodOneForwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e target
        (oneHeadPeriodOneTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    let ξ :=
      originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hrels : ∀ r ∈ relators source,
        FreeGroup.lift (ellipticQuotientGeneratorImage source ξ) r = 1 := by
      simpa [ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
        originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
    (PresentedGroup.toGroup (rels := relators source)
      (f := ellipticQuotientGeneratorImage source ξ) hrels).ker ≃*
        FuchsianPresentedGroup target := by
  classical
  dsimp
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  exact
    originalFirstReductionPeriodOneKernelEquivOfRelatorData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods target
      (oneHeadPeriodOneSchreierRelatorData_of_forwardMapData
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he hm₁'one D)

noncomputable def doublePeriodOneKernelEquivOfForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x)
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1) (hm₂'one : m₂' = 1)
    (D :
      let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
      OriginalFirstReductionPeriodOneForwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e target
        (doublePeriodOneTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    let ξ :=
      originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hrels : ∀ r ∈ relators source,
        FreeGroup.lift (ellipticQuotientGeneratorImage source ξ) r = 1 := by
      simpa [ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
        originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
    (PresentedGroup.toGroup (rels := relators source)
      (f := ellipticQuotientGeneratorImage source ξ) hrels).ker ≃*
        FuchsianPresentedGroup target := by
  classical
  dsimp
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  exact
    originalFirstReductionPeriodOneKernelEquivOfRelatorData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods target
      (doublePeriodOneSchreierRelatorData_of_forwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he
          hm₁'one hm₂'one D)


end FenchelNielsen
