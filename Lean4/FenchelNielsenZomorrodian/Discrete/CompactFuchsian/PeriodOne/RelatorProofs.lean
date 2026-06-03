import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.SourceMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/RelatorProofs.lean
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

private theorem originalFirstReductionPeriodOneFirstPowerKernel_mem_sourceRelators_normalClosure
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
    (hm₁'one : m₁' = 1) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    ((originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
          FreeGroup (FuchsianGenerator source)) ∈
      Subgroup.normalClosure (relators source) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hrel :
      xWord source (e (.inl (0 : Fin 2))) ^ source.periods (e (.inl (0 : Fin 2))) ∈
        relators source := Or.inl ⟨e (.inl (0 : Fin 2)), rfl⟩
  have hN :
      xWord source (e (.inl (0 : Fin 2))) ^ source.periods (e (.inl (0 : Fin 2))) ∈
        Subgroup.normalClosure (relators source) :=
    Subgroup.subset_normalClosure hrel
  have hPeriod : source.periods (e (.inl (0 : Fin 2))) = p := by
    rw [hperiods (.inl (0 : Fin 2))]
    simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, hm₁'one, mul_one, Fin.isValue,
  Fin.cases_zero]
  rw [originalFirstReductionPeriodOneFirstPowerKernel_coe]
  simpa [x, xWord, hPeriod] using hN

private theorem originalFirstReductionPeriodOneSecondPowerKernel_pow_mem_sourceRelators_normalClosure
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
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    (((originalFirstReductionPeriodOneSecondPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) ^ m₂' : φ.ker) :
          FreeGroup (FuchsianGenerator source)) ∈
      Subgroup.normalClosure (relators source) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  have hrel :
      xWord source (e (.inl (1 : Fin 2))) ^ source.periods (e (.inl (1 : Fin 2))) ∈
        relators source := Or.inl ⟨e (.inl (1 : Fin 2)), rfl⟩
  have hN :
      xWord source (e (.inl (1 : Fin 2))) ^ source.periods (e (.inl (1 : Fin 2))) ∈
        Subgroup.normalClosure (relators source) :=
    Subgroup.subset_normalClosure hrel
  have hPeriod : source.periods (e (.inl (1 : Fin 2))) = p * m₂' := by
    rw [hperiods (.inl (1 : Fin 2))]
    simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, Fin.isValue, fin_cases_const_one]
  change
    (((originalFirstReductionPeriodOneSecondPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
          FreeGroup (FuchsianGenerator source)) ^ m₂') ∈
      Subgroup.normalClosure (relators source)
  rw [originalFirstReductionPeriodOneSecondPowerKernel_coe]
  simpa [y, xWord, hPeriod, pow_mul] using hN

private theorem originalFirstReductionPeriodOneTailKernelElement_pow_mem_sourceRelators_normalClosure
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
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    (((originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k : φ.ker) ^ tail j : φ.ker) :
          FreeGroup (FuchsianGenerator source)) ∈
      Subgroup.normalClosure (relators source) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inr j))
  let r := xWord source (e (.inr j)) ^ source.periods (e (.inr j))
  let t : FreeGroup (FuchsianGenerator source) := (FreeGroup.of x) ^ k.val
  have hrel : r ∈ relators source := Or.inl ⟨e (.inr j), rfl⟩
  have hN : r ∈ Subgroup.normalClosure (relators source) :=
    Subgroup.subset_normalClosure hrel
  have hconj :
      t * r * t⁻¹ ∈ Subgroup.normalClosure (relators source) :=
    Subgroup.normalClosure_normal.conj_mem r hN t
  have hPeriod : source.periods (e (.inr j)) = tail j := by
    rw [hperiods (.inr j)]
    simp only [originalFirstReductionPeriods]
  change
    (((originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k : φ.ker) :
          FreeGroup (FuchsianGenerator source)) ^ tail j) ∈
      Subgroup.normalClosure (relators source)
  rw [originalFirstReductionPeriodOneTailKernelElement_coe]
  simpa [t, r, x, y, xWord, hPeriod, conj_pow] using hconj

private theorem originalFirstReductionPeriodOneSecondPowerKernel_schreierPower_mem_normalClosure
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
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    (basis.symm
        (originalFirstReductionPeriodOneSecondPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) ^ m₂' ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let b :=
    originalFirstReductionPeriodOneSecondPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hrels : ∀ r ∈ relators source, FreeGroup.lift f r = 1 := by
    simpa [f, ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  have hk :
      ((b ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator source)) ∈
        Subgroup.normalClosure (relators source) := by
    simpa [b, φ] using
      originalFirstReductionPeriodOneSecondPowerKernel_pow_mem_sourceRelators_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  have hmem :
      basis.symm (b ^ m₂') ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [basis, φ] using
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
        hrels hT.1 basis hk
  have hpow : (basis.symm b) ^ m₂' = basis.symm (b ^ m₂') :=
    (map_pow basis.symm b m₂').symm
  rw [hpow]
  exact hmem

private theorem originalFirstReductionPeriodOneFirstPowerKernel_schreier_mem_normalClosure
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
    (hm₁'one : m₁' = 1) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    basis.symm
      (originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hrels : ∀ r ∈ relators source, FreeGroup.lift f r = 1 := by
    simpa [f, ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  have hk :
      ((a : φ.ker) : FreeGroup (FuchsianGenerator source)) ∈
        Subgroup.normalClosure (relators source) := by
    simpa [a, φ] using
      originalFirstReductionPeriodOneFirstPowerKernel_mem_sourceRelators_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods hm₁'one
  simpa [basis, φ] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
      hrels hT.1 basis hk

private theorem originalFirstReductionPeriodOneTailKernelElement_schreierPower_mem_normalClosure
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
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    (basis.symm
        (originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)) ^ tail j ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let c :=
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  have hrels : ∀ r ∈ relators source, FreeGroup.lift f r = 1 := by
    simpa [f, ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  have hk :
      ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator source)) ∈
        Subgroup.normalClosure (relators source) := by
    simpa [c, φ] using
      originalFirstReductionPeriodOneTailKernelElement_pow_mem_sourceRelators_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods j k
  have hmem :
      basis.symm (c ^ tail j) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [basis, φ] using
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
        hrels hT.1 basis hk
  have hpow : (basis.symm c) ^ tail j = basis.symm (c ^ tail j) :=
    (map_pow basis.symm c (tail j)).symm
  rw [hpow]
  exact hmem

private theorem originalFirstReductionPeriodOneCanonicalSchreier_cyclicBlockTotalProduct_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let e : OriginalFirstReductionIndex tailLen ≃ Fin source.numPeriods := by
      simpa [source, originalFirstReductionSignature] using
        originalFirstReductionOrderedIndexEquiv tailLen
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
    let a :=
      originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let b :=
      originalFirstReductionPeriodOneSecondPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let c : Fin tailLen → Fin p →
        (originalFirstReductionPeriodOneFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).ker := fun j k =>
      originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
    basis.symm a * basis.symm b *
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen => basis.symm (c j k))).prod)).prod ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let e : OriginalFirstReductionIndex tailLen ≃ Fin source.numPeriods := by
    simpa [source, originalFirstReductionSignature] using
      originalFirstReductionOrderedIndexEquiv tailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source :=
    FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let hperiods :
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x := by
    intro z
    simpa [source, e] using
      originalFirstReduction_canonical_periods_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen z
  have hrels : ∀ r ∈ relators source, FreeGroup.lift f r = 1 := by
    simpa [f, ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let b :=
    originalFirstReductionPeriodOneSecondPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let kBlock : φ.ker :=
    a * b *
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod
  have hTailRel :
      FreeGroup.of x * FreeGroup.of y *
          (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod ∈
        Subgroup.normalClosure (relators source) := by
    have hTotal :=
      originalFirstReduction_source_totalRelation_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hTailEq :
        totalRelation source =
          FreeGroup.of x * FreeGroup.of y *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod := by
      simpa [source, e, x, y, tailGen, xWord,
        originalFirstReductionPeriodOneDistinguishedGenerator,
        originalFirstReductionOrderedIndexEquiv] using hTotal
    rw [← hTailEq]
    exact Subgroup.subset_normalClosure (Or.inr rfl)
  have hSourceBlock :
      (FreeGroup.of x) ^ p * (FreeGroup.of y) ^ p *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              (FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
                ((FreeGroup.of x) ^ (k : ℕ))⁻¹)).prod)).prod ∈
        Subgroup.normalClosure (relators source) := by
    simpa [x, y, tailGen] using
      pow_mul_pow_mul_conjugateBlockProduct_mem_normalClosure_of_mul_mem_normalClosure
        (FreeGroup.of x) (FreeGroup.of y)
        (fun j : Fin tailLen => FreeGroup.of (tailGen j)) p hTailRel
  have hBlockCoe :
      (((List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            ((c j k : φ.ker) : FreeGroup (FuchsianGenerator source)))).prod)).prod := by
    simpa using
      (MonoidHom.map_list_prod_ofFn₂ φ.ker.subtype
        (fun k : Fin p => fun j : Fin tailLen => c j k))
  have hkSource : (kBlock : FreeGroup (FuchsianGenerator source)) ∈
      Subgroup.normalClosure (relators source) := by
    change
      ((a : φ.ker) : FreeGroup (FuchsianGenerator source)) *
          ((b : φ.ker) : FreeGroup (FuchsianGenerator source)) *
        (((List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator source)) ∈
        Subgroup.normalClosure (relators source)
    rw [hBlockCoe]
    rw [originalFirstReductionPeriodOneFirstPowerKernel_coe]
    rw [originalFirstReductionPeriodOneSecondPowerKernel_coe]
    simp only [c]
    simpa [a, b, x, y, tailGen, originalFirstReductionPeriodOneDistinguishedGenerator,
      originalFirstReductionPeriodOneTailKernelElement_coe]
      using hSourceBlock
  have hmem :
      basis.symm kBlock ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    exact
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
        hrels hT.1 basis hkSource
  have hBlockMap :
      basis.symm ((List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod) =
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen => basis.symm (c j k))).prod)).prod := by
    simpa using
      (MonoidHom.map_list_prod_ofFn₂ basis.symm.toMonoidHom
        (fun k : Fin p => fun j : Fin tailLen => c j k))
  have hmem' :
      basis.symm a * basis.symm b *
          basis.symm
            ((List.ofFn (fun k : Fin p =>
              (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [kBlock, map_mul] using hmem
  rw [hBlockMap] at hmem'
  simpa [a, b, c, source, e, ξ, f, φ, T, hT, basis] using hmem'

private theorem originalFirstReductionPeriodOne_distinguished_schreierGenerator_wrap_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    schreierGenerator hT ((FreeGroup.of x) ^ (p - 1)) x =
      originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  simpa [originalFirstReductionPeriodOneSchreierTransversal,
    originalFirstReductionPeriodOneFirstPowerKernel, source, φ, x] using
    cyclicQuotient_distinguished_schreierGenerator_wrap_eq φ x hx

private theorem originalFirstReductionPeriodOne_distinguished_schreierGenerator_eq_one_of_succ_lt
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    {k : ℕ} (hk : k + 1 < p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    schreierGenerator hT ((FreeGroup.of x) ^ k) x = 1 := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  simpa [originalFirstReductionPeriodOneSchreierTransversal, source, φ, x] using
    cyclicQuotient_distinguished_schreierGenerator_eq_one_of_succ_lt φ x hx hk

private theorem originalFirstReductionPeriodOneFirstPowerKernel_mem_schreierGeneratorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    (originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  refine ⟨(FreeGroup.of x) ^ (p - 1), ?_, x, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
        originalFirstReductionPeriodOneFreeQuotientHom_head_zero
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    simpa [T, originalFirstReductionPeriodOneSchreierTransversal, source, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := p - 1) (by omega)
  · simpa [hT, source, φ, x] using
      (originalFirstReductionPeriodOne_distinguished_schreierGenerator_wrap_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) h
    have hpow : (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p = 1 := by
      simpa [source, φ, x, originalFirstReductionPeriodOneFirstPowerKernel,
        originalFirstReductionPeriodOneDistinguishedGenerator] using hval
    exact freeGroup_of_pow_ne_one x (by omega) hpow

private theorem originalFirstReductionPeriodOne_second_schreierGenerator_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
    simpa [φ, y] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_one
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  simpa [originalFirstReductionPeriodOneSchreierTransversal,
    originalFirstReductionPeriodOneSecondEdgeKernelElement, source, φ, x, y] using
    cyclicQuotient_negOneImage_schreierGenerator_eq φ x y hx hy k

private theorem originalFirstReductionPeriodOneSecondEdgeKernelElement_mem_schreierGeneratorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    (originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  refine ⟨(FreeGroup.of x) ^ k.val, ?_, y, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
        originalFirstReductionPeriodOneFreeQuotientHom_head_zero
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    simpa [T, originalFirstReductionPeriodOneSchreierTransversal, source, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) k.isLt
  · simpa [hT, source, φ, x, y] using
      (originalFirstReductionPeriodOne_second_schreierGenerator_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) h
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hsecondWord :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ = 1 := by
      simpa [source, φ, x, y, r,
        originalFirstReductionPeriodOneSecondEdgeKernelElement,
        originalFirstReductionPeriodOneDistinguishedGenerator] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hxne : x ≠ y := by
      intro hEq
      simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, zero_ne_one, x, y] at hEq
    have hmap := congrArg (FreeGroup.lift χ) hsecondWord
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, map_one, ofAdd_eq_one, one_ne_zero, χ] at hmap

private theorem originalFirstReductionPeriodOne_tail_schreierGenerator_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inr j))
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inr j))
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hy : φ (FreeGroup.of y) = 1 := by
    simpa [φ, y] using
      originalFirstReductionPeriodOneFreeQuotientHom_tail
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j
  simpa [originalFirstReductionPeriodOneSchreierTransversal,
    originalFirstReductionPeriodOneTailKernelElement, source, φ, x, y] using
    cyclicQuotient_trivialImage_schreierGenerator_eq_conj φ x y hx hy k

private theorem originalFirstReductionPeriodOneTailKernelElement_mem_schreierGeneratorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    (originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inr j))
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  refine ⟨(FreeGroup.of x) ^ k.val, ?_, y, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
        originalFirstReductionPeriodOneFreeQuotientHom_head_zero
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    simpa [T, originalFirstReductionPeriodOneSchreierTransversal, source, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) k.isLt
  · simpa [hT, source, φ, x, y] using
      (originalFirstReductionPeriodOne_tail_schreierGenerator_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) h
    have htailWord :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ = 1 := by
      simp only [originalFirstReductionPeriodOneTailKernelElement, Lean.Elab.WF.paramLet,
  originalFirstReductionPeriodOneDistinguishedGenerator, Fin.isValue, id_eq, OneMemClass.coe_one, conj_eq_one_iff,
  FreeGroup.of_ne_one, φ] at hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hxne : x ≠ y := by
      intro hEq
      simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, x, y] at hEq
    have hmap := congrArg (FreeGroup.lift χ) htailWord
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, map_one, ofAdd_eq_one, one_ne_zero, χ] at hmap

private theorem originalFirstReductionPeriodOne_schreierGeneratorSet_cases
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    ∀ z : ↥(schreierGeneratorSet hT),
      (z : φ.ker) =
          originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e ∨
        (∃ k : Fin p,
          (z : φ.ker) =
            originalFirstReductionPeriodOneSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∨
        (∃ j : Fin tailLen, ∃ k : Fin p,
          (z : φ.ker) =
            originalFirstReductionPeriodOneTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  intro z
  rcases z.property with ⟨t, ht, g, hz, hne⟩
  have htPower : ∃ k : Fin p, t = (FreeGroup.of x) ^ k.val := by
    simpa [hT, originalFirstReductionPeriodOneSchreierTransversal, φ, x] using
      (mem_range_cyclicQuotientRightRep_iff_generatorPower φ (x := x) hx).1 ht
  rcases htPower with ⟨k, rfl⟩
  cases g with
  | elliptic i =>
      cases hidx : e.symm i with
      | inl head =>
          have hi : i = e (.inl head) := by
            have h := congrArg e hidx
            simpa using h
          fin_cases head
          · by_cases hwrap : k.val + 1 < p
            · have hgen :
                  schreierGenerator hT ((FreeGroup.of x) ^ k.val) x = 1 := by
                simpa [hT, source, φ, x,
                  originalFirstReductionPeriodOneDistinguishedGenerator] using
                  originalFirstReductionPeriodOne_distinguished_schreierGenerator_eq_one_of_succ_lt
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hwrap
              exact False.elim (hne (by simpa [hz, x, hi,
                originalFirstReductionPeriodOneDistinguishedGenerator] using hgen))
            · have hk : k.val = p - 1 := by
                have hklt := k.isLt
                omega
              left
              calc
                (z : φ.ker) =
                    schreierGenerator hT ((FreeGroup.of x) ^ k.val) x := by
                  simpa [x, hi, originalFirstReductionPeriodOneDistinguishedGenerator] using hz
                _ = schreierGenerator hT ((FreeGroup.of x) ^ (p - 1)) x := by
                  rw [hk]
                _ =
                    originalFirstReductionPeriodOneFirstPowerKernel
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e := by
                  simpa [hT, source, φ, x,
                    originalFirstReductionPeriodOneDistinguishedGenerator] using
                    originalFirstReductionPeriodOne_distinguished_schreierGenerator_wrap_eq
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          · right
            left
            refine ⟨k, ?_⟩
            calc
              (z : φ.ker) =
                  schreierGenerator hT ((FreeGroup.of x) ^ k.val)
                    (FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))) := by
                simpa [hi] using hz
              _ =
                  originalFirstReductionPeriodOneSecondEdgeKernelElement
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k := by
                simpa [hT, source, φ, x] using
                  originalFirstReductionPeriodOne_second_schreierGenerator_eq
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
      | inr j =>
          have hi : i = e (.inr j) := by
            have h := congrArg e hidx
            simpa using h
          right
          right
          refine ⟨j, k, ?_⟩
          calc
            (z : φ.ker) =
                schreierGenerator hT ((FreeGroup.of x) ^ k.val)
                  (FuchsianGenerator.elliptic (e (.inr j))) := by
              simpa [hi] using hz
            _ =
                originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k := by
              simpa [hT, source, φ, x] using
                originalFirstReductionPeriodOne_tail_schreierGenerator_eq
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  | surfaceA i =>
      exact Fin.elim0 (by
        simpa [source, originalFirstReductionSignature] using i)
  | surfaceB i =>
      exact Fin.elim0 (by
        simpa [source, originalFirstReductionSignature] using i)

private theorem originalFirstReductionPeriodOne_tailBlock_secondEdge_schreier_mem_normalClosure
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
    (he : e = originalFirstReductionOrderedIndexEquiv tailLen)
    (hm₁'one : m₁' = 1)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    let prev : Fin p :=
      if k.val = 0 then ⟨p - 1, by omega⟩ else ⟨k.val - 1, by omega⟩
    (List.ofFn (fun j : Fin tailLen =>
          basis.symm
            (originalFirstReductionPeriodOneTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j prev))).prod *
        basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let P : FreeGroup (FuchsianGenerator source) :=
    (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod
  let prev : Fin p :=
    if k.val = 0 then ⟨p - 1, by omega⟩ else ⟨k.val - 1, by omega⟩
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let d : φ.ker := (List.ofFn (fun j : Fin tailLen => c j prev)).prod * edge k
  have hrels : ∀ r ∈ relators source, FreeGroup.lift f r = 1 := by
    simpa [f, ξ, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  have hTotalMem :
      FreeGroup.of x * FreeGroup.of y * P ∈
        Subgroup.normalClosure (relators source) := by
    subst e
    have hTotal :=
      originalFirstReduction_source_totalRelation_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hTailEq :
        totalRelation source =
          FreeGroup.of x * FreeGroup.of y * P := by
      simpa [source, x, y, tailGen, P, xWord,
        originalFirstReductionPeriodOneDistinguishedGenerator,
        originalFirstReductionOrderedIndexEquiv] using hTotal
    rw [← hTailEq]
    exact Subgroup.subset_normalClosure (Or.inr rfl)
  have hRotMem :
      P * FreeGroup.of x * FreeGroup.of y ∈
        Subgroup.normalClosure (relators source) := by
    have h₁ :
        FreeGroup.of y * P * FreeGroup.of x ∈
          Subgroup.normalClosure (relators source) := by
      simpa [mul_assoc] using
        ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
          (R := relators source) (a := FreeGroup.of x) (b := FreeGroup.of y * P)
          (by simpa [mul_assoc] using hTotalMem)
    simpa [mul_assoc] using
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := relators source) (a := FreeGroup.of y) (b := P * FreeGroup.of x)
        (by simpa [mul_assoc] using h₁)
  have hA :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p ∈
        Subgroup.normalClosure (relators source) := by
    simpa [source, φ, x] using
      originalFirstReductionPeriodOneFirstPowerKernel_mem_sourceRelators_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods hm₁'one
  have hblockCoe :
      (((List.ofFn (fun j : Fin tailLen => c j prev)).prod : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
        (FreeGroup.of x) ^ prev.val * P * ((FreeGroup.of x) ^ prev.val)⁻¹ := by
    change
      φ.ker.subtype ((List.ofFn (fun j : Fin tailLen => c j prev)).prod) =
        (FreeGroup.of x) ^ prev.val * P * ((FreeGroup.of x) ^ prev.val)⁻¹
    rw [map_list_prod, List.map_ofFn]
    calc
      (List.ofFn (fun j : Fin tailLen => φ.ker.subtype (c j prev))).prod =
          (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ prev.val *
            FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ prev.val)⁻¹)).prod := by
            apply congrArg List.prod
            apply List.ofFn_inj.2
            funext j
            simpa [c, source, φ, x, tailGen] using
              originalFirstReductionPeriodOneTailKernelElement_coe
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j prev
      _ = (FreeGroup.of x) ^ prev.val * P *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ prev.val)⁻¹ := by
            simpa [P] using
              (ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ prev.val)
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).symm
  have hedgeCoe :
      ((edge k : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        (FreeGroup.of x) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ (((k.val : ZMod p) - 1).val))⁻¹ := by
    simpa [edge, source, φ, x, y] using
      originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
  have hdSource :
      ((d : φ.ker) : FreeGroup (FuchsianGenerator source)) ∈
        Subgroup.normalClosure (relators source) := by
    let N : Subgroup (FreeGroup (FuchsianGenerator source)) :=
      Subgroup.normalClosure (relators source)
    let q : FreeGroup (FuchsianGenerator source) →*
        FreeGroup (FuchsianGenerator source) ⧸ N := QuotientGroup.mk' N
    have hqRot : q (P * FreeGroup.of x * FreeGroup.of y) = 1 :=
      (QuotientGroup.eq_one_iff (N := N) (P * FreeGroup.of x * FreeGroup.of y)).2
        (by simpa [N] using hRotMem)
    have hqA : q ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p) = 1 :=
      (QuotientGroup.eq_one_iff (N := N)
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p)).2
        (by simpa [N] using hA)
    have hqA' : q (FreeGroup.of x) ^ p = 1 := by
      simpa [map_pow] using hqA
    have hqTarget : q ((d : φ.ker) : FreeGroup (FuchsianGenerator source)) = 1 := by
      haveI : Fact (1 < p) := ⟨by omega⟩
      change q ((((List.ofFn (fun j : Fin tailLen => c j prev)).prod : φ.ker) :
          FreeGroup (FuchsianGenerator source)) * ((edge k : φ.ker) :
            FreeGroup (FuchsianGenerator source))) = 1
      rw [hblockCoe, hedgeCoe]
      by_cases h0 : k.val = 0
      · have hprev : prev = ⟨p - 1, by omega⟩ := by
          simp only [h0, ↓reduceIte, prev]
        have hr0 : ((((0 : ℕ) : ZMod p) - 1).val) = p - 1 := by
          have hsucc : (p - 1).succ = p := by omega
          simp only [sub_eq_add_neg, Nat.cast_zero, zero_add]
          rw [← hsucc]
          exact ZMod.val_neg_one (p - 1)
        have hr : (((k.val : ZMod p) - 1).val) = p - 1 := by
          simpa [h0] using hr0
        rw [hprev]
        rw [hr, h0]
        have hxpred_mul :
            q (FreeGroup.of x) ^ (p - 1) * q (FreeGroup.of x) = 1 := by
          rw [← pow_succ]
          have hpred : p - 1 + 1 = p := by omega
          rw [hpred]
          exact hqA'
        have hxpred :
            q (FreeGroup.of x) ^ (p - 1) = (q (FreeGroup.of x))⁻¹ :=
          eq_inv_of_mul_eq_one_left hxpred_mul
        simp only [map_mul, map_inv, map_pow, pow_zero, one_mul]
        rw [hxpred]
        calc
          (q (FreeGroup.of x))⁻¹ * q P * q (FreeGroup.of x) *
                (q (FreeGroup.of y) * q (FreeGroup.of x)) =
              (q (FreeGroup.of x))⁻¹ *
                (q P * q (FreeGroup.of x) * q (FreeGroup.of y)) *
                q (FreeGroup.of x) := by group
          _ = 1 := by
            have hrot' :
                q P * q (FreeGroup.of x) * q (FreeGroup.of y) = 1 := by
              simpa [q, map_mul, mul_assoc] using hqRot
            simp only [hrot', mul_one, inv_mul_cancel]
      · have hprev : prev = ⟨k.val - 1, by omega⟩ := by
          simp only [h0, ↓reduceIte, prev]
        have hk : k.val = (k.val - 1) + 1 := by omega
        have hr : (((k.val : ZMod p) - 1).val) = k.val - 1 := by
          let kNat := k.val
          have hkpos : 0 < kNat := by
            dsimp [kNat]
            omega
          have hklt : kNat < p := by
            dsimp [kNat]
            exact k.isLt
          have hkval : ((kNat : ZMod p)).val = kNat :=
            ZMod.val_natCast_of_lt hklt
          have hsubval : ((kNat : ZMod p) - 1).val = kNat - 1 := by
            have hle : (1 : ZMod p).val ≤ (kNat : ZMod p).val := by
              rw [hkval, ZMod.val_one]
              exact Nat.succ_le_iff.mpr hkpos
            rw [ZMod.val_sub hle, hkval, ZMod.val_one]
          simpa [kNat] using hsubval
        rw [hprev]
        rw [hr]
        have hpowk :
            q (FreeGroup.of x) ^ k.val =
              q (FreeGroup.of x) ^ (k.val - 1 + 1) := by
          exact congrArg (fun n => q (FreeGroup.of x) ^ n) hk
        simp only [map_mul, map_inv, map_pow]
        rw [hpowk]
        calc
          q (FreeGroup.of x) ^ (k.val - 1) * q P *
                (q (FreeGroup.of x) ^ (k.val - 1))⁻¹ *
              (q (FreeGroup.of x) ^ (k.val - 1 + 1) * q (FreeGroup.of y) *
                (q (FreeGroup.of x) ^ (k.val - 1))⁻¹) =
              q (FreeGroup.of x) ^ (k.val - 1) *
                (q P * q (FreeGroup.of x) * q (FreeGroup.of y)) *
                (q (FreeGroup.of x) ^ (k.val - 1))⁻¹ := by
              rw [pow_succ]
              group
          _ = 1 := by
            have hrot' :
                q P * q (FreeGroup.of x) * q (FreeGroup.of y) = 1 := by
              simpa [q, map_mul, mul_assoc] using hqRot
            simp only [hrot', mul_one, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := N)
      ((d : φ.ker) : FreeGroup (FuchsianGenerator source))).1 hqTarget
  have hmem :
      basis.symm d ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    exact
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
        hrels hT.1 basis hdSource
  have hmap :
      basis.symm d =
        (List.ofFn (fun j : Fin tailLen =>
          basis.symm (c j prev))).prod * basis.symm (edge k) := by
    dsimp [d]
    rw [map_mul, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def]
  have hgoal :
      (List.ofFn (fun j : Fin tailLen =>
          basis.symm (c j prev))).prod * basis.symm (edge k) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [hmap] using hmem
  simpa [source, ξ, f, T, basis, prev, c, edge] using hgoal

private theorem oneHeadPeriodOneTargetToSchreier_powerRelator_mem_normalClosure
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
    (idx : OneHeadPeriodOneTargetIndex tailLen p) :
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
    θ
        ((xWord target (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p idx)) ^
          target.periods (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p idx)) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
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
  cases idx using Sum.casesOn with
  | inl i =>
      fin_cases i
      have hPeriod :
          target.periods
              (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p
                (.inl (0 : Fin 1))) = m₂' := by
        simp only [oneHeadPeriodOneTargetSignature, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, oneHeadPeriodOneTargetPeriods,
  Fin.isValue, Equiv.trans_apply, Sum.map_inl, id_eq, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd,
  target]
      have hmem :=
        originalFirstReductionPeriodOneSecondPowerKernel_schreierPower_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
      simpa [θ, oneHeadPeriodOneTargetToSchreierHom,
        oneHeadPeriodOneTargetToSchreierGeneratorImage, target, xWord, hPeriod,
        basis, source, ξ, f, T, oneHeadPeriodOneTargetPeriods,
        Equiv.symm_apply_apply] using hmem
  | inr jk =>
      have hPeriod :
          target.periods
              (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p
                (.inr jk)) = tail jk.2 := by
        simp only [oneHeadPeriodOneTargetSignature, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, oneHeadPeriodOneTargetPeriods,
  Equiv.trans_apply, Sum.map_inr, finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd,
  Equiv.symm_apply_apply, target]
      have hmem :=
        originalFirstReductionPeriodOneTailKernelElement_schreierPower_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods jk.2 jk.1
      simpa [θ, oneHeadPeriodOneTargetToSchreierHom,
        oneHeadPeriodOneTargetToSchreierGeneratorImage, target, xWord, hPeriod,
        basis, source, ξ, f, T, oneHeadPeriodOneTargetPeriods,
        Equiv.symm_apply_apply] using hmem

private theorem doublePeriodOneTargetToSchreier_powerRelator_mem_normalClosure
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
    (jk : Fin p × Fin tailLen) :
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
    θ
        ((xWord target (finProdFinEquiv jk)) ^
          target.periods (finProdFinEquiv jk)) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
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
  have hIndex : finProdFinEquiv.symm (finProdFinEquiv jk) = jk := by
    exact finProdFinEquiv.symm_apply_apply jk
  have hIndexPair :
      ((finProdFinEquiv jk).divNat, (finProdFinEquiv jk).modNat) = jk := by
    have h := finProdFinEquiv.symm_apply_apply jk
    rw [finProdFinEquiv_symm_apply] at h
    exact h
  have hIndexFst : (finProdFinEquiv jk).divNat = jk.1 :=
    congrArg Prod.fst hIndexPair
  have hIndexSnd : (finProdFinEquiv jk).modNat = jk.2 :=
    congrArg Prod.snd hIndexPair
  have hPeriod :
      target.periods (finProdFinEquiv jk) = tail jk.2 := by
    simp only [doublePeriodOneTailReplicatedSignature, finProdFinEquiv_symm_apply, hIndexSnd, target]
  have hmem :=
    originalFirstReductionPeriodOneTailKernelElement_schreierPower_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods jk.2 jk.1
  simpa [θ, doublePeriodOneTargetToSchreierHom,
    doublePeriodOneTargetToSchreierGeneratorImage, target, xWord, hPeriod,
    basis, source, ξ, f, T, hIndexFst, hIndexSnd] using hmem

private theorem oneHeadPeriodOneTarget_totalRelation_eq_blocks
    {tailLen p : ℕ}
    (m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j)
    (hTailLen : 0 < tailLen) :
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    totalRelation target =
      xWord target
          (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inl (0 : Fin 1))) *
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            xWord target
              (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))).prod)).prod := by
  classical
  dsimp
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let flat : List (FreeGroup (FuchsianGenerator target)) :=
    List.ofFn (fun r : Fin (p * tailLen) =>
      xWord target ⟨1 + r.val, by
        dsimp [target, oneHeadPeriodOneTargetSignature]
        omega⟩)
  let blocks : FreeGroup (FuchsianGenerator target) :=
    (List.ofFn (fun k : Fin p =>
      (List.ofFn (fun j : Fin tailLen =>
        xWord target
          (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))).prod)).prod
  have hFlatBlocks : flat.prod = blocks := by
    dsimp [flat, blocks]
    rw [list_prod_ofFn_mul_blocks]
    congr
    funext k
    congr
    funext j
    apply congrArg (xWord target)
    ext
    simp only [oneHeadPeriodOneTargetOrderedIndexEquiv, finProdFinEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_refl, Equiv.coe_fn_mk, Sum.map_inr, finSumFinEquiv_apply_right, Fin.natAdd_mk, Nat.add_left_cancel_iff]
    rw [Nat.mul_comm tailLen k.val]
    omega
  have hHead :
      (⟨0, by omega⟩ : Fin (1 + p * tailLen)) =
        oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inl (0 : Fin 1)) := by
    ext
    simp only [oneHeadPeriodOneTargetOrderedIndexEquiv, Fin.isValue, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_refl, Sum.map_inl, id_eq, finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.val_eq_zero]
  have hFlat :
      totalRelation target =
        xWord target (⟨0, by omega⟩ : Fin (1 + p * tailLen)) * flat.prod := by
    rw [totalRelation]
    simpa [target, oneHeadPeriodOneTargetSignature, flat, List.ofFn_eq_map,
      List.prod_cons, mul_assoc] using
      congrArg List.prod
        (list_ofFn_one_add
          (fun i : Fin (1 + p * tailLen) => xWord target i))
  simpa [hHead, hFlatBlocks, blocks] using hFlat

private theorem doublePeriodOneTarget_totalRelation_eq_blocks
    {tailLen p : ℕ}
    (tail : Fin tailLen → ℕ)
    (htail : ∀ j, 2 ≤ tail j) (hHigh : 3 ≤ p * tailLen) :
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    totalRelation target =
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          xWord target (finProdFinEquiv (k, j)))).prod)).prod := by
  classical
  dsimp
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  have hFlat :
      totalRelation target =
        (List.ofFn (fun r : Fin (p * tailLen) => xWord target r)).prod := by
    rw [totalRelation]
    simp only [doublePeriodOneTailReplicatedSignature, finProdFinEquiv_symm_apply, List.finRange_zero,
  List.map_nil, List.prod_nil, mul_one, List.ofFn_eq_map, target]
  rw [hFlat]
  rw [list_prod_ofFn_mul_blocks]
  congr
  funext k
  congr
  funext j
  apply congrArg (xWord target)
  ext
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  rw [Nat.mul_comm tailLen k.val]
  omega

private theorem oneHeadPeriodOneTargetToSchreier_totalRelator_mem_normalClosure
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
    θ (totalRelation target) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
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
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let b :=
    originalFirstReductionPeriodOneSecondPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let c :
      Fin tailLen → Fin p →
        (originalFirstReductionPeriodOneFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).ker := fun j k =>
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let S :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)
  let tailBlock : FreeGroup ↥(schreierGeneratorSet
      (originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) :=
    (List.ofFn (fun k : Fin p =>
      (List.ofFn (fun j : Fin tailLen => basis.symm (c j k))).prod)).prod
  have hImage :
      θ (totalRelation target) = basis.symm b * tailBlock := by
    rw [oneHeadPeriodOneTarget_totalRelation_eq_blocks
      m₂' tail hp hm₂'ge htail hTailLen]
    rw [map_mul]
    rw [MonoidHom.map_list_prod_ofFn₂ θ
      (fun k : Fin p => fun j : Fin tailLen =>
        xWord target (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))]
    simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneTargetToSchreierHom,
  oneHeadPeriodOneTargetToSchreierGeneratorImage, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, id_eq, xWord, Fin.isValue,
  Equiv.trans_apply, Sum.map_inl, finSumFinEquiv_apply_left, FreeGroup.lift_apply_of,
  finSumFinEquiv_symm_apply_castAdd, Sum.map_inr, finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd,
  Equiv.symm_apply_apply, θ, target, basis, b, tailBlock, c]
  have hCyclic :
      basis.symm a * basis.symm b * tailBlock ∈ Subgroup.normalClosure S := by
    subst e
    simpa [source, ξ, f, T, basis, a, b, c, S, tailBlock] using
      originalFirstReductionPeriodOneCanonicalSchreier_cyclicBlockTotalProduct_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hA :
      basis.symm a ∈ Subgroup.normalClosure S := by
    simpa [source, ξ, f, T, basis, a, S] using
      originalFirstReductionPeriodOneFirstPowerKernel_schreier_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods hm₁'one
  have hTail :
      basis.symm b * tailBlock ∈ Subgroup.normalClosure S := by
    exact ReidemeisterSchreier.Discrete.Presentations.mem_of_left_mul_mem_normalClosure hA (by simpa [mul_assoc] using hCyclic)
  change θ (totalRelation target) ∈ Subgroup.normalClosure S
  rw [hImage]
  exact hTail

private theorem doublePeriodOneTargetToSchreier_totalRelator_mem_normalClosure
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
    θ (totalRelation target) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
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
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let b :=
    originalFirstReductionPeriodOneSecondPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let c :
      Fin tailLen → Fin p →
        (originalFirstReductionPeriodOneFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).ker := fun j k =>
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let S :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)
  let tailBlock : FreeGroup ↥(schreierGeneratorSet
      (originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) :=
    (List.ofFn (fun k : Fin p =>
      (List.ofFn (fun j : Fin tailLen => basis.symm (c j k))).prod)).prod
  have hImage :
      θ (totalRelation target) = tailBlock := by
    have hIndexFst :
        ∀ (k : Fin p) (j : Fin tailLen),
          (finProdFinEquiv (k, j)).divNat = k := by
      intro k j
      have h := finProdFinEquiv.symm_apply_apply (k, j)
      rw [finProdFinEquiv_symm_apply] at h
      exact congrArg Prod.fst h
    have hIndexSnd :
        ∀ (k : Fin p) (j : Fin tailLen),
          (finProdFinEquiv (k, j)).modNat = j := by
      intro k j
      have h := finProdFinEquiv.symm_apply_apply (k, j)
      rw [finProdFinEquiv_symm_apply] at h
      exact congrArg Prod.snd h
    rw [doublePeriodOneTarget_totalRelation_eq_blocks
      tail htail hHigh]
    rw [MonoidHom.map_list_prod_ofFn₂ θ
      (fun k : Fin p => fun j : Fin tailLen =>
        xWord target (finProdFinEquiv (k, j)))]
    simp only [doublePeriodOneTargetToSchreierHom, doublePeriodOneTargetToSchreierGeneratorImage,
  Lean.Elab.WF.paramLet, finProdFinEquiv_symm_apply, id_eq, xWord, FreeGroup.lift_apply_of, hIndexSnd, hIndexFst, θ,
  target, tailBlock, basis, c]
  have hCyclic :
      basis.symm a * basis.symm b * tailBlock ∈ Subgroup.normalClosure S := by
    subst e
    simpa [source, ξ, f, T, basis, a, b, c, S, tailBlock] using
      originalFirstReductionPeriodOneCanonicalSchreier_cyclicBlockTotalProduct_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hA :
      basis.symm a ∈ Subgroup.normalClosure S := by
    simpa [source, ξ, f, T, basis, a, S] using
      originalFirstReductionPeriodOneFirstPowerKernel_schreier_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods hm₁'one
  have hB :
      basis.symm b ∈ Subgroup.normalClosure S := by
    have hPow :=
      originalFirstReductionPeriodOneSecondPowerKernel_schreierPower_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
    simpa [source, ξ, f, T, basis, b, S, hm₂'one] using hPow
  have hAfterA :
      basis.symm b * tailBlock ∈ Subgroup.normalClosure S := by
    exact ReidemeisterSchreier.Discrete.Presentations.mem_of_left_mul_mem_normalClosure hA (by simpa [mul_assoc] using hCyclic)
  have hTail :
      tailBlock ∈ Subgroup.normalClosure S := by
    exact ReidemeisterSchreier.Discrete.Presentations.mem_of_left_mul_mem_normalClosure hB hAfterA
  change θ (totalRelation target) ∈ Subgroup.normalClosure S
  rw [hImage]
  exact hTail

private theorem fuchsianTarget_mapsRelators_of_power_and_total
    (τ : FuchsianSignature) {G : Type*} [Group G] {S : Set G}
    (η : FreeGroup (FuchsianGenerator τ) →* G)
    (hPower :
      ∀ i : Fin τ.numPeriods,
        η (xWord τ i ^ τ.periods i) ∈ Subgroup.normalClosure S)
    (hTotal : η (totalRelation τ) ∈ Subgroup.normalClosure S) :
    ∀ r ∈ relators τ, η r ∈ Subgroup.normalClosure S := by
  intro r hr
  rcases hr with ⟨i, rfl⟩ | rfl
  · exact hPower i
  · exact hTotal

theorem oneHeadPeriodOneTargetToSchreier_mapsTargetRelators
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
    ∀ r ∈ relators target,
      θ r ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
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
  refine
    fuchsianTarget_mapsRelators_of_power_and_total target θ ?_ ?_
  · intro i
    let idx := (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p).symm i
    have h :=
      oneHeadPeriodOneTargetToSchreier_powerRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods idx
    simpa [source, target, ξ, f, T, basis, θ, idx] using h
  · simpa [source, target, ξ, f, T, basis, θ] using
      oneHeadPeriodOneTargetToSchreier_totalRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he hm₁'one

theorem doublePeriodOneTargetToSchreier_mapsTargetRelators
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
    ∀ r ∈ relators target,
      θ r ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
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
  refine
    fuchsianTarget_mapsRelators_of_power_and_total target θ ?_ ?_
  · intro i
    let jk := finProdFinEquiv.symm i
    have hidx : finProdFinEquiv jk = i := by
      simpa [jk] using finProdFinEquiv.apply_symm_apply i
    have h :=
      doublePeriodOneTargetToSchreier_powerRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods jk
    simpa [source, target, ξ, f, T, basis, θ, hidx] using h
  · simpa [source, target, ξ, f, T, basis, θ] using
      doublePeriodOneTargetToSchreier_totalRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he
          hm₁'one hm₂'one

private theorem oneHeadPeriodOneSchreierToTargetHom_firstPowerWord
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
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    η
        (basis.symm
          (originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) =
      (1 : FreeGroup (FuchsianGenerator target)) := by
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
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e,
      originalFirstReductionPeriodOneFirstPowerKernel_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e⟩
  have hzWord :
      basis.symm
          (originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) =
        (FreeGroup.of z)⁻¹ := by
    simpa [source, φ, hT, basis, z] using
      originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z
  have hzImage : η (FreeGroup.of z) = (1 : FreeGroup (FuchsianGenerator target)) := by
    simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneSchreierToTargetHom,
  oneHeadPeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, ↓reduceIte, η, z,
  target, source]
  calc
    η
        (basis.symm
          (originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by rw [map_inv]
    _ = (1 : FreeGroup (FuchsianGenerator target)) := by rw [hzImage, inv_one]

private theorem doublePeriodOneSchreierToTargetHom_firstPowerWord
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
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    η
        (basis.symm
          (originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) =
      (1 : FreeGroup (FuchsianGenerator target)) := by
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
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e,
      originalFirstReductionPeriodOneFirstPowerKernel_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e⟩
  have hzWord :
      basis.symm
          (originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) =
        (FreeGroup.of z)⁻¹ := by
    simpa [source, φ, hT, basis, z] using
      originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z
  have hzImage : η (FreeGroup.of z) = (1 : FreeGroup (FuchsianGenerator target)) := by
    simp only [Lean.Elab.WF.paramLet, doublePeriodOneSchreierToTargetHom,
  doublePeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, ↓reduceIte, η, z,
  target, source]
  calc
    η
        (basis.symm
          (originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by rw [map_inv]
    _ = (1 : FreeGroup (FuchsianGenerator target)) := by rw [hzImage, inv_one]

private theorem oneHeadPeriodOneSchreierToTargetHom_tailWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    η
        (basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)) =
      xWord target (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))) := by
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
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k,
      originalFirstReductionPeriodOneTailKernelElement_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k⟩
  have hzWord :
      basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [source, φ, hT, basis, z] using
      originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z
  have hxne : x ≠ tailGen j := by
    intro hEq
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, x, tailGen] at hEq
  have hyne : y ≠ tailGen j := by
    intro hEq
    simp only [Fin.isValue, FuchsianGenerator.elliptic.injEq, y, tailGen] at hEq
    have hbad := e.injective hEq
    cases hbad
  have hFirst :
      ¬ (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      simpa [z, source, φ, x, tailGen] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
    have hright :
        ((originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ p := by
      simpa [source, φ, x] using
        originalFirstReductionPeriodOneFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hSecond :
      ¬ ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      simpa [z, source, φ, x, tailGen] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
    let r : ℕ := ((k'.val : ZMod p) - 1).val
    have hright :
        ((originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k'.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simpa [source, φ, x, y, r] using
        originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k'
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k'.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, hyne, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hTail :
      ∃ j' : Fin tailLen, ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' := ⟨j, k, rfl⟩
  let j' : Fin tailLen := Classical.choose hTail
  let hk' : ∃ k' : Fin p,
      (z : φ.ker) =
        originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' :=
    Classical.choose_spec hTail
  let k' : Fin p := Classical.choose hk'
  have hTailChoose :
      oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k', j')) =
        oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j)) := by
    have hEqTail :
        originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' := by
      simpa [z, j', hk', k'] using Classical.choose_spec hk'
    rcases
      originalFirstReductionPeriodOneTailKernelElement_inj
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hEqTail with
      ⟨hj, hk⟩
    simp only [hk, hj]
  have hzImage :
      η (FreeGroup.of z) =
        (xWord target
          (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneSchreierToTargetHom,
  oneHeadPeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, hTail, hTailChoose, η, z, target, source, j', k']
  calc
    η
        (basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by rw [map_inv]
    _ =
        ((xWord target
          (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        xWord target
          (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))) := by
          rw [inv_inv]

private theorem doublePeriodOneSchreierToTargetHom_tailWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    η
        (basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)) =
      xWord target (finProdFinEquiv (k, j)) := by
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
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k,
      originalFirstReductionPeriodOneTailKernelElement_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k⟩
  have hzWord :
      basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [source, φ, hT, basis, z] using
      originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z
  have hxne : x ≠ tailGen j := by
    intro hEq
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, x, tailGen] at hEq
  have hyne : y ≠ tailGen j := by
    intro hEq
    simp only [Fin.isValue, FuchsianGenerator.elliptic.injEq, y, tailGen] at hEq
    have hbad := e.injective hEq
    cases hbad
  have hFirst :
      ¬ (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      simpa [z, source, φ, x, tailGen] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
    have hright :
        ((originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ p := by
      simpa [source, φ, x] using
        originalFirstReductionPeriodOneFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hSecond :
      ¬ ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      simpa [z, source, φ, x, tailGen] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
    let r : ℕ := ((k'.val : ZMod p) - 1).val
    have hright :
        ((originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k'.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simpa [source, φ, x, y, r] using
        originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k'
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k'.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, hyne, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hTail :
      ∃ j' : Fin tailLen, ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' := ⟨j, k, rfl⟩
  let j' : Fin tailLen := Classical.choose hTail
  let hk' : ∃ k' : Fin p,
      (z : φ.ker) =
        originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' :=
    Classical.choose_spec hTail
  let k' : Fin p := Classical.choose hk'
  have hTailChoose :
      finProdFinEquiv (k', j') = finProdFinEquiv (k, j) := by
    have hEqTail :
        originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' := by
      simpa [z, j', hk', k'] using Classical.choose_spec hk'
    rcases
      originalFirstReductionPeriodOneTailKernelElement_inj
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hEqTail with
      ⟨hj, hk⟩
    simp only [hk, hj]
  have hzImage :
      η (FreeGroup.of z) =
        (xWord target (finProdFinEquiv (k, j)))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, doublePeriodOneSchreierToTargetHom,
  doublePeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, hTail, hTailChoose, η, z, target, source, j', k']
  calc
    η
        (basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by rw [map_inv]
    _ = ((xWord target (finProdFinEquiv (k, j)))⁻¹)⁻¹ := by
          rw [hzImage]
    _ = xWord target (finProdFinEquiv (k, j)) := by
          rw [inv_inv]

private theorem oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    η
        (basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k)) =
      (oneHeadPeriodOneSecondEdgeForwardWord
        m₂' tail hp hm₂'ge htail hTailLen k)⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k,
      originalFirstReductionPeriodOneSecondEdgeKernelElement_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k⟩
  have hzWord :
      basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [source, φ, hT, basis, z] using
      originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z
  have hxne : x ≠ y := by
    intro hEq
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, zero_ne_one, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simpa [z, source, φ, x, y, r] using
        originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
    have hright :
        ((originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ p := by
      simpa [source, φ, x] using
        originalFirstReductionPeriodOneFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hTail :
      ¬ ∃ j' : Fin tailLen, ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' := by
    intro h
    rcases h with ⟨j', k', hEq⟩
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simpa [z, source, φ, x, y, r] using
        originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
    have hright :
        ((originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k'.val * FreeGroup.of (tailGen j') *
            ((FreeGroup.of x) ^ k'.val)⁻¹ := by
      simpa [source, φ, x, tailGen] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k'
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k'.val *
            FreeGroup.of (tailGen j') *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k'.val)⁻¹ := by
      simpa [hleft, hright] using hval
    have hyne : y ≠ tailGen j' := by
      intro hEq'
      simp only [Fin.isValue, FuchsianGenerator.elliptic.injEq, y, tailGen] at hEq'
      have hbad := e.injective hEq'
      cases hbad
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, mul_ite, left_eq_ite_iff, ofAdd_eq_one, one_ne_zero, imp_false, Decidable.not_not, χ] at hmap
    exact hyne hmap.symm
  have hSecond :
      ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' := ⟨k, rfl⟩
  let k' : Fin p := Classical.choose hSecond
  have hSecondChoose :
      oneHeadPeriodOneSecondEdgeForwardWord
          m₂' tail hp hm₂'ge htail hTailLen k' =
        oneHeadPeriodOneSecondEdgeForwardWord
          m₂' tail hp hm₂'ge htail hTailLen k := by
    have hEqSecond :
        originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' := by
      simpa [z, k'] using Classical.choose_spec hSecond
    have hk :=
      originalFirstReductionPeriodOneSecondEdgeKernelElement_inj
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hEqSecond
    simp only [hk]
  have hzImage :
      η (FreeGroup.of z) =
        oneHeadPeriodOneSecondEdgeForwardWord
          m₂' tail hp hm₂'ge htail hTailLen k := by
    simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneSchreierToTargetHom,
  oneHeadPeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, hSecondChoose, η, z, k', source]
  calc
    η
        (basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by rw [map_inv]
    _ =
        (oneHeadPeriodOneSecondEdgeForwardWord
          m₂' tail hp hm₂'ge htail hTailLen k)⁻¹ := by
          rw [hzImage]

private theorem doublePeriodOneSchreierToTargetHom_secondEdgeWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    η
        (basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k)) =
      (doublePeriodOneSecondEdgeForwardWord
        tail hp htail hHigh k)⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k,
      originalFirstReductionPeriodOneSecondEdgeKernelElement_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k⟩
  have hzWord :
      basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [source, φ, hT, basis, z] using
      originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z
  have hxne : x ≠ y := by
    intro hEq
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, zero_ne_one, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simpa [z, source, φ, x, y, r] using
        originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
    have hright :
        ((originalFirstReductionPeriodOneFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ p := by
      simpa [source, φ, x] using
        originalFirstReductionPeriodOneFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ p := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hTail :
      ¬ ∃ j' : Fin tailLen, ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' := by
    intro h
    rcases h with ⟨j', k', hEq⟩
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simpa [z, source, φ, x, y, r] using
        originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
    have hright :
        ((originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k' : φ.ker) :
              FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x) ^ k'.val * FreeGroup.of (tailGen j') *
            ((FreeGroup.of x) ^ k'.val)⁻¹ := by
      simpa [source, φ, x, tailGen] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j' k'
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k'.val *
            FreeGroup.of (tailGen j') *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k'.val)⁻¹ := by
      simpa [hleft, hright] using hval
    have hyne : y ≠ tailGen j' := by
      intro hEq'
      simp only [Fin.isValue, FuchsianGenerator.elliptic.injEq, y, tailGen] at hEq'
      have hbad := e.injective hEq'
      cases hbad
    let χ : FuchsianGenerator source → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, mul_ite, left_eq_ite_iff, ofAdd_eq_one, one_ne_zero, imp_false, Decidable.not_not, χ] at hmap
    exact hyne hmap.symm
  have hSecond :
      ∃ k' : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' := ⟨k, rfl⟩
  let k' : Fin p := Classical.choose hSecond
  have hSecondChoose :
      doublePeriodOneSecondEdgeForwardWord
          tail hp htail hHigh k' =
        doublePeriodOneSecondEdgeForwardWord
          tail hp htail hHigh k := by
    have hEqSecond :
        originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k' := by
      simpa [z, k'] using Classical.choose_spec hSecond
    have hk :=
      originalFirstReductionPeriodOneSecondEdgeKernelElement_inj
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hEqSecond
    simp only [hk]
  have hzImage :
      η (FreeGroup.of z) =
        doublePeriodOneSecondEdgeForwardWord
          tail hp htail hHigh k := by
    simp only [Lean.Elab.WF.paramLet, doublePeriodOneSchreierToTargetHom,
  doublePeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, hSecondChoose, η, z, k', source]
  calc
    η
        (basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by rw [map_inv]
    _ =
        (doublePeriodOneSecondEdgeForwardWord
          tail hp htail hHigh k)⁻¹ := by
          rw [hzImage]

theorem doublePeriodOneSchreierToTarget_toInv_generators_mem_normalClosure
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
    let θ :=
      doublePeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    ∀ y : FuchsianGenerator target,
      η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
        Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  intro y
  cases y with
  | elliptic i =>
      let jk : Fin p × Fin tailLen := finProdFinEquiv.symm i
      have hidx : finProdFinEquiv jk = i := by
        simpa [jk] using finProdFinEquiv.apply_symm_apply i
      have hword :
          η
              ((originalFirstReductionPeriodOneSchreierBasisEquiv
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).symm
                (originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e jk.2 jk.1)) =
            xWord target (finProdFinEquiv (jk.1, jk.2)) := by
        simpa [source, target, η] using
          doublePeriodOneSchreierToTargetHom_tailWord
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e jk.2 jk.1
      have hidxPair : finProdFinEquiv (jk.1, jk.2) = i := by
        simpa [jk] using hidx
      have hword' :
          η
              ((originalFirstReductionPeriodOneSchreierBasisEquiv
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).symm
                (originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e jk.2 jk.1)) =
            FreeGroup.of (FuchsianGenerator.elliptic i) := by
        simpa [xWord, hidxPair] using hword
      have hcomp :
          η (θ (FreeGroup.of (FuchsianGenerator.elliptic i))) =
            FreeGroup.of (FuchsianGenerator.elliptic i) := by
        simpa [θ, η, doublePeriodOneTargetToSchreierHom,
          doublePeriodOneTargetToSchreierGeneratorImage, target, jk] using
          hword'
      have hprod :
          η (θ (FreeGroup.of (FuchsianGenerator.elliptic i))) *
              (FreeGroup.of (FuchsianGenerator.elliptic i))⁻¹ =
            1 := by
        simp only [Lean.Elab.WF.paramLet, hcomp, mul_inv_cancel]
      rw [hprod]
      exact Subgroup.one_mem (Subgroup.normalClosure (relators target))
  | surfaceA a =>
      fin_cases a
  | surfaceB b =>
      fin_cases b

theorem doublePeriodOneSchreierToTarget_toInv_mem_normalClosure_of_generators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hgen :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
      letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
      let θ :=
        doublePeriodOneTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
      let η :=
        doublePeriodOneSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
      ∀ y : FuchsianGenerator target,
        η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators target)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let θ :=
      doublePeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    ∀ y : FreeGroup (FuchsianGenerator target),
      η (θ y) * y⁻¹ ∈ Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let F : FreeGroup (FuchsianGenerator target) →* FreeGroup (FuchsianGenerator target) :=
    η.comp θ
  have hgen' :
      ∀ y : FuchsianGenerator target,
        F (FreeGroup.of y) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators target) := by
    intro y
    simpa [source, target, θ, η, F] using hgen y
  intro y
  simpa [F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv
      (relators target) F hgen' y

private theorem oneHeadPeriodOneTargetToSchreierHom_tailBlock
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let θ :=
      oneHeadPeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    θ (oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen k) =
      (List.ofFn (fun j : Fin tailLen =>
        basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k))).prod := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  change
    θ
        ((List.ofFn (fun j : Fin tailLen =>
          xWord target
            (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))).prod) =
      (List.ofFn (fun j : Fin tailLen =>
        basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k))).prod
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext j
  simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneTargetToSchreierHom,
  oneHeadPeriodOneTargetToSchreierGeneratorImage, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, id_eq, xWord, Equiv.trans_apply,
  Sum.map_inr, finSumFinEquiv_apply_right, Function.comp_apply, FreeGroup.lift_apply_of,
  finSumFinEquiv_symm_apply_natAdd, Equiv.symm_apply_apply, θ, target, basis]

private theorem oneHeadPeriodOneSecondEdgeForward_invComp_mem_normalClosure
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
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    let θ :=
      oneHeadPeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    θ (oneHeadPeriodOneSecondEdgeForwardWord m₂' tail hp hm₂'ge htail hTailLen k) *
        basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let prev : Fin p :=
    if k.val = 0 then ⟨p - 1, by omega⟩ else ⟨k.val - 1, by omega⟩
  have hbase :
      (List.ofFn (fun j : Fin tailLen =>
            basis.symm
              (originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j prev))).prod *
          basis.symm
            (originalFirstReductionPeriodOneSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [source, ξ, f, T, basis, prev] using
      originalFirstReductionPeriodOne_tailBlock_secondEdge_schreier_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods he hm₁'one k
  by_cases h0 : k.val = 0
  · have hword :
        oneHeadPeriodOneSecondEdgeForwardWord m₂' tail hp hm₂'ge htail hTailLen k =
          oneHeadPeriodOneTargetTailBlockWord
            m₂' tail hp hm₂'ge htail hTailLen ⟨p - 1, by omega⟩ := by
      unfold oneHeadPeriodOneSecondEdgeForwardWord
      dsimp
      rw [if_pos h0]
    rw [hword]
    rw [oneHeadPeriodOneTargetToSchreierHom_tailBlock]
    simpa [source, ξ, f, T, basis, θ, prev, h0] using hbase
  · have hword :
        oneHeadPeriodOneSecondEdgeForwardWord m₂' tail hp hm₂'ge htail hTailLen k =
          oneHeadPeriodOneTargetTailBlockWord
            m₂' tail hp hm₂'ge htail hTailLen ⟨k.val - 1, by omega⟩ := by
      unfold oneHeadPeriodOneSecondEdgeForwardWord
      dsimp
      rw [if_neg h0]
    rw [hword]
    rw [oneHeadPeriodOneTargetToSchreierHom_tailBlock]
    simpa [source, ξ, f, T, basis, θ, prev, h0] using hbase

private theorem oneHeadPeriodOneSchreierToTarget_invComp_generator_mem_normalClosure
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
    (z :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
      let hT :=
        originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
      ↥(schreierGeneratorSet hT)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    let θ :=
      oneHeadPeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)
  have hzWord :
      (FreeGroup.of z)⁻¹ = basis.symm (z : φ.ker) := by
    symm
    simp only [Lean.Elab.WF.paramLet, originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply, basis]
  by_cases hFirst :
      (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  · have hzFirstWord :
        (FreeGroup.of z)⁻¹ =
          basis.symm
            (originalFirstReductionPeriodOneFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) := by
      rw [hzWord, hFirst]
    have hη :
        η (FreeGroup.of z) = 1 := by
      simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneSchreierToTargetHom,
  oneHeadPeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, η,
  source]
    have hmem :
        basis.symm
            (originalFirstReductionPeriodOneFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) ∈
          Subgroup.normalClosure R := by
      simpa [source, ξ, f, T, basis, R] using
        originalFirstReductionPeriodOneFirstPowerKernel_schreier_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods hm₁'one
    have hprod :
        θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ =
          basis.symm
            (originalFirstReductionPeriodOneFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) := by
      simp only [Lean.Elab.WF.paramLet, hη, map_one, hzFirstWord, one_mul]
    simpa [R] using hprod ▸ hmem
  · by_cases hSecond :
      ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
    · let k : Fin p := Classical.choose hSecond
      have hzK :
          (z : φ.ker) =
            originalFirstReductionPeriodOneSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k :=
        Classical.choose_spec hSecond
      have hzKWord :
          (FreeGroup.of z)⁻¹ =
            basis.symm
              (originalFirstReductionPeriodOneSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) := by
        rw [hzWord, hzK]
      have hη :
          η (FreeGroup.of z) =
            oneHeadPeriodOneSecondEdgeForwardWord m₂' tail hp hm₂'ge htail hTailLen k := by
        simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneSchreierToTargetHom,
  oneHeadPeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, η, k, source]
      have hmem :
          θ (oneHeadPeriodOneSecondEdgeForwardWord m₂' tail hp hm₂'ge htail hTailLen k) *
              basis.symm
                (originalFirstReductionPeriodOneSecondEdgeKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
            Subgroup.normalClosure R := by
        simpa [source, ξ, f, T, basis, θ, R] using
          oneHeadPeriodOneSecondEdgeForward_invComp_mem_normalClosure
            m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he
            hm₁'one k
      have hprod :
          θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ =
            θ (oneHeadPeriodOneSecondEdgeForwardWord
                  m₂' tail hp hm₂'ge htail hTailLen k) *
              basis.symm
                (originalFirstReductionPeriodOneSecondEdgeKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) := by
        rw [hη, hzKWord]
      simpa [R] using hprod ▸ hmem
    · rcases
        originalFirstReductionPeriodOne_schreierGeneratorSet_cases
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z with
        hFirstCase | hSecondCase | hTailCase
      · exact False.elim (hFirst hFirstCase)
      · exact False.elim (hSecond hSecondCase)
      · let j : Fin tailLen := Classical.choose hTailCase
        let hk : ∃ k : Fin p,
            (z : φ.ker) =
              originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k :=
          Classical.choose_spec hTailCase
        let k : Fin p := Classical.choose hk
        have hzTail :
            (z : φ.ker) =
              originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k :=
          Classical.choose_spec hk
        have hzTailWord :
            (FreeGroup.of z)⁻¹ =
              basis.symm
                (originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) := by
          rw [hzWord, hzTail]
        have hη :
            η (FreeGroup.of z) =
              (xWord target
                (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))⁻¹ := by
          simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneSchreierToTargetHom,
  oneHeadPeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, hTailCase, η, target, k, j, source]
        have hθ :
            θ (xWord target
                (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j)))) =
              basis.symm
                (originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) := by
          simp only [Lean.Elab.WF.paramLet, oneHeadPeriodOneTargetToSchreierHom,
  oneHeadPeriodOneTargetToSchreierGeneratorImage, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, id_eq, xWord, Equiv.trans_apply,
  Sum.map_inr, finSumFinEquiv_apply_right, FreeGroup.lift_apply_of, finSumFinEquiv_symm_apply_natAdd,
  Equiv.symm_apply_apply, θ, target, basis]
        have hprod :
            θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ = 1 := by
          rw [hη, map_inv, hθ, hzTailWord]
          group
        rw [hprod]
        exact Subgroup.one_mem (Subgroup.normalClosure R)

theorem oneHeadPeriodOneSchreierToTarget_invComp_mem_normalClosure
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
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    ∀ w : FreeGroup ↥(schreierGeneratorSet hT),
      θ (η w) * w⁻¹ ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)
  let F : FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup ↥(schreierGeneratorSet hT) :=
    θ.comp η
  have hgen :
      ∀ z : ↥(schreierGeneratorSet hT),
        F (FreeGroup.of z) * (FreeGroup.of z)⁻¹ ∈ Subgroup.normalClosure R := by
    intro z
    simpa [source, ξ, f, T, hT, basis, θ, η, R, F] using
      oneHeadPeriodOneSchreierToTarget_invComp_generator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he hm₁'one z
  intro w
  simpa [R, F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv R F hgen w

private theorem doublePeriodOneTargetToSchreierHom_tailBlock
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let θ :=
      doublePeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    θ (doublePeriodOneTargetTailBlockWord tail htail hHigh k) =
      (List.ofFn (fun j : Fin tailLen =>
        basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k))).prod := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  have hIndexFst :
      ∀ (j : Fin tailLen), (finProdFinEquiv (k, j)).divNat = k := by
    intro j
    have h := finProdFinEquiv.symm_apply_apply (k, j)
    rw [finProdFinEquiv_symm_apply] at h
    exact congrArg Prod.fst h
  have hIndexSnd :
      ∀ (j : Fin tailLen), (finProdFinEquiv (k, j)).modNat = j := by
    intro j
    have h := finProdFinEquiv.symm_apply_apply (k, j)
    rw [finProdFinEquiv_symm_apply] at h
    exact congrArg Prod.snd h
  change
    θ
        ((List.ofFn (fun j : Fin tailLen =>
          xWord target (finProdFinEquiv (k, j)))).prod) =
      (List.ofFn (fun j : Fin tailLen =>
        basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k))).prod
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext j
  simp only [Lean.Elab.WF.paramLet, doublePeriodOneTargetToSchreierHom,
  doublePeriodOneTargetToSchreierGeneratorImage, finProdFinEquiv_symm_apply, id_eq, xWord, Function.comp_apply,
  FreeGroup.lift_apply_of, hIndexSnd j, hIndexFst j, θ, target, basis]

private theorem doublePeriodOneSecondEdgeForward_invComp_mem_normalClosure
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
    (hm₁'one : m₁' = 1)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    let θ :=
      doublePeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    θ (doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh k) *
        basis.symm
          (originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let prev : Fin p :=
    if k.val = 0 then ⟨p - 1, by omega⟩ else ⟨k.val - 1, by omega⟩
  have hbase :
      (List.ofFn (fun j : Fin tailLen =>
            basis.symm
              (originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j prev))).prod *
          basis.symm
            (originalFirstReductionPeriodOneSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
    simpa [source, ξ, f, T, basis, prev] using
      originalFirstReductionPeriodOne_tailBlock_secondEdge_schreier_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods he hm₁'one k
  by_cases h0 : k.val = 0
  · have hword :
        doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh k =
          doublePeriodOneTargetTailBlockWord tail htail hHigh ⟨p - 1, by omega⟩ := by
      unfold doublePeriodOneSecondEdgeForwardWord
      dsimp
      rw [if_pos h0]
    rw [hword]
    rw [doublePeriodOneTargetToSchreierHom_tailBlock]
    simpa [source, ξ, f, T, basis, θ, prev, h0] using hbase
  · have hword :
        doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh k =
          doublePeriodOneTargetTailBlockWord tail htail hHigh ⟨k.val - 1, by omega⟩ := by
      unfold doublePeriodOneSecondEdgeForwardWord
      dsimp
      rw [if_neg h0]
    rw [hword]
    rw [doublePeriodOneTargetToSchreierHom_tailBlock]
    simpa [source, ξ, f, T, basis, θ, prev, h0] using hbase

private theorem doublePeriodOneSchreierToTarget_invComp_generator_mem_normalClosure
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
    (hm₁'one : m₁' = 1)
    (z :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
      let hT :=
        originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
      ↥(schreierGeneratorSet hT)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    let θ :=
      doublePeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let ξ :=
    originalFirstReductionPeriodOneQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let f := ellipticQuotientGeneratorImage source ξ
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let T :=
    originalFirstReductionPeriodOneSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hT :=
    originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let θ :=
    doublePeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)
  have hzWord :
      (FreeGroup.of z)⁻¹ = basis.symm (z : φ.ker) := by
    symm
    simp only [Lean.Elab.WF.paramLet, originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply, basis]
  by_cases hFirst :
      (z : φ.ker) =
        originalFirstReductionPeriodOneFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  · have hzFirstWord :
        (FreeGroup.of z)⁻¹ =
          basis.symm
            (originalFirstReductionPeriodOneFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) := by
      rw [hzWord, hFirst]
    have hη :
        η (FreeGroup.of z) = 1 := by
      simp only [Lean.Elab.WF.paramLet, doublePeriodOneSchreierToTargetHom,
  doublePeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, η,
  source]
    have hmem :
        basis.symm
            (originalFirstReductionPeriodOneFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) ∈
          Subgroup.normalClosure R := by
      simpa [source, ξ, f, T, basis, R] using
        originalFirstReductionPeriodOneFirstPowerKernel_schreier_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods hm₁'one
    have hprod :
        θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ =
          basis.symm
            (originalFirstReductionPeriodOneFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) := by
      simp only [Lean.Elab.WF.paramLet, hη, map_one, hzFirstWord, one_mul]
    simpa [R] using hprod ▸ hmem
  · by_cases hSecond :
      ∃ k : Fin p,
        (z : φ.ker) =
          originalFirstReductionPeriodOneSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
    · let k : Fin p := Classical.choose hSecond
      have hzK :
          (z : φ.ker) =
            originalFirstReductionPeriodOneSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k :=
        Classical.choose_spec hSecond
      have hzKWord :
          (FreeGroup.of z)⁻¹ =
            basis.symm
              (originalFirstReductionPeriodOneSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) := by
        rw [hzWord, hzK]
      have hη :
          η (FreeGroup.of z) =
            doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh k := by
        simp only [Lean.Elab.WF.paramLet, doublePeriodOneSchreierToTargetHom,
  doublePeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, η, k, source]
      have hmem :
          θ (doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh k) *
              basis.symm
                (originalFirstReductionPeriodOneSecondEdgeKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) ∈
            Subgroup.normalClosure R := by
        simpa [source, ξ, f, T, basis, θ, R] using
          doublePeriodOneSecondEdgeForward_invComp_mem_normalClosure
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he
            hm₁'one k
      have hprod :
          θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ =
            θ (doublePeriodOneSecondEdgeForwardWord tail hp htail hHigh k) *
              basis.symm
                (originalFirstReductionPeriodOneSecondEdgeKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k) := by
        rw [hη, hzKWord]
      simpa [R] using hprod ▸ hmem
    · rcases
        originalFirstReductionPeriodOne_schreierGeneratorSet_cases
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e z with
        hFirstCase | hSecondCase | hTailCase
      · exact False.elim (hFirst hFirstCase)
      · exact False.elim (hSecond hSecondCase)
      · let j : Fin tailLen := Classical.choose hTailCase
        let hk : ∃ k : Fin p,
            (z : φ.ker) =
              originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k :=
          Classical.choose_spec hTailCase
        let k : Fin p := Classical.choose hk
        have hzTail :
            (z : φ.ker) =
              originalFirstReductionPeriodOneTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k :=
          Classical.choose_spec hk
        have hzTailWord :
            (FreeGroup.of z)⁻¹ =
              basis.symm
                (originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) := by
          rw [hzWord, hzTail]
        have hη :
            η (FreeGroup.of z) =
              (xWord target (finProdFinEquiv (k, j)))⁻¹ := by
          simp only [Lean.Elab.WF.paramLet, doublePeriodOneSchreierToTargetHom,
  doublePeriodOneSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte,
  hSecond, ↓reduceDIte, hTailCase, η, target, k, j, source]
        have hIndexFst :
            (finProdFinEquiv (k, j)).divNat = k := by
          have h := finProdFinEquiv.symm_apply_apply (k, j)
          rw [finProdFinEquiv_symm_apply] at h
          exact congrArg Prod.fst h
        have hIndexSnd :
            (finProdFinEquiv (k, j)).modNat = j := by
          have h := finProdFinEquiv.symm_apply_apply (k, j)
          rw [finProdFinEquiv_symm_apply] at h
          exact congrArg Prod.snd h
        have hθ :
            θ (xWord target (finProdFinEquiv (k, j))) =
              basis.symm
                (originalFirstReductionPeriodOneTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k) := by
          simp only [Lean.Elab.WF.paramLet, doublePeriodOneTargetToSchreierHom,
  doublePeriodOneTargetToSchreierGeneratorImage, finProdFinEquiv_symm_apply, id_eq, xWord, FreeGroup.lift_apply_of,
  hIndexSnd, hIndexFst, θ, target, basis]
        have hprod :
            θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ = 1 := by
          rw [hη, map_inv, hθ, hzTailWord]
          group
        rw [hprod]
        exact Subgroup.one_mem (Subgroup.normalClosure R)

theorem doublePeriodOneSchreierToTarget_invComp_mem_normalClosure
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
    (hm₁'one : m₁' = 1) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
    ∀ w : FreeGroup ↥(schreierGeneratorSet hT),
      θ (η w) * w⁻¹ ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
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
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T)
  let F : FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup ↥(schreierGeneratorSet hT) :=
    θ.comp η
  have hgen :
      ∀ z : ↥(schreierGeneratorSet hT),
        F (FreeGroup.of z) * (FreeGroup.of z)⁻¹ ∈ Subgroup.normalClosure R := by
    intro z
    simpa [source, ξ, f, T, hT, basis, θ, η, R, F] using
      doublePeriodOneSchreierToTarget_invComp_generator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he hm₁'one z
  intro w
  simpa [R, F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv R F hgen w

private theorem periodOne_negOneCycleSegmentProduct_eq {G : Type*} [Group G]
    (x y : G) : ∀ (n l : ℕ), l ≤ n →
    (List.ofFn (fun i : Fin l =>
      x ^ (n - i.val) * y * (x ^ (n - 1 - i.val))⁻¹)).prod =
        x ^ n * y ^ l * (x ^ (n - l))⁻¹
  | n, 0, _ => by
      simp only [List.ofFn_zero, List.prod_nil, pow_zero, mul_one, tsub_zero, mul_inv_cancel]
  | n, l + 1, h => by
      have hl : l ≤ n - 1 := by omega
      rw [List.ofFn_succ, List.prod_cons]
      simp only [Fin.val_zero, tsub_zero]
      change
        x ^ n * y * (x ^ (n - 1))⁻¹ *
            (List.ofFn (fun i : Fin l =>
              x ^ (n - (i.val + 1)) * y * (x ^ (n - 1 - (i.val + 1)))⁻¹)).prod =
          x ^ n * y ^ (l + 1) * (x ^ (n - (l + 1)))⁻¹
      have htail :
          (List.ofFn (fun i : Fin l =>
              x ^ (n - (i.val + 1)) * y * (x ^ (n - 1 - (i.val + 1)))⁻¹)).prod =
            (List.ofFn (fun i : Fin l =>
              x ^ (n - 1 - i.val) * y * (x ^ (n - 1 - 1 - i.val))⁻¹)).prod := by
        congr
        funext i
        have h1 : n - (i.val + 1) = n - 1 - i.val := by omega
        have h2 : n - 1 - (i.val + 1) = n - 1 - 1 - i.val := by omega
        simp only [h1, h2]
      rw [htail]
      rw [periodOne_negOneCycleSegmentProduct_eq x y (n - 1) l hl]
      have hnl : n - 1 - l = n - (l + 1) := by omega
      rw [hnl]
      rw [pow_succ']
      group

private theorem periodOne_list_ofFn_desc_inv_prod_eq
    {G : Type*} [Group G] {n : ℕ} (B : Fin n → G) :
    (List.ofFn (fun i : Fin n => (B ⟨n - 1 - i.val, by omega⟩)⁻¹)).prod =
      (List.ofFn B).prod⁻¹ := by
  by_cases hn : n = 0
  · subst n
    simp only [zero_tsub, List.ofFn_zero, List.prod_nil, inv_one]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hrev := list_ofFn_reverse_last_desc hpos B
    rw [List.prod_inv_reverse]
    rw [← List.map_reverse, hrev, List.map_cons, List.prod_cons, List.map_ofFn]
    have hlen : n = (n - 1) + 1 := by omega
    rw [List.ofFn_congr hlen]
    rw [List.ofFn_succ, List.prod_cons]
    congr 1
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    apply congrArg Inv.inv
    apply congrArg B
    ext
    simp only [Fin.val_cast, Fin.val_succ]
    omega

private theorem periodOne_list_ofFn_split_at
    {α : Type*} {p k : ℕ} (hk : k ≤ p) (f : Fin p → α) :
    List.ofFn f =
      List.ofFn (fun i : Fin k => f ⟨i.val, by omega⟩) ++
        List.ofFn (fun i : Fin (p - k) => f ⟨k + i.val, by omega⟩) := by
  let pref : Fin k → α := fun i => f ⟨i.val, by omega⟩
  let suff : Fin (p - k) → α := fun i => f ⟨k + i.val, by omega⟩
  have hlen : p = k + (p - k) := by omega
  rw [List.ofFn_congr hlen]
  rw [← List.ofFn_fin_append pref suff]
  congr
  funext i
  cases i using Fin.addCases with
  | left r =>
      dsimp [pref, suff]
      rw [Fin.append_left]
      apply congrArg f
      ext
      simp only [Fin.val_cast, Fin.val_castAdd]
  | right j =>
      dsimp [pref, suff]
      rw [Fin.append_right]
      apply congrArg f
      ext
      simp only [Fin.val_cast, Fin.val_natAdd]

private theorem periodOne_cyclic_rotated_inv_mem_normalClosure_of_list_prod
    {G : Type*} [Group G] {R : Set G} {p : ℕ}
    (block : Fin p → G) (k : Fin p)
    (hTotal : (List.ofFn block).prod ∈ Subgroup.normalClosure R) :
    ((List.ofFn (fun i : Fin (p - k.val) => block ⟨k.val + i.val, by omega⟩)).prod *
        (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod)⁻¹ ∈
      Subgroup.normalClosure R := by
  let N : Subgroup G := Subgroup.normalClosure R
  let pref : G := (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod
  let suff : G :=
    (List.ofFn (fun i : Fin (p - k.val) => block ⟨k.val + i.val, by omega⟩)).prod
  have hsplit : (List.ofFn block).prod = pref * suff := by
    rw [periodOne_list_ofFn_split_at (Nat.le_of_lt k.isLt) block]
    rw [List.prod_append]
  have hprefSuff : pref * suff ∈ N := by
    simpa [N, hsplit] using hTotal
  have hrot : suff * pref ∈ N := by
    simpa [N] using
      (ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := R) (a := pref) (b := suff) hprefSuff)
  exact N.inv_mem hrot

private theorem periodOne_cyclic_rotated_inv_pow_mem_normalClosure_of_head_mul_list_prod
    {G : Type*} [Group G] {R : Set G} {p : ℕ}
    (head : G) (block : Fin p → G) (k : Fin p) (m : ℕ)
    (hTotal : head * (List.ofFn block).prod ∈ Subgroup.normalClosure R)
    (hHeadPow : head ^ m ∈ Subgroup.normalClosure R) :
    (((List.ofFn (fun i : Fin (p - k.val) =>
          block ⟨k.val + i.val, by omega⟩)).prod *
        (List.ofFn (fun i : Fin k.val =>
          block ⟨i.val, by omega⟩)).prod)⁻¹) ^ m ∈
      Subgroup.normalClosure R := by
  let N : Subgroup G := Subgroup.normalClosure R
  let pref : G :=
    (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod
  let suff : G :=
    (List.ofFn (fun i : Fin (p - k.val) => block ⟨k.val + i.val, by omega⟩)).prod
  let full : G := (List.ofFn block).prod
  have hsplit : full = pref * suff := by
    dsimp [full, pref, suff]
    rw [periodOne_list_ofFn_split_at (Nat.le_of_lt k.isLt) block]
    rw [List.prod_append]
  have hfullInvHead :
      full⁻¹ * head⁻¹ ∈ N := by
    have hinv : (head * full)⁻¹ ∈ N := N.inv_mem hTotal
    simpa [N, mul_assoc] using hinv
  have hfullInvPow : full⁻¹ ^ m ∈ N :=
    ReidemeisterSchreier.Discrete.Presentations.pow_mem_normalClosure_of_mul_inv_mem
      (R := R) (u := full⁻¹) (v := head) (n := m) hfullInvHead hHeadPow
  have hrotEq : (suff * pref)⁻¹ = pref⁻¹ * full⁻¹ * pref := by
    rw [hsplit]
    group
  have hpowEq :
      (suff * pref)⁻¹ ^ m = pref⁻¹ * (full⁻¹ ^ m) * pref := by
    rw [hrotEq]
    have h :
        (pref⁻¹ * full⁻¹ * (pref⁻¹)⁻¹) ^ m =
          pref⁻¹ * (full⁻¹ ^ m) * (pref⁻¹)⁻¹ := by
      rw [conj_pow]
    simpa using h
  have hconj :
      pref⁻¹ * (full⁻¹ ^ m) * (pref⁻¹)⁻¹ ∈ N :=
    Subgroup.normalClosure_normal.conj_mem (full⁻¹ ^ m) hfullInvPow pref⁻¹
  have hrotPow : (suff * pref)⁻¹ ^ m ∈ N := by
    rw [hpowEq]
    simpa using hconj
  simpa [pref, suff] using hrotPow

private theorem periodOne_cyclic_desc_prevBlock_inv_product_eq_rotated_inv
    {G : Type*} [Group G] {p : ℕ} (hp : 2 ≤ p) (block : Fin p → G) (k : Fin p) :
    (List.ofFn (fun i : Fin k.val =>
          (block ⟨k.val - 1 - i.val, by omega⟩)⁻¹)).prod *
        (block ⟨p - 1, by omega⟩)⁻¹ *
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod =
      ((List.ofFn (fun i : Fin (p - k.val) =>
          block ⟨k.val + i.val, by omega⟩)).prod *
        (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod)⁻¹ := by
  let prefB : Fin k.val → G := fun i => block ⟨i.val, by omega⟩
  let suffB : Fin (p - k.val) → G := fun i => block ⟨k.val + i.val, by omega⟩
  have hLower :
      (List.ofFn (fun i : Fin k.val =>
          (block ⟨k.val - 1 - i.val, by omega⟩)⁻¹)).prod =
        (List.ofFn prefB).prod⁻¹ := by
    simpa [prefB] using periodOne_list_ofFn_desc_inv_prod_eq prefB
  have hSuffDesc :
      (List.ofFn (fun i : Fin (p - k.val) =>
          (suffB ⟨p - k.val - 1 - i.val, by omega⟩)⁻¹)).prod =
        (List.ofFn suffB).prod⁻¹ :=
    periodOne_list_ofFn_desc_inv_prod_eq suffB
  have hSuffSplit :
      (List.ofFn (fun i : Fin (p - k.val) =>
          (suffB ⟨p - k.val - 1 - i.val, by omega⟩)⁻¹)).prod =
        (block ⟨p - 1, by omega⟩)⁻¹ *
          (List.ofFn (fun i : Fin (p - 1 - k.val) =>
            (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    have hlen : p - k.val = (p - 1 - k.val) + 1 := by omega
    rw [List.ofFn_congr hlen]
    rw [List.ofFn_succ, List.prod_cons]
    congr 1
    · simp only [Fin.val_cast, Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero, inv_inj, suffB]
      apply congrArg block
      ext
      simp only
      omega
    · apply congrArg List.prod
      apply List.ofFn_inj.2
      funext i
      simp only [Fin.val_cast, Fin.val_succ, inv_inj, suffB]
      apply congrArg block
      ext
      simp only
      omega
  have hSuff :
      (block ⟨p - 1, by omega⟩)⁻¹ *
          (List.ofFn (fun i : Fin (p - 1 - k.val) =>
            (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod =
        (List.ofFn suffB).prod⁻¹ := by
    rw [← hSuffSplit]
    exact hSuffDesc
  rw [hLower]
  rw [mul_assoc]
  rw [hSuff]
  simp only [mul_inv_rev, prefB, suffB]

private theorem originalFirstReductionPeriodOneSecondShiftedCycle_eq_conjugate_secondPower
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let x : FuchsianGenerator source :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
    let edge : Fin p → φ.ker :=
      originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let lower :=
      (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
    let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
    let upper :=
      (List.ofFn (fun i : Fin (p - 1 - k.val) => edge ⟨p - 1 - i.val, by omega⟩)).prod
    lower * wrap * upper =
      (⟨(FreeGroup.of x) ^ k.val * (FreeGroup.of y) ^ p *
          ((FreeGroup.of x) ^ k.val)⁻¹, by
        rw [MonoidHom.mem_ker]
        have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
          simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
            originalFirstReductionPeriodOneFreeQuotientHom_head_zero
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
          simpa [φ, y] using
            originalFirstReductionPeriodOneFreeQuotientHom_head_one
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
        apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
        simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let upper :=
    (List.ofFn (fun i : Fin (p - 1 - k.val) => edge ⟨p - 1 - i.val, by omega⟩)).prod
  apply Subtype.ext
  change
    ((lower * wrap * upper : φ.ker) : FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
        (FreeGroup.of y) ^ p *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹
  have hlowerCoe :
      ((lower : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        (List.ofFn (fun i : Fin k.val =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (k.val - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^
              (k.val - 1 - i.val))⁻¹)).prod := by
    change
      φ.ker.subtype lower =
        (List.ofFn (fun i : Fin k.val =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (k.val - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^
              (k.val - 1 - i.val))⁻¹)).prod
    simp only [Subgroup.subtype_apply, Subgroup.val_list_prod, List.map_ofFn, lower, edge]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    haveI : Fact (1 < p) := ⟨by omega⟩
    have hrval :
        (((k.val - i.val : ℕ) : ZMod p) - 1).val = k.val - 1 - i.val := by
      have hrpos : 0 < k.val - i.val := by omega
      have hrlt : k.val - i.val < p := by omega
      have hval : ((k.val - i.val : ℕ) : ZMod p).val = k.val - i.val :=
        ZMod.val_natCast_of_lt hrlt
      have hle : (1 : ZMod p).val ≤ ((k.val - i.val : ℕ) : ZMod p).val := by
        rw [hval, ZMod.val_one]
        exact Nat.succ_le_iff.mpr hrpos
      rw [ZMod.val_sub hle, hval, ZMod.val_one]
      omega
    have hrvalZ :
        ((k.val : ZMod p) - (i.val : ZMod p) - 1).val = k.val - 1 - i.val := by
      have hkval : ((k.val : ℕ) : ZMod p).val = k.val :=
        ZMod.val_natCast_of_lt k.isLt
      have hilt : i.val < p := by omega
      have hival : ((i.val : ℕ) : ZMod p).val = i.val :=
        ZMod.val_natCast_of_lt hilt
      have hleki : ((i.val : ℕ) : ZMod p).val ≤ ((k.val : ℕ) : ZMod p).val := by
        rw [hkval, hival]
        omega
      have hsub :
          ((k.val : ZMod p) - (i.val : ZMod p)).val = k.val - i.val := by
        rw [ZMod.val_sub hleki, hkval, hival]
      have hrpos : 0 < k.val - i.val := by omega
      have hle :
          (1 : ZMod p).val ≤ ((k.val : ZMod p) - (i.val : ZMod p)).val := by
        rw [hsub, ZMod.val_one]
        exact Nat.succ_le_iff.mpr hrpos
      rw [ZMod.val_sub hle, hsub, ZMod.val_one]
      omega
    simpa [source, φ, x, y, edge, hrval, hrvalZ] using
      originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (⟨k.val - i.val, by omega⟩ : Fin p)
  have hwrapCoe :
      ((wrap : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹ := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    have hr0 : ((-1 : ZMod p).val) = p - 1 := by
      have hsucc : (p - 1).succ = p := by omega
      rw [← hsucc]
      exact ZMod.val_neg_one (p - 1)
    simpa [source, φ, x, y, edge, wrap, hr0] using
      originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : Fin p)
  have hupperCoe :
      ((upper : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1 - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^
              (p - 1 - 1 - i.val))⁻¹)).prod := by
    change
      φ.ker.subtype upper =
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1 - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^
              (p - 1 - 1 - i.val))⁻¹)).prod
    simp only [Subgroup.subtype_apply, Subgroup.val_list_prod, List.map_ofFn, upper, edge]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    haveI : Fact (1 < p) := ⟨by omega⟩
    have hrval :
        (((p - 1 - i.val : ℕ) : ZMod p) - 1).val = p - 1 - 1 - i.val := by
      have hrpos : 0 < p - 1 - i.val := by omega
      have hrlt : p - 1 - i.val < p := by omega
      have hval : ((p - 1 - i.val : ℕ) : ZMod p).val = p - 1 - i.val :=
        ZMod.val_natCast_of_lt hrlt
      have hle : (1 : ZMod p).val ≤ ((p - 1 - i.val : ℕ) : ZMod p).val := by
        rw [hval, ZMod.val_one]
        exact Nat.succ_le_iff.mpr hrpos
      rw [ZMod.val_sub hle, hval, ZMod.val_one]
      omega
    simpa [source, φ, x, y, edge, hrval] using
      originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (⟨p - 1 - i.val, by omega⟩ : Fin p)
  change
    ((lower : φ.ker) : FreeGroup (FuchsianGenerator source)) *
        ((wrap : φ.ker) : FreeGroup (FuchsianGenerator source)) *
        ((upper : φ.ker) : FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
        (FreeGroup.of y) ^ p *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹
  rw [hlowerCoe, hwrapCoe, hupperCoe]
  rw [periodOne_negOneCycleSegmentProduct_eq (FreeGroup.of x) (FreeGroup.of y)
    k.val k.val (by omega)]
  rw [periodOne_negOneCycleSegmentProduct_eq (FreeGroup.of x) (FreeGroup.of y)
    (p - 1) (p - 1 - k.val) (by omega)]
  have hkk : k.val - k.val = 0 := by omega
  have hlast : p - 1 - (p - 1 - k.val) = k.val := by omega
  rw [hkk, hlast]
  simp only [pow_zero, inv_one, mul_one]
  have hkadd : k.val + 1 + (p - 1 - k.val) = p := by omega
  calc
    (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          (FreeGroup.of y) ^ k.val *
          (FreeGroup.of y * ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
          (FreeGroup.of y) ^ (p - 1 - k.val) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)
        =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
        ((FreeGroup.of y) ^ k.val * FreeGroup.of y *
          (FreeGroup.of y) ^ (p - 1 - k.val)) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
        group
    _ =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
        (FreeGroup.of y) ^ p *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
        rw [← pow_succ (FreeGroup.of y) k.val]
        rw [← pow_add (FreeGroup.of y) (k.val + 1) (p - 1 - k.val)]
        rw [hkadd]

private theorem oneHeadPeriodOneSchreierToTargetHom_secondPowerWord
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
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let block := oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen
    η
        (basis.symm
          (originalFirstReductionPeriodOneSecondPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)) =
      (List.ofFn block).prod⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let b :=
    originalFirstReductionPeriodOneSecondPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let kZero : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let lower :=
    (List.ofFn (fun i : Fin kZero.val => edge ⟨kZero.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let upper :=
    (List.ofFn (fun i : Fin (p - 1 - kZero.val) =>
      edge ⟨p - 1 - i.val, by omega⟩)).prod
  let cycle : φ.ker := lower * wrap * upper
  let block := oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen
  have hcycleSource :
      cycle =
        (⟨(FreeGroup.of x) ^ kZero.val * (FreeGroup.of y) ^ p *
            ((FreeGroup.of x) ^ kZero.val)⁻¹, by
          rw [MonoidHom.mem_ker]
          have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
            simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
              originalFirstReductionPeriodOneFreeQuotientHom_head_zero
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
            simpa [φ, y] using
              originalFirstReductionPeriodOneFreeQuotientHom_head_one
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
          apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
          simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
    simpa [source, φ, x, y, edge, lower, wrap, upper, cycle] using
      originalFirstReductionPeriodOneSecondShiftedCycle_eq_conjugate_secondPower
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e kZero
  have hbCycle : b = cycle := by
    apply Subtype.ext
    change
      ((b : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator source))
    have hcycleCoe := congrArg
      (fun u : φ.ker => (u : FreeGroup (FuchsianGenerator source))) hcycleSource
    have hcycleCoe' :
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ kZero.val *
            (FreeGroup.of y) ^ p *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ kZero.val)⁻¹ := by
      simpa using hcycleCoe
    rw [hcycleCoe']
    rw [originalFirstReductionPeriodOneSecondPowerKernel_coe]
    simp only [Fin.isValue, pow_zero, one_mul, inv_one, mul_one, x, y, kZero]
  have hLowerImage :
      η (basis.symm lower) =
        (List.ofFn (fun i : Fin kZero.val =>
          (block ⟨kZero.val - 1 - i.val, by omega⟩)⁻¹)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let r : Fin p := ⟨kZero.val - i.val, by omega⟩
    have hrne : ¬ r.val = 0 := by
      dsimp [r]
      omega
    have hword :=
      oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e r
    have hprev : kZero.val - i.val - 1 = kZero.val - 1 - i.val := by omega
    simpa [source, basis, η, edge, block, r, oneHeadPeriodOneSecondEdgeForwardWord,
      hrne, hprev] using hword
  have hWrapImage :
      η (basis.symm wrap) = (block ⟨p - 1, by omega⟩)⁻¹ := by
    have hword :=
      oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
        (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : Fin p)
    simpa [source, basis, η, edge, wrap, block,
      oneHeadPeriodOneSecondEdgeForwardWord] using hword
  have hUpperImage :
      η (basis.symm upper) =
        (List.ofFn (fun i : Fin (p - 1 - kZero.val) =>
          (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let r : Fin p := ⟨p - 1 - i.val, by omega⟩
    have hrne : ¬ r.val = 0 := by
      dsimp [r]
      omega
    have hword :=
      oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e r
    have hprev : p - 1 - i.val - 1 = p - 2 - i.val := by omega
    simpa [source, basis, η, edge, block, r, oneHeadPeriodOneSecondEdgeForwardWord,
      hrne, hprev] using hword
  have hImageDesc :
      η (basis.symm cycle) =
        (List.ofFn (fun i : Fin kZero.val =>
            (block ⟨kZero.val - 1 - i.val, by omega⟩)⁻¹)).prod *
          (block ⟨p - 1, by omega⟩)⁻¹ *
          (List.ofFn (fun i : Fin (p - 1 - kZero.val) =>
            (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    have hmap :
        basis.symm cycle =
          basis.symm lower * basis.symm wrap * basis.symm upper := by
      simp only [mul_assoc, map_mul, cycle]
    rw [hmap, map_mul, map_mul, hLowerImage, hWrapImage, hUpperImage]
  have hDescEq :=
    periodOne_cyclic_desc_prevBlock_inv_product_eq_rotated_inv
      (G := FreeGroup (FuchsianGenerator target)) hp block kZero
  change η (basis.symm b) = (List.ofFn block).prod⁻¹
  rw [hbCycle, hImageDesc]
  have hrot :
      ((List.ofFn (fun i : Fin (p - kZero.val) =>
          block ⟨kZero.val + i.val, by omega⟩)).prod *
        (List.ofFn (fun i : Fin kZero.val => block ⟨i.val, by omega⟩)).prod)⁻¹ =
        (List.ofFn block).prod⁻¹ := by
    dsimp [kZero]
    simp only [zero_add, Fin.eta, List.ofFn_zero, List.prod_nil, mul_one]
  rw [hDescEq]
  exact hrot

theorem oneHeadPeriodOneSchreierToTarget_toInv_generators_mem_normalClosure
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
    let θ :=
      oneHeadPeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    ∀ y : FuchsianGenerator target,
      η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
        Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let block := oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen
  intro y
  cases y with
  | elliptic i =>
      let idx := (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p).symm i
      have hidx : oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p idx = i := by
        simp only [Equiv.apply_symm_apply, idx]
      cases hidxCases : idx with
      | inl a =>
          fin_cases a
          let headIdx :=
            oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inl (0 : Fin 1))
          have hidxHead : headIdx = i := by
            simpa [headIdx, idx, hidxCases] using hidx
          have hcomp :
              η (θ (FreeGroup.of (FuchsianGenerator.elliptic i))) =
                (List.ofFn block).prod⁻¹ := by
            simpa [θ, η, oneHeadPeriodOneTargetToSchreierHom,
              oneHeadPeriodOneTargetToSchreierGeneratorImage, target, basis,
              idx, hidxCases, block] using
              oneHeadPeriodOneSchreierToTargetHom_secondPowerWord
                m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
          have hHeadWord :
              xWord target headIdx =
                FreeGroup.of (FuchsianGenerator.elliptic i) := by
            simp only [xWord, hidxHead]
          let N : Subgroup (FreeGroup (FuchsianGenerator target)) :=
            Subgroup.normalClosure (relators target)
          have hTotalRel :
              totalRelation target ∈ N :=
            Subgroup.subset_normalClosure (Or.inr rfl)
          have hTotalBlocks :
              xWord target headIdx * (List.ofFn block).prod ∈ N := by
            simpa [N, target, headIdx, block,
              oneHeadPeriodOneTarget_totalRelation_eq_blocks] using hTotalRel
          have hmem :
              (List.ofFn block).prod⁻¹ *
                  (xWord target headIdx)⁻¹ ∈ N := by
            have hinv : (xWord target headIdx * (List.ofFn block).prod)⁻¹ ∈ N :=
              N.inv_mem hTotalBlocks
            simpa [N, mul_assoc] using hinv
          have hprod :
              η (θ (FreeGroup.of (FuchsianGenerator.elliptic i))) *
                  (FreeGroup.of (FuchsianGenerator.elliptic i))⁻¹ =
                (List.ofFn block).prod⁻¹ * (xWord target headIdx)⁻¹ := by
            rw [hcomp, hHeadWord]
          simpa [N] using hprod ▸ hmem
      | inr jk =>
          have hword :
              η
                  ((originalFirstReductionPeriodOneSchreierBasisEquiv
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).symm
                    (originalFirstReductionPeriodOneTailKernelElement
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e jk.2 jk.1)) =
                xWord target
                  (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (jk.1, jk.2))) := by
            simpa [source, target, η] using
              oneHeadPeriodOneSchreierToTargetHom_tailWord
                m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e jk.2 jk.1
          have hidxPair :
              oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (jk.1, jk.2)) = i := by
            simpa [idx, hidxCases] using hidx
          have hword' :
              η
                  ((originalFirstReductionPeriodOneSchreierBasisEquiv
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).symm
                    (originalFirstReductionPeriodOneTailKernelElement
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e jk.2 jk.1)) =
                FreeGroup.of (FuchsianGenerator.elliptic i) := by
            simpa [xWord, hidxPair] using hword
          have hcomp :
              η (θ (FreeGroup.of (FuchsianGenerator.elliptic i))) =
                FreeGroup.of (FuchsianGenerator.elliptic i) := by
            simpa [θ, η, oneHeadPeriodOneTargetToSchreierHom,
              oneHeadPeriodOneTargetToSchreierGeneratorImage, target, basis,
              idx, hidxCases] using hword'
          have hprod :
              η (θ (FreeGroup.of (FuchsianGenerator.elliptic i))) *
                  (FreeGroup.of (FuchsianGenerator.elliptic i))⁻¹ =
                1 := by
            simp only [Lean.Elab.WF.paramLet, hcomp, mul_inv_cancel]
          rw [hprod]
          exact Subgroup.one_mem (Subgroup.normalClosure (relators target))
  | surfaceA a =>
      fin_cases a
  | surfaceB b =>
      fin_cases b

theorem oneHeadPeriodOneSchreierToTarget_toInv_mem_normalClosure_of_generators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hgen :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
      letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
      let θ :=
        oneHeadPeriodOneTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
      let η :=
        oneHeadPeriodOneSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
      ∀ y : FuchsianGenerator target,
        η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators target)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let θ :=
      oneHeadPeriodOneTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    ∀ y : FreeGroup (FuchsianGenerator target),
      η (θ y) * y⁻¹ ∈ Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let θ :=
    oneHeadPeriodOneTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let F : FreeGroup (FuchsianGenerator target) →* FreeGroup (FuchsianGenerator target) :=
    η.comp θ
  have hgen' :
      ∀ y : FuchsianGenerator target,
        F (FreeGroup.of y) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators target) := by
    intro y
    simpa [source, target, θ, η, F] using hgen y
  intro y
  simpa [F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv
      (relators target) F hgen' y

private theorem originalFirstReductionPeriodOneSecondEdgeKernelElement_zero_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let x : FuchsianGenerator source :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
    ((originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : Fin p) : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
      FreeGroup.of y *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hr0 : ((-1 : ZMod p).val) = p - 1 := by
    have hsucc : (p - 1).succ = p := by omega
    rw [← hsucc]
    exact ZMod.val_neg_one (p - 1)
  simpa [source, φ, x, y, hr0] using
    originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
      (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : Fin p)

private theorem originalFirstReductionPeriodOneSecondEdgeKernelElement_succ_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (i : Fin (p - 1)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let x : FuchsianGenerator source :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
    ((originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (⟨i.val + 1, by omega⟩ : Fin p) : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (i.val + 1) *
        FreeGroup.of y *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ i.val)⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hrval : ((((i.val + 1 : ℕ) : ZMod p) - 1).val) = i.val := by
    have hrlt : i.val + 1 < p := by omega
    have hval : ((i.val + 1 : ℕ) : ZMod p).val = i.val + 1 :=
      ZMod.val_natCast_of_lt hrlt
    have hle : (1 : ZMod p).val ≤ ((i.val + 1 : ℕ) : ZMod p).val := by
      rw [hval, ZMod.val_one]
      omega
    rw [ZMod.val_sub hle, hval, ZMod.val_one]
    omega
  have hmod : i.val % p = i.val := Nat.mod_eq_of_lt (by omega)
  simpa [source, φ, x, y, hrval, hmod] using
    originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
      (⟨i.val + 1, by omega⟩ : Fin p)

private theorem oneHeadPeriodOneSchreierToTargetHom_tailBlockWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (hm₂'ge : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    η
        ((List.ofFn (fun j : Fin tailLen =>
          basis.symm
            (originalFirstReductionPeriodOneTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k))).prod) =
      oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen k := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  rw [map_list_prod, List.map_ofFn]
  change
    (List.ofFn (fun j : Fin tailLen =>
      η
        (basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)))).prod =
      (List.ofFn (fun j : Fin tailLen =>
        xWord target
          (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))))).prod
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext j
  simpa [source, target, basis, η] using
    oneHeadPeriodOneSchreierToTargetHom_tailWord
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e j k

private theorem oneHeadPeriodOneSchreierToTarget_firstPower_sourceCase_mem_normalClosure
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
    (hm₁'one : m₁' = 1)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let i₀ := e (.inl (0 : Fin 2))
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord source i₀) ^ source.periods i₀) = 1 := by
              simpa [source, φ, i₀, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  ((xWord source i₀) ^ source.periods i₀) (Or.inl ⟨i₀, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let i₀ := e (.inl (0 : Fin 2))
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ :
          φ ((xWord source i₀) ^ source.periods i₀) = 1 := by
        simpa [source, φ, i₀, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            ((xWord source i₀) ^ source.periods i₀) (Or.inl ⟨i₀, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hPeriod : source.periods i₀ = p := by
    rw [show i₀ = e (.inl (0 : Fin 2)) by rfl]
    rw [hperiods (.inl (0 : Fin 2))]
    simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, hm₁'one, mul_one, Fin.isValue,
  Fin.cases_zero]
  have hz : z = a := by
    apply Subtype.ext
    have hxEq : x = FuchsianGenerator.elliptic i₀ := by
      simp only [Lean.Elab.WF.paramLet, originalFirstReductionPeriodOneDistinguishedGenerator, Fin.isValue, id_eq,
  x, i₀]
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          ((xWord source i₀) ^ source.periods i₀) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
        ((a : φ.ker) : FreeGroup (FuchsianGenerator source))
    rw [originalFirstReductionPeriodOneFirstPowerKernel_coe]
    rw [hxEq]
    simp only [xWord, hPeriod]
    let g : FreeGroup (FuchsianGenerator source) :=
      FreeGroup.of (FuchsianGenerator.elliptic i₀)
    change g ^ k.val * g ^ p * (g ^ k.val)⁻¹ = g ^ p
    have hcomm : Commute (g ^ k.val) (g ^ p) :=
      (Commute.refl g).pow_pow k.val p
    calc
      g ^ k.val * g ^ p * (g ^ k.val)⁻¹ =
          (g ^ p * g ^ k.val) * (g ^ k.val)⁻¹ := by
            rw [hcomm.eq]
      _ = g ^ p := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  rw [hz]
  rw [oneHeadPeriodOneSchreierToTargetHom_firstPowerWord]
  exact Subgroup.one_mem (Subgroup.normalClosure (relators target))

private theorem oneHeadPeriodOneSchreierToTarget_tailPower_sourceCase_mem_normalClosure
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
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let iTail := e (.inr j)
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord source iTail) ^ source.periods iTail) = 1 := by
              simpa [source, φ, iTail, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  ((xWord source iTail) ^ source.periods iTail) (Or.inl ⟨iTail, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let iTail := e (.inr j)
  let c :=
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ :
          φ ((xWord source iTail) ^ source.periods iTail) = 1 := by
        simpa [source, φ, iTail, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            ((xWord source iTail) ^ source.periods iTail) (Or.inl ⟨iTail, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hPeriod : source.periods iTail = tail j := by
    rw [show iTail = e (.inr j) by rfl]
    rw [hperiods (.inr j)]
    simp only [originalFirstReductionPeriods]
  have hz : z = c ^ tail j := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          ((xWord source iTail) ^ source.periods iTail) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
        ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator source))
    rw [show ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        ((c : φ.ker) : FreeGroup (FuchsianGenerator source)) ^ tail j by
          exact (map_pow (φ.ker.subtype) c (tail j))]
    rw [originalFirstReductionPeriodOneTailKernelElement_coe]
    simp only [xWord, hPeriod, conj_pow, x, iTail]
  have hTargetPeriod :
      target.periods (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))) =
        tail j := by
    simp only [oneHeadPeriodOneTargetSignature, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, oneHeadPeriodOneTargetPeriods,
  Equiv.trans_apply, Sum.map_inr, finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd,
  Equiv.symm_apply_apply, target]
  have hTargetRel :
      xWord target (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))) ^
          tail j ∈
        Subgroup.normalClosure (relators target) := by
    have hrel :
        xWord target (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))) ^
            target.periods (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j))) ∈
          relators target :=
      Or.inl ⟨oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inr (k, j)), rfl⟩
    simpa [hTargetPeriod] using Subgroup.subset_normalClosure hrel
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  rw [hz]
  rw [map_pow (basis.symm) c (tail j), map_pow]
  rw [oneHeadPeriodOneSchreierToTargetHom_tailWord]
  exact hTargetRel

private theorem oneHeadPeriodOneSchreierToTarget_secondPower_sourceCase_mem_normalClosure
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
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let i₁ := e (.inl (1 : Fin 2))
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord source i₁) ^ source.periods i₁) = 1 := by
              simpa [source, φ, i₁, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  ((xWord source i₁) ^ source.periods i₁) (Or.inl ⟨i₁, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let i₁ := e (.inl (1 : Fin 2))
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic i₁
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let upper :=
    (List.ofFn (fun i : Fin (p - 1 - k.val) => edge ⟨p - 1 - i.val, by omega⟩)).prod
  let cycle : φ.ker := lower * wrap * upper
  let block := oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ :
          φ ((xWord source i₁) ^ source.periods i₁) = 1 := by
        simpa [source, φ, i₁, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            ((xWord source i₁) ^ source.periods i₁) (Or.inl ⟨i₁, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hPeriod : source.periods i₁ = p * m₂' := by
    rw [show i₁ = e (.inl (1 : Fin 2)) by rfl]
    rw [hperiods (.inl (1 : Fin 2))]
    simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, Fin.isValue, fin_cases_const_one]
  have hcycleSource :
      cycle =
        (⟨(FreeGroup.of x) ^ k.val * (FreeGroup.of y) ^ p *
            ((FreeGroup.of x) ^ k.val)⁻¹, by
          rw [MonoidHom.mem_ker]
          have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
            simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
              originalFirstReductionPeriodOneFreeQuotientHom_head_zero
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
            simpa [φ, y, i₁] using
              originalFirstReductionPeriodOneFreeQuotientHom_head_one
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
          apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
          simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
    simpa [source, φ, x, y, edge, lower, wrap, upper, cycle] using
      originalFirstReductionPeriodOneSecondShiftedCycle_eq_conjugate_secondPower
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
  have hz : z = cycle ^ m₂' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          ((xWord source i₁) ^ source.periods i₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
        ((cycle ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator source))
    rw [show ((cycle ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator source)) ^ m₂' by
          exact (map_pow (φ.ker.subtype) cycle m₂')]
    have hcycleCoe := congrArg
      (fun u : φ.ker => (u : FreeGroup (FuchsianGenerator source))) hcycleSource
    have hcycleCoe' :
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            (FreeGroup.of y) ^ p *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
      simpa using hcycleCoe
    rw [hcycleCoe']
    simp only [xWord, Fin.isValue, hPeriod, conj_pow, mul_left_inj, mul_right_inj, x, i₁, y]
    rw [pow_mul]
  have hLowerImage :
      η (basis.symm lower) =
        (List.ofFn (fun i : Fin k.val =>
          (block ⟨k.val - 1 - i.val, by omega⟩)⁻¹)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let r : Fin p := ⟨k.val - i.val, by omega⟩
    have hrne : ¬ r.val = 0 := by
      dsimp [r]
      omega
    have hword :=
      oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e r
    have hprev : k.val - i.val - 1 = k.val - 1 - i.val := by omega
    simpa [source, basis, η, edge, block, r, oneHeadPeriodOneSecondEdgeForwardWord,
      hrne, hprev] using hword
  have hWrapImage :
      η (basis.symm wrap) = (block ⟨p - 1, by omega⟩)⁻¹ := by
    have hword :=
      oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
        (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : Fin p)
    simpa [source, basis, η, edge, wrap, block, oneHeadPeriodOneSecondEdgeForwardWord] using
      hword
  have hUpperImage :
      η (basis.symm upper) =
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let r : Fin p := ⟨p - 1 - i.val, by omega⟩
    have hrne : ¬ r.val = 0 := by
      dsimp [r]
      omega
    have hword :=
      oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e r
    have hprev : p - 1 - i.val - 1 = p - 2 - i.val := by omega
    simpa [source, basis, η, edge, block, r, oneHeadPeriodOneSecondEdgeForwardWord,
      hrne, hprev] using hword
  have hImageDesc :
      η (basis.symm cycle) =
        (List.ofFn (fun i : Fin k.val =>
            (block ⟨k.val - 1 - i.val, by omega⟩)⁻¹)).prod *
          (block ⟨p - 1, by omega⟩)⁻¹ *
          (List.ofFn (fun i : Fin (p - 1 - k.val) =>
            (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    have hmap :
        basis.symm cycle =
          basis.symm lower * basis.symm wrap * basis.symm upper := by
      simp only [mul_assoc, map_mul, cycle]
    rw [hmap, map_mul, map_mul, hLowerImage, hWrapImage, hUpperImage]
  have hDescEq :=
    periodOne_cyclic_desc_prevBlock_inv_product_eq_rotated_inv
      (G := FreeGroup (FuchsianGenerator target)) hp block k
  let headIdx :=
    oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (.inl (0 : Fin 1))
  let headWord : FreeGroup (FuchsianGenerator target) := xWord target headIdx
  let N : Subgroup (FreeGroup (FuchsianGenerator target)) :=
    Subgroup.normalClosure (relators target)
  have hHeadPeriod : target.periods headIdx = m₂' := by
    simp only [oneHeadPeriodOneTargetSignature, oneHeadPeriodOneTargetOrderedIndexEquiv, Equiv.symm_trans_apply,
  Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl, oneHeadPeriodOneTargetPeriods,
  Fin.isValue, Equiv.trans_apply, Sum.map_inl, id_eq, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd,
  headIdx, target]
  have hHeadPow : headWord ^ m₂' ∈ N := by
    have hrel : headWord ^ target.periods headIdx ∈ relators target :=
      Or.inl ⟨headIdx, rfl⟩
    simpa [N, headWord, hHeadPeriod] using Subgroup.subset_normalClosure hrel
  have hTotalBlocks : headWord * (List.ofFn block).prod ∈ N := by
    have hTotalRel : totalRelation target ∈ N :=
      Subgroup.subset_normalClosure (Or.inr rfl)
    simpa [N, target, headWord, headIdx, block,
      oneHeadPeriodOneTarget_totalRelation_eq_blocks] using hTotalRel
  have hRotInvPow :
      (((List.ofFn (fun i : Fin (p - k.val) =>
            block ⟨k.val + i.val, by omega⟩)).prod *
          (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod)⁻¹) ^ m₂' ∈ N :=
    periodOne_cyclic_rotated_inv_pow_mem_normalClosure_of_head_mul_list_prod
      (R := relators target) headWord block k m₂' hTotalBlocks hHeadPow
  have hCycleImage :
      η (basis.symm cycle) =
        ((List.ofFn (fun i : Fin (p - k.val) =>
            block ⟨k.val + i.val, by omega⟩)).prod *
          (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod)⁻¹ := by
    rw [hImageDesc, hDescEq]
  have hCyclePowMem : η (basis.symm cycle) ^ m₂' ∈ N := by
    rw [hCycleImage]
    exact hRotInvPow
  change η (basis.symm z) ∈ N
  rw [hz]
  rw [map_pow (basis.symm) cycle m₂', map_pow]
  exact hCyclePowMem

private theorem oneHeadPeriodOneSchreierToTarget_total_sourceCase_mem_normalClosure
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
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * totalRelation source *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * totalRelation source *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ : φ (totalRelation source) = 1 := by
              simpa [source, φ, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  (totalRelation source) (Or.inr rfl)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let block := oneHeadPeriodOneTargetTailBlockWord m₂' tail hp hm₂'ge htail hTailLen
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * totalRelation source *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * totalRelation source *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ (totalRelation source) = 1 := by
        simpa [source, φ, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            (totalRelation source) (Or.inr rfl)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hTailEq :
      totalRelation source =
        FreeGroup.of x * FreeGroup.of y *
          (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod := by
    subst e
    have hTotal :=
      originalFirstReduction_source_totalRelation_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    simpa [source, x, y, tailGen, xWord,
      originalFirstReductionPeriodOneDistinguishedGenerator,
      originalFirstReductionOrderedIndexEquiv] using hTotal
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  by_cases hlast : k.val = p - 1
  · let kLast : Fin p := ⟨p - 1, by omega⟩
    let kZero : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
    have hprodCoe :
        (((List.ofFn (fun j : Fin tailLen => c j kLast)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
          (List.ofFn (fun j : Fin tailLen =>
            ((c j kLast : φ.ker) : FreeGroup (FuchsianGenerator source)))).prod := by
      change
        φ.ker.subtype ((List.ofFn (fun j : Fin tailLen => c j kLast)).prod) =
          (List.ofFn (fun j : Fin tailLen => φ.ker.subtype (c j kLast))).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    have htailList :
        (List.ofFn (fun j : Fin tailLen =>
          ((c j kLast : φ.ker) : FreeGroup (FuchsianGenerator source)))) =
          List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹) := by
      apply List.ofFn_inj.2
      funext j
      simpa [source, φ, x, tailGen, c, kLast] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j kLast
    have htailConj :
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹)).prod =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹ := by
      calc
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹)).prod =
            (List.map
              (fun u =>
                (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
                  u *
                  ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹)
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).prod := by
              rw [List.map_ofFn]
              rfl
        _ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹ := by
              rw [← ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))]
    have hkerEq :
        z = a * edge kZero * (List.ofFn (fun j : Fin tailLen => c j kLast)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            totalRelation source *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          ((a : φ.ker) : FreeGroup (FuchsianGenerator source)) *
            ((edge kZero : φ.ker) : FreeGroup (FuchsianGenerator source)) *
            (((List.ofFn (fun j : Fin tailLen => c j kLast)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator source))
      rw [hprodCoe, htailList, htailConj]
      rw [originalFirstReductionPeriodOneFirstPowerKernel_coe]
      rw [originalFirstReductionPeriodOneSecondEdgeKernelElement_zero_coe]
      rw [hTailEq]
      rw [hlast]
      simp only [x, y, tailGen, mul_assoc]
      rw [← mul_assoc]
      rw [← pow_succ]
      have hsuccNat : p - 1 + 1 = p := by omega
      rw [hsuccNat]
      group
    have htailMap :
        basis.symm ((List.ofFn (fun j : Fin tailLen => c j kLast)).prod) =
          (List.ofFn (fun j : Fin tailLen => basis.symm (c j kLast))).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    have hmap :
        basis.symm (a * edge kZero * (List.ofFn (fun j : Fin tailLen => c j kLast)).prod) =
          basis.symm a * basis.symm (edge kZero) *
            (List.ofFn (fun j : Fin tailLen => basis.symm (c j kLast))).prod := by
      rw [map_mul, map_mul, htailMap]
    let tailWord :=
      (List.ofFn (fun j : Fin tailLen => basis.symm (c j kLast))).prod
    let firstWord := basis.symm a
    let secondWord := basis.symm (edge kZero)
    have hFirstImg : η firstWord = 1 := by
      simpa [source, target, basis, η, a, firstWord] using
        oneHeadPeriodOneSchreierToTargetHom_firstPowerWord
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    have hSecondImg : η secondWord = (block kLast)⁻¹ := by
      have hword :=
        oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e kZero
      simpa [source, target, basis, η, edge, secondWord, block, kZero, kLast,
        oneHeadPeriodOneSecondEdgeForwardWord] using hword
    have hTailImg : η tailWord = block kLast := by
      simpa [source, target, basis, η, c, tailWord, block] using
        oneHeadPeriodOneSchreierToTargetHom_tailBlockWord
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e kLast
    rw [hkerEq, hmap]
    rw [map_mul, map_mul]
    change η firstWord * η secondWord * η tailWord ∈
      Subgroup.normalClosure (relators target)
    rw [hFirstImg, hSecondImg, hTailImg]
    simp only [one_mul, inv_mul_cancel, one_mem]
  · let knw : Fin (p - 1) := ⟨k.val, by omega⟩
    let k0 : Fin p := ⟨knw.val, by omega⟩
    let k1 : Fin p := ⟨knw.val + 1, by omega⟩
    have hprodCoe :
        (((List.ofFn (fun j : Fin tailLen => c j k0)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
          (List.ofFn (fun j : Fin tailLen =>
            ((c j k0 : φ.ker) : FreeGroup (FuchsianGenerator source)))).prod := by
      change
        φ.ker.subtype ((List.ofFn (fun j : Fin tailLen => c j k0)).prod) =
          (List.ofFn (fun j : Fin tailLen => φ.ker.subtype (c j k0))).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    have htailList :
        (List.ofFn (fun j : Fin tailLen =>
          ((c j k0 : φ.ker) : FreeGroup (FuchsianGenerator source)))) =
          List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹) := by
      apply List.ofFn_inj.2
      funext j
      simpa [source, φ, x, tailGen, c, k0, knw] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k0
    have htailConj :
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)).prod =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
      calc
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)).prod =
            (List.map
              (fun u =>
                (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
                  u * ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).prod := by
              rw [List.map_ofFn]
              rfl
        _ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
              rw [← ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))]
    have hkerEq :
        z = edge k1 * (List.ofFn (fun j : Fin tailLen => c j k0)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            totalRelation source *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          ((edge k1 : φ.ker) : FreeGroup (FuchsianGenerator source)) *
            (((List.ofFn (fun j : Fin tailLen => c j k0)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator source))
      rw [hprodCoe, htailList, htailConj]
      rw [originalFirstReductionPeriodOneSecondEdgeKernelElement_succ_coe]
      rw [hTailEq]
      simp only [x, y, tailGen, mul_assoc]
      simp only [Fin.isValue, inv_mul_cancel_left, knw]
      rw [← mul_assoc, ← pow_succ]
    have hmap :
        basis.symm (edge k1 * (List.ofFn (fun j : Fin tailLen => c j k0)).prod) =
        basis.symm (edge k1) *
            (List.ofFn (fun j : Fin tailLen => basis.symm (c j k0))).prod := by
      rw [map_mul, map_list_prod, List.map_ofFn]
      rfl
    let tailWord :=
      (List.ofFn (fun j : Fin tailLen => basis.symm (c j k0))).prod
    let secondWord := basis.symm (edge k1)
    have hSecondImg : η secondWord = (block k0)⁻¹ := by
      have hword :=
        oneHeadPeriodOneSchreierToTargetHom_secondEdgeWord
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e k1
      have hne : ¬ k1.val = 0 := by
        dsimp [k1, knw]
        omega
      have hprev : k1.val - 1 = k0.val := by
        dsimp [k1, k0, knw]
      simpa [source, target, basis, η, edge, secondWord, block, k0, k1,
        oneHeadPeriodOneSecondEdgeForwardWord, hne, hprev] using hword
    have hTailImg : η tailWord = block k0 := by
      simpa [source, target, basis, η, c, tailWord, block] using
        oneHeadPeriodOneSchreierToTargetHom_tailBlockWord
          m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e k0
    rw [hkerEq, hmap]
    rw [map_mul]
    change η secondWord * η tailWord ∈ Subgroup.normalClosure (relators target)
    rw [hSecondImg, hTailImg]
    simp only [inv_mul_cancel, one_mem]

theorem oneHeadPeriodOneSchreierToTarget_mapsRelators
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
    let η :=
      oneHeadPeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
    ∀ r ∈
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T),
      η r ∈ Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂'ge htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
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
  let η :=
    oneHeadPeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [source, φ, x, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hrels :=
    originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  intro r hr
  have hrImage :
      basis r ∈ ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := f) (rels := relators source) T := by
    simpa [basis] using
      (ReidemeisterSchreier.Discrete.Presentations.mem_freeGroupPullbackRelatorSet_iff (e := basis)
        (S := ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := f) (rels := relators source) T)
        (y := r)).1 hr
  rcases hrImage with ⟨t, ht, r₀, hr₀, hval⟩
  have htPower : ∃ k : Fin p, t = (FreeGroup.of x) ^ k.val := by
    simpa [T] using
      (mem_range_cyclicQuotientRightRep_iff_generatorPower φ (x := x) hx).1 ht
  rcases htPower with ⟨k, rfl⟩
  let tPow : FreeGroup (FuchsianGenerator source) := (FreeGroup.of x) ^ k.val
  have relator_eq :
      r =
        basis.symm
          (⟨tPow * r₀ * tPow⁻¹, by
            change φ (tPow * r₀ * tPow⁻¹) = 1
            have hrφ : φ r₀ = 1 := hrels r₀ hr₀
            simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) := by
    let zRel : φ.ker :=
      ⟨tPow * r₀ * tPow⁻¹, by
        change φ (tPow * r₀ * tPow⁻¹) = 1
        have hrφ : φ r₀ = 1 := hrels r₀ hr₀
        simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
    have hz : basis r = zRel := by
      apply Subtype.ext
      simpa [tPow, zRel] using hval
    calc
      r = basis.symm (basis r) := by simp only [MulEquiv.symm_apply_apply]
      _ = basis.symm zRel := by rw [hz]
  rcases hr₀ with ⟨i, rfl⟩ | rfl
  · let idx : OriginalFirstReductionIndex tailLen := e.symm i
    have hi : i = e idx := by
      symm
      simp only [Equiv.apply_symm_apply, idx]
    cases hidx : idx with
    | inl a =>
        fin_cases a
        · rw [relator_eq]
          simpa [source, target, φ, basis, η, x, tPow, hi, hidx] using
            oneHeadPeriodOneSchreierToTarget_firstPower_sourceCase_mem_normalClosure
              m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods
              hm₁'one k
        · rw [relator_eq]
          simpa [source, target, φ, basis, η, x, tPow, hi, hidx] using
            oneHeadPeriodOneSchreierToTarget_secondPower_sourceCase_mem_normalClosure
              m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods k
    | inr j =>
        rw [relator_eq]
        simpa [source, target, φ, basis, η, x, tPow, hi, hidx] using
          oneHeadPeriodOneSchreierToTarget_tailPower_sourceCase_mem_normalClosure
            m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods j k
  · rw [relator_eq]
    simpa [source, target, φ, basis, η, x, tPow] using
      oneHeadPeriodOneSchreierToTarget_total_sourceCase_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' hm₂'ge htail hTailLen e hperiods he k

private theorem doublePeriodOneSchreierToTarget_firstPower_sourceCase_mem_normalClosure
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
    (hm₁'one : m₁' = 1)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let i₀ := e (.inl (0 : Fin 2))
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord source i₀) ^ source.periods i₀) = 1 := by
              simpa [source, φ, i₀, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  ((xWord source i₀) ^ source.periods i₀) (Or.inl ⟨i₀, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let i₀ := e (.inl (0 : Fin 2))
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord source i₀) ^ source.periods i₀) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ :
          φ ((xWord source i₀) ^ source.periods i₀) = 1 := by
        simpa [source, φ, i₀, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            ((xWord source i₀) ^ source.periods i₀) (Or.inl ⟨i₀, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hPeriod : source.periods i₀ = p := by
    rw [show i₀ = e (.inl (0 : Fin 2)) by rfl]
    rw [hperiods (.inl (0 : Fin 2))]
    simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, hm₁'one, mul_one, Fin.isValue,
  Fin.cases_zero]
  have hz : z = a := by
    apply Subtype.ext
    have hxEq : x = FuchsianGenerator.elliptic i₀ := by
      simp only [Lean.Elab.WF.paramLet, originalFirstReductionPeriodOneDistinguishedGenerator, Fin.isValue, id_eq,
  x, i₀]
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          ((xWord source i₀) ^ source.periods i₀) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
        ((a : φ.ker) : FreeGroup (FuchsianGenerator source))
    rw [originalFirstReductionPeriodOneFirstPowerKernel_coe]
    rw [hxEq]
    simp only [xWord, hPeriod]
    let g : FreeGroup (FuchsianGenerator source) :=
      FreeGroup.of (FuchsianGenerator.elliptic i₀)
    change g ^ k.val * g ^ p * (g ^ k.val)⁻¹ = g ^ p
    have hcomm : Commute (g ^ k.val) (g ^ p) :=
      (Commute.refl g).pow_pow k.val p
    calc
      g ^ k.val * g ^ p * (g ^ k.val)⁻¹ =
          (g ^ p * g ^ k.val) * (g ^ k.val)⁻¹ := by
            rw [hcomm.eq]
      _ = g ^ p := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  rw [hz]
  rw [doublePeriodOneSchreierToTargetHom_firstPowerWord]
  exact Subgroup.one_mem (Subgroup.normalClosure (relators target))

private theorem doublePeriodOneSchreierToTarget_secondPower_sourceCase_mem_normalClosure
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
    (hm₂'one : m₂' = 1)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let i₁ := e (.inl (1 : Fin 2))
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord source i₁) ^ source.periods i₁) = 1 := by
              simpa [source, φ, i₁, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  ((xWord source i₁) ^ source.periods i₁) (Or.inl ⟨i₁, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let i₁ := e (.inl (1 : Fin 2))
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic i₁
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let upper :=
    (List.ofFn (fun i : Fin (p - 1 - k.val) => edge ⟨p - 1 - i.val, by omega⟩)).prod
  let cycle : φ.ker := lower * wrap * upper
  let block := doublePeriodOneTargetTailBlockWord tail htail hHigh
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord source i₁) ^ source.periods i₁) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ :
          φ ((xWord source i₁) ^ source.periods i₁) = 1 := by
        simpa [source, φ, i₁, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            ((xWord source i₁) ^ source.periods i₁) (Or.inl ⟨i₁, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hPeriod : source.periods i₁ = p := by
    rw [show i₁ = e (.inl (1 : Fin 2)) by rfl]
    rw [hperiods (.inl (1 : Fin 2))]
    simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, hm₂'one, mul_one, Fin.isValue,
  fin_cases_const_one]
  have hcycleSource :
      cycle =
        (⟨(FreeGroup.of x) ^ k.val * (FreeGroup.of y) ^ p *
            ((FreeGroup.of x) ^ k.val)⁻¹, by
          rw [MonoidHom.mem_ker]
          have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
            simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
              originalFirstReductionPeriodOneFreeQuotientHom_head_zero
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
            simpa [φ, y, i₁] using
              originalFirstReductionPeriodOneFreeQuotientHom_head_one
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
          rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
          apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
          simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
    simpa [source, φ, x, y, edge, lower, wrap, upper, cycle] using
      originalFirstReductionPeriodOneSecondShiftedCycle_eq_conjugate_secondPower
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k
  have hz : z = cycle := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          ((xWord source i₁) ^ source.periods i₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator source))
    have hcycleCoe := congrArg
      (fun u : φ.ker => (u : FreeGroup (FuchsianGenerator source))) hcycleSource
    have hcycleCoe' :
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator source)) =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            (FreeGroup.of y) ^ p *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
      simpa using hcycleCoe
    rw [hcycleCoe']
    simp only [xWord, Fin.isValue, hPeriod, x, i₁, y]
  have hLowerImage :
      η (basis.symm lower) =
        (List.ofFn (fun i : Fin k.val =>
          (block ⟨k.val - 1 - i.val, by omega⟩)⁻¹)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let r : Fin p := ⟨k.val - i.val, by omega⟩
    have hrne : ¬ r.val = 0 := by
      dsimp [r]
      omega
    have hword :=
      doublePeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e r
    have hprev : k.val - i.val - 1 = k.val - 1 - i.val := by omega
    simpa [source, basis, η, edge, block, r, doublePeriodOneSecondEdgeForwardWord,
      hrne, hprev] using hword
  have hWrapImage :
      η (basis.symm wrap) = (block ⟨p - 1, by omega⟩)⁻¹ := by
    have hword :=
      doublePeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
        (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : Fin p)
    simpa [source, basis, η, edge, wrap, block, doublePeriodOneSecondEdgeForwardWord] using
      hword
  have hUpperImage :
      η (basis.symm upper) =
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let r : Fin p := ⟨p - 1 - i.val, by omega⟩
    have hrne : ¬ r.val = 0 := by
      dsimp [r]
      omega
    have hword :=
      doublePeriodOneSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e r
    have hprev : p - 1 - i.val - 1 = p - 2 - i.val := by omega
    simpa [source, basis, η, edge, block, r, doublePeriodOneSecondEdgeForwardWord,
      hrne, hprev] using hword
  have hImageDesc :
      η (basis.symm cycle) =
        (List.ofFn (fun i : Fin k.val =>
            (block ⟨k.val - 1 - i.val, by omega⟩)⁻¹)).prod *
          (block ⟨p - 1, by omega⟩)⁻¹ *
          (List.ofFn (fun i : Fin (p - 1 - k.val) =>
            (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
    have hmap :
        basis.symm cycle =
          basis.symm lower * basis.symm wrap * basis.symm upper := by
      simp only [mul_assoc, map_mul, cycle]
    rw [hmap, map_mul, map_mul, hLowerImage, hWrapImage, hUpperImage]
  have hTotalBlocks :
      (List.ofFn (fun k : Fin p => block k)).prod ∈
        Subgroup.normalClosure (relators target) := by
    have hTotalRel :
        totalRelation target ∈ Subgroup.normalClosure (relators target) :=
      Subgroup.subset_normalClosure (Or.inr rfl)
    simpa [target, block, doublePeriodOneTargetTailBlockWord,
      doublePeriodOneTarget_totalRelation_eq_blocks] using hTotalRel
  have hRotInv :
      ((List.ofFn (fun i : Fin (p - k.val) =>
          block ⟨k.val + i.val, by omega⟩)).prod *
        (List.ofFn (fun i : Fin k.val => block ⟨i.val, by omega⟩)).prod)⁻¹ ∈
        Subgroup.normalClosure (relators target) :=
    periodOne_cyclic_rotated_inv_mem_normalClosure_of_list_prod
      (R := relators target) block k hTotalBlocks
  have hDescEq :=
    periodOne_cyclic_desc_prevBlock_inv_product_eq_rotated_inv
      (G := FreeGroup (FuchsianGenerator target)) hp block k
  have hCycleMem :
      η (basis.symm cycle) ∈ Subgroup.normalClosure (relators target) := by
    rw [hImageDesc, hDescEq]
    exact hRotInv
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  rw [hz]
  exact hCycleMem

private theorem doublePeriodOneSchreierToTarget_tailPower_sourceCase_mem_normalClosure
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
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let iTail := e (.inr j)
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord source iTail) ^ source.periods iTail) = 1 := by
              simpa [source, φ, iTail, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  ((xWord source iTail) ^ source.periods iTail) (Or.inl ⟨iTail, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let iTail := e (.inr j)
  let c :=
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord source iTail) ^ source.periods iTail) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ :
          φ ((xWord source iTail) ^ source.periods iTail) = 1 := by
        simpa [source, φ, iTail, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            ((xWord source iTail) ^ source.periods iTail) (Or.inl ⟨iTail, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hPeriod : source.periods iTail = tail j := by
    rw [show iTail = e (.inr j) by rfl]
    rw [hperiods (.inr j)]
    simp only [originalFirstReductionPeriods]
  have hz : z = c ^ tail j := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
          ((xWord source iTail) ^ source.periods iTail) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
        ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator source))
    rw [show ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator source)) =
        ((c : φ.ker) : FreeGroup (FuchsianGenerator source)) ^ tail j by
          exact (map_pow (φ.ker.subtype) c (tail j))]
    rw [originalFirstReductionPeriodOneTailKernelElement_coe]
    simp only [xWord, hPeriod, conj_pow, x, iTail]
  have hIndexPair :
      ((finProdFinEquiv (k, j)).divNat, (finProdFinEquiv (k, j)).modNat) = (k, j) := by
    have h := finProdFinEquiv.symm_apply_apply (k, j)
    rw [finProdFinEquiv_symm_apply] at h
    exact h
  have hIndexSnd : (finProdFinEquiv (k, j)).modNat = j :=
    congrArg Prod.snd hIndexPair
  have hTargetPeriod :
      target.periods (finProdFinEquiv (k, j)) = tail j := by
    simp only [doublePeriodOneTailReplicatedSignature, finProdFinEquiv_symm_apply, hIndexSnd, target]
  have hTargetRel :
      xWord target (finProdFinEquiv (k, j)) ^ tail j ∈
        Subgroup.normalClosure (relators target) := by
    have hrel :
        xWord target (finProdFinEquiv (k, j)) ^
            target.periods (finProdFinEquiv (k, j)) ∈ relators target :=
      Or.inl ⟨finProdFinEquiv (k, j), rfl⟩
    simpa [hTargetPeriod] using Subgroup.subset_normalClosure hrel
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  rw [hz]
  rw [map_pow (basis.symm) c (tail j), map_pow]
  rw [doublePeriodOneSchreierToTargetHom_tailWord]
  exact hTargetRel

private theorem doublePeriodOneSchreierToTargetHom_tailBlockWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hHigh : 3 ≤ p * tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    η
        ((List.ofFn (fun j : Fin tailLen =>
          basis.symm
            (originalFirstReductionPeriodOneTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k))).prod) =
      doublePeriodOneTargetTailBlockWord tail htail hHigh k := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  rw [map_list_prod, List.map_ofFn]
  change
    (List.ofFn (fun j : Fin tailLen =>
      η
        (basis.symm
          (originalFirstReductionPeriodOneTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k)))).prod =
      (List.ofFn (fun j : Fin tailLen =>
        xWord target (finProdFinEquiv (k, j)))).prod
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext j
  simpa [source, target, basis, η] using
    doublePeriodOneSchreierToTargetHom_tailWord
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e j k

private theorem doublePeriodOneSchreierToTarget_total_sourceCase_mem_normalClosure
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
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let basis :=
      originalFirstReductionPeriodOneSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    let x :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    η
        (basis.symm
          (⟨(FreeGroup.of x) ^ k.val * totalRelation source *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * totalRelation source *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ : φ (totalRelation source) = 1 := by
              simpa [source, φ, originalFirstReductionPeriodOneFreeQuotientHom] using
                originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
                  (totalRelation source) (Or.inr rfl)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  let block := doublePeriodOneTargetTailBlockWord tail htail hHigh
  let a :=
    originalFirstReductionPeriodOneFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let edge : Fin p → φ.ker :=
    originalFirstReductionPeriodOneSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    originalFirstReductionPeriodOneTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * totalRelation source *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * totalRelation source *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ (totalRelation source) = 1 := by
        simpa [source, φ, originalFirstReductionPeriodOneFreeQuotientHom] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
            (totalRelation source) (Or.inr rfl)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hTailEq :
      totalRelation source =
        FreeGroup.of x * FreeGroup.of y *
          (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod := by
    subst e
    have hTotal :=
      originalFirstReduction_source_totalRelation_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    simpa [source, x, y, tailGen, xWord,
      originalFirstReductionPeriodOneDistinguishedGenerator,
      originalFirstReductionOrderedIndexEquiv] using hTotal
  change η (basis.symm z) ∈ Subgroup.normalClosure (relators target)
  by_cases hlast : k.val = p - 1
  · let kLast : Fin p := ⟨p - 1, by omega⟩
    let kZero : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
    have hprodCoe :
        (((List.ofFn (fun j : Fin tailLen => c j kLast)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
          (List.ofFn (fun j : Fin tailLen =>
            ((c j kLast : φ.ker) : FreeGroup (FuchsianGenerator source)))).prod := by
      change
        φ.ker.subtype ((List.ofFn (fun j : Fin tailLen => c j kLast)).prod) =
          (List.ofFn (fun j : Fin tailLen => φ.ker.subtype (c j kLast))).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    have htailList :
        (List.ofFn (fun j : Fin tailLen =>
          ((c j kLast : φ.ker) : FreeGroup (FuchsianGenerator source)))) =
          List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹) := by
      apply List.ofFn_inj.2
      funext j
      simpa [source, φ, x, tailGen, c, kLast] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j kLast
    have htailConj :
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹)).prod =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹ := by
      calc
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹)).prod =
            (List.map
              (fun u =>
                (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
                  u *
                  ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹)
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).prod := by
              rw [List.map_ofFn]
              rfl
        _ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1) *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))⁻¹ := by
              rw [← ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ (p - 1))
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))]
    have hkerEq :
        z = a * edge kZero * (List.ofFn (fun j : Fin tailLen => c j kLast)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            totalRelation source *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          ((a : φ.ker) : FreeGroup (FuchsianGenerator source)) *
            ((edge kZero : φ.ker) : FreeGroup (FuchsianGenerator source)) *
            (((List.ofFn (fun j : Fin tailLen => c j kLast)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator source))
      rw [hprodCoe, htailList, htailConj]
      rw [originalFirstReductionPeriodOneFirstPowerKernel_coe]
      rw [originalFirstReductionPeriodOneSecondEdgeKernelElement_zero_coe]
      rw [hTailEq]
      rw [hlast]
      simp only [x, y, tailGen, mul_assoc]
      rw [← mul_assoc]
      rw [← pow_succ]
      have hsuccNat : p - 1 + 1 = p := by omega
      rw [hsuccNat]
      group
    have htailMap :
        basis.symm ((List.ofFn (fun j : Fin tailLen => c j kLast)).prod) =
          (List.ofFn (fun j : Fin tailLen => basis.symm (c j kLast))).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    have hmap :
        basis.symm (a * edge kZero * (List.ofFn (fun j : Fin tailLen => c j kLast)).prod) =
          basis.symm a * basis.symm (edge kZero) *
            (List.ofFn (fun j : Fin tailLen => basis.symm (c j kLast))).prod := by
      rw [map_mul, map_mul, htailMap]
    let tailWord :=
      (List.ofFn (fun j : Fin tailLen => basis.symm (c j kLast))).prod
    let firstWord := basis.symm a
    let secondWord := basis.symm (edge kZero)
    have hFirstImg : η firstWord = 1 := by
      simpa [source, target, basis, η, a, firstWord] using
        doublePeriodOneSchreierToTargetHom_firstPowerWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    have hSecondImg : η secondWord = (block kLast)⁻¹ := by
      have hword :=
        doublePeriodOneSchreierToTargetHom_secondEdgeWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e kZero
      simpa [source, target, basis, η, edge, secondWord, block, kZero, kLast,
        doublePeriodOneSecondEdgeForwardWord] using hword
    have hTailImg : η tailWord = block kLast := by
      simpa [source, target, basis, η, c, tailWord, block] using
        doublePeriodOneSchreierToTargetHom_tailBlockWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e kLast
    rw [hkerEq, hmap]
    rw [map_mul, map_mul]
    change η firstWord * η secondWord * η tailWord ∈
      Subgroup.normalClosure (relators target)
    rw [hFirstImg, hSecondImg, hTailImg]
    simp only [one_mul, inv_mul_cancel, one_mem]
  · let knw : Fin (p - 1) := ⟨k.val, by omega⟩
    let k0 : Fin p := ⟨knw.val, by omega⟩
    let k1 : Fin p := ⟨knw.val + 1, by omega⟩
    have hprodCoe :
        (((List.ofFn (fun j : Fin tailLen => c j k0)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
          (List.ofFn (fun j : Fin tailLen =>
            ((c j k0 : φ.ker) : FreeGroup (FuchsianGenerator source)))).prod := by
      change
        φ.ker.subtype ((List.ofFn (fun j : Fin tailLen => c j k0)).prod) =
          (List.ofFn (fun j : Fin tailLen => φ.ker.subtype (c j k0))).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    have htailList :
        (List.ofFn (fun j : Fin tailLen =>
          ((c j k0 : φ.ker) : FreeGroup (FuchsianGenerator source)))) =
          List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹) := by
      apply List.ofFn_inj.2
      funext j
      simpa [source, φ, x, tailGen, c, k0, knw] using
        originalFirstReductionPeriodOneTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k0
    have htailConj :
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)).prod =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
      calc
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
              FreeGroup.of (tailGen j) *
              ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)).prod =
            (List.map
              (fun u =>
                (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
                  u * ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹)
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).prod := by
              rw [List.map_ofFn]
              rfl
        _ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ := by
              rw [← ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))]
    have hkerEq :
        z = edge k1 * (List.ofFn (fun j : Fin tailLen => c j k0)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val *
            totalRelation source *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k.val)⁻¹ =
          ((edge k1 : φ.ker) : FreeGroup (FuchsianGenerator source)) *
            (((List.ofFn (fun j : Fin tailLen => c j k0)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator source))
      rw [hprodCoe, htailList, htailConj]
      rw [originalFirstReductionPeriodOneSecondEdgeKernelElement_succ_coe]
      rw [hTailEq]
      simp only [x, y, tailGen, mul_assoc]
      simp only [Fin.isValue, inv_mul_cancel_left, knw]
      rw [← mul_assoc, ← pow_succ]
    have hmap :
        basis.symm (edge k1 * (List.ofFn (fun j : Fin tailLen => c j k0)).prod) =
        basis.symm (edge k1) *
            (List.ofFn (fun j : Fin tailLen => basis.symm (c j k0))).prod := by
      rw [map_mul, map_list_prod, List.map_ofFn]
      rfl
    let tailWord :=
      (List.ofFn (fun j : Fin tailLen => basis.symm (c j k0))).prod
    let secondWord := basis.symm (edge k1)
    have hSecondImg : η secondWord = (block k0)⁻¹ := by
      have hword :=
        doublePeriodOneSchreierToTargetHom_secondEdgeWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e k1
      have hne : ¬ k1.val = 0 := by
        dsimp [k1, knw]
        omega
      have hprev : k1.val - 1 = k0.val := by
        dsimp [k1, k0, knw]
      simpa [source, target, basis, η, edge, secondWord, block, k0, k1,
        doublePeriodOneSecondEdgeForwardWord, hne, hprev] using hword
    have hTailImg : η tailWord = block k0 := by
      simpa [source, target, basis, η, c, tailWord, block] using
        doublePeriodOneSchreierToTargetHom_tailBlockWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e k0
    rw [hkerEq, hmap]
    rw [map_mul]
    change η secondWord * η tailWord ∈ Subgroup.normalClosure (relators target)
    rw [hSecondImg, hTailImg]
    simp only [inv_mul_cancel, one_mem]

theorem doublePeriodOneSchreierToTarget_mapsRelators
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
    let η :=
      doublePeriodOneSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
    ∀ r ∈
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet basis
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := relators source) T),
      η r ∈ Subgroup.normalClosure (relators target) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
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
  let η :=
    doublePeriodOneSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e
  let x :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [source, φ, x, originalFirstReductionPeriodOneFreeQuotientHom] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let hrels :=
    originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods
  intro r hr
  have hrImage :
      basis r ∈ ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := f) (rels := relators source) T := by
    simpa [basis] using
      (ReidemeisterSchreier.Discrete.Presentations.mem_freeGroupPullbackRelatorSet_iff (e := basis)
        (S := ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := f) (rels := relators source) T)
        (y := r)).1 hr
  rcases hrImage with ⟨t, ht, r₀, hr₀, hval⟩
  have htPower : ∃ k : Fin p, t = (FreeGroup.of x) ^ k.val := by
    simpa [T] using
      (mem_range_cyclicQuotientRightRep_iff_generatorPower φ (x := x) hx).1 ht
  rcases htPower with ⟨k, rfl⟩
  let tPow : FreeGroup (FuchsianGenerator source) := (FreeGroup.of x) ^ k.val
  have relator_eq :
      r =
        basis.symm
          (⟨tPow * r₀ * tPow⁻¹, by
            change φ (tPow * r₀ * tPow⁻¹) = 1
            have hrφ : φ r₀ = 1 := hrels r₀ hr₀
            simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) := by
    let zRel : φ.ker :=
      ⟨tPow * r₀ * tPow⁻¹, by
        change φ (tPow * r₀ * tPow⁻¹) = 1
        have hrφ : φ r₀ = 1 := hrels r₀ hr₀
        simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
    have hz : basis r = zRel := by
      apply Subtype.ext
      simpa [tPow, zRel] using hval
    calc
      r = basis.symm (basis r) := by simp only [MulEquiv.symm_apply_apply]
      _ = basis.symm zRel := by rw [hz]
  rcases hr₀ with ⟨i, rfl⟩ | rfl
  · let idx : OriginalFirstReductionIndex tailLen := e.symm i
    have hi : i = e idx := by
      symm
      simp only [Equiv.apply_symm_apply, idx]
    cases hidx : idx with
    | inl a =>
        fin_cases a
        · rw [relator_eq]
          simpa [source, target, φ, basis, η, x, tPow, hi, hidx] using
            doublePeriodOneSchreierToTarget_firstPower_sourceCase_mem_normalClosure
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods
              hm₁'one k
        · rw [relator_eq]
          simpa [source, target, φ, basis, η, x, tPow, hi, hidx] using
            doublePeriodOneSchreierToTarget_secondPower_sourceCase_mem_normalClosure
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods
              hm₂'one k
    | inr j =>
        rw [relator_eq]
        simpa [source, target, φ, basis, η, x, tPow, hi, hidx] using
          doublePeriodOneSchreierToTarget_tailPower_sourceCase_mem_normalClosure
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods j k
  · rw [relator_eq]
    simpa [source, target, φ, basis, η, x, tPow] using
      doublePeriodOneSchreierToTarget_total_sourceCase_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hHigh e hperiods he k

end FenchelNielsen
