import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceCore

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/Relators/SourceHead.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen

theorem secondReductionToTransportSecondBranch_headZero_sourceCase_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let i₀ :=
      secondReductionCanonicalSourceZeroIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ i₀) ^ σ.periods i₀) = 1 :=
              secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ((xWord σ i₀) ^ σ.periods i₀) (Or.inl ⟨i₀, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let i₀ :=
    secondReductionCanonicalSourceZeroIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let zHead :=
    secondReductionCanonicalHeadZeroKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ i₀) ^ σ.periods i₀) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ((xWord σ i₀) ^ σ.periods i₀) (Or.inl ⟨i₀, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = zHead ^ m₁' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ i₀) ^ σ.periods i₀) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((zHead ^ m₁' : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((zHead ^ m₁' : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((zHead : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ m₁' by
          exact (map_pow (φ.ker.subtype) zHead m₁')]
    simp only [secondReductionCanonicalSourceSignature, secondReductionCanonicalDistinguishedGenerator, xWord,
  secondReductionCanonicalSourceZeroIndex, Fin.mk_zero', secondReductionCanonicalSourcePeriod, Fin.coe_ofNat_eq_mod,
  Nat.zero_mod, ↓reduceDIte, secondReductionCanonicalHeadZeroKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalZeroImageKernelElement, id_eq, conj_pow, x, i₀, zHead, σ]
  have hmain : (η (e.symm zHead)) ^ m₁' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    have hword :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom_headZeroWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
    have hrel :
        (secondReductionCanonicalTransportTargetWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
            (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k)) ^
          m₁' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have hmem :
          (xWord τ
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k))) ^
            τ.periods
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k)) ∈
            secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail :=
        secondReductionCanonicalTransport_powerRelator_mem_blockRelators
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail _
      simpa [τ, secondReductionCanonicalTransportTargetWord,
        secondReductionTransportSignature, familyFuchsianSignature_periods,
        secondReductionTransportPeriods, singermanTransportPeriodsFamily,
        secondReductionSourceTransportPeriods, secondReductionSourceCycleCount, twoPeriods] using
        Subgroup.subset_normalClosure hmem
    simpa [σ, e, η, zHead, hword] using hrel
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hz, map_pow]
  simpa [zHead] using hmain
theorem secondReductionToTransportSecondBranch_headOne_sourceCase_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let i₁ :=
      secondReductionCanonicalSourceOneIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ i₁) ^ σ.periods i₁) = 1 :=
              secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ((xWord σ i₁) ^ σ.periods i₁) (Or.inl ⟨i₁, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let i₁ :=
    secondReductionCanonicalSourceOneIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let zHead :=
    secondReductionCanonicalHeadOneKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ i₁) ^ σ.periods i₁) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ((xWord σ i₁) ^ σ.periods i₁) (Or.inl ⟨i₁, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = zHead ^ m₂' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ i₁) ^ σ.periods i₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((zHead ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((zHead ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((zHead : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ m₂' by
          exact (map_pow (φ.ker.subtype) zHead m₂')]
    simp only [secondReductionCanonicalSourceSignature, secondReductionCanonicalDistinguishedGenerator, xWord,
  secondReductionCanonicalSourceOneIndex, secondReductionCanonicalSourcePeriod, one_ne_zero, ↓reduceDIte,
  secondReductionCanonicalHeadOneKernelElement, Lean.Elab.WF.paramLet, secondReductionCanonicalZeroImageKernelElement,
  id_eq, conj_pow, x, i₁, zHead, σ]
  have hmain : (η (e.symm zHead)) ^ m₂' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    have hword :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom_headOneWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
    have hrel :
        (secondReductionCanonicalTransportTargetWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
            (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k)) ^
          m₂' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have hmem :
          (xWord τ
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k))) ^
            τ.periods
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k)) ∈
            secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail :=
        secondReductionCanonicalTransport_powerRelator_mem_blockRelators
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail _
      simpa [τ, secondReductionCanonicalTransportTargetWord,
        secondReductionTransportSignature, familyFuchsianSignature_periods,
        secondReductionTransportPeriods, singermanTransportPeriodsFamily,
        secondReductionSourceTransportPeriods, secondReductionSourceCycleCount, twoPeriods] using
        Subgroup.subset_normalClosure hmem
    simpa [σ, e, η, zHead, hword] using hrel
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hz, map_pow]
  simpa [zHead] using hmain

end FenchelNielsen
