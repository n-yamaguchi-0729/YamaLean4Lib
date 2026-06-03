import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceCore

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/Relators/SourceMiddleTail.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen

theorem secondReductionToTransportSecondBranch_tail_sourceCase_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
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
    let iTail :=
      secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ iTail) ^ σ.periods iTail) = 1 :=
              secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ((xWord σ iTail) ^ σ.periods iTail) (Or.inl ⟨iTail, rfl⟩)
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
  let iTail :=
    secondReductionCanonicalSourceTailIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j
  let zTail :=
    secondReductionCanonicalTailZeroKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ iTail) ^ σ.periods iTail) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ((xWord σ iTail) ^ σ.periods iTail) (Or.inl ⟨iTail, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = zTail ^ tail j := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ iTail) ^ σ.periods iTail) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((zTail ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((zTail ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((zTail : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ tail j by
          exact (map_pow (φ.ker.subtype) zTail (tail j))]
    have hperiod : σ.periods iTail = tail j := by
      simp only [secondReductionCanonicalSourceSignature_period_tail, σ, iTail]
    simp only [secondReductionCanonicalDistinguishedGenerator, xWord, hperiod,
  secondReductionCanonicalTailZeroKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalZeroImageKernelElement, id_eq, conj_pow, σ, x, iTail, zTail]
  have hmain : (η (e.symm zTail)) ^ tail j ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    have hword :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom_tailWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
    have hrel :
        (secondReductionCanonicalTransportTargetWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
            (secondReductionCanonicalTransportTailIndex tailLen p q b j k)) ^
          tail j ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have hmem :
          (xWord τ
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportTailIndex tailLen p q b j k))) ^
            τ.periods
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportTailIndex tailLen p q b j k)) ∈
            secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail :=
        secondReductionCanonicalTransport_powerRelator_mem_blockRelators
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail _
      simpa [τ, secondReductionCanonicalTransportTargetWord,
        secondReductionTransportSignature, familyFuchsianSignature_periods,
        secondReductionTransportPeriods, singermanTransportPeriodsFamily,
        secondReductionSourceTransportPeriods, secondReductionSourceCycleCount] using
        Subgroup.subset_normalClosure hmem
    simpa [σ, e, η, zTail, hword] using hrel
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hz, map_pow]
  simpa [zTail] using hmain
theorem secondReductionToTransportSecondBranch_middleRest_sourceCase_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (r : Fin (p - 2)) (k : Fin q) :
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
    let rSource : Fin p := ⟨2 + r.val, by omega⟩
    let iMiddle :=
      secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail rSource
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ iMiddle) ^ σ.periods iMiddle) = 1 :=
              secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ((xWord σ iMiddle) ^ σ.periods iMiddle) (Or.inl ⟨iMiddle, rfl⟩)
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
  let rSource : Fin p := ⟨2 + r.val, by omega⟩
  let iMiddle :=
    secondReductionCanonicalSourceMiddleIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail rSource
  let zMiddle :=
    secondReductionCanonicalMiddleRestZeroKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ iMiddle) ^ σ.periods iMiddle) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ((xWord σ iMiddle) ^ σ.periods iMiddle) (Or.inl ⟨iMiddle, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = zMiddle ^ (q * m₃') := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ iMiddle) ^ σ.periods iMiddle) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((zMiddle ^ (q * m₃') : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((zMiddle ^ (q * m₃') : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((zMiddle : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ (q * m₃') by
          exact (map_pow (φ.ker.subtype) zMiddle (q * m₃'))]
    have hperiod : σ.periods iMiddle = q * m₃' := by
      simp only [secondReductionCanonicalSourceSignature_period_middle, σ, iMiddle, rSource]
    simp only [secondReductionCanonicalDistinguishedGenerator, xWord, hperiod,
  secondReductionCanonicalMiddleRestZeroKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalZeroImageKernelElement, id_eq, conj_pow, σ, x, iMiddle, rSource, zMiddle]
  have hmain : (η (e.symm zMiddle)) ^ (q * m₃') ∈
      Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    have hword :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom_middleRestWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
    have hrel :
        (secondReductionCanonicalTransportTargetWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
            (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k)) ^
          (q * m₃') ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have hmem :
          (xWord τ
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))) ^
            τ.periods
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k)) ∈
            secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail :=
        secondReductionCanonicalTransport_powerRelator_mem_blockRelators
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail _
      simpa [τ, secondReductionCanonicalTransportTargetWord,
        secondReductionTransportSignature, familyFuchsianSignature_periods,
        secondReductionTransportPeriods, singermanTransportPeriodsFamily,
        secondReductionSourceTransportPeriods, secondReductionSourceCycleCount] using
        Subgroup.subset_normalClosure hmem
    simpa [σ, e, η, zMiddle, hword] using hrel
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hz, map_pow]
  simpa [zMiddle] using hmain
theorem secondReductionToTransportSecondBranch_posMiddle_sourceCase_mem_normalClosure
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
    let iMiddle :=
      secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ iMiddle) ^ σ.periods iMiddle) = 1 :=
              secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ((xWord σ iMiddle) ^ σ.periods iMiddle) (Or.inl ⟨iMiddle, rfl⟩)
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
  let iMiddle :=
    secondReductionCanonicalSourceMiddleIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩
  let zFirst :=
    secondReductionCanonicalFirstPowerKernel
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ iMiddle) ^ σ.periods iMiddle) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ((xWord σ iMiddle) ^ σ.periods iMiddle) (Or.inl ⟨iMiddle, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = zFirst ^ m₃' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ iMiddle) ^ σ.periods iMiddle) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((zFirst ^ m₃' : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((zFirst ^ m₃' : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((zFirst : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ m₃' by
          exact (map_pow (φ.ker.subtype) zFirst m₃')]
    have hperiod : σ.periods iMiddle = q * m₃' := by
      simp only [secondReductionCanonicalSourceSignature_period_middle, σ, iMiddle]
    rw [secondReductionCanonicalFirstPowerKernel_coe]
    rw [hperiod]
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, xWord, pow_mul, σ, x, iMiddle]
    group
  have hmain : (η (e.symm zFirst)) ^ m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    have hword :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom_firstPowerWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    have hrel :
        (secondReductionCanonicalTransportTargetWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
            (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)) ^
          m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have hmem :
          (xWord τ
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))) ^
            τ.periods
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
                (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)) ∈
            secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail :=
        secondReductionCanonicalTransport_powerRelator_mem_blockRelators
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail _
      simpa [τ, secondReductionCanonicalTransportTargetWord,
        secondReductionTransportSignature, familyFuchsianSignature_periods,
        secondReductionTransportPeriods, singermanTransportPeriodsFamily,
        secondReductionSourceTransportPeriods, secondReductionSourceCycleCount] using
        Subgroup.subset_normalClosure hmem
    simpa [σ, e, η, zFirst, hword] using hrel
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hz, map_pow]
  simpa [zFirst] using hmain
def SecondReductionCanonicalSecondBranchNegativeMiddleSourceCase
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) : Prop :=
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
  let iMiddle :=
    secondReductionCanonicalSourceMiddleIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩
  ∀ k : Fin q,
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ iMiddle) ^ σ.periods iMiddle) = 1 :=
              secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ((xWord σ iMiddle) ^ σ.periods iMiddle) (Or.inl ⟨iMiddle, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
theorem secondReductionCanonicalSecondBranchNegativeMiddleSourceCase_mem_blockRelators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    SecondReductionCanonicalSecondBranchNegativeMiddleSourceCase
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
  classical
  dsimp [SecondReductionCanonicalSecondBranchNegativeMiddleSourceCase]
  intro k
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let iMiddle :=
    secondReductionCanonicalSourceMiddleIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩
  let y : FuchsianGenerator σ := FuchsianGenerator.elliptic iMiddle
  let edge : Fin q → φ.ker :=
    secondReductionCanonicalSecondEdgeKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
  let upper :=
    (List.ofFn (fun i : Fin (q - 1 - k.val) => edge ⟨q - 1 - i.val, by omega⟩)).prod
  let cycle := lower * wrap * upper
  let base :=
    secondReductionCanonicalSecondPowerKernel
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ iMiddle) ^ σ.periods iMiddle) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ iMiddle) ^ σ.periods iMiddle) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ((xWord σ iMiddle) ^ σ.periods iMiddle) (Or.inl ⟨iMiddle, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hcycleSource :
      cycle =
        (⟨(FreeGroup.of x) ^ k.val * (FreeGroup.of y) ^ q *
            ((FreeGroup.of x) ^ k.val)⁻¹, by
          rw [MonoidHom.mem_ker]
          have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
            simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
          have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
            simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y, iMiddle]
          rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
          apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
          simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
    simpa [σ, φ, x, y, iMiddle, edge, lower, wrap, upper, cycle] using
      secondReductionCanonicalSecondShiftedCycle_eq_conjugate_secondPower
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  have hz : z = cycle ^ m₃' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ iMiddle) ^ σ.periods iMiddle) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((cycle ^ m₃' : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((cycle ^ m₃' : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ m₃' by
          exact (map_pow (φ.ker.subtype) cycle m₃')]
    have hcycleCoe :=
      congrArg (fun u : φ.ker => (u : FreeGroup (FuchsianGenerator σ))) hcycleSource
    have hcycleCoe' :
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            (FreeGroup.of y) ^ q *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ := by
      simpa using hcycleCoe
    rw [hcycleCoe']
    have hperiod : σ.periods iMiddle = q * m₃' := by
      simp only [secondReductionCanonicalSourceSignature_period_middle, σ, iMiddle]
    rw [hperiod]
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, xWord, Nat.reduceAdd, pow_mul, conj_pow, σ, x, iMiddle, y]
  have hbasePower : (η (e.symm base)) ^ m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    let idxB := secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩
    let B :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idxB)
    have hTheta : θ B = e.symm base := by
      simpa [σ, τ, e, θ, idxB, B, base] using
        secondReductionCanonicalTransportToSchreierHom_negativeDistinguished
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    have hmod :
        η (e.symm base) * B⁻¹ ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have htoInv :=
        secondReductionToTransportSecondBranch_toInv_negDist_mem_blockRelators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      change η (θ B) * B⁻¹ ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) at htoInv
      rw [hTheta] at htoInv
      simpa using htoInv
    have hBrel : B ^ m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
      have hmem :
          (xWord τ
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idxB)) ^
            τ.periods
              ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idxB) ∈
            secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail :=
        secondReductionCanonicalTransport_powerRelator_mem_blockRelators
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail _
      simpa [τ, B, idxB, secondReductionTransportSignature,
        familyFuchsianSignature_periods, secondReductionTransportPeriods,
        singermanTransportPeriodsFamily, secondReductionSourceTransportPeriods,
        secondReductionSourceCycleCount] using Subgroup.subset_normalClosure hmem
    exact
      ReidemeisterSchreier.Discrete.Presentations.pow_mem_normalClosure_of_mul_inv_mem
        (R := secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
        (u := η (e.symm base)) (v := B) hmod hBrel
  have htailSplit :
      (List.ofFn (fun i : Fin (q - 1) => edge ⟨q - 1 - i.val, by omega⟩)).prod =
        upper * lower := by
    have hlist := secondReduction_list_ofFn_desc_split (p := q) (k := k.val) k.isLt edge
    simpa [upper, lower] using congrArg List.prod hlist
  have hbaseEq : base = (wrap * upper) * lower := by
    have hdesc :
        wrap *
            (List.ofFn (fun i : Fin (q - 1) =>
              edge ⟨q - 1 - i.val, by omega⟩)).prod =
          base := by
      simpa [σ, φ, edge, wrap, base] using
        secondReductionCanonicalSecondDescendingCycle_eq_secondPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    rw [htailSplit] at hdesc
    calc
      base = wrap * (upper * lower) := hdesc.symm
      _ = (wrap * upper) * lower := by group
  let a := η (e.symm (wrap * upper))
  let b := η (e.symm lower)
  have hbaseAB : (a * b) ^ m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    rw [hbaseEq] at hbasePower
    simpa [a, b, map_mul, mul_assoc] using hbasePower
  have hrot :
      (b * a) ^ m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) :=
    ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_pow_mem_normalClosure
      (R := secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
      (a := a) (b := b) hbaseAB
  have hcycleTarget :
      (η (e.symm cycle)) ^ m₃' ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    have hcycleImage : η (e.symm cycle) = b * a := by
      simp only [Lean.Elab.WF.paramLet, mul_assoc, map_mul, cycle, b, a]
    simpa [hcycleImage] using hrot
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hz, map_pow]
  simpa [cycle] using hcycleTarget

end FenchelNielsen
