import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.QuotientAndBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/TransportMaps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen
noncomputable def secondReductionCanonicalTransportToSchreierGenerator
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    SecondReductionTransportIndex tailLen p q → FreeGroup ↥(schreierGeneratorSet hT) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let distinguishedPos : φ.ker := ⟨(FreeGroup.of x) ^ q, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
  let distinguishedNeg : φ.ker := ⟨(FreeGroup.of y) ^ q, by
    have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y]
    rw [MonoidHom.mem_ker, map_pow, hy]
    apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
    simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
  let zeroConjugateKernel :
      (i : Fin σ.numPeriods) →
        φ (xWord σ i) = 1 → Fin q → φ.ker := fun i hi k =>
    ⟨(FreeGroup.of x) ^ k.val * xWord σ i * ((FreeGroup.of x) ^ k.val)⁻¹, by
      change
        φ ((FreeGroup.of x) ^ k.val * xWord σ i *
          ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hx, hi, mul_one, map_inv, mul_inv_cancel]⟩
  intro idx
  rcases idx with ⟨src, k⟩
  cases src with
  | inl head =>
      by_cases h0 : head.val = 0
      · let i :=
          secondReductionCanonicalSourceZeroIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        exact e.symm (zeroConjugateKernel i (by
          simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, i]) k)
      · have h1 : head.val = 1 := by omega
        let i :=
          secondReductionCanonicalSourceOneIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        exact e.symm (zeroConjugateKernel i (by
          simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, i]) k)
  | inr rest =>
      cases rest with
      | inl distinguished =>
          by_cases h0 : distinguished.val = 0
          · exact e.symm distinguishedPos
          · have h1 : distinguished.val = 1 := by omega
            exact e.symm distinguishedNeg
      | inr rest =>
          cases rest with
          | inl r =>
              let i :=
                secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  ⟨2 + r.val, by omega⟩
              exact e.symm (zeroConjugateKernel i (by
                have hnot3 : ¬ 2 + (2 + r.val) = 3 := by omega
                simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, i]) k)
          | inr jk =>
              rcases jk with ⟨j, b⟩
              let i :=
                secondReductionCanonicalSourceTailIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j
              exact e.symm (zeroConjugateKernel i (by
                have hnot2 : ¬ 2 + p + b.val * tailLen + j.val = 2 := by omega
                have hnot3 : ¬ 2 + p + b.val * tailLen + j.val = 3 := by omega
                simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, hnot2, ↓reduceIte, hnot3, φ, i]) k)
noncomputable def secondReductionCanonicalTransportToSchreierGeneratorImage
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    FuchsianGenerator τ → FreeGroup ↥(schreierGeneratorSet hT)
  | .elliptic i =>
      secondReductionCanonicalTransportToSchreierGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)).symm i)
  | .surfaceA _ => 1
  | .surfaceB _ => 1
noncomputable def secondReductionCanonicalTransportToSchreierHom
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    FreeGroup (FuchsianGenerator τ) →* FreeGroup ↥(schreierGeneratorSet hT) :=
  FreeGroup.lift
    (secondReductionCanonicalTransportToSchreierGeneratorImage
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
private theorem secondReductionCanonicalTransportSchreierGenerator_power_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (idx : SecondReductionTransportIndex tailLen p q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let e :=
        secondReductionCanonicalSchreierBasisEquiv
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      (secondReductionCanonicalTransportToSchreierGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail idx) ^
        secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail idx ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (secondReductionCanonicalSourceQuotientImage
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (rels := relators σ)
          (secondReductionCanonicalSchreierTransversal
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  rcases idx with ⟨src, k⟩
  cases src with
  | inl head =>
      fin_cases head
      · let i :=
          secondReductionCanonicalSourceZeroIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        let z : φ.ker :=
          ⟨(FreeGroup.of x) ^ k.val * xWord σ i * ((FreeGroup.of x) ^ k.val)⁻¹, by
            change
              φ ((FreeGroup.of x) ^ k.val * xWord σ i *
                ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hi : φ (xWord σ i) = 1 := by
              simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, i]
            simp only [Lean.Elab.WF.paramLet, Fin.zero_eta, Fin.isValue, map_mul, map_pow, hx, hi, mul_one, map_inv,
  mul_inv_cancel]⟩
        have hpowRel : (xWord σ i) ^ m₁' ∈ relators σ := by
          have hrel : (xWord σ i) ^ σ.periods i ∈ relators σ := Or.inl ⟨i, rfl⟩
          simpa [σ, i] using hrel
        have hkSource : ((z ^ m₁' : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
            Subgroup.normalClosure (relators σ) := by
          change
            ((FreeGroup.of x) ^ k.val * xWord σ i *
                ((FreeGroup.of x) ^ k.val)⁻¹) ^ m₁' ∈
              Subgroup.normalClosure (relators σ)
          exact conjugate_pow_mem_normalClosure_of_pow_mem
            (G := FreeGroup (FuchsianGenerator σ)) (R := relators σ)
            (x := xWord σ i) (g := (FreeGroup.of x) ^ k.val) (n := m₁') hpowRel
        have hmem :
            (e.symm z) ^ m₁' ∈
              Subgroup.normalClosure
                (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
                  (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
                    (f := ellipticQuotientGeneratorImage σ
                      (secondReductionCanonicalSourceQuotientImage
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
                    (rels := relators σ)
                    (secondReductionCanonicalSchreierTransversal
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
          rw [← map_pow]
          exact
            ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
              hrels hT.1 e hkSource
        simpa [σ, φ, hT, e, hrels, x, hx, i, z,
          secondReductionCanonicalTransportToSchreierGenerator,
          secondReductionTransportPeriods, singermanTransportPeriodsFamily,
          secondReductionSourceTransportPeriods, secondReductionSourceCycleCount, twoPeriods]
          using hmem
      · let i :=
          secondReductionCanonicalSourceOneIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        let z : φ.ker :=
          ⟨(FreeGroup.of x) ^ k.val * xWord σ i * ((FreeGroup.of x) ^ k.val)⁻¹, by
            change
              φ ((FreeGroup.of x) ^ k.val * xWord σ i *
                ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hi : φ (xWord σ i) = 1 := by
              simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, i]
            simp only [Lean.Elab.WF.paramLet, Fin.mk_one, Fin.isValue, map_mul, map_pow, hx, hi, mul_one, map_inv,
  mul_inv_cancel]⟩
        have hpowRel : (xWord σ i) ^ m₂' ∈ relators σ := by
          have hrel : (xWord σ i) ^ σ.periods i ∈ relators σ := Or.inl ⟨i, rfl⟩
          simpa [σ, i] using hrel
        have hkSource : ((z ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
            Subgroup.normalClosure (relators σ) := by
          change
            ((FreeGroup.of x) ^ k.val * xWord σ i *
                ((FreeGroup.of x) ^ k.val)⁻¹) ^ m₂' ∈
              Subgroup.normalClosure (relators σ)
          exact conjugate_pow_mem_normalClosure_of_pow_mem
            (G := FreeGroup (FuchsianGenerator σ)) (R := relators σ)
            (x := xWord σ i) (g := (FreeGroup.of x) ^ k.val) (n := m₂') hpowRel
        have hmem :
            (e.symm z) ^ m₂' ∈
              Subgroup.normalClosure
                (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
                  (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
                    (f := ellipticQuotientGeneratorImage σ
                      (secondReductionCanonicalSourceQuotientImage
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
                    (rels := relators σ)
                    (secondReductionCanonicalSchreierTransversal
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
          rw [← map_pow]
          exact
            ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
              hrels hT.1 e hkSource
        simpa [σ, φ, hT, e, hrels, x, hx, i, z,
          secondReductionCanonicalTransportToSchreierGenerator,
          secondReductionTransportPeriods, singermanTransportPeriodsFamily,
          secondReductionSourceTransportPeriods, secondReductionSourceCycleCount, twoPeriods]
          using hmem
  | inr rest =>
      cases rest with
      | inl distinguished =>
          fin_cases distinguished
          · let i :=
              secondReductionCanonicalSourceMiddleIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩
            let z : φ.ker := ⟨(FreeGroup.of x) ^ q, by
              rw [MonoidHom.mem_ker, map_pow, hx]
              apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
              simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
            have hpowRel : (xWord σ i) ^ (q * m₃') ∈ relators σ := by
              have hrel : (xWord σ i) ^ σ.periods i ∈ relators σ := Or.inl ⟨i, rfl⟩
              simpa [σ, i] using hrel
            have hkSource : ((z ^ m₃' : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
                Subgroup.normalClosure (relators σ) := by
              change ((FreeGroup.of x) ^ q) ^ m₃' ∈ Subgroup.normalClosure (relators σ)
              have hxword : FreeGroup.of x = xWord σ i := by
                simp only [secondReductionCanonicalDistinguishedGenerator, xWord, x, i]
              rw [← pow_mul]
              simpa [hxword] using Subgroup.subset_normalClosure hpowRel
            have hmem :
                (e.symm z) ^ m₃' ∈
                  Subgroup.normalClosure
                    (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
                      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
                        (f := ellipticQuotientGeneratorImage σ
                          (secondReductionCanonicalSourceQuotientImage
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
                        (rels := relators σ)
                        (secondReductionCanonicalSchreierTransversal
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
              rw [← map_pow]
              exact
                ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
                  hrels hT.1 e hkSource
            simpa [σ, φ, hT, e, hrels, x, hx, i, z,
              secondReductionCanonicalTransportToSchreierGenerator,
              secondReductionTransportPeriods, singermanTransportPeriodsFamily,
              secondReductionSourceTransportPeriods, secondReductionSourceCycleCount]
              using hmem
          · let i :=
              secondReductionCanonicalSourceMiddleIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩
            let y : FuchsianGenerator σ := FuchsianGenerator.elliptic i
            let z : φ.ker := ⟨(FreeGroup.of y) ^ q, by
              have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
                simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y, i]
              rw [MonoidHom.mem_ker, map_pow, hy]
              apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
              simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
            have hpowRel : (xWord σ i) ^ (q * m₃') ∈ relators σ := by
              have hrel : (xWord σ i) ^ σ.periods i ∈ relators σ := Or.inl ⟨i, rfl⟩
              simpa [σ, i] using hrel
            have hkSource : ((z ^ m₃' : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
                Subgroup.normalClosure (relators σ) := by
              change ((FreeGroup.of y) ^ q) ^ m₃' ∈ Subgroup.normalClosure (relators σ)
              have hyword : FreeGroup.of y = xWord σ i := by
                simp only [xWord, y]
              rw [← pow_mul]
              simpa [hyword] using Subgroup.subset_normalClosure hpowRel
            have hmem :
                (e.symm z) ^ m₃' ∈
                  Subgroup.normalClosure
                    (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
                      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
                        (f := ellipticQuotientGeneratorImage σ
                          (secondReductionCanonicalSourceQuotientImage
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
                        (rels := relators σ)
                        (secondReductionCanonicalSchreierTransversal
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
              rw [← map_pow]
              exact
                ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
                  hrels hT.1 e hkSource
            simpa [σ, φ, hT, e, hrels, x, hx, i, y, z,
              secondReductionCanonicalTransportToSchreierGenerator,
              secondReductionTransportPeriods, singermanTransportPeriodsFamily,
              secondReductionSourceTransportPeriods, secondReductionSourceCycleCount]
              using hmem
      | inr rest =>
          cases rest with
          | inl r =>
              let i :=
                secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  ⟨2 + r.val, by omega⟩
              let z : φ.ker :=
                ⟨(FreeGroup.of x) ^ k.val * xWord σ i *
                    ((FreeGroup.of x) ^ k.val)⁻¹, by
                  change
                    φ ((FreeGroup.of x) ^ k.val * xWord σ i *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                  have hi : φ (xWord σ i) = 1 := by
                    have hnot3 : ¬ 2 + (2 + r.val) = 3 := by omega
                    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, i]
                  simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hx, hi, mul_one, map_inv, mul_inv_cancel]⟩
              have hpowRel : (xWord σ i) ^ (q * m₃') ∈ relators σ := by
                have hrel : (xWord σ i) ^ σ.periods i ∈ relators σ := Or.inl ⟨i, rfl⟩
                simpa [σ, i] using hrel
              have hkSource : ((z ^ (q * m₃') : φ.ker) :
                    FreeGroup (FuchsianGenerator σ)) ∈
                  Subgroup.normalClosure (relators σ) := by
                change
                  ((FreeGroup.of x) ^ k.val * xWord σ i *
                      ((FreeGroup.of x) ^ k.val)⁻¹) ^ (q * m₃') ∈
                    Subgroup.normalClosure (relators σ)
                exact conjugate_pow_mem_normalClosure_of_pow_mem
                  (G := FreeGroup (FuchsianGenerator σ)) (R := relators σ)
                  (x := xWord σ i) (g := (FreeGroup.of x) ^ k.val)
                  (n := q * m₃') hpowRel
              have hmem :
                  (e.symm z) ^ (q * m₃') ∈
                    Subgroup.normalClosure
                      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
                        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
                          (f := ellipticQuotientGeneratorImage σ
                            (secondReductionCanonicalSourceQuotientImage
                            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
                          (rels := relators σ)
                          (secondReductionCanonicalSchreierTransversal
                            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
                rw [← map_pow]
                exact
                  ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
                    hrels hT.1 e hkSource
              simpa [σ, φ, hT, e, hrels, x, hx, i, z,
                secondReductionCanonicalTransportToSchreierGenerator,
                secondReductionTransportPeriods, singermanTransportPeriodsFamily,
                secondReductionSourceTransportPeriods, secondReductionSourceCycleCount]
                using hmem
          | inr jk =>
              rcases jk with ⟨j, b⟩
              let i :=
                secondReductionCanonicalSourceTailIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j
              let z : φ.ker :=
                ⟨(FreeGroup.of x) ^ k.val * xWord σ i *
                    ((FreeGroup.of x) ^ k.val)⁻¹, by
                  change
                    φ ((FreeGroup.of x) ^ k.val * xWord σ i *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                  have hi : φ (xWord σ i) = 1 := by
                    have hnot2 : ¬ 2 + p + b.val * tailLen + j.val = 2 := by omega
                    have hnot3 : ¬ 2 + p + b.val * tailLen + j.val = 3 := by omega
                    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq, xWord,
  secondReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, hnot2, ↓reduceIte, hnot3, φ, i]
                  simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hx, hi, mul_one, map_inv, mul_inv_cancel]⟩
              have hpowRel : (xWord σ i) ^ tail j ∈ relators σ := by
                have hrel : (xWord σ i) ^ σ.periods i ∈ relators σ := Or.inl ⟨i, rfl⟩
                simpa [σ, i] using hrel
              have hkSource : ((z ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
                  Subgroup.normalClosure (relators σ) := by
                change
                  ((FreeGroup.of x) ^ k.val * xWord σ i *
                      ((FreeGroup.of x) ^ k.val)⁻¹) ^ tail j ∈
                    Subgroup.normalClosure (relators σ)
                exact conjugate_pow_mem_normalClosure_of_pow_mem
                  (G := FreeGroup (FuchsianGenerator σ)) (R := relators σ)
                  (x := xWord σ i) (g := (FreeGroup.of x) ^ k.val)
                  (n := tail j) hpowRel
              have hmem :
                  (e.symm z) ^ tail j ∈
                    Subgroup.normalClosure
                      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
                        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
                          (f := ellipticQuotientGeneratorImage σ
                            (secondReductionCanonicalSourceQuotientImage
                            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
                          (rels := relators σ)
                          (secondReductionCanonicalSchreierTransversal
                            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
                rw [← map_pow]
                exact
                  ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
                    hrels hT.1 e hkSource
              simpa [σ, φ, hT, e, hrels, x, hx, i, z,
                secondReductionCanonicalTransportToSchreierGenerator,
                secondReductionTransportPeriods, singermanTransportPeriodsFamily,
                secondReductionSourceTransportPeriods, secondReductionSourceCycleCount]
                using hmem
theorem secondReductionCanonicalTransportToSchreier_powerRelator_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i :
      Fin
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).numPeriods) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let e :=
        secondReductionCanonicalSchreierBasisEquiv
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      secondReductionCanonicalTransportToSchreierHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ((xWord τ i) ^ τ.periods i) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (secondReductionCanonicalSourceQuotientImage
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (rels := relators σ)
          (secondReductionCanonicalSchreierTransversal
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let idx : SecondReductionTransportIndex tailLen p q :=
    (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)).symm i
  have hi : (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx = i := by
    simp only [Equiv.apply_symm_apply, idx]
  rw [← hi]
  simpa [τ, idx, secondReductionCanonicalTransportToSchreierHom,
    secondReductionCanonicalTransportToSchreierGeneratorImage,
    secondReductionTransportSignature, familyFuchsianSignature_periods, xWord] using
    secondReductionCanonicalTransportSchreierGenerator_power_mem_normalClosure
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail idx
end FenchelNielsen
