import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.TransportMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/FirstReduction/RelatorProofs.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# First compact zero-genus reduction

The first explicit finite quotient reduction for compact zero-genus Fuchsian presentations, including quotient maps, basis transport, signatures, and relator verification.
-/

namespace FenchelNielsen
private theorem cyclic_rotate_three_eq_one {G : Type*} [Group G] {a b c : G}
    (h : a * b * c = 1) :
    b * c * a = 1 := by
  have ha : a = (b * c)⁻¹ := by
    calc
      a = (a * b * c) * (b * c)⁻¹ := by group
      _ = (b * c)⁻¹ := by rw [h]; simp only [mul_inv_rev, one_mul]
  rw [ha]
  group
theorem negOneCycleSegmentProduct_eq {G : Type*} [Group G]
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
      rw [negOneCycleSegmentProduct_eq x y (n - 1) l hl]
      have hnl : n - 1 - l = n - (l + 1) := by omega
      rw [hnl]
      rw [pow_succ']
      group
theorem list_ofFn_desc_split {α : Type*} {p k : ℕ} (hk : k < p)
    (f : Fin p → α) :
    List.ofFn (fun i : Fin (p - 1) => f ⟨p - 1 - i.val, by omega⟩) =
      List.ofFn (fun i : Fin (p - 1 - k) => f ⟨p - 1 - i.val, by omega⟩) ++
        List.ofFn (fun i : Fin k => f ⟨k - i.val, by omega⟩) := by
  let a : Fin (p - 1 - k) → α :=
    fun i => f ⟨p - 1 - i.val, by omega⟩
  let b : Fin k → α :=
    fun i => f ⟨k - i.val, by omega⟩
  have hlen : p - 1 = (p - 1 - k) + k := by omega
  rw [List.ofFn_congr hlen]
  rw [← List.ofFn_fin_append a b]
  congr
  funext i
  cases i using Fin.addCases with
  | left r =>
      dsimp [a, b]
      rw [Fin.append_left]
  | right j =>
      dsimp [a, b]
      rw [Fin.append_right]
      apply congrArg f
      ext
      simp only
      omega
private theorem firstReductionCanonicalSchreierToTarget_mapsRelators_of_source_cases
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hFirst :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let φ :=
        firstReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let e :=
        firstReductionCanonicalSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let x : FuchsianGenerator σ :=
        firstReductionCanonicalDistinguishedGenerator
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let i₀ :=
        firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ k : Fin p,
        η
            (e.symm
              (⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
                  ((FreeGroup.of x) ^ k.val)⁻¹, by
                change φ
                    ((FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                have hrφ :
                    φ ((xWord σ i₀) ^ σ.periods i₀) = 1 :=
                  firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                    ((xWord σ i₀) ^ σ.periods i₀) (Or.inl ⟨i₀, rfl⟩)
                simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
          Subgroup.normalClosure (relators τ))
    (hSecond :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let φ :=
        firstReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let e :=
        firstReductionCanonicalSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let x : FuchsianGenerator σ :=
        firstReductionCanonicalDistinguishedGenerator
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let i₁ :=
        firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ k : Fin p,
        η
            (e.symm
              (⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
                  ((FreeGroup.of x) ^ k.val)⁻¹, by
                change φ
                    ((FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                have hrφ :
                    φ ((xWord σ i₁) ^ σ.periods i₁) = 1 :=
                  firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                    ((xWord σ i₁) ^ σ.periods i₁) (Or.inl ⟨i₁, rfl⟩)
                simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
          Subgroup.normalClosure (relators τ))
    (hTail :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let φ :=
        firstReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let e :=
        firstReductionCanonicalSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let x : FuchsianGenerator σ :=
        firstReductionCanonicalDistinguishedGenerator
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ j : Fin tailLen, ∀ k : Fin p,
        let iTail :=
          firstReductionCanonicalSourceTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
        η
            (e.symm
              (⟨(FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
                  ((FreeGroup.of x) ^ k.val)⁻¹, by
                change φ
                    ((FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                have hrφ :
                    φ ((xWord σ iTail) ^ σ.periods iTail) = 1 :=
                  firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                    ((xWord σ iTail) ^ σ.periods iTail) (Or.inl ⟨iTail, rfl⟩)
                simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
          Subgroup.normalClosure (relators τ))
    (hTotal :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let φ :=
        firstReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let e :=
        firstReductionCanonicalSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let x : FuchsianGenerator σ :=
        firstReductionCanonicalDistinguishedGenerator
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ k : Fin p,
        η
            (e.symm
              (⟨(FreeGroup.of x) ^ k.val * totalRelation σ *
                  ((FreeGroup.of x) ^ k.val)⁻¹, by
                change φ
                    ((FreeGroup.of x) ^ k.val * totalRelation σ *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                have hrφ : φ (totalRelation σ) = 1 :=
                  firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                    (totalRelation σ) (Or.inr rfl)
                simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
          Subgroup.normalClosure (relators τ)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ r ∈
        ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T),
        η r ∈ Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  intro r hr
  have hrImage :
      e r ∈ ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := ellipticQuotientGeneratorImage σ
          (firstReductionCanonicalSourceQuotientImage
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
        (rels := relators σ) T := by
    simpa [e] using
      (ReidemeisterSchreier.Discrete.Presentations.mem_freeGroupPullbackRelatorSet_iff (e := e)
        (S := ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (firstReductionCanonicalSourceQuotientImage
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
          (rels := relators σ) T)
        (y := r)).1 hr
  rcases hrImage with ⟨t, ht, r₀, hr₀, hval⟩
  have htPower : ∃ k : Fin p, t = (FreeGroup.of x) ^ k.val := by
    simpa [T] using
      (mem_range_cyclicQuotientRightRep_iff_generatorPower φ (x := x) hx).1 ht
  rcases htPower with ⟨k, rfl⟩
  let tPow : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ k.val
  have relator_eq :
      r =
        e.symm
          (⟨tPow * r₀ * tPow⁻¹, by
            change φ (tPow * r₀ * tPow⁻¹) = 1
            have hrφ : φ r₀ = 1 := hrels r₀ hr₀
            simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) := by
    let zRel : φ.ker :=
      ⟨tPow * r₀ * tPow⁻¹, by
        change φ (tPow * r₀ * tPow⁻¹) = 1
        have hrφ : φ r₀ = 1 := hrels r₀ hr₀
        simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
    have hz : e r = zRel := by
      apply Subtype.ext
      simpa [tPow, zRel] using hval
    calc
      r = e.symm (e r) := by simp only [MulEquiv.symm_apply_apply]
      _ = e.symm zRel := by rw [hz]
  rcases hr₀ with ⟨i, rfl⟩ | rfl
  · by_cases h0 : i.val = 0
    · have hi :
          i =
            firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
        ext
        simpa [firstReductionCanonicalSourceZeroIndex] using h0
      subst i
      rw [relator_eq]
      simpa [σ, τ, φ, e, η, x, tPow] using hFirst k
    · by_cases h1 : i.val = 1
      · have hi :
            i =
            firstReductionCanonicalSourceOneIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
          ext
          simpa [firstReductionCanonicalSourceOneIndex] using h1
        subst i
        rw [relator_eq]
        simpa [σ, τ, φ, e, η, x, tPow] using hSecond k
      · let j : Fin tailLen := ⟨i.val - 2, by
            have hi_lt : i.val < 2 + tailLen := by
              change i.val < 2 + tailLen
              exact i.isLt
            omega⟩
        have hiTail :
            i =
              firstReductionCanonicalSourceTailIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j := by
          ext
          simp only [firstReductionCanonicalSourceTailIndex, j]
          omega
        rw [relator_eq]
        simpa [σ, τ, φ, e, η, x, tPow, hiTail] using hTail j k
  · rw [relator_eq]
    simpa [σ, τ, φ, e, η, x, tPow] using hTotal k
private theorem firstReductionCanonicalSchreierToTarget_firstPower_sourceCase_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let i₀ :=
      firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ i₀) ^ σ.periods i₀) = 1 :=
              firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                ((xWord σ i₀) ^ σ.periods i₀) (Or.inl ⟨i₀, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let i₀ :=
    firstReductionCanonicalSourceZeroIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let a :=
    firstReductionCanonicalFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ i₀) ^ σ.periods i₀) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ i₀) ^ σ.periods i₀) = 1 :=
        firstReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ((xWord σ i₀) ^ σ.periods i₀) (Or.inl ⟨i₀, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = a ^ m₁' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ i₀) ^ σ.periods i₀) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((a ^ m₁' : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((a ^ m₁' : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((a : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ m₁' by
          exact (map_pow (φ.ker.subtype) a m₁')]
    rw [firstReductionCanonicalFirstPowerKernel_coe]
    simp only [firstReductionCanonicalSourceSignature, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceZeroIndex, Fin.mk_zero', xWord, firstReductionCanonicalSourcePeriod,
  Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceDIte, pow_mul, x, i₀, σ]
    group
  have hmain :=
    firstReductionCanonicalSchreierToTarget_firstPowerRelator_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change η (e.symm z) ∈ Subgroup.normalClosure (relators τ)
  rw [hz, map_pow]
  simpa [σ, τ, φ, e, η, a] using hmain
private theorem firstReductionCanonicalSecondShiftedCycle_eq_conjugate_secondPower
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let edge : Fin p → φ.ker :=
      firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
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
          simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
        have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
          simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
        rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
        apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
        simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let edge : Fin p → φ.ker :=
    firstReductionCanonicalSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let upper :=
    (List.ofFn (fun i : Fin (p - 1 - k.val) => edge ⟨p - 1 - i.val, by omega⟩)).prod
  apply Subtype.ext
  change
    ((lower * wrap * upper : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        (FreeGroup.of y) ^ p *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹
  have hlowerCoe :
      ((lower : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun i : Fin k.val =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (k.val - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^
              (k.val - 1 - i.val))⁻¹)).prod := by
    change
      φ.ker.subtype lower =
        (List.ofFn (fun i : Fin k.val =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (k.val - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^
              (k.val - 1 - i.val))⁻¹)).prod
    simp only [Subgroup.subtype_apply, Subgroup.val_list_prod, List.map_ofFn, lower, edge]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let i' : Fin (p - 1) := ⟨k.val - 1 - i.val, by omega⟩
    have hidx :
        (⟨i'.val + 1, by omega⟩ : Fin p) = ⟨k.val - i.val, by omega⟩ := by
      ext
      simp only [i']
      omega
    have hs : k.val - 1 - i.val + 1 = k.val - i.val := by omega
    simpa [σ, φ, x, y, edge, i', hidx, hs] using
      firstReductionCanonicalSecondEdgeKernelElement_succ_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i'
  have hwrapCoe :
      ((wrap : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (p - 1))⁻¹ := by
    simpa [σ, φ, x, y, edge, wrap] using
      firstReductionCanonicalSecondEdgeKernelElement_zero_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hupperCoe :
      ((upper : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (p - 1 - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^
              (p - 1 - 1 - i.val))⁻¹)).prod := by
    change
      φ.ker.subtype upper =
        (List.ofFn (fun i : Fin (p - 1 - k.val) =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (p - 1 - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^
              (p - 1 - 1 - i.val))⁻¹)).prod
    simp only [Subgroup.subtype_apply, Subgroup.val_list_prod, List.map_ofFn, upper, edge]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let i' : Fin (p - 1) := ⟨i.val, by omega⟩
    simpa [σ, φ, x, y, edge, i'] using
      firstReductionCanonicalSecondEdgeKernelElement_descending_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i'
  change
    ((lower : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
        ((wrap : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
        ((upper : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        (FreeGroup.of y) ^ p *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹
  rw [hlowerCoe, hwrapCoe, hupperCoe]
  rw [negOneCycleSegmentProduct_eq (FreeGroup.of x) (FreeGroup.of y) k.val k.val
    (by omega)]
  rw [negOneCycleSegmentProduct_eq (FreeGroup.of x) (FreeGroup.of y)
    (p - 1) (p - 1 - k.val) (by omega)]
  have hkk : k.val - k.val = 0 := by omega
  have hlast : p - 1 - (p - 1 - k.val) = k.val := by omega
  rw [hkk, hlast]
  simp only [pow_zero, inv_one, mul_one]
  have hkadd : k.val + 1 + (p - 1 - k.val) = p := by omega
  calc
    (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          (FreeGroup.of y) ^ k.val *
          (FreeGroup.of y * ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (p - 1))⁻¹) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (p - 1) *
          (FreeGroup.of y) ^ (p - 1 - k.val) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹)
        =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        ((FreeGroup.of y) ^ k.val * FreeGroup.of y *
          (FreeGroup.of y) ^ (p - 1 - k.val)) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ := by
        group
    _ =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        (FreeGroup.of y) ^ p *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ := by
        rw [← pow_succ (FreeGroup.of y) k.val]
        rw [← pow_add (FreeGroup.of y) (k.val + 1) (p - 1 - k.val)]
        rw [hkadd]
private theorem firstReductionCanonicalSchreierToTarget_secondPower_sourceCase_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let i₁ :=
      firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ i₁) ^ σ.periods i₁) = 1 :=
              firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                ((xWord σ i₁) ^ σ.periods i₁) (Or.inl ⟨i₁, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let i₁ :=
    firstReductionCanonicalSourceOneIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let y : FuchsianGenerator σ := FuchsianGenerator.elliptic i₁
  let edge : Fin p → φ.ker :=
    firstReductionCanonicalSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let upper :=
    (List.ofFn (fun i : Fin (p - 1 - k.val) => edge ⟨p - 1 - i.val, by omega⟩)).prod
  let cycle := lower * wrap * upper
  let base :=
    firstReductionCanonicalSecondPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ i₁) ^ σ.periods i₁) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ i₁) ^ σ.periods i₁) = 1 :=
        firstReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ((xWord σ i₁) ^ σ.periods i₁) (Or.inl ⟨i₁, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hcycleSource :
      cycle =
        (⟨(FreeGroup.of x) ^ k.val * (FreeGroup.of y) ^ p *
            ((FreeGroup.of x) ^ k.val)⁻¹, by
          rw [MonoidHom.mem_ker]
          have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
            simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
          have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
            simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y, i₁]
          rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
          apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
          simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
    simpa [σ, φ, x, y, i₁, edge, lower, wrap, upper, cycle] using
      firstReductionCanonicalSecondShiftedCycle_eq_conjugate_secondPower
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k
  have hz : z = cycle ^ m₂' := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ i₁) ^ σ.periods i₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((cycle ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((cycle ^ m₂' : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ m₂' by
          exact (map_pow (φ.ker.subtype) cycle m₂')]
    have hcycleCoe :=
      congrArg (fun u : φ.ker => (u : FreeGroup (FuchsianGenerator σ))) hcycleSource
    have hcycleCoe' :
        ((cycle : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            (FreeGroup.of y) ^ p *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ := by
      simpa using hcycleCoe
    rw [hcycleCoe']
    simp only [firstReductionCanonicalSourceSignature, firstReductionCanonicalDistinguishedGenerator, xWord,
  firstReductionCanonicalSourceOneIndex, firstReductionCanonicalSourcePeriod, one_ne_zero, ↓reduceDIte, pow_mul,
  conj_pow, x, i₁, y, σ]
  have hbasePower : (η (e.symm base)) ^ m₂' ∈ Subgroup.normalClosure (relators τ) := by
    have hmain :=
      firstReductionCanonicalSchreierToTarget_secondPowerRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hmain' :
        η ((e.symm base) ^ m₂') ∈ Subgroup.normalClosure (relators τ) := by
      simpa [σ, τ, φ, e, η, base] using hmain
    rw [map_pow] at hmain'
    simpa using hmain'
  have htailSplit :
      (List.ofFn (fun i : Fin (p - 1) => edge ⟨p - 1 - i.val, by omega⟩)).prod =
        upper * lower := by
    have hlist := list_ofFn_desc_split (p := p) (k := k.val) k.isLt edge
    simpa [upper, lower] using congrArg List.prod hlist
  have hbaseEq : base = (wrap * upper) * lower := by
    have hdesc :
        wrap *
            (List.ofFn (fun i : Fin (p - 1) =>
              edge ⟨p - 1 - i.val, by omega⟩)).prod =
          base := by
      simpa [σ, φ, edge, wrap, base] using
        firstReductionCanonicalSecondDescendingNamedCycle_eq_secondPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    rw [htailSplit] at hdesc
    calc
      base = wrap * (upper * lower) := hdesc.symm
      _ = (wrap * upper) * lower := by group
  let a := η (e.symm (wrap * upper))
  let b := η (e.symm lower)
  have hbaseAB : (a * b) ^ m₂' ∈ Subgroup.normalClosure (relators τ) := by
    rw [hbaseEq] at hbasePower
    simpa [a, b, map_mul, mul_assoc] using hbasePower
  have hrot :
      (b * a) ^ m₂' ∈ Subgroup.normalClosure (relators τ) :=
    ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_pow_mem_normalClosure
      (R := relators τ) (a := a) (b := b) hbaseAB
  have hcycleTarget :
      (η (e.symm cycle)) ^ m₂' ∈ Subgroup.normalClosure (relators τ) := by
    have hcycleImage : η (e.symm cycle) = b * a := by
      simp only [Lean.Elab.WF.paramLet, mul_assoc, map_mul, cycle, b, a]
    simpa [hcycleImage] using hrot
  change η (e.symm z) ∈ Subgroup.normalClosure (relators τ)
  rw [hz, map_pow]
  simpa [cycle] using hcycleTarget
private theorem firstReductionCanonicalSchreierToTarget_tailPower_sourceCase_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let iTail :=
      firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ :
                φ ((xWord σ iTail) ^ σ.periods iTail) = 1 :=
              firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                ((xWord σ iTail) ^ σ.periods iTail) (Or.inl ⟨iTail, rfl⟩)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let iTail :=
    firstReductionCanonicalSourceTailIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
  let c :=
    firstReductionCanonicalTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * ((xWord σ iTail) ^ σ.periods iTail) *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ ((xWord σ iTail) ^ σ.periods iTail) = 1 :=
        firstReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ((xWord σ iTail) ^ σ.periods iTail) (Or.inl ⟨iTail, rfl⟩)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hz : z = c ^ tail j := by
    apply Subtype.ext
    change
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          ((xWord σ iTail) ^ σ.periods iTail) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator σ))
    rw [show ((c ^ tail j : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        ((c : φ.ker) : FreeGroup (FuchsianGenerator σ)) ^ tail j by
          exact (map_pow (φ.ker.subtype) c (tail j))]
    rw [firstReductionCanonicalTailKernelElement_coe]
    have htailOne : 2 + j.val ≠ 1 := by omega
    simp only [firstReductionCanonicalSourceSignature, firstReductionCanonicalDistinguishedGenerator, xWord,
  firstReductionCanonicalSourceTailIndex, firstReductionCanonicalSourcePeriod, Nat.add_eq_zero_iff,
  OfNat.ofNat_ne_zero, false_and, ↓reduceDIte, htailOne, add_tsub_cancel_left, Fin.eta, conj_pow, x, iTail, σ]
  have hmain :=
    firstReductionCanonicalSchreierToTarget_tailPowerRelator_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k
  change η (e.symm z) ∈ Subgroup.normalClosure (relators τ)
  rw [hz, map_pow]
  simpa [σ, τ, φ, e, η, c] using hmain
private theorem firstReductionCanonicalSchreierToTarget_total_sourceCase_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
          (⟨(FreeGroup.of x) ^ k.val * totalRelation σ *
              ((FreeGroup.of x) ^ k.val)⁻¹, by
            change φ
                ((FreeGroup.of x) ^ k.val * totalRelation σ *
                  ((FreeGroup.of x) ^ k.val)⁻¹) = 1
            have hrφ : φ (totalRelation σ) = 1 :=
              firstReductionCanonicalSourceFreeQuotientHom_respects_relators
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
                (totalRelation σ) (Or.inr rfl)
            simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * totalRelation σ *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * totalRelation σ *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ (totalRelation σ) = 1 :=
        firstReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          (totalRelation σ) (Or.inr rfl)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  change η (e.symm z) ∈ Subgroup.normalClosure (relators τ)
  by_cases hlast : k.val = p - 1
  · let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let kLast : Fin p := ⟨p - 1, by omega⟩
    let kZero : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
    let t : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ k.val
    let r : FreeGroup (FuchsianGenerator σ) := totalRelation σ
    have hprodCoe :
        (((List.ofFn (fun j : Fin tailLen =>
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
          (List.ofFn (fun j : Fin tailLen =>
            ((firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast : φ.ker) :
                FreeGroup (FuchsianGenerator σ)))).prod := by
      change
        φ.ker.subtype
            ((List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod) =
          (List.ofFn (fun j : Fin tailLen =>
            φ.ker.subtype
              (firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast))).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    have htailList :
        (List.ofFn (fun j : Fin tailLen =>
          ((firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))) =
          List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x) ^ (p - 1) * FreeGroup.of (tailGen j) *
              ((FreeGroup.of x) ^ (p - 1))⁻¹) := by
      apply List.ofFn_inj.2
      funext j
      simpa [σ, φ, x, tailGen, kLast] using
        firstReductionCanonicalTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast
    have htailConj :
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x) ^ (p - 1) * FreeGroup.of (tailGen j) *
              ((FreeGroup.of x) ^ (p - 1))⁻¹)).prod =
          (FreeGroup.of x) ^ (p - 1) *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x) ^ (p - 1))⁻¹ := by
      calc
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x) ^ (p - 1) * FreeGroup.of (tailGen j) *
              ((FreeGroup.of x) ^ (p - 1))⁻¹)).prod =
            (List.map
              (fun u =>
                (FreeGroup.of x) ^ (p - 1) * u *
                  ((FreeGroup.of x) ^ (p - 1))⁻¹)
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).prod := by
              rw [List.map_ofFn]
              rfl
        _ =
          (FreeGroup.of x) ^ (p - 1) *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x) ^ (p - 1))⁻¹ := by
              rw [← ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x) ^ (p - 1))
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))]
    have hkerEq :
        z =
          firstReductionCanonicalFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen *
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero *
            (List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * totalRelation σ *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
          ((firstReductionCanonicalFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen : φ.ker) :
                FreeGroup (FuchsianGenerator σ)) *
            ((firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero : φ.ker) :
                  FreeGroup (FuchsianGenerator σ)) *
            (((List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod : φ.ker) :
                  FreeGroup (FuchsianGenerator σ))
      rw [hprodCoe, htailList, htailConj]
      rw [firstReductionCanonicalFirstPowerKernel_coe]
      rw [firstReductionCanonicalSecondEdgeKernelElement_zero_coe]
      have hTotal :=
        firstReductionCanonicalSource_totalRelation_eq
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      rw [hTotal]
      simp only [x, tailGen, xWord,
        firstReductionCanonicalDistinguishedGenerator, mul_assoc]
      rw [hlast]
      rw [← mul_assoc]
      rw [← pow_succ]
      have hsuccNat : p - 1 + 1 = p := by
        omega
      rw [hsuccNat]
      group
    have htailMap :
        e.symm
            ((List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod) =
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast))).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    have hmap :
        e.symm
            (firstReductionCanonicalFirstPowerKernel
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen *
              firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero *
              (List.ofFn (fun j : Fin tailLen =>
                firstReductionCanonicalTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod) =
          e.symm
              (firstReductionCanonicalFirstPowerKernel
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
            e.symm
              (firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero) *
            (List.ofFn (fun j : Fin tailLen =>
              e.symm
                (firstReductionCanonicalTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast))).prod := by
      rw [map_mul, map_mul, htailMap]
    let tailWord :=
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast))).prod
    let firstWord :=
      e.symm
        (firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let secondWord :=
      e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero)
    have hwrap :=
      firstReductionCanonicalSchreierToTarget_wrapTotalRelator_image_eq_one
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hwrap' : η tailWord * η firstWord * η secondWord = 1 := by
      simpa [σ, τ, e, η, kLast, kZero, tailWord, firstWord, secondWord, map_mul] using hwrap
    have hrot : η firstWord * η secondWord * η tailWord = 1 :=
      cyclic_rotate_three_eq_one hwrap'
    rw [hkerEq, hmap]
    rw [map_mul, map_mul]
    change η firstWord * η secondWord * η tailWord ∈ Subgroup.normalClosure (relators τ)
    rw [hrot]
    exact Subgroup.one_mem _
  · let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let knw : Fin (p - 1) := ⟨k.val, by omega⟩
    let k0 : Fin p := ⟨knw.val, by omega⟩
    let k1 : Fin p := ⟨knw.val + 1, by omega⟩
    let t : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ k.val
    let r : FreeGroup (FuchsianGenerator σ) := totalRelation σ
    have hprodCoe :
        (((List.ofFn (fun j : Fin tailLen =>
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
          (List.ofFn (fun j : Fin tailLen =>
            ((firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0 : φ.ker) :
                FreeGroup (FuchsianGenerator σ)))).prod := by
      change
        φ.ker.subtype
            ((List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod) =
          (List.ofFn (fun j : Fin tailLen =>
            φ.ker.subtype
              (firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0))).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    have htailList :
        (List.ofFn (fun j : Fin tailLen =>
          ((firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0 : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))) =
          List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
              ((FreeGroup.of x) ^ k.val)⁻¹) := by
      apply List.ofFn_inj.2
      funext j
      simpa [σ, φ, x, tailGen, k0, knw] using
        firstReductionCanonicalTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0
    have htailConj :
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
              ((FreeGroup.of x) ^ k.val)⁻¹)).prod =
          (FreeGroup.of x) ^ k.val *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      calc
        (List.ofFn (fun j : Fin tailLen =>
            (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
              ((FreeGroup.of x) ^ k.val)⁻¹)).prod =
            (List.map
              (fun u =>
                (FreeGroup.of x) ^ k.val * u * ((FreeGroup.of x) ^ k.val)⁻¹)
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))).prod := by
              rw [List.map_ofFn]
              rfl
        _ =
          (FreeGroup.of x) ^ k.val *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
              rw [← ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod
                ((FreeGroup.of x) ^ k.val)
                (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j)))]
    have hkerEq :
        z =
          firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1 *
            (List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * totalRelation σ *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
          ((firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1 : φ.ker) :
                FreeGroup (FuchsianGenerator σ)) *
            (((List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod : φ.ker) :
                  FreeGroup (FuchsianGenerator σ))
      rw [hprodCoe, htailList, htailConj]
      rw [firstReductionCanonicalSecondEdgeKernelElement_succ_coe]
      have hTotal :=
        firstReductionCanonicalSource_totalRelation_eq
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      rw [hTotal]
      simp only [x, tailGen, xWord,
        firstReductionCanonicalDistinguishedGenerator, mul_assoc]
      simp only [inv_mul_cancel_left, knw]
      group
    have hmap :
        e.symm
            (firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1 *
              (List.ofFn (fun j : Fin tailLen =>
                firstReductionCanonicalTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod) =
          e.symm
              (firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1) *
            (List.ofFn (fun j : Fin tailLen =>
              e.symm
                (firstReductionCanonicalTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0))).prod := by
      rw [map_mul, map_list_prod, List.map_ofFn]
      rfl
    have hnonwrap :=
      firstReductionCanonicalSchreierToTarget_nonwrapTotalRelator_image_eq_one
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen knw
    have hEqOne :
        η
            (e.symm
                (firstReductionCanonicalSecondEdgeKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1) *
              (List.ofFn (fun j : Fin tailLen =>
                e.symm
                  (firstReductionCanonicalTailKernelElement
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0))).prod) = 1 := by
      simpa [σ, τ, e, η, knw, k0, k1] using hnonwrap
    rw [hkerEq, hmap]
    rw [hEqOne]
    exact Subgroup.one_mem _
private theorem firstReductionCanonicalSchreierToTarget_mapsRelators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ r ∈
        ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T),
        η r ∈ Subgroup.normalClosure (relators τ) :=
  firstReductionCanonicalSchreierToTarget_mapsRelators_of_source_cases
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalSchreierToTarget_firstPower_sourceCase_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    (firstReductionCanonicalSchreierToTarget_secondPower_sourceCase_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    (firstReductionCanonicalSchreierToTarget_tailPower_sourceCase_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    (firstReductionCanonicalSchreierToTarget_total_sourceCase_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
noncomputable def firstReductionCanonicalForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FirstReductionCanonicalForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen :=
  firstReductionCanonicalForwardMapData_of_mapsRelators
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (by
      simpa [firstReductionCanonicalDistinguishedGenerator] using
        firstReductionCanonicalSchreierToTarget_mapsRelators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
noncomputable def firstReductionCanonicalKernelEquiv
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :=
  firstReductionCanonicalKernelEquivOfForwardMapData
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
end FenchelNielsen
