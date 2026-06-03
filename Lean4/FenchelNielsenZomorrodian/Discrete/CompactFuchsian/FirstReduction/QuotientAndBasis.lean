import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.Signatures
import FenchelNielsenZomorrodian.Discrete.Singerman.CyclicProductIdentities
import FenchelNielsenZomorrodian.Discrete.Singerman.CyclicSchreierKernel

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/FirstReduction/QuotientAndBasis.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# First compact zero-genus reduction

The first explicit finite quotient reduction for compact zero-genus Fuchsian presentations, including quotient maps, basis transport, signatures, and relator verification.
-/

namespace FenchelNielsen
noncomputable def firstReductionCanonicalSourceQuotientImage
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    (let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
     Fin σ.numPeriods → Multiplicative (ZMod p)) :=
  fun i =>
    if i.val = 0 then Multiplicative.ofAdd (1 : ZMod p)
    else if i.val = 1 then Multiplicative.ofAdd (-1 : ZMod p)
    else 1
theorem firstReductionCanonicalSourceQuotientImage_pow
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ i : Fin σ.numPeriods,
      firstReductionCanonicalSourceQuotientImage
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i ^
        σ.periods i = 1 := by
  classical
  dsimp
  intro i
  by_cases h0 : i.val = 0
  · have hi :
        i =
          firstReductionCanonicalSourceZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
      ext
      simpa [firstReductionCanonicalSourceZeroIndex] using h0
    subst i
    have hzval :
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).val = 0 := by
      simp only [firstReductionCanonicalSourceZeroIndex]
    rw [firstReductionCanonicalSourceQuotientImage, if_pos hzval]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [firstReductionCanonicalSourceSignature_period_zero, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_one, toAdd_one]
  · by_cases h1 : i.val = 1
    · have hi :
          i =
            firstReductionCanonicalSourceOneIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
        ext
        simpa [firstReductionCanonicalSourceOneIndex] using h1
      subst i
      have hoval :
          (firstReductionCanonicalSourceOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).val = 1 := by
        simp only [firstReductionCanonicalSourceOneIndex]
      have hnot0 :
          (firstReductionCanonicalSourceOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).val ≠ 0 := by
        simp only [firstReductionCanonicalSourceOneIndex, ne_eq, one_ne_zero, not_false_eq_true]
      rw [firstReductionCanonicalSourceQuotientImage, if_neg hnot0, if_pos hoval]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [ofAdd_neg, firstReductionCanonicalSourceSignature_period_one, inv_pow, toAdd_inv, toAdd_pow,
  toAdd_ofAdd, nsmul_eq_mul, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_one, neg_zero, toAdd_one]
    · simp only [firstReductionCanonicalSourceQuotientImage, h0, ↓reduceIte, h1, one_pow]
theorem firstReductionCanonicalSourceQuotientImage_prod
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∏ i : Fin σ.numPeriods,
      firstReductionCanonicalSourceQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i = 1 := by
  classical
  dsimp
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change ∏ i : Fin σ.numPeriods,
      firstReductionCanonicalSourceQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i = 1
  rw [Fin.prod_univ_def]
  rw [← List.ofFn_eq_map]
  have hNum : σ.numPeriods = 2 + tailLen := by
    simp only [firstReductionCanonicalSourceSignature, σ]
  rw [List.ofFn_congr hNum]
  rw [list_ofFn_two_add]
  simp only [List.prod_cons]
  have htailOne :
      (List.ofFn fun j : Fin tailLen =>
        firstReductionCanonicalSourceQuotientImage
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          (Fin.cast hNum.symm ⟨2 + j.val, by omega⟩)) =
        List.ofFn (fun _ : Fin tailLen => (1 : Multiplicative (ZMod p))) := by
    apply List.ofFn_inj.2
    funext j
    simp only [firstReductionCanonicalSourceQuotientImage, Fin.cast_eq_self, Nat.add_eq_zero_iff,
  OfNat.ofNat_ne_zero, false_and, ↓reduceIte, ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one]
    omega
  rw [htailOne]
  simp only [firstReductionCanonicalSourceQuotientImage, Fin.mk_zero', Fin.cast_eq_self, Fin.coe_ofNat_eq_mod,
  Nat.zero_mod, ↓reduceIte, one_ne_zero, ofAdd_neg, List.ofFn_const, List.prod_replicate, one_pow, mul_one,
  mul_inv_cancel]
noncomputable def firstReductionCanonicalSourceFreeQuotientHom
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    FreeGroup (FuchsianGenerator σ) →* Multiplicative (ZMod p) := by
  classical
  dsimp
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  exact
    FreeGroup.lift
      (ellipticQuotientGeneratorImage σ
        (firstReductionCanonicalSourceQuotientImage
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
@[simp 900] theorem firstReductionCanonicalSourceFreeQuotientHom_firstGenerator
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (FreeGroup.of
          (FuchsianGenerator.elliptic
            (firstReductionCanonicalSourceZeroIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))) =
      Multiplicative.ofAdd (1 : ZMod p) := by
  classical
  dsimp
  simp only [firstReductionCanonicalSourceFreeQuotientHom, Lean.Elab.WF.paramLet, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte]
theorem firstReductionCanonicalSourceFreeQuotientHom_respects_relators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ r ∈ relators σ,
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r = 1 := by
  classical
  dsimp
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  simpa [firstReductionCanonicalSourceFreeQuotientHom, σ] using
    ellipticQuotientGeneratorImage_respects_relators σ
      (firstReductionCanonicalSourceQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      (firstReductionCanonicalSourceQuotientImage_pow
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      (firstReductionCanonicalSourceQuotientImage_prod
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
noncomputable abbrev firstReductionCanonicalDistinguishedGenerator
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianGenerator
      (firstReductionCanonicalSourceSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) :=
  FuchsianGenerator.elliptic
    (firstReductionCanonicalSourceZeroIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
noncomputable def firstReductionCanonicalSchreierTransversal
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    Set (FreeGroup (FuchsianGenerator σ)) := by
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
  exact Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
theorem firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    IsRightSchreierTransversal φ.ker
      (firstReductionCanonicalSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
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
  simpa [firstReductionCanonicalSchreierTransversal, σ, φ, x] using
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
noncomputable def firstReductionCanonicalSchreierBasisEquiv
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
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
  simpa [firstReductionCanonicalSchreierTransversal, σ, φ, x] using
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
@[simp 900] theorem firstReductionCanonicalSchreierBasisEquiv_symm_apply
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ z : ↥(schreierGeneratorSet hT),
      (firstReductionCanonicalSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).symm (z : φ.ker) =
        (FreeGroup.of z)⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
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
  intro z
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  apply e.injective
  simp only [firstReductionCanonicalSchreierTransversal, Lean.Elab.WF.paramLet, id_eq,
  firstReductionCanonicalSchreierBasisEquiv, MulEquiv.apply_symm_apply, map_inv,
  freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator_of φ x hx z, inv_inv, e, φ, x]
noncomputable def firstReductionCanonicalFirstPowerKernel
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    φ.ker := by
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
  refine ⟨(FreeGroup.of x) ^ p, ?_⟩
  rw [MonoidHom.mem_ker, map_pow]
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  rw [hx]
  apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
  simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]
theorem firstReductionCanonicalFirstPowerKernel_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ((firstReductionCanonicalFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ p := by
  classical
  dsimp
  simp only [firstReductionCanonicalFirstPowerKernel, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq]
noncomputable def firstReductionCanonicalSecondPowerKernel
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  refine ⟨(FreeGroup.of y) ^ p, ?_⟩
  rw [MonoidHom.mem_ker, map_pow]
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
  rw [hy]
  apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
  simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]
noncomputable def firstReductionCanonicalSecondEdgeKernelElement
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    φ.ker := by
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
  let r : ℕ := ((k.val : ZMod p) - 1).val
  refine ⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ r)⁻¹, ?_⟩
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
  rw [MonoidHom.mem_ker]
  rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
  apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
  simp only [ofAdd_neg, toAdd_mul, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, toAdd_inv, ZMod.natCast_val,
  dvd_refl, ZMod.cast_sub, ZMod.cast_natCast, ZMod.cast_one, neg_sub, toAdd_one, r]
  ring
theorem firstReductionCanonicalSecondEdgeKernelElement_zero_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
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
    ((firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      FreeGroup.of y * ((FreeGroup.of x) ^ (p - 1))⁻¹ := by
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
  have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
  have hsucc : (p - 1).succ = p := by omega
  have hval : (-1 : ZMod p).val = p - 1 := by
    rw [← hsucc]
    exact ZMod.val_neg_one (p - 1)
  simp only [firstReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, pow_zero, one_mul, Nat.cast_zero, zero_sub, hval, id_eq]
theorem firstReductionCanonicalSecondEdgeKernelElement_descending_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (i : Fin (p - 1)) :
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
    ((firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨p - 1 - i.val, by omega⟩ :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ (p - 1 - i.val) * FreeGroup.of y *
        ((FreeGroup.of x) ^ (p - 1 - 1 - i.val))⁻¹ := by
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
  let kNat := p - 1 - i.val
  have hp_gt_one : 1 < p := lt_of_lt_of_le (by decide : 1 < 2) hp
  haveI : Fact (1 < p) := ⟨hp_gt_one⟩
  have hkpos : 0 < kNat := by
    dsimp [kNat]
    omega
  have hklt : kNat < p := by
    dsimp [kNat]
    omega
  have hkval : ((kNat : ZMod p)).val = kNat :=
    ZMod.val_natCast_of_lt hklt
  have hsubval : ((kNat : ZMod p) - 1).val = kNat - 1 := by
    have hle : (1 : ZMod p).val ≤ (kNat : ZMod p).val := by
      rw [hkval, ZMod.val_one]
      exact Nat.succ_le_iff.mpr hkpos
    rw [ZMod.val_sub hle, hkval, ZMod.val_one]
  have hkSub : kNat - 1 = p - 1 - 1 - i.val := by
    dsimp [kNat]
    omega
  have hsubval' :
      (((p - 1 - i.val : ℕ) : ZMod p) - 1).val =
        p - 1 - 1 - i.val := by
    simpa [kNat, hkSub] using hsubval
  dsimp [firstReductionCanonicalSecondEdgeKernelElement,
    firstReductionCanonicalDistinguishedGenerator]
  rw [hsubval']
theorem firstReductionCanonicalSecondEdgeKernelElement_succ_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin (p - 1)) :
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
    ((firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨k.val + 1, by omega⟩ :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ (k.val + 1) * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
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
  let kNat := k.val + 1
  have hp_gt_one : 1 < p := lt_of_lt_of_le (by decide : 1 < 2) hp
  haveI : Fact (1 < p) := ⟨hp_gt_one⟩
  have hkpos : 0 < kNat := by
    dsimp [kNat]
    omega
  have hklt : kNat < p := by
    dsimp [kNat]
    omega
  have hkval : ((kNat : ZMod p)).val = kNat :=
    ZMod.val_natCast_of_lt hklt
  have hsubval : ((kNat : ZMod p) - 1).val = kNat - 1 := by
    have hle : (1 : ZMod p).val ≤ (kNat : ZMod p).val := by
      rw [hkval, ZMod.val_one]
      exact Nat.succ_le_iff.mpr hkpos
    rw [ZMod.val_sub hle, hkval, ZMod.val_one]
  have hkSub : kNat - 1 = k.val := by
    omega
  have hsubval' :
      (((k.val + 1 : ℕ) : ZMod p) - 1).val = k.val := by
    simpa [kNat, hkSub] using hsubval
  dsimp [firstReductionCanonicalSecondEdgeKernelElement,
    firstReductionCanonicalDistinguishedGenerator]
  rw [hsubval']
theorem firstReductionCanonicalSecondDescendingNamedCycle_eq_secondPowerKernel
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let n := p - 1
    firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ *
      (List.ofFn (fun i : Fin n =>
        firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨n - i.val, by omega⟩)).prod =
        firstReductionCanonicalSecondPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let n := p - 1
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
  apply Subtype.ext
  change
    ((firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) *
      (((List.ofFn (fun i : Fin n =>
        firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨n - i.val, by omega⟩)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
      ((firstReductionCanonicalSecondPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen : φ.ker) :
            FreeGroup (FuchsianGenerator σ))
  have hprodCoe :
      (((List.ofFn (fun i : Fin n =>
        firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨n - i.val, by omega⟩)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun i : Fin n =>
          ((firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
            ⟨n - i.val, by omega⟩ : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))).prod := by
    change
      φ.ker.subtype
          ((List.ofFn (fun i : Fin n =>
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨n - i.val, by omega⟩)).prod) =
        (List.ofFn (fun i : Fin n =>
          φ.ker.subtype
            (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨n - i.val, by omega⟩))).prod
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [hprodCoe]
  rw [firstReductionCanonicalSecondEdgeKernelElement_zero_coe]
  have htailList :
      (List.ofFn (fun i : Fin n =>
          ((firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
            ⟨n - i.val, by omega⟩ : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))) =
        List.ofFn (fun i : Fin n =>
          (FreeGroup.of x) ^ (n - i.val) * FreeGroup.of y *
            ((FreeGroup.of x) ^ (n - 1 - i.val))⁻¹) := by
    apply List.ofFn_inj.2
    funext i
    simpa [n, σ, φ, x, y] using
      firstReductionCanonicalSecondEdgeKernelElement_descending_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i
  rw [htailList]
  change
    FreeGroup.of y * ((FreeGroup.of x) ^ n)⁻¹ *
        negOneCycleTailProduct (FreeGroup.of x) (FreeGroup.of y) n =
      (FreeGroup.of y) ^ p
  have hn : n + 1 = p := by
    dsimp [n]
    omega
  rw [← hn]
  exact negOneCycleProduct_eq_pow (FreeGroup.of x) (FreeGroup.of y) n
theorem firstReductionCanonicalSecondDescendingNamedCycle_schreierWord_eq_secondPower
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let n := p - 1
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩) *
      (List.ofFn (fun i : Fin n =>
        e.symm
          (firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
            ⟨n - i.val, by omega⟩))).prod =
        e.symm
          (firstReductionCanonicalSecondPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let n := p - 1
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hcycle :
      firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ *
        (List.ofFn (fun i : Fin n =>
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
            ⟨n - i.val, by omega⟩)).prod =
          firstReductionCanonicalSecondPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
    simpa [n] using
      firstReductionCanonicalSecondDescendingNamedCycle_eq_secondPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hmap := congrArg e.symm hcycle
  have htailMap :
      e.symm
          ((List.ofFn (fun i : Fin n =>
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨n - i.val, by omega⟩)).prod) =
        (List.ofFn (fun i : Fin n =>
          e.symm
            (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨n - i.val, by omega⟩))).prod := by
    rw [map_list_prod, List.map_ofFn]
    rfl
  simpa [map_mul, htailMap] using hmap
noncomputable def firstReductionCanonicalTailKernelElement
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    φ.ker := by
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
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  refine
    ⟨(FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
        ((FreeGroup.of x) ^ k.val)⁻¹, ?_⟩
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
    change
      firstReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          (FreeGroup.of
            (FuchsianGenerator.elliptic
              (firstReductionCanonicalSourceTailIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j))) = 1
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one]
    omega
  rw [MonoidHom.mem_ker]
  change
    φ ((FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
  simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]
private theorem firstReductionCanonical_distinguished_schreierGenerator_eq_one_of_succ_lt
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    {k : ℕ} (hk : k + 1 < p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    schreierGenerator hT ((FreeGroup.of x) ^ k) x = 1 := by
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
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  simpa [firstReductionCanonicalSchreierTransversal, φ, x] using
    cyclicQuotient_distinguished_schreierGenerator_eq_one_of_succ_lt φ x hx hk
private theorem firstReductionCanonical_distinguished_schreierGenerator_wrap_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    schreierGenerator hT ((FreeGroup.of x) ^ (p - 1)) x =
      firstReductionCanonicalFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
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
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  simpa [firstReductionCanonicalSchreierTransversal,
    firstReductionCanonicalFirstPowerKernel, φ, x] using
    cyclicQuotient_distinguished_schreierGenerator_wrap_eq φ x hx
theorem firstReductionCanonicalFirstPowerKernel_mem_schreierGeneratorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalFirstPowerKernel
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let T :=
    firstReductionCanonicalSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  refine ⟨(FreeGroup.of x) ^ (p - 1), ?_, x, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
    simpa [T, firstReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := p - 1) (by omega)
  · simpa [hT, σ, φ, x, firstReductionCanonicalDistinguishedGenerator] using
      (firstReductionCanonical_distinguished_schreierGenerator_wrap_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) h
    have hpow : (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ p = 1 := by
      simpa [σ, φ, x, firstReductionCanonicalDistinguishedGenerator,
        firstReductionCanonicalFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen] using hval
    exact freeGroup_of_pow_ne_one x (by omega) hpow
private theorem firstReductionCanonical_second_schreierGenerator_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k := by
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
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
  simpa [firstReductionCanonicalSchreierTransversal,
    firstReductionCanonicalSecondEdgeKernelElement, φ, x, y] using
    cyclicQuotient_negOneImage_schreierGenerator_eq φ x y hx hy k
theorem firstReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalSecondEdgeKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
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
  let T :=
    firstReductionCanonicalSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  refine ⟨(FreeGroup.of x) ^ k.val, ?_, y, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
    simpa [T, firstReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) k.isLt
  · simpa [hT, σ, φ, x, y, firstReductionCanonicalDistinguishedGenerator] using
      (firstReductionCanonical_second_schreierGenerator_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) h
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hsecondWord :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ = 1 := by
      simpa [φ, x, y, r, firstReductionCanonicalSecondEdgeKernelElement,
        firstReductionCanonicalDistinguishedGenerator] using hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hxne : x ≠ y := by
      intro hEq
      simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceOneIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, zero_ne_one, x, y] at hEq
    have hmap := congrArg (FreeGroup.lift χ) hsecondWord
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, map_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
theorem firstReductionCanonicalSecondEdgeKernelElement_inj
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    {k₁ k₂ : Fin p}
    (hEq :
      firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k₁ =
        firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k₂) :
    k₁ = k₂ := by
  classical
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
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  let r₁ : ℕ := ((k₁.val : ZMod p) - 1).val
  let r₂ : ℕ := ((k₂.val : ZMod p) - 1).val
  have hleft :
      ((firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k₁ : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r₁)⁻¹ := by
    simp only [firstReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r₁]
  have hright :
      ((firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k₂ : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r₂)⁻¹ := by
    simp only [firstReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r₂]
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r₁)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r₂)⁻¹ := by
    simpa [hleft, hright] using hval
  have hxne : x ≠ y := by
    intro hEq'
    simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceOneIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, zero_ne_one, x, y] at hEq'
  exact Fin.ext
    (freeGroup_pow_mul_of_mul_pow_inv_left_exponent_eq_of_eq hxne hword)
private theorem firstReductionCanonical_tail_schreierGenerator_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) (tailGen j) =
      firstReductionCanonicalTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k := by
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
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
    omega
  simpa [firstReductionCanonicalSchreierTransversal,
    firstReductionCanonicalTailKernelElement, φ, x, tailGen] using
    cyclicQuotient_trivialImage_schreierGenerator_eq_conj φ x (tailGen j) hx htailMap k
theorem firstReductionCanonicalTailKernelElement_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      firstReductionCanonicalDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    ((firstReductionCanonicalTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
  classical
  dsimp
  simp only [firstReductionCanonicalTailKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq]
theorem firstReductionCanonicalTailKernelElement_inj
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    {j₁ j₂ : Fin tailLen} {k₁ k₂ : Fin p}
    (hEq :
      firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j₁ k₁ =
        firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j₂ k₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  have hleft :
      ((firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j₁ k₁ : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of (tailGen j₁) *
          ((FreeGroup.of x) ^ k₁.val)⁻¹ := by
    simpa [σ, φ, x, tailGen] using
      firstReductionCanonicalTailKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j₁ k₁
  have hright :
      ((firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j₂ k₂ : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of (tailGen j₂) *
          ((FreeGroup.of x) ^ k₂.val)⁻¹ := by
    simpa [σ, φ, x, tailGen] using
      firstReductionCanonicalTailKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j₂ k₂
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
          FreeGroup.of (tailGen j₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val *
          FreeGroup.of (tailGen j₂) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val)⁻¹ := by
    simpa [hleft, hright] using hval
  have hxne₁ : x ≠ tailGen j₁ := by
    intro hEq'
    simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x, tailGen] at hEq'
    omega
  have hxne₂ : x ≠ tailGen j₂ := by
    intro hEq'
    simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x, tailGen] at hEq'
    omega
  have hlen := congrArg
    (fun w : FreeGroup (FuchsianGenerator σ) => (FreeGroup.toWord w).length) hword
  change
    (FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
        FreeGroup.of (tailGen j₁) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹)).length =
    (FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val *
        FreeGroup.of (tailGen j₂) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val)⁻¹)).length at hlen
  rw [freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₁ k₁.val k₁.val,
    freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₂ k₂.val k₂.val] at hlen
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_replicate,
  List.length_cons] at hlen
  have hk : k₁ = k₂ := by
    ext
    omega
  subst k₂
  have hwords := congrArg
    (fun w : FreeGroup (FuchsianGenerator σ) => FreeGroup.toWord w) hword
  change
    FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
        FreeGroup.of (tailGen j₁) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹) =
    FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
        FreeGroup.of (tailGen j₂) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹) at hwords
  rw [freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₁ k₁.val k₁.val,
    freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₂ k₁.val k₁.val] at hwords
  have hdrop := congrArg
    (fun L : List (FuchsianGenerator σ × Bool) => L.drop k₁.val) hwords
  have hhead := congrArg List.head? hdrop
  have htailGenEq : tailGen j₁ = tailGen j₂ := by
    simpa using hhead
  have hjVal : j₁.val = j₂.val := by
    simp only [firstReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq,
  Nat.add_left_cancel_iff, tailGen] at htailGenEq
    omega
  exact ⟨Fin.ext hjVal, rfl⟩
theorem firstReductionCanonicalTailKernelElement_mem_schreierGeneratorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalTailKernelElement
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  let T :=
    firstReductionCanonicalSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  refine ⟨(FreeGroup.of x) ^ k.val, ?_, tailGen j, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
    simpa [T, firstReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) k.isLt
  · simpa [hT, σ, φ, x, tailGen] using
      (firstReductionCanonical_tail_schreierGenerator_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) h
    have htailWord :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ = 1 := by
      simp only [firstReductionCanonicalTailKernelElement_coe m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k,
  OneMemClass.coe_one, conj_eq_one_iff, FreeGroup.of_ne_one, φ] at hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun y => if y = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hxne : x ≠ tailGen j := by
      intro hEq
      simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x, tailGen] at hEq
      omega
    have hmap := congrArg (FreeGroup.lift χ) htailWord
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, map_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
theorem firstReductionCanonical_schreierGeneratorSet_cases
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ z : ↥(schreierGeneratorSet hT),
      (z : φ.ker) =
          firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen ∨
        (∃ k : Fin p,
          (z : φ.ker) =
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k) ∨
        (∃ j : Fin tailLen, ∃ k : Fin p,
          (z : φ.ker) =
            firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    firstReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  intro z
  rcases z.property with ⟨t, ht, g, hz, hne⟩
  have htPower : ∃ k : Fin p, t = (FreeGroup.of x) ^ k.val := by
    simpa [hT, firstReductionCanonicalSchreierTransversal, φ, x] using
      (mem_range_cyclicQuotientRightRep_iff_generatorPower φ (x := x) hx).1 ht
  rcases htPower with ⟨k, rfl⟩
  cases g with
  | elliptic i =>
      by_cases h0 : i.val = 0
      · have hi :
            i =
              firstReductionCanonicalSourceZeroIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
          ext
          simpa [firstReductionCanonicalSourceZeroIndex] using h0
        subst i
        by_cases hwrap : k.val + 1 < p
        · have hgen :
              schreierGenerator hT ((FreeGroup.of x) ^ k.val) x = 1 := by
            simpa [hT, σ, φ, x, firstReductionCanonicalDistinguishedGenerator] using
              firstReductionCanonical_distinguished_schreierGenerator_eq_one_of_succ_lt
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hwrap
          exact False.elim (hne (by simpa [hz, x] using hgen))
        · have hk : k.val = p - 1 := by
            have hklt := k.isLt
            omega
          left
          calc
            (z : φ.ker) = schreierGenerator hT ((FreeGroup.of x) ^ k.val) x := by
              simpa [x, firstReductionCanonicalDistinguishedGenerator] using hz
            _ = schreierGenerator hT ((FreeGroup.of x) ^ (p - 1)) x := by
              rw [hk]
            _ =
                firstReductionCanonicalFirstPowerKernel
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
              simpa [hT, σ, φ, x, firstReductionCanonicalDistinguishedGenerator] using
                firstReductionCanonical_distinguished_schreierGenerator_wrap_eq
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      · by_cases h1 : i.val = 1
        · have hi :
              i =
                firstReductionCanonicalSourceOneIndex
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
            ext
            simpa [firstReductionCanonicalSourceOneIndex] using h1
          subst i
          right
          left
          refine ⟨k, ?_⟩
          calc
            (z : φ.ker) =
                schreierGenerator hT ((FreeGroup.of x) ^ k.val)
                  (FuchsianGenerator.elliptic
                    (firstReductionCanonicalSourceOneIndex
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) := hz
            _ =
                firstReductionCanonicalSecondEdgeKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k := by
              simpa [hT, σ, φ, x, firstReductionCanonicalDistinguishedGenerator] using
                firstReductionCanonical_second_schreierGenerator_eq
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k
        · right
          right
          let j : Fin tailLen := ⟨i.val - 2, by
            have hiLt : i.val < 2 + tailLen := by
              simp only [firstReductionCanonicalSourceSignature] at i
              exact i.isLt
            omega⟩
          have hiTail :
              i =
                firstReductionCanonicalSourceTailIndex
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j := by
            ext
            simp only [firstReductionCanonicalSourceTailIndex, j]
            omega
          refine ⟨j, k, ?_⟩
          have hzTail :
              (z : φ.ker) =
                schreierGenerator hT ((FreeGroup.of x) ^ k.val)
                  (FuchsianGenerator.elliptic
                    (firstReductionCanonicalSourceTailIndex
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)) := by
            simpa [hiTail] using hz
          calc
            (z : φ.ker) =
                schreierGenerator hT ((FreeGroup.of x) ^ k.val)
                  (FuchsianGenerator.elliptic
                    (firstReductionCanonicalSourceTailIndex
                      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)) := hzTail
            _ =
                firstReductionCanonicalTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k := by
              simpa [hT, σ, φ, x, firstReductionCanonicalDistinguishedGenerator] using
                firstReductionCanonical_tail_schreierGenerator_eq
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k
  | surfaceA i =>
      exact Fin.elim0 (by
        simpa [σ, firstReductionCanonicalSourceSignature] using i)
  | surfaceB i =>
      exact Fin.elim0 (by
        simpa [σ, firstReductionCanonicalSourceSignature] using i)
end FenchelNielsen
