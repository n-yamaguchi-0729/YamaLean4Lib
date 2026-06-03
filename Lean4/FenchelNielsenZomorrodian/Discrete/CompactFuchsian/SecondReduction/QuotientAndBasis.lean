import FenchelNielsenZomorrodian.Discrete.Singerman.CyclicProductIdentities
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.OrderedTargetSignature

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/QuotientAndBasis.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen
noncomputable def secondReductionCanonicalSourceFreeQuotientHom
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    FreeGroup (FuchsianGenerator σ) →* Multiplicative (ZMod q) := by
  classical
  dsimp
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  exact
    FreeGroup.lift
      (ellipticQuotientGeneratorImage σ
        (secondReductionCanonicalSourceQuotientImage
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
@[simp 900] theorem secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        (FreeGroup.of
          (FuchsianGenerator.elliptic
            (secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩))) =
      Multiplicative.ofAdd (1 : ZMod q) := by
  classical
  dsimp
  simp only [secondReductionCanonicalSourceFreeQuotientHom, Lean.Elab.WF.paramLet, id_eq,
  secondReductionCanonicalSourceMiddleIndex, add_zero, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, ↓reduceIte]
theorem secondReductionCanonicalSourceFreeQuotientHom_respects_relators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ r ∈ relators σ,
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r = 1 := by
  classical
  dsimp
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  simpa [secondReductionCanonicalSourceFreeQuotientHom, σ] using
    ellipticQuotientGeneratorImage_respects_relators σ
      (secondReductionCanonicalSourceQuotientImage
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (secondReductionCanonicalSourceQuotientImage_pow
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (secondReductionCanonicalSourceQuotientImage_prod
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
noncomputable abbrev secondReductionCanonicalDistinguishedGenerator
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    FuchsianGenerator
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) :=
  FuchsianGenerator.elliptic
    (secondReductionCanonicalSourceMiddleIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩)
noncomputable def secondReductionCanonicalSchreierTransversal
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    Set (FreeGroup (FuchsianGenerator σ)) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  exact Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
theorem secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    IsRightSchreierTransversal φ.ker
      (secondReductionCanonicalSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  simpa [secondReductionCanonicalSchreierTransversal, σ, φ, x] using
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
noncomputable def secondReductionCanonicalSchreierBasisEquiv
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  simpa [secondReductionCanonicalSchreierTransversal, σ, φ, x] using
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
@[simp 900] theorem secondReductionCanonicalSchreierBasisEquiv_symm_apply
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ z : ↥(schreierGeneratorSet hT),
      (secondReductionCanonicalSchreierBasisEquiv
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm (z : φ.ker) =
        (FreeGroup.of z)⁻¹ := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  intro z
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  apply e.injective
  simp only [secondReductionCanonicalSchreierTransversal, Lean.Elab.WF.paramLet, id_eq,
  secondReductionCanonicalSchreierBasisEquiv, MulEquiv.apply_symm_apply, map_inv,
  freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator_of φ x hx z, inv_inv, e, φ, x]

theorem secondReductionCanonicalSchreierToTarget_mapsRelators_of_source_cases
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (τ : FuchsianSignature)
      (η :
        letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
        let σ :=
          secondReductionCanonicalSourceSignature
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
        let hT :=
          secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup (FuchsianGenerator τ))
      (targetRelators : Set (FreeGroup (FuchsianGenerator τ)))
      (hZero :
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
      let x : FuchsianGenerator σ :=
        secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      let i₀ :=
        secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ∀ k : Fin q,
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
            Subgroup.normalClosure targetRelators)
    (hOne :
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
      let x : FuchsianGenerator σ :=
        secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      let i₁ :=
        secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ∀ k : Fin q,
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
            Subgroup.normalClosure targetRelators)
    (hMiddle :
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
      let x : FuchsianGenerator σ :=
        secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ∀ r : Fin p, ∀ k : Fin q,
        let iMiddle :=
          secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r
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
            Subgroup.normalClosure targetRelators)
    (hTail :
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
      let x : FuchsianGenerator σ :=
        secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ∀ b : Fin p, ∀ j : Fin tailLen, ∀ k : Fin q,
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
            Subgroup.normalClosure targetRelators)
    (hTotal :
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
      let x : FuchsianGenerator σ :=
        secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ∀ k : Fin q,
        η
            (e.symm
              (⟨(FreeGroup.of x) ^ k.val * totalRelation σ *
                  ((FreeGroup.of x) ^ k.val)⁻¹, by
                change φ
                    ((FreeGroup.of x) ^ k.val * totalRelation σ *
                      ((FreeGroup.of x) ^ k.val)⁻¹) = 1
                have hrφ : φ (totalRelation σ) = 1 :=
                  secondReductionCanonicalSourceFreeQuotientHom_respects_relators
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                    (totalRelation σ) (Or.inr rfl)
                simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker)) ∈
            Subgroup.normalClosure targetRelators) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    ∀ r ∈ ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (secondReductionCanonicalSourceQuotientImage
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (rels := relators σ) T),
        η r ∈ Subgroup.normalClosure targetRelators := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  intro r hr
  have hrImage :
      e r ∈
        ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (secondReductionCanonicalSourceQuotientImage
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (rels := relators σ) T := by
    simpa [e] using
      (ReidemeisterSchreier.Discrete.Presentations.mem_freeGroupPullbackRelatorSet_iff (e := e)
        (S := ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (secondReductionCanonicalSourceQuotientImage
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (rels := relators σ) T)
        (y := r)).1 hr
  rcases hrImage with ⟨t, ht, r₀, hr₀, hval⟩
  have htPower : ∃ k : Fin q, t = (FreeGroup.of x) ^ k.val := by
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
            secondReductionCanonicalSourceZeroIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
        ext
        simpa [secondReductionCanonicalSourceZeroIndex] using h0
      subst i
      rw [relator_eq]
      simpa [σ, φ, e, x, tPow] using hZero k
    · by_cases h1 : i.val = 1
      · have hi :
            i =
              secondReductionCanonicalSourceOneIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
          ext
          simpa [secondReductionCanonicalSourceOneIndex] using h1
        subst i
        rw [relator_eq]
        simpa [σ, φ, e, x, tPow] using hOne k
      · by_cases hmid : i.val < 2 + p
        · let rMid : Fin p := ⟨i.val - 2, by omega⟩
          have hiMid :
              i =
                secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail rMid := by
            ext
            simp only [secondReductionCanonicalSourceMiddleIndex, rMid]
            omega
          rw [relator_eq]
          simpa [σ, φ, e, x, tPow, hiMid] using hMiddle rMid k
        · have htailLen_pos : 0 < tailLen := by
            by_contra htl
            have htl0 : tailLen = 0 := Nat.eq_zero_of_not_pos htl
            have hlt : i.val < 2 + p := by
              have hi_lt : i.val < 2 + (p + tailLen * p) := by
                change i.val < 2 + (p + tailLen * p)
                exact i.isLt
              have hprod0 : tailLen * p = 0 := by
                rw [htl0]
                simp only [zero_mul]
              omega
            exact hmid hlt
          let n : ℕ := i.val - (2 + p)
          have hnlt : n < tailLen * p := by
            have hi_lt : i.val < 2 + (p + tailLen * p) := by
              change i.val < 2 + (p + tailLen * p)
              exact i.isLt
            dsimp [n]
            omega
          let b : Fin p := ⟨n / tailLen, by
            have hdiv : n / tailLen < p := by
              rw [Nat.div_lt_iff_lt_mul htailLen_pos]
              simpa [Nat.mul_comm] using hnlt
            exact hdiv⟩
          let j : Fin tailLen := ⟨n % tailLen, Nat.mod_lt _ htailLen_pos⟩
          have hn_eq : n = b.val * tailLen + j.val := by
            dsimp [b, j]
            rw [Nat.mul_comm, Nat.add_comm]
            exact (Nat.mod_add_div n tailLen).symm
          have hi_val : i.val = 2 + p + b.val * tailLen + j.val := by
            dsimp [n] at hn_eq
            omega
          have hiTail :
              i =
                secondReductionCanonicalSourceTailIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j := by
            ext
            simp only [hi_val, secondReductionCanonicalSourceTailIndex]
          rw [relator_eq]
          simpa [σ, φ, e, x, tPow, hiTail] using hTail b j k
  · rw [relator_eq]
    simpa [σ, φ, e, x, tPow] using hTotal k

abbrev SecondReductionCanonicalOrderedTargetIndex (tailLen p q : ℕ) :=
  Fin 2 ⊕
    (Fin q × (Fin (p - 2) ⊕ ((Fin p × Fin tailLen) ⊕ Fin 2)))

def secondReductionTransportIndexEquivCanonicalOrderedTargetIndex
    (tailLen p q : ℕ) :
    SecondReductionTransportIndex tailLen p q ≃
      SecondReductionCanonicalOrderedTargetIndex tailLen p q where
  toFun
    | ⟨.inl h, k⟩ => .inr (k, .inr (.inr h))
    | ⟨.inr (.inl d), _⟩ => .inl d
    | ⟨.inr (.inr (.inl r)), k⟩ => .inr (k, .inl r)
    | ⟨.inr (.inr (.inr jk)), k⟩ => .inr (k, .inr (.inl (jk.2, jk.1)))
  invFun
    | .inl d => ⟨.inr (.inl d), (0 : Fin 1)⟩
    | .inr (k, .inl r) => ⟨.inr (.inr (.inl r)), k⟩
    | .inr (k, .inr (.inl bj)) => ⟨.inr (.inr (.inr (bj.2, bj.1))), k⟩
    | .inr (k, .inr (.inr h)) => ⟨.inl h, k⟩
  left_inv x := by
    rcases x with ⟨src, k⟩
    cases src with
    | inl _ => rfl
    | inr rest =>
        cases rest with
        | inl _ =>
            fin_cases k
            rfl
        | inr rest =>
            cases rest with
            | inl _ => rfl
            | inr _ => rfl
  right_inv x := by
    cases x with
    | inl _ => rfl
    | inr rest =>
        rcases rest with ⟨_, block⟩
        cases block with
        | inl _ => rfl
        | inr rest =>
            cases rest with
            | inl bj =>
                rcases bj with ⟨_, _⟩
                rfl
            | inr _ => rfl
def secondReductionCanonicalOrderedTargetBlockIndexEquivFin
    (tailLen p : ℕ) :
    (Fin (p - 2) ⊕ ((Fin p × Fin tailLen) ⊕ Fin 2)) ≃
      Fin (secondReductionCanonicalOrderedTargetBlockLen tailLen p) :=
  ((Equiv.sumCongr (Equiv.refl (Fin (p - 2)))
      ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans
        finSumFinEquiv)).trans finSumFinEquiv).trans
    (finCongr (by
      dsimp [secondReductionCanonicalOrderedTargetBlockLen]
      omega))
def secondReductionCanonicalOrderedTargetIndexEquivFin
    (tailLen p q : ℕ) :
    SecondReductionCanonicalOrderedTargetIndex tailLen p q ≃
      Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2))
      ((Equiv.prodCongr (Equiv.refl (Fin q))
          (secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p)).trans
        finProdFinEquiv)).trans
    finSumFinEquiv
def secondReductionTransportIndexEquivCanonicalOrderedTargetFin
    (tailLen p q : ℕ) :
    SecondReductionTransportIndex tailLen p q ≃
      Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  (secondReductionTransportIndexEquivCanonicalOrderedTargetIndex tailLen p q).trans
    (secondReductionCanonicalOrderedTargetIndexEquivFin tailLen p q)
private theorem secondReduction_negOneCycleSegmentProduct_eq {G : Type*} [Group G]
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
      rw [secondReduction_negOneCycleSegmentProduct_eq x y (n - 1) l hl]
      have hnl : n - 1 - l = n - (l + 1) := by omega
      rw [hnl]
      rw [pow_succ']
      group
theorem secondReduction_list_ofFn_desc_split {α : Type*} {p k : ℕ} (hk : k < p)
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
theorem secondReduction_rotatedBlockProduct_mem_normalClosure
    {G : Type*} [Group G] {R : Set G}
    (x y h₀ h₁ : G) {middleLen tailLen p q : ℕ}
    (middle : Fin middleLen → G) (tail : Fin p → Fin tailLen → G)
    (h :
      x * y *
          ((List.ofFn middle).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen => tail b j)).prod)).prod *
            h₀ * h₁) ∈
        Subgroup.normalClosure R) :
    x ^ q * y ^ q *
        (List.ofFn (fun k : Fin q =>
          (List.ofFn (fun r : Fin middleLen =>
            x ^ k.val * middle r * (x ^ k.val)⁻¹)).prod *
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              x ^ k.val * tail b j * (x ^ k.val)⁻¹)).prod)).prod *
          (x ^ k.val * h₀ * (x ^ k.val)⁻¹) *
          (x ^ k.val * h₁ * (x ^ k.val)⁻¹))).prod ∈
      Subgroup.normalClosure R := by
  classical
  let N : Subgroup G := Subgroup.normalClosure R
  let Q : G →* G ⧸ N := QuotientGroup.mk' N
  let z : G :=
    (List.ofFn middle).prod *
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen => tail b j)).prod)).prod *
      h₀ * h₁
  have hzRel : Q x * Q y * Q z = 1 := by
    have hq : Q (x * y * z) = 1 :=
      (QuotientGroup.eq_one_iff (N := N) (x * y * z)).2 (by simpa [N, z] using h)
    simpa [Q, z, map_mul] using hq
  have hcycle :
      Q x ^ q * Q y ^ q * conjugateRangeProduct (Q x) (Q z) q = 1 :=
    pow_mul_pow_mul_conjugateRangeProduct_eq_one_of_mul_eq_one (Q x) (Q y) (Q z) q hzRel
  have hblock :
      Q
          (x ^ q * y ^ q *
            (List.ofFn (fun k : Fin q =>
              (List.ofFn (fun r : Fin middleLen =>
                x ^ k.val * middle r * (x ^ k.val)⁻¹)).prod *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  x ^ k.val * tail b j * (x ^ k.val)⁻¹)).prod)).prod *
              (x ^ k.val * h₀ * (x ^ k.val)⁻¹) *
              (x ^ k.val * h₁ * (x ^ k.val)⁻¹))).prod) =
        Q x ^ q * Q y ^ q * conjugateRangeProduct (Q x) (Q z) q := by
    simp only [map_mul, map_pow, map_list_prod, List.map_ofFn]
    congr 2
    rw [← List.ofFn_eq_map]
    apply List.ofFn_inj.2
    funext k
    have hmiddle :
        (List.ofFn (fun r : Fin middleLen =>
          Q x ^ k.val * Q (middle r) * (Q x ^ k.val)⁻¹)).prod =
          Q x ^ k.val * (List.ofFn (fun r : Fin middleLen => Q (middle r))).prod *
            (Q x ^ k.val)⁻¹ := by
      simpa using
        (ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod (Q x ^ k.val)
          (List.ofFn (fun r : Fin middleLen => Q (middle r)))).symm
    have htail :
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            Q x ^ k.val * Q (tail b j) * (Q x ^ k.val)⁻¹)).prod)).prod =
          Q x ^ k.val *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen => Q (tail b j))).prod)).prod *
            (Q x ^ k.val)⁻¹ := by
      simpa using
        ReidemeisterSchreier.Discrete.Presentations.nested_conjugate_list_prod (Q x ^ k.val)
          (fun b : Fin p => fun j : Fin tailLen => Q (tail b j))
    simp only [Function.comp_apply, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_pow, map_inv,
  hmiddle, htail, conj_mul, z]
  have htarget :
      Q
          (x ^ q * y ^ q *
            (List.ofFn (fun k : Fin q =>
              (List.ofFn (fun r : Fin middleLen =>
                x ^ k.val * middle r * (x ^ k.val)⁻¹)).prod *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  x ^ k.val * tail b j * (x ^ k.val)⁻¹)).prod)).prod *
              (x ^ k.val * h₀ * (x ^ k.val)⁻¹) *
              (x ^ k.val * h₁ * (x ^ k.val)⁻¹))).prod) = 1 := by
    rw [hblock, hcycle]
  exact
    (QuotientGroup.eq_one_iff
      (N := N)
      (x ^ q * y ^ q *
        (List.ofFn (fun k : Fin q =>
          (List.ofFn (fun r : Fin middleLen =>
            x ^ k.val * middle r * (x ^ k.val)⁻¹)).prod *
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              x ^ k.val * tail b j * (x ^ k.val)⁻¹)).prod)).prod *
          (x ^ k.val * h₀ * (x ^ k.val)⁻¹) *
          (x ^ k.val * h₁ * (x ^ k.val)⁻¹))).prod)).1
      (by simpa [N, Q] using htarget)
def secondReductionCanonicalTransportDistinguishedIndex
    (tailLen p q : ℕ) (d : Fin 2) :
    SecondReductionTransportIndex tailLen p q :=
  ⟨Sum.inr (Sum.inl d), ⟨0, by simp only [secondReductionSourceCycleCount, zero_lt_one]⟩⟩
def secondReductionCanonicalTransportHeadIndex
    (tailLen p q : ℕ) (h : Fin 2) (k : Fin q) :
    SecondReductionTransportIndex tailLen p q :=
  ⟨Sum.inl h, by simpa [secondReductionSourceCycleCount] using k⟩
def secondReductionCanonicalTransportMiddleRestIndex
    (tailLen p q : ℕ) (r : Fin (p - 2)) (k : Fin q) :
    SecondReductionTransportIndex tailLen p q :=
  ⟨Sum.inr (Sum.inr (Sum.inl r)), by simpa [secondReductionSourceCycleCount] using k⟩
def secondReductionCanonicalTransportTailIndex
    (tailLen p q : ℕ) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    SecondReductionTransportIndex tailLen p q :=
  ⟨Sum.inr (Sum.inr (Sum.inr (j, b))), by simpa [secondReductionSourceCycleCount] using k⟩
noncomputable def secondReductionCanonicalTransportTargetWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    SecondReductionTransportIndex tailLen p q →
      FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  intro idx
  exact xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
@[local simp]
theorem secondReduction_forward_finProdFinEquiv_val
    {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i, j) : Fin (m * n)).val = i.val * n + j.val := by
  simp only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm]
theorem secondReductionTransportIndexEquivCanonicalOrderedTargetFin_distinguished
    (tailLen p q : ℕ) (d : Fin 2) :
    secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q d) =
      secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q d := by
  ext
  change
    (finSumFinEquiv (Sum.inl d) :
        Fin (2 + q * secondReductionCanonicalOrderedTargetBlockLen tailLen p)).val =
      (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q d).val
  simp only [finSumFinEquiv_apply_left, Fin.val_castAdd,
  secondReductionCanonicalOrderedTargetDistinguishedIndex]
@[local simp]
theorem
    secondReductionCanonicalOrderedTargetBlockIndexEquivFin_middleRest_val
    (tailLen p : ℕ) (r : Fin (p - 2)) :
    ((secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p) (Sum.inl r)).val =
      r.val := by
  simp only [secondReductionCanonicalOrderedTargetBlockIndexEquivFin, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_refl, Equiv.coe_trans, Sum.map_inl, id_eq, finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast,
  Fin.val_castAdd]
@[local simp]
theorem
    secondReductionCanonicalOrderedTargetBlockIndexEquivFin_tail_val
    (tailLen p : ℕ) (b : Fin p) (j : Fin tailLen) :
    ((secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p)
        (Sum.inr (Sum.inl (b, j)))).val =
      (p - 2) + b.val * tailLen + j.val := by
  simp only [secondReductionCanonicalOrderedTargetBlockLen,
  secondReductionCanonicalOrderedTargetBlockIndexEquivFin, finProdFinEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr, Function.comp_apply, Equiv.coe_fn_mk, Sum.map_inl,
  finSumFinEquiv_apply_left, Fin.castAdd_mk, finSumFinEquiv_apply_right, Fin.natAdd_mk, Nat.add_comm, Nat.add_assoc,
  finCongr_apply, Fin.cast_mk, Nat.mul_comm]
@[local simp]
theorem
    secondReductionCanonicalOrderedTargetBlockIndexEquivFin_head_val
    (tailLen p : ℕ) (h : Fin 2) :
    ((secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p)
        (Sum.inr (Sum.inr h))).val =
      (p - 2) + p * tailLen + h.val := by
  simp only [secondReductionCanonicalOrderedTargetBlockLen,
  secondReductionCanonicalOrderedTargetBlockIndexEquivFin, finProdFinEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr, Function.comp_apply, Equiv.coe_fn_mk, id_eq,
  finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_natAdd, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]
theorem secondReductionTransportIndexEquivCanonicalOrderedTargetFin_head
    (tailLen p q : ℕ) (h : Fin 2) (k : Fin q) :
    secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
        (secondReductionCanonicalTransportHeadIndex tailLen p q h k) =
      secondReductionCanonicalOrderedTargetHeadIndex tailLen p q h k := by
  ext
  change
    2 +
        (finProdFinEquiv
          (k, (secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p)
            (Sum.inr (Sum.inr h))) :
          Fin (q * secondReductionCanonicalOrderedTargetBlockLen tailLen p)).val =
      (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q h k).val
  rw [secondReduction_forward_finProdFinEquiv_val]
  simp only [secondReductionCanonicalOrderedTargetBlockIndexEquivFin_head_val,
  secondReductionCanonicalOrderedTargetHeadIndex]
  omega
theorem secondReductionTransportIndexEquivCanonicalOrderedTargetFin_middleRest
    (tailLen p q : ℕ) (r : Fin (p - 2)) (k : Fin q) :
    secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
        (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k) =
      secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k := by
  ext
  change
    2 +
        (finProdFinEquiv
          (k, (secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p)
            (Sum.inl r)) :
          Fin (q * secondReductionCanonicalOrderedTargetBlockLen tailLen p)).val =
      (secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k).val
  rw [secondReduction_forward_finProdFinEquiv_val]
  simp only [secondReductionCanonicalOrderedTargetBlockIndexEquivFin_middleRest_val,
  secondReductionCanonicalOrderedTargetMiddleRestIndex]
  omega
theorem secondReductionTransportIndexEquivCanonicalOrderedTargetFin_tail
    (tailLen p q : ℕ) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
        (secondReductionCanonicalTransportTailIndex tailLen p q b j k) =
      secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k := by
  ext
  change
    2 +
        (finProdFinEquiv
          (k, (secondReductionCanonicalOrderedTargetBlockIndexEquivFin tailLen p)
            (Sum.inr (Sum.inl (b, j)))) :
          Fin (q * secondReductionCanonicalOrderedTargetBlockLen tailLen p)).val =
      (secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k).val
  rw [secondReduction_forward_finProdFinEquiv_val]
  simp only [secondReductionCanonicalOrderedTargetBlockIndexEquivFin_tail_val,
  secondReductionCanonicalOrderedTargetTailIndex]
  omega
private theorem secondReductionCanonicalOrderedTarget_period_transportIndex
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (idx : SecondReductionTransportIndex tailLen p q) :
    (secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q idx) =
      secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail idx := by
  classical
  let υ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  change υ.periods
      (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q idx) =
    secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail idx
  rcases idx with ⟨src, k⟩
  cases src with
  | inl h =>
      have hidx :
          secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q ⟨Sum.inl h, k⟩ =
            secondReductionCanonicalOrderedTargetHeadIndex tailLen p q h k := by
        simpa [secondReductionCanonicalTransportHeadIndex] using
          secondReductionTransportIndexEquivCanonicalOrderedTargetFin_head tailLen p q h k
      rw [hidx]
      fin_cases h
      · simpa [υ, secondReductionTransportPeriods, singermanTransportPeriodsFamily,
          secondReductionSourceTransportPeriods, secondReductionSourceCycleCount, twoPeriods] using
          secondReductionCanonicalOrderedTargetSignature_period_head_zero
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
      · simpa [υ, secondReductionTransportPeriods, singermanTransportPeriodsFamily,
          secondReductionSourceTransportPeriods, secondReductionSourceCycleCount, twoPeriods] using
          secondReductionCanonicalOrderedTargetSignature_period_head_one
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  | inr rest =>
      cases rest with
      | inl d =>
          fin_cases k
          change υ.periods
              (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
                ⟨Sum.inr (Sum.inl d), (0 : Fin 1)⟩) =
            secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail
              ⟨Sum.inr (Sum.inl d), (0 : Fin 1)⟩
          have hidx :
              secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
                  ⟨Sum.inr (Sum.inl d), (0 : Fin 1)⟩ =
                secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q d := by
            simpa [secondReductionCanonicalTransportDistinguishedIndex] using
              secondReductionTransportIndexEquivCanonicalOrderedTargetFin_distinguished tailLen p q d
          rw [hidx]
          fin_cases d <;>
            simp only [Fin.mk_one, Fin.isValue, secondReductionCanonicalOrderedTargetSignature_period_distinguished,
  secondReductionTransportPeriods, singermanTransportPeriodsFamily, secondReductionSourceTransportPeriods, υ]
      | inr rest =>
          cases rest with
          | inl r =>
              have hidx :
                  secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
                      ⟨Sum.inr (Sum.inr (Sum.inl r)), k⟩ =
                    secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k := by
                simpa [secondReductionCanonicalTransportMiddleRestIndex] using
                  secondReductionTransportIndexEquivCanonicalOrderedTargetFin_middleRest
                    tailLen p q r k
              rw [hidx]
              simp only [secondReductionCanonicalOrderedTargetSignature_period_middleRest, secondReductionTransportPeriods,
  singermanTransportPeriodsFamily, secondReductionSourceTransportPeriods, υ]
          | inr jk =>
              rcases jk with ⟨j, b⟩
              have hidx :
                  secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q
                      ⟨Sum.inr (Sum.inr (Sum.inr (j, b))), k⟩ =
                    secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k := by
                simpa [secondReductionCanonicalTransportTailIndex] using
                  secondReductionTransportIndexEquivCanonicalOrderedTargetFin_tail
                    tailLen p q b j k
              rw [hidx]
              simp only [secondReductionCanonicalOrderedTargetSignature_period_tail, secondReductionTransportPeriods,
  singermanTransportPeriodsFamily, secondReductionSourceTransportPeriods, υ]
theorem secondReductionCanonicalOrderedTarget_mulEquiv_transportSignature_exists
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Nonempty
      (FuchsianPresentedGroup
          (secondReductionCanonicalOrderedTargetSignature
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
        ≃*
        FuchsianPresentedGroup
          (secondReductionTransportSignature (p := p) hq
            m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)) := by
  classical
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
      (secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)
      ?_ ?_
      (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q)
      (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) ?_
  · simp only [secondReductionCanonicalOrderedTargetSignature]
  · simp only [secondReductionTransportSignature, familyFuchsianSignature]
  · intro idx
    calc
      (secondReductionCanonicalOrderedTargetSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
          (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q idx) =
        secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail idx := by
          exact
            secondReductionCanonicalOrderedTarget_period_transportIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail idx
      _ =
        (secondReductionTransportSignature (p := p) hq
            m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).periods
          ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx) := by
          simp only [secondReductionTransportSignature, familyFuchsianSignature_periods]
noncomputable def secondReductionCanonicalTransportFinEquivOrderedTargetFin
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Fin
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).numPeriods ≃
      Fin
        (secondReductionCanonicalOrderedTargetSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods := by
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let υ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hτ :
      τ.numPeriods = Fintype.card (SecondReductionTransportIndex tailLen p q) := by
    simp only [secondReductionTransportSignature, familyFuchsianSignature, Fintype.card_sigma, Fintype.card_fin,
  Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, τ]
  have hυ :
      υ.numPeriods = secondReductionCanonicalOrderedTargetNumPeriods tailLen p q := by
    simp only [secondReductionCanonicalOrderedTargetSignature, υ]
  exact
    (finCongr hτ).trans
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)).symm.trans
        ((secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q).trans
          (finCongr hυ.symm)))
theorem secondReductionCanonicalTransportFinEquivOrderedTargetFin_apply
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (idx : SecondReductionTransportIndex tailLen p q) :
    secondReductionCanonicalTransportFinEquivOrderedTargetFin
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx) =
      secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q idx := by
  simp only [secondReductionCanonicalTransportFinEquivOrderedTargetFin, finCongr_refl, Equiv.trans_refl,
  Equiv.refl_trans, Equiv.trans_apply]
  exact congrArg (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q)
    (Equiv.symm_apply_apply
      (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
noncomputable def secondReductionCanonicalTransportGeneratorEquivOrderedTarget
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    FuchsianGenerator
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail) ≃
      FuchsianGenerator
        (secondReductionCanonicalOrderedTargetSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) where
  toFun
    | .elliptic i =>
        .elliptic
          (secondReductionCanonicalTransportFinEquivOrderedTargetFin
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i)
    | .surfaceA j =>
        Fin.elim0 (by
          simpa [secondReductionTransportSignature, familyFuchsianSignature] using j)
    | .surfaceB j =>
        Fin.elim0 (by
          simpa [secondReductionTransportSignature, familyFuchsianSignature] using j)
  invFun
    | .elliptic i =>
        .elliptic
          ((secondReductionCanonicalTransportFinEquivOrderedTargetFin
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm i)
    | .surfaceA j =>
        Fin.elim0 (by
          simpa [secondReductionCanonicalOrderedTargetSignature] using j)
    | .surfaceB j =>
        Fin.elim0 (by
          simpa [secondReductionCanonicalOrderedTargetSignature] using j)
  left_inv := by
    intro x
    cases x with
    | elliptic i =>
        simp only
        congr
        exact Equiv.symm_apply_apply
          (secondReductionCanonicalTransportFinEquivOrderedTargetFin
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) i
    | surfaceA j =>
        exact Fin.elim0 (by
          simpa [secondReductionTransportSignature, familyFuchsianSignature] using j)
    | surfaceB j =>
        exact Fin.elim0 (by
          simpa [secondReductionTransportSignature, familyFuchsianSignature] using j)
  right_inv := by
    intro x
    cases x with
    | elliptic i =>
        simp only
        congr
        exact Equiv.apply_symm_apply
          (secondReductionCanonicalTransportFinEquivOrderedTargetFin
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) i
    | surfaceA j =>
        exact Fin.elim0 (by
          simpa [secondReductionCanonicalOrderedTargetSignature] using j)
    | surfaceB j =>
        exact Fin.elim0 (by
          simpa [secondReductionCanonicalOrderedTargetSignature] using j)
theorem secondReductionCanonicalTransportOrdered_period
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i : Fin
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).numPeriods) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    let υ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    τ.periods i =
      υ.periods
        (secondReductionCanonicalTransportFinEquivOrderedTargetFin
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let υ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx := (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)).symm i
  have hi :
      (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx = i :=
    Equiv.apply_symm_apply (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) i
  have hidx :
      secondReductionCanonicalTransportFinEquivOrderedTargetFin
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i =
        secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q idx := by
    rw [← hi]
    exact
      secondReductionCanonicalTransportFinEquivOrderedTargetFin_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail idx
  calc
    τ.periods i =
        secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail idx := by
          rw [← hi]
          simp only [secondReductionTransportSignature, familyFuchsianSignature_periods, τ]
    _ =
        υ.periods
          (secondReductionTransportIndexEquivCanonicalOrderedTargetFin tailLen p q idx) := by
          exact
            (secondReductionCanonicalOrderedTarget_period_transportIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail idx).symm
    _ =
        υ.periods
          (secondReductionCanonicalTransportFinEquivOrderedTargetFin
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i) := by
          rw [hidx]
theorem secondReductionCanonicalTransportOrdered_xWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i : Fin
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).numPeriods) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    let υ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    FreeGroup.freeGroupCongr
        (secondReductionCanonicalTransportGeneratorEquivOrderedTarget
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
        (xWord τ i) =
      xWord υ
        (secondReductionCanonicalTransportFinEquivOrderedTargetFin
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i) := by
  classical
  simp only [secondReductionCanonicalTransportGeneratorEquivOrderedTarget, xWord,
  FreeGroup.freeGroupCongr_apply, Equiv.coe_fn_mk, FreeGroup.map.of]
theorem secondReductionCanonicalTransportOrdered_xWord_symm
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i : Fin
      (secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    let υ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    (FreeGroup.freeGroupCongr
        (secondReductionCanonicalTransportGeneratorEquivOrderedTarget
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)).symm
        (xWord υ i) =
      xWord τ
        ((secondReductionCanonicalTransportFinEquivOrderedTargetFin
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm i) := by
  classical
  dsimp
  change FreeGroup.freeGroupCongr
      (secondReductionCanonicalTransportGeneratorEquivOrderedTarget
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm
      (xWord
        (secondReductionCanonicalOrderedTargetSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) i) =
    xWord
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)
      ((secondReductionCanonicalTransportFinEquivOrderedTargetFin
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm i)
  simp only [secondReductionCanonicalTransportGeneratorEquivOrderedTarget, xWord,
  FreeGroup.freeGroupCongr_apply, Equiv.coe_fn_symm_mk, FreeGroup.map.of]
noncomputable def secondReductionCanonicalFirstPowerKernel
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
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
  refine ⟨(FreeGroup.of x) ^ q, ?_⟩
  rw [MonoidHom.mem_ker, map_pow]
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  rw [hx]
  apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
  simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]
theorem secondReductionCanonicalFirstPowerKernel_coe
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
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
    ((secondReductionCanonicalFirstPowerKernel
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ q := by
  classical
  dsimp
  simp only [secondReductionCanonicalFirstPowerKernel, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, id_eq]
private theorem secondReductionCanonical_distinguished_schreierGenerator_eq_one_of_succ_lt
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    {k : ℕ} (hk : k + 1 < q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    schreierGenerator hT ((FreeGroup.of x) ^ k) x = 1 := by
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
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  simpa [secondReductionCanonicalSchreierTransversal, φ, x] using
    cyclicQuotient_distinguished_schreierGenerator_eq_one_of_succ_lt φ x hx hk
private theorem secondReductionCanonical_distinguished_schreierGenerator_wrap_eq
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
    let x :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    schreierGenerator hT ((FreeGroup.of x) ^ (q - 1)) x =
      secondReductionCanonicalFirstPowerKernel
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
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
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  simpa [secondReductionCanonicalSchreierTransversal,
    secondReductionCanonicalFirstPowerKernel, φ, x] using
    cyclicQuotient_distinguished_schreierGenerator_wrap_eq φ x hx
theorem secondReductionCanonicalFirstPowerKernel_mem_schreierGeneratorSet
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
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    (secondReductionCanonicalFirstPowerKernel
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let T :=
    secondReductionCanonicalSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  refine ⟨(FreeGroup.of x) ^ (q - 1), ?_, x, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
    simpa [T, secondReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := q - 1) (by omega)
  · simpa [hT, σ, φ, x, secondReductionCanonicalDistinguishedGenerator] using
      (secondReductionCanonical_distinguished_schreierGenerator_wrap_eq
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) h
    have hpow : (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ q = 1 := by
      simpa [σ, φ, x, secondReductionCanonicalDistinguishedGenerator,
        secondReductionCanonicalFirstPowerKernel_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail] using hval
    exact freeGroup_of_pow_ne_one x (by omega) hpow
noncomputable def secondReductionCanonicalZeroImageKernelElement
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
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
  refine
    ⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹, ?_⟩
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  rw [MonoidHom.mem_ker]
  simp only [map_mul, map_pow, hy, mul_one, map_inv, mul_inv_cancel]
private theorem secondReductionCanonicalZeroImageKernelElement_coe
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (k : Fin q) :
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
    ((secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
  classical
  dsimp
  simp only [secondReductionCanonicalZeroImageKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, id_eq]
noncomputable def secondReductionCanonicalHeadZeroKernelElement
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceZeroIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  have hy : φ (FreeGroup.of y) = 1 := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y]
  exact
    secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
noncomputable def secondReductionCanonicalHeadOneKernelElement
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceOneIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  have hy : φ (FreeGroup.of y) = 1 := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, y]
  exact
    secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
noncomputable def secondReductionCanonicalMiddleRestZeroKernelElement
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (r : Fin (p - 2)) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
  have hy : φ (FreeGroup.of y) = 1 := by
    have hnot3 : ¬ 2 + (2 + r.val) = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, y]
  exact
    secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
noncomputable def secondReductionCanonicalTailZeroKernelElement
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
  have hy : φ (FreeGroup.of y) = 1 := by
    have hnot2 : ¬ 2 + p + b.val * tailLen + j.val = 2 := by omega
    have hnot3 : ¬ 2 + p + b.val * tailLen + j.val = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, hnot2, ↓reduceIte, hnot3, φ, y]
  exact
      secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
theorem secondReductionCanonicalHeadZeroKernelElement_coe
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
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    ((secondReductionCanonicalHeadZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
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
      (secondReductionCanonicalSourceZeroIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  have hy : φ (FreeGroup.of y) = 1 := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y]
  simpa [σ, φ, x, y, secondReductionCanonicalHeadZeroKernelElement] using
    secondReductionCanonicalZeroImageKernelElement_coe
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
theorem secondReductionCanonicalHeadOneKernelElement_coe
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
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    ((secondReductionCanonicalHeadOneKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
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
      (secondReductionCanonicalSourceOneIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  have hy : φ (FreeGroup.of y) = 1 := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, y]
  simpa [σ, φ, x, y, secondReductionCanonicalHeadOneKernelElement] using
    secondReductionCanonicalZeroImageKernelElement_coe
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
theorem secondReductionCanonicalMiddleRestZeroKernelElement_coe
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
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
    ((secondReductionCanonicalMiddleRestZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
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
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
  have hy : φ (FreeGroup.of y) = 1 := by
    have hnot3 : ¬ 2 + (2 + r.val) = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, y]
  simpa [σ, φ, x, y, secondReductionCanonicalMiddleRestZeroKernelElement] using
    secondReductionCanonicalZeroImageKernelElement_coe
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
theorem secondReductionCanonicalTailZeroKernelElement_coe
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
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceTailIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
    ((secondReductionCanonicalTailZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y *
        ((FreeGroup.of x) ^ k.val)⁻¹ := by
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
      (secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
  have hy : φ (FreeGroup.of y) = 1 := by
    have hnot2 : ¬ 2 + p + b.val * tailLen + j.val = 2 := by omega
    have hnot3 : ¬ 2 + p + b.val * tailLen + j.val = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, hnot2, ↓reduceIte, hnot3, φ, y]
  simpa [σ, φ, x, y, secondReductionCanonicalTailZeroKernelElement] using
    secondReductionCanonicalZeroImageKernelElement_coe
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
theorem secondReductionCanonicalZeroImageKernelElement_inj
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    {k₁ k₂ : Fin q}
    (hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y)
    (hEq :
      secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k₁ =
        secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k₂) :
    k₁ = k₂ := by
  classical
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
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  have hleft :
      ((secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k₁ :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ k₁.val)⁻¹ := by
    simpa [σ, φ, x] using
      secondReductionCanonicalZeroImageKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k₁
  have hright :
      ((secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k₂ :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ k₂.val)⁻¹ := by
    simpa [σ, φ, x] using
      secondReductionCanonicalZeroImageKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k₂
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val)⁻¹ := by
    simpa [hleft, hright] using hval
  exact Fin.ext
    (freeGroup_pow_mul_of_mul_pow_inv_left_exponent_eq_of_eq
      (by simpa [x] using hxy) hword)
theorem secondReductionCanonicalZeroImageKernelElement_ne_firstPower
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (k : Fin q)
    (hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y) :
    secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k ≠
      secondReductionCanonicalFirstPowerKernel
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
  classical
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
  intro hEq
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  have hleft :
      ((secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ k.val)⁻¹ := by
    simpa [σ, φ, x] using
      secondReductionCanonicalZeroImageKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
  have hright :
      ((secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ q := by
    simpa [σ, φ, x] using
      secondReductionCanonicalFirstPowerKernel_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ q := by
    simpa [hleft, hright] using hval
  let χ : FuchsianGenerator σ → Multiplicative ℤ :=
    fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
  have hxne : x ≠ y := by
    simpa [x] using hxy
  have hmap := congrArg (FreeGroup.lift χ) hword
  simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
private theorem secondReductionCanonical_zeroImage_schreierGenerator_eq
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k := by
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
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  simpa [secondReductionCanonicalSchreierTransversal,
    secondReductionCanonicalZeroImageKernelElement, φ, x] using
    cyclicQuotient_trivialImage_schreierGenerator_eq_conj φ x y hx hy k
theorem secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (k : Fin q)
    (hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    (secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let T :=
    secondReductionCanonicalSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  refine ⟨(FreeGroup.of x) ^ k.val, ?_, y, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
    simpa [T, secondReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) k.isLt
  · simpa [hT, σ, φ, x] using
      (secondReductionCanonical_zeroImage_schreierGenerator_eq
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) h
    have hzeroWord :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ = 1 := by
      simp only [secondReductionCanonicalZeroImageKernelElement_coe m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy
      k,
  OneMemClass.coe_one, conj_eq_one_iff, FreeGroup.of_ne_one, φ] at hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hxne : x ≠ y := by
      simpa [x] using hxy
    have hmap := congrArg (FreeGroup.lift χ) hzeroWord
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, map_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
theorem secondReductionCanonicalHeadZeroKernelElement_mem_schreierGeneratorSet
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    let hy : φ (FreeGroup.of y) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y]
    (secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceZeroIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  have hy : φ (FreeGroup.of y) = 1 := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y]
  have hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceZeroIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq,
  OfNat.ofNat_ne_zero, y] at hEq
  simpa [σ, φ, y, hy] using
    secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy
theorem secondReductionCanonicalHeadOneKernelElement_mem_schreierGeneratorSet
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    let hy : φ (FreeGroup.of y) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, y]
    (secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceOneIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  have hy : φ (FreeGroup.of y) = 1 := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, y]
  have hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceOneIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq,
  OfNat.ofNat_ne_one, y] at hEq
  simpa [σ, φ, y, hy] using
    secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy
theorem secondReductionCanonicalMiddleZeroKernelElement_mem_schreierGeneratorSet
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (r : Fin (p - 2)) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
    let hy : φ (FreeGroup.of y) = 1 := by
      have hnot3 : ¬ 2 + (2 + r.val) = 3 := by omega
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, y]
    (secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
  have hy : φ (FreeGroup.of y) = 1 := by
    have hnot3 : ¬ 2 + (2 + r.val) = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, y]
  have hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, Nat.left_eq_add, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
  false_and, y] at hEq
  simpa [σ, φ, y, hy] using
    secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy
theorem secondReductionCanonicalTailZeroKernelElement_mem_schreierGeneratorSet
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceTailIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
    let hy : φ (FreeGroup.of y) = 1 := by
      have hnot2 : ¬ 2 + p + b.val * tailLen + j.val = 2 := by omega
      have hnot3 : ¬ 2 + p + b.val * tailLen + j.val = 3 := by omega
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, hnot2, ↓reduceIte, hnot3, φ, y]
    (secondReductionCanonicalZeroImageKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
  have hy : φ (FreeGroup.of y) = 1 := by
    have hnot2 : ¬ 2 + p + b.val * tailLen + j.val = 2 := by omega
    have hnot3 : ¬ 2 + p + b.val * tailLen + j.val = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, hnot2, ↓reduceIte, hnot3, φ, y]
  have hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y] at hEq
    omega
  simpa [σ, φ, y, hy] using
    secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy
noncomputable def secondReductionCanonicalSecondPowerKernel
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
  refine ⟨(FreeGroup.of y) ^ q, ?_⟩
  rw [MonoidHom.mem_ker, map_pow]
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y]
  rw [hy]
  apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
  simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]
theorem secondReductionCanonicalSecondPowerKernel_coe
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
    ((secondReductionCanonicalSecondPowerKernel
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of y) ^ q := by
  classical
  dsimp
  simp only [secondReductionCanonicalSecondPowerKernel, Lean.Elab.WF.paramLet, id_eq]
noncomputable def secondReductionCanonicalSecondEdgeKernelElement
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    φ.ker := by
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
  let r : ℕ := ((k.val : ZMod q) - 1).val
  refine ⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ r)⁻¹, ?_⟩
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y]
  rw [MonoidHom.mem_ker]
  rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
  apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
  simp only [ofAdd_neg, toAdd_mul, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, toAdd_inv, ZMod.natCast_val,
  dvd_refl, ZMod.cast_sub, ZMod.cast_natCast, ZMod.cast_one, neg_sub, toAdd_one, r]
  ring
theorem secondReductionCanonicalSecondEdgeKernelElement_zero_coe
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
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
    ((secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩ :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      FreeGroup.of y * ((FreeGroup.of x) ^ (q - 1))⁻¹ := by
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
  have hq_pos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  have hsucc : (q - 1).succ = q := by omega
  have hval : (-1 : ZMod q).val = q - 1 := by
    rw [← hsucc]
    exact ZMod.val_neg_one (q - 1)
  simp only [secondReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, pow_zero, one_mul, Nat.cast_zero, zero_sub, hval, id_eq]
private theorem secondReductionCanonicalSecondEdgeKernelElement_descending_coe
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i : Fin (q - 1)) :
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
    ((secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ⟨q - 1 - i.val, by omega⟩ :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ (q - 1 - i.val) * FreeGroup.of y *
        ((FreeGroup.of x) ^ (q - 1 - 1 - i.val))⁻¹ := by
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
  let kNat := q - 1 - i.val
  have hq_gt_one : 1 < q := lt_of_lt_of_le (by decide : 1 < 2) hq
  haveI : Fact (1 < q) := ⟨hq_gt_one⟩
  have hkpos : 0 < kNat := by
    dsimp [kNat]
    omega
  have hklt : kNat < q := by
    dsimp [kNat]
    omega
  have hkval : ((kNat : ZMod q)).val = kNat :=
    ZMod.val_natCast_of_lt hklt
  have hsubval : ((kNat : ZMod q) - 1).val = kNat - 1 := by
    have hle : (1 : ZMod q).val ≤ (kNat : ZMod q).val := by
      rw [hkval, ZMod.val_one]
      exact Nat.succ_le_iff.mpr hkpos
    rw [ZMod.val_sub hle, hkval, ZMod.val_one]
  have hkSub : kNat - 1 = q - 1 - 1 - i.val := by
    dsimp [kNat]
    omega
  have hsubval' :
      (((q - 1 - i.val : ℕ) : ZMod q) - 1).val =
        q - 1 - 1 - i.val := by
    simpa [kNat, hkSub] using hsubval
  dsimp [secondReductionCanonicalSecondEdgeKernelElement,
    secondReductionCanonicalDistinguishedGenerator]
  rw [hsubval']
theorem secondReductionCanonicalSecondEdgeKernelElement_succ_coe
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i : Fin (q - 1)) :
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
    ((secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ⟨i.val + 1, by omega⟩ :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x) ^ (i.val + 1) * FreeGroup.of y *
        ((FreeGroup.of x) ^ i.val)⁻¹ := by
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
  let kNat := i.val + 1
  have hq_gt_one : 1 < q := lt_of_lt_of_le (by decide : 1 < 2) hq
  haveI : Fact (1 < q) := ⟨hq_gt_one⟩
  have hkpos : 0 < kNat := by
    dsimp [kNat]
    omega
  have hklt : kNat < q := by
    dsimp [kNat]
    omega
  have hkval : ((kNat : ZMod q)).val = kNat :=
    ZMod.val_natCast_of_lt hklt
  have hsubval : ((kNat : ZMod q) - 1).val = kNat - 1 := by
    have hle : (1 : ZMod q).val ≤ (kNat : ZMod q).val := by
      rw [hkval, ZMod.val_one]
      exact Nat.succ_le_iff.mpr hkpos
    rw [ZMod.val_sub hle, hkval, ZMod.val_one]
  have hkSub : kNat - 1 = i.val := by
    omega
  have hsubval' :
      (((i.val + 1 : ℕ) : ZMod q) - 1).val = i.val := by
    simpa [kNat, hkSub] using hsubval
  dsimp [secondReductionCanonicalSecondEdgeKernelElement,
    secondReductionCanonicalDistinguishedGenerator]
  rw [hsubval']
private theorem secondReductionCanonical_second_schreierGenerator_eq
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let x :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k := by
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
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y]
  simpa [secondReductionCanonicalSchreierTransversal,
    secondReductionCanonicalSecondEdgeKernelElement, φ, x, y] using
    cyclicQuotient_negOneImage_schreierGenerator_eq φ x y hx hy k
theorem secondReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    (secondReductionCanonicalSecondEdgeKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k : φ.ker) ∈
        schreierGeneratorSet hT := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
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
  let T :=
    secondReductionCanonicalSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  refine ⟨(FreeGroup.of x) ^ k.val, ?_, y, ?_, ?_⟩
  · have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
    simpa [T, secondReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) k.isLt
  · simpa [hT, σ, φ, x, y, secondReductionCanonicalDistinguishedGenerator] using
      (secondReductionCanonical_second_schreierGenerator_eq
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k).symm
  · intro h
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) h
    let r : ℕ := ((k.val : ZMod q) - 1).val
    have hsecondWord :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ = 1 := by
      simpa [φ, x, y, r, secondReductionCanonicalSecondEdgeKernelElement,
        secondReductionCanonicalDistinguishedGenerator] using hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hxne : x ≠ y := by
      intro hEq
      simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, Nat.reduceAdd, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, Nat.reduceEqDiff, x, y] at hEq
    have hmap := congrArg (FreeGroup.lift χ) hsecondWord
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, map_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
theorem secondReductionCanonicalSecondEdgeKernelElement_inj
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    {k₁ k₂ : Fin q}
    (hEq :
      secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k₁ =
        secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k₂) :
    k₁ = k₂ := by
  classical
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
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  let r₁ : ℕ := ((k₁.val : ZMod q) - 1).val
  let r₂ : ℕ := ((k₂.val : ZMod q) - 1).val
  have hleft :
      ((secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k₁ : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r₁)⁻¹ := by
    simp only [secondReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r₁]
  have hright :
      ((secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k₂ : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r₂)⁻¹ := by
    simp only [secondReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r₂]
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r₁)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r₂)⁻¹ := by
    simpa [hleft, hright] using hval
  have hxne : x ≠ y := by
    intro hEq'
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, Nat.reduceAdd, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, Nat.reduceEqDiff, x, y] at hEq'
  exact Fin.ext
    (freeGroup_pow_mul_of_mul_pow_inv_left_exponent_eq_of_eq hxne hword)
theorem secondReductionCanonicalZeroImageKernelElement_ne_secondEdge
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (k k' : Fin q)
    (hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y)
    (hyne :
      y ≠ FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)) :
    secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k ≠
      secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
  classical
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
  let yNeg : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
  intro hEq
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  have hleft :
      ((secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ k.val)⁻¹ := by
    simpa [σ, φ, x] using
      secondReductionCanonicalZeroImageKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
  let r : ℕ := ((k'.val : ZMod q) - 1).val
  have hright :
      ((secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k'.val * FreeGroup.of yNeg *
          ((FreeGroup.of x) ^ r)⁻¹ := by
    simp only [secondReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, id_eq, σ, x, yNeg, r]
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k'.val * FreeGroup.of yNeg *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ := by
    simpa [hleft, hright] using hval
  let χ : FuchsianGenerator σ → Multiplicative ℤ :=
    fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
  have hxne : x ≠ y := by
    simpa [x] using hxy
  have hyne' : yNeg ≠ y := by
    simpa [yNeg] using hyne.symm
  have hmap := congrArg (FreeGroup.lift χ) hword
  simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, hyne', ofAdd_eq_one, one_ne_zero, χ] at hmap
theorem secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (y y' :
      FuchsianGenerator
        (secondReductionCanonicalSourceSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
    (hy :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y) = 1)
    (hy' :
      secondReductionCanonicalSourceFreeQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (FreeGroup.of y') = 1)
    (k k' : Fin q)
    (hxy :
      secondReductionCanonicalDistinguishedGenerator
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ≠ y)
    (hyne : y' ≠ y) :
    secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k ≠
      secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y' hy' k' := by
  classical
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
  intro hEq
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  have hleft :
      ((secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ k.val)⁻¹ := by
    simpa [σ, φ, x] using
      secondReductionCanonicalZeroImageKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
  have hright :
      ((secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y' hy' k' :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k'.val * FreeGroup.of y' *
          ((FreeGroup.of x) ^ k'.val)⁻¹ := by
    simpa [σ, φ, x] using
      secondReductionCanonicalZeroImageKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y' hy' k'
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k'.val * FreeGroup.of y' *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k'.val)⁻¹ := by
    simpa [hleft, hright] using hval
  let χ : FuchsianGenerator σ → Multiplicative ℤ :=
    fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
  have hxne : x ≠ y := by
    simpa [x] using hxy
  have hmap := congrArg (FreeGroup.lift χ) hword
  simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, hyne, ofAdd_eq_one, one_ne_zero, χ] at hmap
theorem secondReductionCanonicalMiddleRestZeroKernelElement_inj
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    {r₁ r₂ : Fin (p - 2)} {k₁ k₂ : Fin q}
    (hEq :
      secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r₁ k₁ =
        secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r₂ k₂) :
    r₁ = r₂ ∧ k₁ = k₂ := by
  classical
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
  let y₁ : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r₁.val, by omega⟩)
  let y₂ : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r₂.val, by omega⟩)
  have hy₁ : φ (FreeGroup.of y₁) = 1 := by
    have hnot3 : ¬ 2 + (2 + r₁.val) = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, y₁]
  have hy₂ : φ (FreeGroup.of y₂) = 1 := by
    have hnot3 : ¬ 2 + (2 + r₂.val) = 3 := by omega
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, y₂]
  have hxy₁ : x ≠ y₁ := by
    intro hEq'
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, Nat.left_eq_add, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
  false_and, x, y₁] at hEq'
  by_cases hgen : y₂ = y₁
  · have hr : r₁ = r₂ := by
      have hval := congrArg
        (fun y : FuchsianGenerator σ =>
          match y with
          | .elliptic i => i.val
          | .surfaceA _ => 0
          | .surfaceB _ => 0) hgen.symm
      simp only [secondReductionCanonicalSourceMiddleIndex, Nat.add_left_cancel_iff, y₂, y₁] at hval
      exact Fin.ext (by omega)
    subst r₂
    have hk : k₁ = k₂ := by
      exact
        secondReductionCanonicalZeroImageKernelElement_inj
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y₁ hy₁ hxy₁
          (by
            simpa [σ, φ, y₁, hy₁,
              secondReductionCanonicalMiddleRestZeroKernelElement] using hEq)
    exact ⟨rfl, hk⟩
  · exact False.elim
      (secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y₁ y₂ hy₁ hy₂ k₁ k₂
        hxy₁ hgen hEq)
theorem secondReductionCanonicalTailZeroKernelElement_inj
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    {b₁ b₂ : Fin p} {j₁ j₂ : Fin tailLen} {k₁ k₂ : Fin q}
    (hEq :
      secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b₁ j₁ k₁ =
        secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b₂ j₂ k₂) :
    b₁ = b₂ ∧ j₁ = j₂ ∧ k₁ = k₂ := by
  classical
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
  let tailGen : Fin p → Fin tailLen → FuchsianGenerator σ := fun b j =>
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
  have hleft :
      ((secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b₁ j₁ k₁ :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of (tailGen b₁ j₁) *
          ((FreeGroup.of x) ^ k₁.val)⁻¹ := by
    simp only [secondReductionCanonicalTailZeroKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalZeroImageKernelElement, secondReductionCanonicalDistinguishedGenerator, id_eq, σ, x,
  tailGen]
  have hright :
      ((secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b₂ j₂ k₂ :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of (tailGen b₂ j₂) *
          ((FreeGroup.of x) ^ k₂.val)⁻¹ := by
    simp only [secondReductionCanonicalTailZeroKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalZeroImageKernelElement, secondReductionCanonicalDistinguishedGenerator, id_eq, σ, x,
  tailGen]
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
          FreeGroup.of (tailGen b₁ j₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val *
          FreeGroup.of (tailGen b₂ j₂) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val)⁻¹ := by
    simpa [hleft, hright] using hval
  have hxne₁ : x ≠ tailGen b₁ j₁ := by
    intro hEq'
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x,
  tailGen] at hEq'
    omega
  have hxne₂ : x ≠ tailGen b₂ j₂ := by
    intro hEq'
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x,
  tailGen] at hEq'
    omega
  have hlen := congrArg
    (fun w : FreeGroup (FuchsianGenerator σ) => (FreeGroup.toWord w).length) hword
  change
    (FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
        FreeGroup.of (tailGen b₁ j₁) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹)).length =
    (FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₂.val *
        FreeGroup.of (tailGen b₂ j₂) *
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
        FreeGroup.of (tailGen b₁ j₁) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹) =
    FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val *
        FreeGroup.of (tailGen b₂ j₂) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k₁.val)⁻¹) at hwords
  rw [freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₁ k₁.val k₁.val,
    freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₂ k₁.val k₁.val] at hwords
  have hdrop := congrArg
    (fun L : List (FuchsianGenerator σ × Bool) => L.drop k₁.val) hwords
  have hhead := congrArg List.head? hdrop
  have htailGenEq : tailGen b₁ j₁ = tailGen b₂ j₂ := by
    simpa using hhead
  have hidxVal :
      2 + p + b₁.val * tailLen + j₁.val =
        2 + p + b₂.val * tailLen + j₂.val := by
    have h := congrArg
      (fun y : FuchsianGenerator σ =>
        match y with
        | .elliptic i => i.val
        | .surfaceA _ => 0
        | .surfaceB _ => 0) htailGenEq
    simpa [tailGen, secondReductionCanonicalSourceTailIndex] using h
  have hsum :
      b₁.val * tailLen + j₁.val = b₂.val * tailLen + j₂.val := by
    omega
  have htailLen_pos : 0 < tailLen := lt_of_le_of_lt (Nat.zero_le _) j₁.isLt
  have hdiv₁ : (b₁.val * tailLen + j₁.val) / tailLen = b₁.val := by
    rw [Nat.mul_comm b₁.val tailLen, Nat.mul_add_div htailLen_pos,
      Nat.div_eq_of_lt j₁.isLt]
    simp only [add_zero]
  have hdiv₂ : (b₂.val * tailLen + j₂.val) / tailLen = b₂.val := by
    rw [Nat.mul_comm b₂.val tailLen, Nat.mul_add_div htailLen_pos,
      Nat.div_eq_of_lt j₂.isLt]
    simp only [add_zero]
  have hbVal : b₁.val = b₂.val := by
    have hdiv := congrArg (fun n : ℕ => n / tailLen) hsum
    simpa [hdiv₁, hdiv₂] using hdiv
  have hmod₁ : (b₁.val * tailLen + j₁.val) % tailLen = j₁.val := by
    rw [Nat.mul_comm b₁.val tailLen, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt j₁.isLt]
  have hmod₂ : (b₂.val * tailLen + j₂.val) % tailLen = j₂.val := by
    rw [Nat.mul_comm b₂.val tailLen, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt j₂.isLt]
  have hjVal : j₁.val = j₂.val := by
    have hmod := congrArg (fun n : ℕ => n % tailLen) hsum
    simpa [hmod₁, hmod₂] using hmod
  exact ⟨Fin.ext hbVal, Fin.ext hjVal, rfl⟩
theorem secondReductionCanonicalSecondDescendingCycle_eq_secondPowerKernel
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let n := q - 1
    secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩ *
      (List.ofFn (fun i : Fin n =>
        secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ⟨n - i.val, by omega⟩)).prod =
        secondReductionCanonicalSecondPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let n := q - 1
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
  apply Subtype.ext
  change
    ((secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩ : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) *
      (((List.ofFn (fun i : Fin n =>
        secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ⟨n - i.val, by omega⟩)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
      ((secondReductionCanonicalSecondPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail : φ.ker) :
            FreeGroup (FuchsianGenerator σ))
  have hprodCoe :
      (((List.ofFn (fun i : Fin n =>
        secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ⟨n - i.val, by omega⟩)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun i : Fin n =>
          ((secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨n - i.val, by omega⟩ : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))).prod := by
    change
      φ.ker.subtype
          ((List.ofFn (fun i : Fin n =>
            secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨n - i.val, by omega⟩)).prod) =
        (List.ofFn (fun i : Fin n =>
          φ.ker.subtype
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨n - i.val, by omega⟩))).prod
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [hprodCoe]
  rw [secondReductionCanonicalSecondEdgeKernelElement_zero_coe]
  have htailList :
      (List.ofFn (fun i : Fin n =>
          ((secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨n - i.val, by omega⟩ : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))) =
        List.ofFn (fun i : Fin n =>
          (FreeGroup.of x) ^ (n - i.val) * FreeGroup.of y *
            ((FreeGroup.of x) ^ (n - 1 - i.val))⁻¹) := by
    apply List.ofFn_inj.2
    funext i
    simpa [n, σ, φ, x, y] using
      secondReductionCanonicalSecondEdgeKernelElement_descending_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i
  rw [htailList]
  change
    FreeGroup.of y * ((FreeGroup.of x) ^ n)⁻¹ *
        negOneCycleTailProduct (FreeGroup.of x) (FreeGroup.of y) n =
      (FreeGroup.of y) ^ q
  have hn : n + 1 = q := by
    dsimp [n]
    omega
  rw [← hn]
  exact negOneCycleProduct_eq_pow (FreeGroup.of x) (FreeGroup.of y) n
theorem secondReductionCanonicalSecondDescendingCycle_schreierWord_eq_secondPower
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let n := q - 1
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    e.symm
        (secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩) *
      (List.ofFn (fun i : Fin n =>
        e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨n - i.val, by omega⟩))).prod =
        e.symm
          (secondReductionCanonicalSecondPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let n := q - 1
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hcycle :
      secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩ *
        (List.ofFn (fun i : Fin n =>
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨n - i.val, by omega⟩)).prod =
          secondReductionCanonicalSecondPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
    simpa [n] using
      secondReductionCanonicalSecondDescendingCycle_eq_secondPowerKernel
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hmap := congrArg e.symm hcycle
  have htailMap :
      e.symm
          ((List.ofFn (fun i : Fin n =>
            secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨n - i.val, by omega⟩)).prod) =
        (List.ofFn (fun i : Fin n =>
          e.symm
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨n - i.val, by omega⟩))).prod := by
    rw [map_list_prod, List.map_ofFn]
    rfl
  simpa [map_mul, htailMap] using hmap
theorem secondReductionCanonicalSecondShiftedCycle_eq_conjugate_secondPower
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) :
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
    let edge : Fin q → φ.ker :=
      secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let lower :=
      (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
    let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
    let upper :=
      (List.ofFn (fun i : Fin (q - 1 - k.val) => edge ⟨q - 1 - i.val, by omega⟩)).prod
    lower * wrap * upper =
      (⟨(FreeGroup.of x) ^ k.val * (FreeGroup.of y) ^ q *
          ((FreeGroup.of x) ^ k.val)⁻¹, by
        rw [MonoidHom.mem_ker]
        have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
          simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
        have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod q) := by
          simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.succ_ne_self, ↓reduceIte, ofAdd_neg, φ, y]
        rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
        apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
        simp only [ofAdd_neg, inv_pow, mul_inv_cancel_comm, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  CharP.cast_eq_zero, mul_one, neg_zero, toAdd_one]⟩ : φ.ker) := by
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
  let edge : Fin q → φ.ker :=
    secondReductionCanonicalSecondEdgeKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let lower :=
    (List.ofFn (fun i : Fin k.val => edge ⟨k.val - i.val, by omega⟩)).prod
  let wrap := edge ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
  let upper :=
    (List.ofFn (fun i : Fin (q - 1 - k.val) => edge ⟨q - 1 - i.val, by omega⟩)).prod
  apply Subtype.ext
  change
    ((lower * wrap * upper : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        (FreeGroup.of y) ^ q *
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
    let i' : Fin (q - 1) := ⟨k.val - 1 - i.val, by omega⟩
    have hidx :
        (⟨i'.val + 1, by omega⟩ : Fin q) = ⟨k.val - i.val, by omega⟩ := by
      ext
      simp only [i']
      omega
    have hs : k.val - 1 - i.val + 1 = k.val - i.val := by omega
    simpa [σ, φ, x, y, edge, i', hidx, hs] using
      secondReductionCanonicalSecondEdgeKernelElement_succ_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i'
  have hwrapCoe :
      ((wrap : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (q - 1))⁻¹ := by
    simpa [σ, φ, x, y, edge, wrap] using
      secondReductionCanonicalSecondEdgeKernelElement_zero_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hupperCoe :
      ((upper : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun i : Fin (q - 1 - k.val) =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (q - 1 - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^
              (q - 1 - 1 - i.val))⁻¹)).prod := by
    change
      φ.ker.subtype upper =
        (List.ofFn (fun i : Fin (q - 1 - k.val) =>
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (q - 1 - i.val) *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^
              (q - 1 - 1 - i.val))⁻¹)).prod
    simp only [Subgroup.subtype_apply, Subgroup.val_list_prod, List.map_ofFn, upper, edge]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    let i' : Fin (q - 1) := ⟨i.val, by omega⟩
    simpa [σ, φ, x, y, edge, i'] using
      secondReductionCanonicalSecondEdgeKernelElement_descending_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i'
  change
    ((lower : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
        ((wrap : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
        ((upper : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        (FreeGroup.of y) ^ q *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹
  rw [hlowerCoe, hwrapCoe, hupperCoe]
  rw [secondReduction_negOneCycleSegmentProduct_eq (FreeGroup.of x) (FreeGroup.of y)
    k.val k.val (by omega)]
  rw [secondReduction_negOneCycleSegmentProduct_eq (FreeGroup.of x) (FreeGroup.of y)
    (q - 1) (q - 1 - k.val) (by omega)]
  have hkk : k.val - k.val = 0 := by omega
  have hlast : q - 1 - (q - 1 - k.val) = k.val := by omega
  rw [hkk, hlast]
  simp only [pow_zero, inv_one, mul_one]
  have hkadd : k.val + 1 + (q - 1 - k.val) = q := by omega
  calc
    (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
          (FreeGroup.of y) ^ k.val *
          (FreeGroup.of y * ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (q - 1))⁻¹) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (q - 1) *
          (FreeGroup.of y) ^ (q - 1 - k.val) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹)
        =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        ((FreeGroup.of y) ^ k.val * FreeGroup.of y *
          (FreeGroup.of y) ^ (q - 1 - k.val)) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ := by
        group
    _ =
      (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
        (FreeGroup.of y) ^ q *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ := by
        rw [← pow_succ (FreeGroup.of y) k.val]
        rw [← pow_add (FreeGroup.of y) (k.val + 1) (q - 1 - k.val)]
        rw [hkadd]
theorem secondReductionCanonical_schreierGeneratorSet_cases
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
    let φ :=
      secondReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ z : ↥(schreierGeneratorSet hT),
      (z : φ.ker) =
          secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ∨
        (∃ k : Fin q,
          (z : φ.ker) =
            secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) ∨
        (∃ y :
            FuchsianGenerator
              (secondReductionCanonicalSourceSignature
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail),
          ∃ hy :
            secondReductionCanonicalSourceFreeQuotientHom
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                (FreeGroup.of y) = 1,
          ∃ k : Fin q,
            (z : φ.ker) =
              secondReductionCanonicalZeroImageKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  intro z
  rcases z.property with ⟨t, ht, g, hz, hne⟩
  have htPower : ∃ k : Fin q, t = (FreeGroup.of x) ^ k.val := by
    simpa [hT, secondReductionCanonicalSchreierTransversal, φ, x] using
      (mem_range_cyclicQuotientRightRep_iff_generatorPower φ (x := x) hx).1 ht
  rcases htPower with ⟨k, rfl⟩
  cases g with
  | elliptic i =>
      by_cases h2 : i.val = 2
      · have hi :
            i =
              secondReductionCanonicalSourceMiddleIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ⟨0, by omega⟩ := by
          ext
          simpa [secondReductionCanonicalSourceMiddleIndex] using h2
        by_cases hwrap : k.val + 1 < q
        · have hgen :
              schreierGenerator hT ((FreeGroup.of x) ^ k.val) x = 1 := by
            simpa [hT, σ, φ, x, secondReductionCanonicalDistinguishedGenerator] using
              secondReductionCanonical_distinguished_schreierGenerator_eq_one_of_succ_lt
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail hwrap
          exact False.elim
            (hne (by simpa [hz, x, hi, secondReductionCanonicalDistinguishedGenerator] using hgen))
        · have hk : k.val = q - 1 := by
            have hklt := k.isLt
            omega
          left
          calc
            (z : φ.ker) = schreierGenerator hT ((FreeGroup.of x) ^ k.val) x := by
              simpa [x, hi, secondReductionCanonicalDistinguishedGenerator] using hz
            _ = schreierGenerator hT ((FreeGroup.of x) ^ (q - 1)) x := by
              rw [hk]
            _ =
                secondReductionCanonicalFirstPowerKernel
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
              simpa [hT, σ, φ, x, secondReductionCanonicalDistinguishedGenerator] using
                secondReductionCanonical_distinguished_schreierGenerator_wrap_eq
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      · by_cases h3 : i.val = 3
        · have hp1 : 1 < p := by omega
          have hi :
              i =
                secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  ⟨1, hp1⟩ := by
            ext
            simpa [secondReductionCanonicalSourceMiddleIndex] using h3
          right
          left
          refine ⟨k, ?_⟩
          calc
            (z : φ.ker) =
                schreierGenerator hT ((FreeGroup.of x) ^ k.val)
                  (FuchsianGenerator.elliptic
                    (secondReductionCanonicalSourceMiddleIndex
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, hp1⟩)) := by
              simpa [hi] using hz
            _ =
                secondReductionCanonicalSecondEdgeKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k := by
              simpa [hT, σ, φ, x, secondReductionCanonicalDistinguishedGenerator] using
                secondReductionCanonical_second_schreierGenerator_eq
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
        · right
          right
          let y : FuchsianGenerator σ := FuchsianGenerator.elliptic i
          have hy : φ (FreeGroup.of y) = 1 := by
            simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, secondReductionCanonicalSourceQuotientImage, h2,
  ↓reduceIte, h3, φ, y]
          refine ⟨y, hy, k, ?_⟩
          calc
            (z : φ.ker) =
                schreierGenerator hT ((FreeGroup.of x) ^ k.val) y := by
              simpa [y] using hz
            _ =
                secondReductionCanonicalZeroImageKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k := by
              simpa [hT, σ, φ, x, y] using
                secondReductionCanonical_zeroImage_schreierGenerator_eq
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
  | surfaceA i =>
      exact Fin.elim0 (by
        simpa [σ, secondReductionCanonicalSourceSignature] using i)
  | surfaceB i =>
      exact Fin.elim0 (by
        simpa [σ, secondReductionCanonicalSourceSignature] using i)
end FenchelNielsen
