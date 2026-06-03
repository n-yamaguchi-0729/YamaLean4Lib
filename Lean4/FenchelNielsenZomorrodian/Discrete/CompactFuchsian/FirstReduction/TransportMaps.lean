import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.QuotientAndBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/FirstReduction/TransportMaps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# First compact zero-genus reduction

The first explicit finite quotient reduction for compact zero-genus Fuchsian presentations, including quotient maps, basis transport, signatures, and relator verification.
-/

namespace FenchelNielsen
noncomputable abbrev firstReductionCanonicalSchreierRelatorSet
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    Set (FreeGroup ↥(schreierGeneratorSet hT)) :=
  by
    classical
    exact
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet
        (firstReductionCanonicalSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage
            (firstReductionCanonicalSourceSignature
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
            (firstReductionCanonicalSourceQuotientImage
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
          (rels := relators
            (firstReductionCanonicalSourceSignature
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
          (firstReductionCanonicalSchreierTransversal
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
private theorem firstReductionCanonicalSchreier_nonwrapTotalRelator_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin (p - 1)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨k.val + 1, by omega⟩) *
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
            ⟨k.val, by omega⟩))).prod ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
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
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
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
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let k0 : Fin p := ⟨k.val, by omega⟩
  let k1 : Fin p := ⟨k.val + 1, by omega⟩
  let t : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ k.val
  let r : FreeGroup (FuchsianGenerator σ) := totalRelation σ
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  have ht : t ∈ T := by
    simpa [T, t, firstReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k.val) (by omega)
  have hr : r ∈ relators σ := by
    exact Or.inr rfl
  have hrel :
      e.symm
          (⟨t * r * t⁻¹, by
            change φ (t * r * t⁻¹) = 1
            have hrφ : φ r = 1 := hrels r hr
            simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    have h :=
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure
        hrels e ht hr
    simpa [firstReductionCanonicalSchreierRelatorSet, T, hT, e] using h
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
    simpa [σ, φ, x, tailGen, k0] using
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
      (⟨t * r * t⁻¹, by
        change φ (t * r * t⁻¹) = 1
        have hrφ : φ r = 1 := hrels r hr
        simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) =
        firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1 *
          (List.ofFn (fun j : Fin tailLen =>
            firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod := by
    apply Subtype.ext
    change
      t * r * t⁻¹ =
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
    dsimp [r]
    rw [hTotal]
    simp only [t, x, tailGen, xWord,
      firstReductionCanonicalDistinguishedGenerator, mul_assoc]
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
  have hrel' :
      e.symm
          (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k1 *
            (List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k0)).prod) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    simpa [hkerEq] using hrel
  simpa [k0, k1, hmap] using hrel'
private theorem firstReductionCanonicalSchreier_wrapTotalRelator_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    e.symm
        (firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
      e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩) *
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
            ⟨p - 1, by omega⟩))).prod ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
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
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
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
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let kLast : Fin p := ⟨p - 1, by omega⟩
  let kZero : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩
  let t : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ (p - 1)
  let r : FreeGroup (FuchsianGenerator σ) := totalRelation σ
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalDistinguishedGenerator,
  firstReductionCanonicalSourceFreeQuotientHom_firstGenerator m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, φ, x]
  have ht : t ∈ T := by
    simpa [T, t, firstReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := p - 1) (by omega)
  have hr : r ∈ relators σ := by
    exact Or.inr rfl
  have hrel :
      e.symm
          (⟨t * r * t⁻¹, by
            change φ (t * r * t⁻¹) = 1
            have hrφ : φ r = 1 := hrels r hr
            simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    have h :=
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure
        hrels e ht hr
    simpa [firstReductionCanonicalSchreierRelatorSet, T, hT, e] using h
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
      (⟨t * r * t⁻¹, by
        change φ (t * r * t⁻¹) = 1
        have hrφ : φ r = 1 := hrels r hr
        simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) =
        firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen *
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero *
          (List.ofFn (fun j : Fin tailLen =>
            firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod := by
    apply Subtype.ext
    change
      t * r * t⁻¹ =
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
    dsimp [r]
    rw [hTotal]
    simp only [t, x, tailGen, xWord,
      firstReductionCanonicalDistinguishedGenerator, mul_assoc]
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
  have hrel' :
      e.symm
          (firstReductionCanonicalFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen *
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen kZero *
            (List.ofFn (fun j : Fin tailLen =>
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j kLast)).prod) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    simpa [hkerEq] using hrel
  simpa [kLast, kZero, map_mul, htailMap, mul_assoc] using hrel'
private theorem firstReductionCanonicalSchreier_nonwrapGeneratorElimination_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin (p - 1)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
            ⟨k.val, by omega⟩))).prod *
      e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨k.val + 1, by omega⟩) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have h :=
    firstReductionCanonicalSchreier_nonwrapTotalRelator_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k
  simpa [σ, e, mul_assoc] using
    (ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
      (R := firstReductionCanonicalSchreierRelatorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      (a := e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨k.val + 1, by omega⟩))
      (b := (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
            ⟨k.val, by omega⟩))).prod)
      h)
private theorem firstReductionCanonicalSchreier_wrapGeneratorElimination_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
            ⟨p - 1, by omega⟩))).prod *
      e.symm
        (firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
      e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let a :=
    e.symm
      (firstReductionCanonicalFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let b :=
    e.symm
      (firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩)
  let c :=
    (List.ofFn (fun j : Fin tailLen =>
      e.symm
        (firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
          ⟨p - 1, by omega⟩))).prod
  have habc : a * b * c ∈
      Subgroup.normalClosure
        (firstReductionCanonicalSchreierRelatorSet
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    simpa [σ, e, a, b, c, mul_assoc] using
      firstReductionCanonicalSchreier_wrapTotalRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hbc_a : b * c * a ∈
      Subgroup.normalClosure
        (firstReductionCanonicalSchreierRelatorSet
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := firstReductionCanonicalSchreierRelatorSet
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
        (a := a) (b := b * c)
        (by simpa [mul_assoc] using habc)
    simpa [mul_assoc] using hrot
  have hca_b : c * a * b ∈
      Subgroup.normalClosure
        (firstReductionCanonicalSchreierRelatorSet
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := firstReductionCanonicalSchreierRelatorSet
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
        (a := b) (b := c * a)
        (by simpa [mul_assoc] using hbc_a)
    simpa [mul_assoc] using hrot
  simpa [a, b, c, mul_assoc] using hca_b
private theorem firstReductionCanonicalTarget_totalRelation_inverseRotated_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let A :=
      xWord τ
        (firstReductionCanonicalTargetZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let B :=
      xWord τ
        (firstReductionCanonicalTargetOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let C :=
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod)).prod
    A⁻¹ * C⁻¹ * B⁻¹ ∈ Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let A :=
    xWord τ
      (firstReductionCanonicalTargetZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let B :=
    xWord τ
      (firstReductionCanonicalTargetOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let C :=
    (List.ofFn (fun k : Fin p =>
      (List.ofFn (fun j : Fin tailLen =>
        xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod)).prod
  let N : Subgroup (FreeGroup (FuchsianGenerator τ)) :=
    Subgroup.normalClosure (relators τ)
  have htotal : A * B * C ∈ N := by
    have hmem : totalRelation τ ∈ relators τ := Or.inr rfl
    have hmemN : totalRelation τ ∈ N := Subgroup.subset_normalClosure hmem
    have hTotal :=
      firstReductionCanonicalTarget_totalRelation_eq_blocks
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    simpa [N, τ, A, B, C, hTotal] using hmemN
  have hinv : (A * B * C)⁻¹ ∈ N := N.inv_mem htotal
  have hCBA : C⁻¹ * B⁻¹ * A⁻¹ ∈ N := by
    simpa [N, mul_assoc] using hinv
  have hBA_C : B⁻¹ * A⁻¹ * C⁻¹ ∈ N := by
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := relators τ) (a := C⁻¹) (b := B⁻¹ * A⁻¹)
        (by simpa [N, mul_assoc] using hCBA)
    simpa [N, mul_assoc] using hrot
  have hA_CB : A⁻¹ * C⁻¹ * B⁻¹ ∈ N := by
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := relators τ) (a := B⁻¹) (b := A⁻¹ * C⁻¹)
        (by simpa [N, mul_assoc] using hBA_C)
    simpa [N, mul_assoc] using hrot
  simpa [N, τ, A, B, C, mul_assoc] using hA_CB
noncomputable def firstReductionCanonicalTargetTailBlockWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    Fin p → FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  intro k
  exact
    (List.ofFn (fun j : Fin tailLen =>
      xWord τ
        (firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod
noncomputable def firstReductionCanonicalSecondEdgeForwardWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    Fin p → FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let A :=
    xWord τ
      (firstReductionCanonicalTargetZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let block :=
    firstReductionCanonicalTargetTailBlockWord
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  intro k
  if h0 : k.val = 0 then
    exact block ⟨p - 1, by omega⟩ * A
  else
    exact block ⟨k.val - 1, by omega⟩
noncomputable def firstReductionCanonicalSchreierToTargetGeneratorImage
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
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ↥(schreierGeneratorSet hT) → FreeGroup (FuchsianGenerator τ) := by
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
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let A :=
    xWord τ
      (firstReductionCanonicalTargetZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let secondWord :=
    firstReductionCanonicalSecondEdgeForwardWord
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  intro z
  if hFirst :
      (z : φ.ker) =
        firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen then
    exact A⁻¹
  else if hSecond :
      ∃ k : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k then
    exact secondWord (Classical.choose hSecond)
  else if hTail :
      ∃ j : Fin tailLen, ∃ k : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k then
    let j : Fin tailLen := Classical.choose hTail
    let hk : ∃ k : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k :=
      Classical.choose_spec hTail
    let k : Fin p := Classical.choose hk
    exact
      (xWord τ
        (firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))⁻¹
  else
    exact 1
noncomputable def firstReductionCanonicalSchreierToTargetHom
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
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup (FuchsianGenerator τ) :=
  FreeGroup.lift
    (firstReductionCanonicalSchreierToTargetGeneratorImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
private theorem firstReductionCanonicalSchreierToTargetHom_firstPowerWord
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
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
          (firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
      xWord τ
        (firstReductionCanonicalTargetZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
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
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨firstReductionCanonicalFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen,
      firstReductionCanonicalFirstPowerKernel_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen⟩
  have hzWord :
      e.symm
          (firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      firstReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen z
  have hFirst :
      (z : φ.ker) =
        firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := rfl
  have hzImage :
      η (FreeGroup.of z) =
        (xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSchreierToTargetHom,
  firstReductionCanonicalSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, ↓reduceIte, η,
  z, τ, σ]
  calc
    η
        (e.symm
          (firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        ((xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
          simp only [inv_inv]
private theorem firstReductionCanonicalSchreierToTargetHom_tailWord
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
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k)) =
      xWord τ
        (firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j) := by
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
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨firstReductionCanonicalTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k,
      firstReductionCanonicalTailKernelElement_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k⟩
  have hzWord :
      e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      firstReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen z
  have hxne : x ≠ tailGen j := by
    intro hEq
    simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x, tailGen] at hEq
    omega
  have hyne : y ≠ tailGen j := by
    intro hEq
    simp only [firstReductionCanonicalSourceOneIndex, firstReductionCanonicalSourceTailIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y, tailGen] at hEq
    omega
  have hFirst :
      ¬ (z : φ.ker) =
        firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      simpa [z, σ, φ, x, tailGen] using
        firstReductionCanonicalTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k
    have hright :
        ((firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ p := by
      simpa [σ, φ, x] using
        firstReductionCanonicalFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ p := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hSecond :
      ¬ ∃ k' : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen j) *
            ((FreeGroup.of x) ^ k.val)⁻¹ := by
      simpa [z, σ, φ, x, tailGen] using
        firstReductionCanonicalTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k
    let r : ℕ := ((k'.val : ZMod p) - 1).val
    have hright :
        ((firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k'.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simp only [firstReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r]
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of (tailGen j) *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k'.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = tailGen j then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, hyne, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hTail :
      ∃ j' : Fin tailLen, ∃ k' : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j' k' := ⟨j, k, rfl⟩
  let j' : Fin tailLen := Classical.choose hTail
  let hk' : ∃ k' : Fin p,
      (z : φ.ker) =
        firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j' k' :=
    Classical.choose_spec hTail
  let k' : Fin p := Classical.choose hk'
  have hTailChoose :
      firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' j' =
        firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j := by
    have hEqTail :
        firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k =
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j' k' := by
      simpa [z, j', hk', k'] using
        Classical.choose_spec hk'
    rcases
      firstReductionCanonicalTailKernelElement_inj
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hEqTail with
      ⟨hj, hk⟩
    simp only [hk, hj]
  have hzImage :
      η (FreeGroup.of z) =
        (xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSchreierToTargetHom,
  firstReductionCanonicalSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst,
  ↓reduceIte, hSecond, ↓reduceDIte, hTail, hTailChoose, η, z, τ, σ, k', j']
  calc
    η
        (e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        ((xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j) := by
          simp only [inv_inv]
private theorem firstReductionCanonicalSchreierToTargetHom_secondEdgeWord
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
          (firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k)) =
      (firstReductionCanonicalSecondEdgeForwardWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k)⁻¹ := by
  classical
  dsimp
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
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let x : FuchsianGenerator σ :=
    firstReductionCanonicalDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨firstReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k,
      firstReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k⟩
  have hzWord :
      e.symm
          (firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      firstReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen z
  have hxne : x ≠ y := by
    intro hEq
    simp only [firstReductionCanonicalDistinguishedGenerator, firstReductionCanonicalSourceZeroIndex,
  firstReductionCanonicalSourceOneIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, zero_ne_one, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simp only [firstReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r, z]
    have hright :
        ((firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ p := by
      simpa [σ, φ, x] using
        firstReductionCanonicalFirstPowerKernel_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ p := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hTail :
      ¬ ∃ j' : Fin tailLen, ∃ k' : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j' k' := by
    intro h
    rcases h with ⟨j', k', hEq⟩
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
    let r : ℕ := ((k.val : ZMod p) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simp only [firstReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  firstReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r, z]
    have hright :
        ((firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j' k' : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k'.val * FreeGroup.of (tailGen j') *
            ((FreeGroup.of x) ^ k'.val)⁻¹ := by
      simpa [σ, φ, x, tailGen] using
        firstReductionCanonicalTailKernelElement_coe
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j' k'
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k'.val *
            FreeGroup.of (tailGen j') *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k'.val)⁻¹ := by
      simpa [hleft, hright] using hval
    have hyne : y ≠ tailGen j' := by
      intro hEq'
      simp only [firstReductionCanonicalSourceOneIndex, firstReductionCanonicalSourceTailIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y, tailGen] at hEq'
      omega
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, mul_ite, left_eq_ite_iff, ofAdd_eq_one, one_ne_zero, imp_false, Decidable.not_not, χ] at hmap
    exact hyne hmap.symm
  have hSecond :
      ∃ k' : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' := ⟨k, rfl⟩
  let k' : Fin p := Classical.choose hSecond
  have hSecondChoose :
      firstReductionCanonicalSecondEdgeForwardWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' =
        firstReductionCanonicalSecondEdgeForwardWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k := by
    have hEqSecond :
        firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k =
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' := by
      simpa [z, k'] using Classical.choose_spec hSecond
    have hk :=
      firstReductionCanonicalSecondEdgeKernelElement_inj
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hEqSecond
    simp only [hk]
  have hzImage :
      η (FreeGroup.of z) =
        firstReductionCanonicalSecondEdgeForwardWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSchreierToTargetHom,
  firstReductionCanonicalSchreierToTargetGeneratorImage, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst,
  ↓reduceIte, hSecond, ↓reduceDIte, hSecondChoose, η, z, k', σ]
  calc
    η
        (e.symm
          (firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        (firstReductionCanonicalSecondEdgeForwardWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k)⁻¹ := by
          rw [hzImage]
private theorem firstReductionCanonicalSchreier_cyclicBlockTotalProduct_mem_normalClosure
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
    let x : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
    let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
      have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
      rw [MonoidHom.mem_ker, map_pow, hy]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
    let c : Fin tailLen → Fin p → φ.ker := fun j k =>
      ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
          ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
        have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
          simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
          omega
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
    e.symm a * e.symm b *
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen => e.symm (c j k))).prod)).prod ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
  let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
    have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
    rw [MonoidHom.mem_ker, map_pow, hy]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
        ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
      have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
        omega
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
  let kBlock : φ.ker :=
    a * b *
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod
  have hTailRel :
      FreeGroup.of x * FreeGroup.of y *
          (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod ∈
        Subgroup.normalClosure (relators σ) := by
    have hTotal :=
      firstReductionCanonicalSource_totalRelation_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hTailEq :
        totalRelation σ =
          FreeGroup.of x * FreeGroup.of y *
            (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen j))).prod := by
      simpa [σ, x, y, tailGen, xWord] using hTotal
    rw [← hTailEq]
    exact Subgroup.subset_normalClosure (Or.inr rfl)
  have hSourceBlock :
      (FreeGroup.of x) ^ p * (FreeGroup.of y) ^ p *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              (FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
                ((FreeGroup.of x) ^ (k : ℕ))⁻¹)).prod)).prod ∈
        Subgroup.normalClosure (relators σ) := by
    simpa [x, y, tailGen] using
      pow_mul_pow_mul_conjugateBlockProduct_mem_normalClosure_of_mul_mem_normalClosure
        (FreeGroup.of x) (FreeGroup.of y)
        (fun j : Fin tailLen => FreeGroup.of (tailGen j)) p hTailRel
  have hBlockCoe :
      (((List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            ((c j k : φ.ker) : FreeGroup (FuchsianGenerator σ)))).prod)).prod := by
    simpa using
      (MonoidHom.map_list_prod_ofFn₂ φ.ker.subtype
        (fun k : Fin p => fun j : Fin tailLen => c j k))
  have hkSource : (kBlock : FreeGroup (FuchsianGenerator σ)) ∈
      Subgroup.normalClosure (relators σ) := by
    change
      ((a : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
          ((b : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
        (((List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod : φ.ker) :
            FreeGroup (FuchsianGenerator σ)) ∈
        Subgroup.normalClosure (relators σ)
    rw [hBlockCoe]
    simpa [a, b, c, x, y, tailGen] using hSourceBlock
  have hmem :
      e.symm kBlock ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
    exact
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
        hrels hT.1 e hkSource
  have hBlockMap :
      e.symm ((List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod) =
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin tailLen => e.symm (c j k))).prod)).prod := by
    simpa using
      (MonoidHom.map_list_prod_ofFn₂ e.symm.toMonoidHom
        (fun k : Fin p => fun j : Fin tailLen => c j k))
  have hmem' :
      e.symm a * e.symm b *
          e.symm
            ((List.ofFn (fun k : Fin p =>
              (List.ofFn (fun j : Fin tailLen => c j k)).prod)).prod) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
    simpa [kBlock, map_mul] using hmem
  rw [hBlockMap] at hmem'
  simpa [a, b, c] using hmem'
private theorem firstReductionCanonicalTarget_totalRelation_image_mem_normalClosure
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
    let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
      have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
      rw [MonoidHom.mem_ker, map_pow, hy]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
    let c : Fin tailLen → Fin p → φ.ker := fun j k =>
      ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
          ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
        have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
          simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
          omega
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
    ∀ (η :
        FreeGroup (FuchsianGenerator τ) →*
          FreeGroup ↥(schreierGeneratorSet hT)),
      η (xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) = e.symm a →
      η (xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) = e.symm b →
      (∀ k : Fin p, ∀ j : Fin tailLen,
        η (xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j)) = e.symm (c j k)) →
      η (totalRelation τ) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
  let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
    have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
    rw [MonoidHom.mem_ker, map_pow, hy]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
        ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
      have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
        omega
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
  intro η hzero hone htailMap
  have hImage :
      η (totalRelation τ) =
        e.symm a * e.symm b *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin tailLen => e.symm (c j k))).prod)).prod := by
    rw [firstReductionCanonicalTarget_totalRelation_eq_blocks
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen]
    rw [map_mul, map_mul]
    rw [MonoidHom.map_list_prod_ofFn₂ η
      (fun k : Fin p => fun j : Fin tailLen =>
        xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))]
    simp only [hzero, hone, htailMap, τ, φ, e, x, a, b, y, c, tailGen]
  rw [hImage]
  simpa [σ, φ, x, y, tailGen, T, hT, e, hrels, a, b, c] using
    firstReductionCanonicalSchreier_cyclicBlockTotalProduct_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
private theorem firstReductionCanonicalTarget_mapsRelators_of_power_and_total
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    {G : Type*} [Group G] {S : Set G}
    (η :
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      FreeGroup (FuchsianGenerator τ) →* G)
    (hPower :
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ i : Fin τ.numPeriods,
        η ((xWord τ i) ^ τ.periods i) ∈ Subgroup.normalClosure S)
    (hTotal :
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      η (totalRelation τ) ∈ Subgroup.normalClosure S) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ r ∈ relators τ, η r ∈ Subgroup.normalClosure S := by
  classical
  dsimp
  intro r hr
  rcases hr with ⟨i, rfl⟩ | rfl
  · exact hPower i
  · exact hTotal
noncomputable def firstReductionCanonicalTargetToSchreierGeneratorImage
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    FuchsianGenerator τ → FreeGroup ↥(schreierGeneratorSet hT) := by
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
  let x : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
  let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
    have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
    rw [MonoidHom.mem_ker, map_pow, hy]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
        ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
      have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
        omega
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
  intro g
  cases g with
  | elliptic i =>
      by_cases h0 : i.val = 0
      · exact e.symm a
      · by_cases h1 : i.val = 1
        · exact e.symm b
        · let r : Fin (p * tailLen) := ⟨i.val - 2, by
            have hi : i.val < 2 + p * tailLen := by
              simp only [firstReductionCanonicalTargetSignature] at i
              exact i.isLt
            omega⟩
          let k : Fin p := ⟨r.val / tailLen, by
            exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using r.isLt)⟩
          let j : Fin tailLen := ⟨r.val % tailLen, Nat.mod_lt _ hTailLen⟩
          exact e.symm (c j k)
  | surfaceA _ => exact 1
  | surfaceB _ => exact 1
noncomputable def firstReductionCanonicalTargetToSchreierHom
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    FreeGroup (FuchsianGenerator τ) →* FreeGroup ↥(schreierGeneratorSet hT) :=
  FreeGroup.lift
    (firstReductionCanonicalTargetToSchreierGeneratorImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
private theorem firstReductionCanonicalTargetToSchreierHom_zero
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
      e.symm a := by
  classical
  dsimp
  simp only [firstReductionCanonicalTargetToSchreierHom, firstReductionCanonicalTargetToSchreierGeneratorImage,
  Lean.Elab.WF.paramLet, id_eq, xWord, firstReductionCanonicalTargetZeroIndex, FreeGroup.lift_apply_of, ↓reduceDIte]
private theorem firstReductionCanonicalTargetToSchreierHom_one
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
      have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
      rw [MonoidHom.mem_ker, map_pow, hy]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
      e.symm b := by
  classical
  dsimp
  simp only [firstReductionCanonicalTargetToSchreierHom, firstReductionCanonicalTargetToSchreierGeneratorImage,
  Lean.Elab.WF.paramLet, id_eq, xWord, firstReductionCanonicalTargetOneIndex, FreeGroup.lift_apply_of, one_ne_zero,
  ↓reduceDIte]
private theorem firstReductionCanonicalTargetToSchreierHom_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let c : Fin tailLen → Fin p → φ.ker := fun j k =>
      ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
          ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
        have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
          simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
          omega
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j)) =
      e.symm (c j k) := by
  classical
  dsimp
  have hzero : 2 + k.val * tailLen + j.val ≠ 0 := by omega
  have hone : 2 + k.val * tailLen + j.val ≠ 1 := by omega
  have hsub :
      2 + k.val * tailLen + j.val - 2 = k.val * tailLen + j.val := by
    omega
  have hdiv : (2 + k.val * tailLen + j.val - 2) / tailLen = k.val := by
    rw [hsub, Nat.mul_comm k.val tailLen, Nat.mul_add_div hTailLen,
      Nat.div_eq_of_lt j.isLt]
    simp only [add_zero]
  have hmod : (2 + k.val * tailLen + j.val - 2) % tailLen = j.val := by
    rw [hsub, Nat.mul_comm k.val tailLen, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  simp only [firstReductionCanonicalTargetToSchreierHom, firstReductionCanonicalTargetToSchreierGeneratorImage,
  Lean.Elab.WF.paramLet, id_eq, xWord, firstReductionCanonicalTargetTailIndex, FreeGroup.lift_apply_of,
  Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, mul_eq_zero, false_and, ↓reduceDIte, hone, hdiv, hmod, Fin.eta]
private theorem firstReductionCanonicalTargetToSchreierHom_zero_named
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
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
      e.symm
        (firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  simpa [firstReductionCanonicalSchreierBasisEquiv,
    firstReductionCanonicalSchreierTransversal,
    firstReductionCanonicalFirstPowerKernel] using
    firstReductionCanonicalTargetToSchreierHom_zero
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
private theorem firstReductionCanonicalTargetToSchreierHom_one_named
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
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
      e.symm
        (firstReductionCanonicalSecondPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  simpa [firstReductionCanonicalSchreierBasisEquiv,
    firstReductionCanonicalSchreierTransversal,
    firstReductionCanonicalSecondPowerKernel] using
    firstReductionCanonicalTargetToSchreierHom_one
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
private theorem firstReductionCanonicalTargetToSchreierHom_tail_named
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (xWord τ
          (firstReductionCanonicalTargetTailIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j)) =
      e.symm
        (firstReductionCanonicalTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k) := by
  classical
  dsimp
  simpa [firstReductionCanonicalSchreierBasisEquiv,
    firstReductionCanonicalSchreierTransversal,
    firstReductionCanonicalTailKernelElement] using
    firstReductionCanonicalTargetToSchreierHom_tail
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j
private theorem firstReductionCanonicalTargetToSchreierHom_tailBlock
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (firstReductionCanonicalTargetTailBlockWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k) =
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k))).prod := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change
    θ
        ((List.ofFn (fun j : Fin tailLen =>
          xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod) =
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k))).prod
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext j
  simpa [σ, τ, e, θ] using
    firstReductionCanonicalTargetToSchreierHom_tail_named
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j
private theorem firstReductionCanonicalSchreierToTarget_toInv_zeroGenerator_mem_normalClosure
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
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (θ
          (xWord τ
            (firstReductionCanonicalTargetZeroIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))) *
      (xWord τ
        (firstReductionCanonicalTargetZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))⁻¹ ∈
        Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [firstReductionCanonicalTargetToSchreierHom_zero_named]
  rw [firstReductionCanonicalSchreierToTargetHom_firstPowerWord]
  simp only [mul_inv_cancel, one_mem]
private theorem firstReductionCanonicalSchreierToTarget_toInv_tailGenerator_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (θ
          (xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))) *
      (xWord τ
        (firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))⁻¹ ∈
        Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  rw [firstReductionCanonicalTargetToSchreierHom_tail_named]
  rw [firstReductionCanonicalSchreierToTargetHom_tailWord]
  simp only [mul_inv_cancel, one_mem]
private theorem firstReductionCanonicalSchreierToTarget_toInv_oneGenerator_mem_normalClosure
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
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (θ
          (xWord τ
            (firstReductionCanonicalTargetOneIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))) *
      (xWord τ
        (firstReductionCanonicalTargetOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))⁻¹ ∈
        Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let n := p - 1
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let A :=
    xWord τ
      (firstReductionCanonicalTargetZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let B :=
    xWord τ
      (firstReductionCanonicalTargetOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let C :=
    (List.ofFn (fun k : Fin p =>
      firstReductionCanonicalTargetTailBlockWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k)).prod
  let secondWord :=
    firstReductionCanonicalSecondEdgeForwardWord
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
  have hTheta :
      θ B =
        e.symm
          (firstReductionCanonicalSecondPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    simpa [σ, τ, e, θ, B] using
      firstReductionCanonicalTargetToSchreierHom_one_named
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hcycle :
      e.symm
          (firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
            ⟨0, hp_pos⟩) *
        (List.ofFn (fun i : Fin n =>
          e.symm
            (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨n - i.val, by omega⟩))).prod =
          e.symm
            (firstReductionCanonicalSecondPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
    simpa [n, σ, e] using
      firstReductionCanonicalSecondDescendingNamedCycle_schreierWord_eq_secondPower
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hImage :
      η
          (e.symm
            (firstReductionCanonicalSecondPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) =
        (secondWord ⟨0, hp_pos⟩)⁻¹ *
          (List.ofFn (fun i : Fin n =>
            (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod := by
    rw [← hcycle]
    rw [map_mul]
    rw [firstReductionCanonicalSchreierToTargetHom_secondEdgeWord]
    rw [map_list_prod, List.map_ofFn]
    congr 1
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    simpa [σ, e, η, secondWord] using
      firstReductionCanonicalSchreierToTargetHom_secondEdgeWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨n - i.val, by omega⟩
  have hDesc :
      (secondWord ⟨0, hp_pos⟩)⁻¹ *
          (List.ofFn (fun i : Fin n =>
            (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod =
        A⁻¹ * C⁻¹ := by
    let block :=
      firstReductionCanonicalTargetTailBlockWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hleft :
        (secondWord ⟨0, hp_pos⟩)⁻¹ *
            (List.ofFn (fun i : Fin n =>
              (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod =
          (block ⟨p - 1, by omega⟩ * A)⁻¹ *
            (List.ofFn (fun i : Fin (p - 1) =>
              (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := by
      subst n
      dsimp [secondWord, block, A, firstReductionCanonicalSecondEdgeForwardWord]
      congr 1
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext i
      have hne : ¬p - 1 - i.val = 0 := by omega
      rw [if_neg hne]
      congr 1
      apply congrArg block
      ext
      simp only
      omega
    have hdesc :
        (block ⟨p - 1, by omega⟩ * A)⁻¹ *
            (List.ofFn (fun i : Fin (p - 1) =>
              (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod =
          A⁻¹ * (List.ofFn block).prod⁻¹ :=
      descending_block_inv_product_eq hp_pos A block
    calc
      (secondWord ⟨0, hp_pos⟩)⁻¹ *
          (List.ofFn (fun i : Fin n =>
            (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod =
          (block ⟨p - 1, by omega⟩ * A)⁻¹ *
            (List.ofFn (fun i : Fin (p - 1) =>
              (block ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod := hleft
      _ = A⁻¹ * (List.ofFn block).prod⁻¹ := hdesc
  have hTarget :
      (A⁻¹ * C⁻¹) * B⁻¹ ∈ Subgroup.normalClosure (relators τ) := by
    simpa [τ, A, B, C, mul_assoc] using
      firstReductionCanonicalTarget_totalRelation_inverseRotated_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [show xWord τ
        (firstReductionCanonicalTargetOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) = B by rfl]
  rw [hTheta, hImage]
  rw [hDesc]
  simpa [mul_assoc] using hTarget
private theorem firstReductionCanonicalSchreierToTarget_toInv_generators_of_oneGenerator
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hOne :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let θ :=
        firstReductionCanonicalTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      η
          (θ
            (xWord τ
              (firstReductionCanonicalTargetOneIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))) *
        (xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))⁻¹ ∈
          Subgroup.normalClosure (relators τ)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ y : FuchsianGenerator τ,
      η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
        Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  intro y
  cases y with
  | elliptic i =>
      by_cases h0 : i.val = 0
      · have hi :
            i =
              firstReductionCanonicalTargetZeroIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
          ext
          simpa [firstReductionCanonicalTargetZeroIndex] using h0
        subst i
        simpa [τ, xWord] using
          firstReductionCanonicalSchreierToTarget_toInv_zeroGenerator_mem_normalClosure
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      · by_cases h1 : i.val = 1
        · have hi :
              i =
                firstReductionCanonicalTargetOneIndex
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
            ext
            simpa [firstReductionCanonicalTargetOneIndex] using h1
          subst i
          simpa [τ, xWord] using hOne
        · let r : Fin (p * tailLen) := ⟨i.val - 2, by
              have hi : i.val < 2 + p * tailLen := by
                simp only [firstReductionCanonicalTargetSignature] at i
                exact i.isLt
              omega⟩
          let k : Fin p := ⟨r.val / tailLen, by
            exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using r.isLt)⟩
          let j : Fin tailLen := ⟨r.val % tailLen, Nat.mod_lt _ hTailLen⟩
          have hiTail :
              i =
                firstReductionCanonicalTargetTailIndex
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j := by
            simpa [r, k, j] using
              firstReductionCanonicalTargetIndex_eq_tailIndex_of_ne_zero_one
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i h0 h1
          rw [hiTail]
          simpa [τ, xWord, r, k, j] using
            firstReductionCanonicalSchreierToTarget_toInv_tailGenerator_mem_normalClosure
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j
  | surfaceA i =>
      exact Fin.elim0 (by
        simpa [τ, firstReductionCanonicalTargetSignature] using i)
  | surfaceB i =>
      exact Fin.elim0 (by
        simpa [τ, firstReductionCanonicalTargetSignature] using i)
private theorem firstReductionCanonicalSchreierToTarget_toInv_generators_mem_normalClosure
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
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ y : FuchsianGenerator τ,
      η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
        Subgroup.normalClosure (relators τ) :=
  firstReductionCanonicalSchreierToTarget_toInv_generators_of_oneGenerator
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalSchreierToTarget_toInv_oneGenerator_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
private theorem firstReductionCanonicalSecondEdgeForwardWord_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    firstReductionCanonicalSecondEdgeForwardWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ =
      firstReductionCanonicalTargetTailBlockWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          ⟨p - 1, by omega⟩ *
        xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp [firstReductionCanonicalSecondEdgeForwardWord]
private theorem firstReductionCanonicalSecondEdgeForwardWord_of_ne_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (h0 : k.val ≠ 0) :
    firstReductionCanonicalSecondEdgeForwardWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k =
      firstReductionCanonicalTargetTailBlockWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨k.val - 1, by omega⟩ := by
  classical
  dsimp [firstReductionCanonicalSecondEdgeForwardWord]
  rw [if_neg h0]
theorem firstReductionCanonicalSchreierToTarget_nonwrapTotalRelator_image_eq_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin (p - 1)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        (e.symm
            (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨k.val + 1, by omega⟩) *
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
                ⟨k.val, by omega⟩))).prod) = 1 := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let block :=
    firstReductionCanonicalTargetTailBlockWord
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [map_mul]
  rw [firstReductionCanonicalSchreierToTargetHom_secondEdgeWord]
  rw [map_list_prod, List.map_ofFn]
  have hne : (⟨k.val + 1, by omega⟩ : Fin p).val ≠ 0 := by
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true]
  rw [firstReductionCanonicalSecondEdgeForwardWord_of_ne_zero
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ⟨k.val + 1, by omega⟩ hne]
  have hprev :
      block ⟨(⟨k.val + 1, by omega⟩ : Fin p).val - 1, by omega⟩ =
        block ⟨k.val, by omega⟩ := by
    apply congrArg block
    ext
    simp only [add_tsub_cancel_right]
  have htailMap :
      (List.ofFn (fun j : Fin tailLen =>
        η
          (e.symm
            (firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
              ⟨k.val, by omega⟩)))) =
        List.ofFn (fun j : Fin tailLen =>
          xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨k.val, by omega⟩ j)) := by
    apply List.ofFn_inj.2
    funext j
    simpa [σ, τ, e, η] using
      firstReductionCanonicalSchreierToTargetHom_tailWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
        ⟨k.val, by omega⟩
  change
    (block ⟨(⟨k.val + 1, by omega⟩ : Fin p).val - 1, by omega⟩)⁻¹ *
        (List.ofFn (fun j : Fin tailLen =>
          η
            (e.symm
              (firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
                ⟨k.val, by omega⟩)))).prod = 1
  rw [htailMap]
  change
    (block ⟨(⟨k.val + 1, by omega⟩ : Fin p).val - 1, by omega⟩)⁻¹ *
      block ⟨k.val, by omega⟩ = 1
  rw [hprev]
  simp only [inv_mul_cancel]
theorem firstReductionCanonicalSchreierToTarget_wrapTotalRelator_image_eq_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        ((List.ofFn (fun j : Fin tailLen =>
            e.symm
              (firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
                ⟨p - 1, by omega⟩))).prod *
          e.symm
            (firstReductionCanonicalFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
          e.symm
            (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩)) = 1 := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let A :=
    xWord τ
      (firstReductionCanonicalTargetZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let block :=
    firstReductionCanonicalTargetTailBlockWord
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [map_mul, map_mul]
  rw [map_list_prod, List.map_ofFn]
  have htailMap :
      (List.ofFn (fun j : Fin tailLen =>
        η
          (e.symm
            (firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
              ⟨p - 1, by omega⟩)))) =
        List.ofFn (fun j : Fin tailLen =>
          xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨p - 1, by omega⟩ j)) := by
    apply List.ofFn_inj.2
    funext j
    simpa [σ, τ, e, η] using
      firstReductionCanonicalSchreierToTargetHom_tailWord
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
        ⟨p - 1, by omega⟩
  change
      (List.ofFn (fun j : Fin tailLen =>
        η
          (e.symm
            (firstReductionCanonicalTailKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
              ⟨p - 1, by omega⟩)))).prod *
        η
          (e.symm
            (firstReductionCanonicalFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) *
        η
          (e.symm
            (firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
              ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩)) = 1
  rw [htailMap]
  rw [firstReductionCanonicalSchreierToTargetHom_firstPowerWord]
  rw [firstReductionCanonicalSchreierToTargetHom_secondEdgeWord]
  rw [firstReductionCanonicalSecondEdgeForwardWord_zero]
  change block ⟨p - 1, by omega⟩ * A *
      (block ⟨p - 1, by omega⟩ * A)⁻¹ = 1
  group
private theorem firstReductionCanonicalSecondEdgeForward_invComp_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (firstReductionCanonicalSecondEdgeForwardWord
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k) *
      e.symm
        (firstReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k) ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  by_cases h0 : k.val = 0
  · have hk :
        k = ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hp⟩ := by
      ext
      simpa using h0
    subst k
    rw [firstReductionCanonicalSecondEdgeForwardWord_zero]
    rw [map_mul]
    rw [firstReductionCanonicalTargetToSchreierHom_tailBlock]
    rw [firstReductionCanonicalTargetToSchreierHom_zero_named]
    simpa [σ, τ, e, θ, mul_assoc] using
      firstReductionCanonicalSchreier_wrapGeneratorElimination_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  · let i : Fin (p - 1) := ⟨k.val - 1, by
        have hklt := k.isLt
        omega⟩
    have hkSucc :
        (⟨i.val + 1, by omega⟩ : Fin p) = k := by
      ext
      simp only [i]
      omega
    rw [firstReductionCanonicalSecondEdgeForwardWord_of_ne_zero
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k h0]
    rw [firstReductionCanonicalTargetToSchreierHom_tailBlock]
    simpa [σ, τ, e, θ, i, hkSucc, mul_assoc] using
      firstReductionCanonicalSchreier_nonwrapGeneratorElimination_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i
private theorem firstReductionCanonicalSchreierToTarget_invComp_generator_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (z :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let hT :=
        firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ↥(schreierGeneratorSet hT)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
      Subgroup.normalClosure
        (firstReductionCanonicalSchreierRelatorSet
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
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
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hzWord :
      (FreeGroup.of z)⁻¹ = e.symm (z : φ.ker) := by
    symm
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSchreierBasisEquiv_symm_apply, e]
  by_cases hFirst :
      (z : φ.ker) =
        firstReductionCanonicalFirstPowerKernel
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  · have hzFirst :
        (FreeGroup.of z)⁻¹ =
          e.symm
            (firstReductionCanonicalFirstPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
      rw [hzWord, hFirst]
    simp only [firstReductionCanonicalSchreierToTargetHom, firstReductionCanonicalSchreierToTargetGeneratorImage,
  Lean.Elab.WF.paramLet, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, map_inv,
  firstReductionCanonicalTargetToSchreierHom_zero_named, hzFirst, inv_mul_cancel, one_mem, e, σ]
  · by_cases hSecond :
      ∃ k : Fin p,
        (z : φ.ker) =
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k
    · rcases hSecond with ⟨k, hzK⟩
      let k' : Fin p := Classical.choose (show ∃ k : Fin p,
        (z : φ.ker) =
          firstReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k from ⟨k, hzK⟩)
      have hzK' :
          (z : φ.ker) =
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k' :=
        Classical.choose_spec (show ∃ k : Fin p,
          (z : φ.ker) =
            firstReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k from ⟨k, hzK⟩)
      have hzKWord :
          (FreeGroup.of z)⁻¹ =
            e.symm
              (firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k') := by
        rw [hzWord, hzK']
      have hSecond' :
          ∃ k : Fin p,
            (z : φ.ker) =
              firstReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k := ⟨k, hzK⟩
      simpa [σ, τ, φ, hT, e, θ, η,
        firstReductionCanonicalSchreierToTargetHom,
        firstReductionCanonicalSchreierToTargetGeneratorImage,
        hFirst, hSecond', k', hzKWord] using
        firstReductionCanonicalSecondEdgeForward_invComp_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k'
    · rcases
        firstReductionCanonical_schreierGeneratorSet_cases
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen z with
        hFirstCase | hSecondCase | hTailCase
      · exact False.elim (hFirst hFirstCase)
      · exact False.elim (hSecond hSecondCase)
      · let j : Fin tailLen := Classical.choose hTailCase
        let hk : ∃ k : Fin p,
            (z : φ.ker) =
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k :=
          Classical.choose_spec hTailCase
        let k : Fin p := Classical.choose hk
        have hzTail :
            (z : φ.ker) =
              firstReductionCanonicalTailKernelElement
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k :=
          Classical.choose_spec hk
        have hzTailWord :
            (FreeGroup.of z)⁻¹ =
              e.symm
                (firstReductionCanonicalTailKernelElement
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k) := by
          rw [hzWord, hzTail]
        simp only [firstReductionCanonicalSchreierToTargetHom, firstReductionCanonicalSchreierToTargetGeneratorImage,
  Lean.Elab.WF.paramLet, dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, hSecond, ↓reduceDIte,
  hTailCase, map_inv, firstReductionCanonicalTargetToSchreierHom_tail_named, hzTailWord, inv_mul_cancel, one_mem, e,
  j, k, σ]
private theorem firstReductionCanonicalSchreierToTarget_invComp_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let hT :=
      firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ w : FreeGroup ↥(schreierGeneratorSet hT),
      θ (η w) * w⁻¹ ∈
        Subgroup.normalClosure
          (firstReductionCanonicalSchreierRelatorSet
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let hT :=
    firstReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let R :=
    firstReductionCanonicalSchreierRelatorSet
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let F : FreeGroup ↥(schreierGeneratorSet hT) →* FreeGroup ↥(schreierGeneratorSet hT) :=
    θ.comp η
  have hgen :
      ∀ z : ↥(schreierGeneratorSet hT),
        F (FreeGroup.of z) * (FreeGroup.of z)⁻¹ ∈ Subgroup.normalClosure R := by
    intro z
    simpa [σ, τ, hT, θ, η, R, F] using
      firstReductionCanonicalSchreierToTarget_invComp_generator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen z
  intro w
  simpa [R, F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv R F hgen w
private theorem firstReductionCanonicalSchreierToTarget_toInv_mem_normalClosure_of_generators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hgen :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let θ :=
        firstReductionCanonicalTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ y : FuchsianGenerator τ,
        η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators τ)) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ y : FreeGroup (FuchsianGenerator τ),
      η (θ y) * y⁻¹ ∈ Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let F : FreeGroup (FuchsianGenerator τ) →* FreeGroup (FuchsianGenerator τ) := η.comp θ
  have hgen' :
      ∀ y : FuchsianGenerator τ,
        F (FreeGroup.of y) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators τ) := by
    intro y
    simpa [σ, τ, θ, η, F] using hgen y
  intro y
  simpa [F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv
      (relators τ) F hgen' y
theorem firstReductionCanonicalSchreierToTarget_firstPowerRelator_mem_normalClosure
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
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        ((e.symm
          (firstReductionCanonicalFirstPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) ^ m₁') ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [map_pow, firstReductionCanonicalSchreierToTargetHom_firstPowerWord]
  exact
    Subgroup.subset_normalClosure
      (Or.inl
        ⟨firstReductionCanonicalTargetZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, by
          simp only [firstReductionCanonicalTargetSignature_period_zero]⟩)
theorem firstReductionCanonicalSchreierToTarget_tailPowerRelator_mem_normalClosure
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
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        ((e.symm
          (firstReductionCanonicalTailKernelElement
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k)) ^ tail j) ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [map_pow, firstReductionCanonicalSchreierToTargetHom_tailWord]
  exact
    Subgroup.subset_normalClosure
      (Or.inl
        ⟨firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j, by
          simp only [firstReductionCanonicalTargetSignature_period_tail]⟩)
theorem firstReductionCanonicalSchreierToTarget_secondPowerRelator_mem_normalClosure
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
    let e :=
      firstReductionCanonicalSchreierBasisEquiv
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let η :=
      firstReductionCanonicalSchreierToTargetHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    η
        ((e.symm
          (firstReductionCanonicalSecondPowerKernel
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) ^ m₂') ∈
      Subgroup.normalClosure (relators τ) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    firstReductionCanonicalSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let B :=
    xWord τ
      (firstReductionCanonicalTargetOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  have hcongr :
      η
          (e.symm
            (firstReductionCanonicalSecondPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) *
        B⁻¹ ∈ Subgroup.normalClosure (relators τ) := by
    have hTheta :
        firstReductionCanonicalTargetToSchreierHom
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen B =
          e.symm
            (firstReductionCanonicalSecondPowerKernel
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
      simpa [σ, τ, e, B] using
        firstReductionCanonicalTargetToSchreierHom_one_named
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    have hOne :
        η
            (firstReductionCanonicalTargetToSchreierHom
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen B) *
          B⁻¹ ∈ Subgroup.normalClosure (relators τ) := by
      simpa [σ, τ, η, B] using
        firstReductionCanonicalSchreierToTarget_toInv_oneGenerator_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    rwa [hTheta] at hOne
  have hBpow : B ^ m₂' ∈ Subgroup.normalClosure (relators τ) :=
    Subgroup.subset_normalClosure
      (Or.inl
        ⟨firstReductionCanonicalTargetOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen, by
          simp only [firstReductionCanonicalTargetSignature_period_one, τ, B]⟩)
  rw [map_pow]
  exact ReidemeisterSchreier.Discrete.Presentations.pow_mem_normalClosure_of_mul_inv_mem hcongr hBpow
private theorem firstReductionCanonicalSchreier_firstDistinguishedPower_mem_normalClosure
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
    let x : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
    (e.symm a) ^ m₁' ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let a : φ.ker := ⟨(FreeGroup.of x) ^ p, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩
  let i₀ :=
    firstReductionCanonicalSourceZeroIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let r := (xWord σ i₀) ^ σ.periods i₀
  have ht : (1 : FreeGroup (FuchsianGenerator σ)) ∈ T := by
    have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
    simpa [T] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := 0) hp_pos
  have hr : r ∈ relators σ := Or.inl ⟨i₀, rfl⟩
  have hrel :
      e.symm
          (⟨(1 : FreeGroup (FuchsianGenerator σ)) * r * 1⁻¹, by
            change φ ((1 : FreeGroup (FuchsianGenerator σ)) * r * 1⁻¹) = 1
            have hrφ : φ r = 1 := hrels r hr
            simp only [Lean.Elab.WF.paramLet, one_mul, inv_one, mul_one, hrφ]⟩ : φ.ker) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure hrels e ht hr
  change
    (e.symm a) ^ m₁' ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T))
  have hpow : (e.symm a) ^ m₁' = e.symm (a ^ m₁') :=
    (map_pow e.symm a m₁').symm
  rw [hpow]
  simpa [a, r, i₀, x, σ, xWord, firstReductionCanonicalSourceSignature,
    firstReductionCanonicalSourceZeroIndex, firstReductionCanonicalSourcePeriod,
    pow_mul] using hrel
private theorem firstReductionCanonicalSchreier_secondDistinguishedPower_mem_normalClosure
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
    let x : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let y : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
      have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
      rw [MonoidHom.mem_ker, map_pow, hy]
      apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
      simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
    (e.symm b) ^ m₂' ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceOneIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let b : φ.ker := ⟨(FreeGroup.of y) ^ p, by
    have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, one_ne_zero, ↓reduceIte, ofAdd_neg, φ, y]
    rw [MonoidHom.mem_ker, map_pow, hy]
    apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
    simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]⟩
  let i₁ :=
    firstReductionCanonicalSourceOneIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let r := (xWord σ i₁) ^ σ.periods i₁
  have ht : (1 : FreeGroup (FuchsianGenerator σ)) ∈ T := by
    have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
    simpa [T] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := 0) hp_pos
  have hr : r ∈ relators σ := Or.inl ⟨i₁, rfl⟩
  have hrel :
      e.symm
          (⟨(1 : FreeGroup (FuchsianGenerator σ)) * r * 1⁻¹, by
            change φ ((1 : FreeGroup (FuchsianGenerator σ)) * r * 1⁻¹) = 1
            have hrφ : φ r = 1 := hrels r hr
            simp only [Lean.Elab.WF.paramLet, one_mul, inv_one, mul_one, hrφ]⟩ : φ.ker) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure hrels e ht hr
  change
    (e.symm b) ^ m₂' ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T))
  have hpow : (e.symm b) ^ m₂' = e.symm (b ^ m₂') :=
    (map_pow e.symm b m₂').symm
  rw [hpow]
  simpa [b, r, i₁, y, σ, xWord, firstReductionCanonicalSourceSignature,
    firstReductionCanonicalSourceOneIndex, firstReductionCanonicalSourcePeriod,
    pow_mul] using hrel
private theorem firstReductionCanonicalSchreier_tailPower_mem_normalClosure
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
    let x : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    let c : Fin tailLen → Fin p → φ.ker := fun j k =>
      ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
          ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
        have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
          simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
          omega
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
    (e.symm (c j k)) ^ tail j ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let tailGen : Fin tailLen → FuchsianGenerator σ := fun j =>
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let c : Fin tailLen → Fin p → φ.ker := fun j k =>
    ⟨(FreeGroup.of x) ^ (k : ℕ) * FreeGroup.of (tailGen j) *
        ((FreeGroup.of x) ^ (k : ℕ))⁻¹, by
      have htailMap : φ (FreeGroup.of (tailGen j)) = 1 := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceTailIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceIte,
  ofAdd_neg, ite_eq_right_iff, inv_eq_one, ofAdd_eq_one, φ, tailGen]
        omega
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_pow, hx, htailMap, mul_one, map_inv, mul_inv_cancel]⟩
  let iTail :=
    firstReductionCanonicalSourceTailIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j
  let r := (xWord σ iTail) ^ σ.periods iTail
  let t : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ (k : ℕ)
  have ht : t ∈ T := by
    simpa [T, t] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := (k : ℕ)) k.isLt
  have hr : r ∈ relators σ := Or.inl ⟨iTail, rfl⟩
  have hrel :
      e.symm
          (⟨t * r * t⁻¹, by
            change φ (t * r * t⁻¹) = 1
            have hrφ : φ r = 1 := hrels r hr
            simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure hrels e ht hr
  change
    (e.symm (c j k)) ^ tail j ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T))
  have hpow : (e.symm (c j k)) ^ tail j = e.symm ((c j k) ^ tail j) :=
    (map_pow e.symm (c j k) (tail j)).symm
  rw [hpow]
  have htailZero : 2 + j.val ≠ 0 := by omega
  have htailOne : 2 + j.val ≠ 1 := by omega
  simpa [c, r, iTail, t, x, tailGen, σ, xWord,
    firstReductionCanonicalSourceSignature, firstReductionCanonicalSourceTailIndex,
    firstReductionCanonicalSourcePeriod, htailZero, htailOne, conj_pow, map_pow] using hrel
private theorem firstReductionCanonicalTargetToSchreier_powerRelator_mem_normalClosure
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (i :
      Fin
        (firstReductionCanonicalTargetSignature
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods) :
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ((xWord τ i) ^ τ.periods i) ∈
      Subgroup.normalClosure
        (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  by_cases h0 : i.val = 0
  · have hi :
        i =
          firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
      ext
      simpa [firstReductionCanonicalTargetZeroIndex] using h0
    subst i
    rw [map_pow]
    rw [firstReductionCanonicalTargetToSchreierHom_zero]
    simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using
      firstReductionCanonicalSchreier_firstDistinguishedPower_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  · by_cases h1 : i.val = 1
    · have hi :
          i =
            firstReductionCanonicalTargetOneIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
        ext
        simpa [firstReductionCanonicalTargetOneIndex] using h1
      subst i
      rw [map_pow]
      rw [firstReductionCanonicalTargetToSchreierHom_one]
      simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using
        firstReductionCanonicalSchreier_secondDistinguishedPower_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    · let r : Fin (p * tailLen) := ⟨i.val - 2, by
        have hi : i.val < 2 + p * tailLen := by
          simp only [firstReductionCanonicalTargetSignature] at i
          exact i.isLt
        omega⟩
      let k : Fin p := ⟨r.val / tailLen, by
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using r.isLt)⟩
      let j : Fin tailLen := ⟨r.val % tailLen, Nat.mod_lt _ hTailLen⟩
      have hiTail :
          i =
            firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j := by
        simpa [r, k, j] using
          firstReductionCanonicalTargetIndex_eq_tailIndex_of_ne_zero_one
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i h0 h1
      rw [hiTail]
      rw [map_pow]
      rw [firstReductionCanonicalTargetToSchreierHom_tail]
      simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η, r, k, j] using
        firstReductionCanonicalSchreier_tailPower_mem_normalClosure
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j k
private theorem firstReductionCanonicalTargetToSchreier_mapsTargetRelators
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
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    ∀ r ∈ relators τ,
      firstReductionCanonicalTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T)) := by
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  refine
    firstReductionCanonicalTarget_mapsRelators_of_power_and_total
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      (η := η)
      ?_ ?_
  · dsimp
    intro i
    simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using
      firstReductionCanonicalTargetToSchreier_powerRelator_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen i
  · refine
      firstReductionCanonicalTarget_totalRelation_image_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        η ?_ ?_ ?_
    · simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using
        firstReductionCanonicalTargetToSchreierHom_zero
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    · simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using
        firstReductionCanonicalTargetToSchreierHom_one
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    · intro k j
      simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using
        firstReductionCanonicalTargetToSchreierHom_tail
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j
def FirstReductionCanonicalSchreierRelatorData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) : Type :=
  (letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    ReidemeisterSchreier.Discrete.Presentations.RelatorQuotientMutualMapData
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T))
      (relators τ))
def FirstReductionCanonicalForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) : Type :=
  (letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let φ :=
      firstReductionCanonicalSourceFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let x : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    ReidemeisterSchreier.Discrete.Presentations.RelatorQuotientForwardMapData
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T))
      (relators τ)
      (firstReductionCanonicalTargetToSchreierHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
noncomputable def firstReductionCanonicalForwardMapData_of_mapsRelators_toInv
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hMapsRelators :
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
        FuchsianGenerator.elliptic
          (firstReductionCanonicalSourceZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
      let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
      let hT : IsRightSchreierTransversal φ.ker T :=
        cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
      let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
        freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ r ∈ ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T),
        η r ∈ Subgroup.normalClosure (relators τ))
    (hToInv :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let θ :=
        firstReductionCanonicalTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ y : FreeGroup (FuchsianGenerator τ),
        η (θ y) * y⁻¹ ∈ Subgroup.normalClosure (relators τ)) :
    FirstReductionCanonicalForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
  classical
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let θ :=
    firstReductionCanonicalTargetToSchreierHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let η :=
    firstReductionCanonicalSchreierToTargetHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  refine
    { toHom := η
      mapsRelators := ?_
      inv_toHom := ?_
      to_invHom := ?_ }
  · intro r hr
    simpa [σ, τ, φ, x, hx, T, hT, e, hrels, η] using hMapsRelators r hr
  · intro w
    simpa [σ, τ, φ, x, hx, T, hT, e, hrels, θ, η] using
      firstReductionCanonicalSchreierToTarget_invComp_mem_normalClosure
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen w
  · intro y
    simpa [σ, τ, θ, η] using hToInv y
noncomputable def firstReductionCanonicalForwardMapData_of_mapsRelators_toInvGenerators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hMapsRelators :
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
        FuchsianGenerator.elliptic
          (firstReductionCanonicalSourceZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
      let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
      let hT : IsRightSchreierTransversal φ.ker T :=
        cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
      let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
        freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ r ∈ ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T),
        η r ∈ Subgroup.normalClosure (relators τ))
    (hToInvGenerators :
      letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
      let σ :=
        firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let τ :=
        firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
      let θ :=
        firstReductionCanonicalTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ y : FuchsianGenerator τ,
        η (θ (FreeGroup.of y)) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure (relators τ)) :
    FirstReductionCanonicalForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen :=
  firstReductionCanonicalForwardMapData_of_mapsRelators_toInv
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    hMapsRelators
    (firstReductionCanonicalSchreierToTarget_toInv_mem_normalClosure_of_generators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen hToInvGenerators)
noncomputable def firstReductionCanonicalForwardMapData_of_mapsRelators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (hMapsRelators :
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
        FuchsianGenerator.elliptic
          (firstReductionCanonicalSourceZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
        simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
      let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
      let hT : IsRightSchreierTransversal φ.ker T :=
        cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
      let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
        freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
      let η :=
        firstReductionCanonicalSchreierToTargetHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ r ∈ ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T),
        η r ∈ Subgroup.normalClosure (relators τ)) :
    FirstReductionCanonicalForwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen :=
  firstReductionCanonicalForwardMapData_of_mapsRelators_toInvGenerators
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    hMapsRelators
    (firstReductionCanonicalSchreierToTarget_toInv_generators_mem_normalClosure
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
noncomputable def firstReductionCanonicalSchreierRelatorData_of_forwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (D :
      FirstReductionCanonicalForwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) :
    FirstReductionCanonicalSchreierRelatorData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen := by
  classical
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
    FuchsianGenerator.elliptic
      (firstReductionCanonicalSourceZeroIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
  let hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [Lean.Elab.WF.paramLet, firstReductionCanonicalSourceFreeQuotientHom, id_eq,
  firstReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  firstReductionCanonicalSourceQuotientImage, ↓reduceIte, φ, x]
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let hrels :=
    firstReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  simpa [FirstReductionCanonicalSchreierRelatorData, σ, τ, φ, x, hx, T, hT, e, hrels] using
    (ReidemeisterSchreier.Discrete.Presentations.relatorQuotientMutualMapDataOfForwardMapData
      (R := ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
          (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (firstReductionCanonicalSourceQuotientImage
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen))
            (rels := relators σ) T))
      (S := relators τ)
      (invHom :=
        firstReductionCanonicalTargetToSchreierHom
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      (firstReductionCanonicalTargetToSchreier_mapsTargetRelators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      D)
noncomputable def firstReductionCanonicalKernelEquivOfRelatorData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (D :
      FirstReductionCanonicalSchreierRelatorData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let ξ :=
      firstReductionCanonicalSourceQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let hrels : ∀ r ∈ relators σ,
        FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ) r = 1 := by
      simpa [ξ, firstReductionCanonicalSourceFreeQuotientHom] using
        firstReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (PresentedGroup.toGroup (rels := relators σ)
      (f := ellipticQuotientGeneratorImage σ ξ) hrels).ker ≃*
        FuchsianPresentedGroup τ := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let ξ :=
    firstReductionCanonicalSourceQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hpow : ∀ i, ξ i ^ σ.periods i = 1 :=
    firstReductionCanonicalSourceQuotientImage_pow
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hprod : ∏ i : Fin σ.numPeriods, ξ i = 1 :=
    firstReductionCanonicalSourceQuotientImage_prod
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let hrels : ∀ r ∈ relators σ,
      FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ) r = 1 := by
    simpa [ξ, firstReductionCanonicalSourceFreeQuotientHom] using
      firstReductionCanonicalSourceFreeQuotientHom_respects_relators
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let i₀ :=
    firstReductionCanonicalSourceZeroIndex
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  have hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [firstReductionCanonicalSourceZeroIndex, firstReductionCanonicalSourceQuotientImage, ↓reduceIte, ξ,
  i₀]
  have hData :
      FuchsianEllipticCyclicSchreierRelatorData σ τ ξ i₀ hi₀ := by
    simpa [FuchsianEllipticCyclicSchreierRelatorData,
      FirstReductionCanonicalSchreierRelatorData, σ, τ, ξ, i₀, hi₀,
      firstReductionCanonicalSourceFreeQuotientHom] using D
  simpa [ellipticQuotientHom, σ, τ, ξ, hpow, hprod, hrels] using
    fuchsianEllipticCyclicKernelEquivOfRelatorData
      σ τ ξ hpow hprod i₀ hi₀ hData
noncomputable def firstReductionCanonicalKernelEquivOfForwardMapData
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (D :
      FirstReductionCanonicalForwardMapData
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) :=
  firstReductionCanonicalKernelEquivOfRelatorData
    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (firstReductionCanonicalSchreierRelatorData_of_forwardMapData
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen D)
end FenchelNielsen
