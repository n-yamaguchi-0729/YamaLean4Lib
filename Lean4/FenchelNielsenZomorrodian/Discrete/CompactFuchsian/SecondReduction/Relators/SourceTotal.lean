import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceCore

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/Relators/SourceTotal.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen

def SecondReductionCanonicalSecondBranchSourceTotalCase
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
        Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
theorem secondReductionCanonicalSecondBranchSourceTotalCase_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    SecondReductionCanonicalSecondBranchSourceTotalCase
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
  classical
  dsimp [SecondReductionCanonicalSecondBranchSourceTotalCase]
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
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let h0Gen : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceZeroIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  let h1Gen : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceOneIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
  let midGen : Fin (p - 2) → FuchsianGenerator σ := fun r =>
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
  let tailGen : Fin p → Fin tailLen → FuchsianGenerator σ := fun b j =>
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
  let z : φ.ker :=
    ⟨(FreeGroup.of x) ^ k.val * totalRelation σ *
        ((FreeGroup.of x) ^ k.val)⁻¹, by
      change φ
          ((FreeGroup.of x) ^ k.val * totalRelation σ *
            ((FreeGroup.of x) ^ k.val)⁻¹) = 1
      have hrφ : φ (totalRelation σ) = 1 :=
        secondReductionCanonicalSourceFreeQuotientHom_respects_relators
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (totalRelation σ) (Or.inr rfl)
      simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  change η (e.symm z) ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  by_cases hlast : k.val = q - 1
  · let kLast : Fin q := ⟨q - 1, by omega⟩
    let kZero : Fin q := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
    let xk : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ (q - 1)
    have hk : k = kLast := Fin.ext hlast
    have hmiddleConj :
        (List.ofFn (fun r : Fin (p - 2) =>
          xk * FreeGroup.of (midGen r) * xk⁻¹)).prod =
            xk * (List.ofFn (fun r : Fin (p - 2) =>
              FreeGroup.of (midGen r))).prod * xk⁻¹ := by
      simpa using
        (ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod xk
          (List.ofFn (fun r : Fin (p - 2) => FreeGroup.of (midGen r)))).symm
    have htailConj :
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod =
            xk *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  FreeGroup.of (tailGen b j))).prod)).prod *
              xk⁻¹ := by
      simpa using
        ReidemeisterSchreier.Discrete.Presentations.nested_conjugate_list_prod xk
          (fun b : Fin p => fun j : Fin tailLen => FreeGroup.of (tailGen b j))
    have hsecondZeroCoe :
        ((secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
            FreeGroup.of y * xk⁻¹ := by
      simpa [σ, φ, x, y, xk, kZero] using
        secondReductionCanonicalSecondEdgeKernelElement_zero_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    have hmiddleZeroVals :
        (List.ofFn (fun r : Fin (p - 2) =>
          ((secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))).prod =
            (List.ofFn (fun r : Fin (p - 2) =>
              xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext r
      simpa [σ, φ, x, midGen, xk, kLast] using
        secondReductionCanonicalMiddleRestZeroKernelElement_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast
    have htailZeroVals :
        (List.ofFn (fun b : Fin p =>
          (((List.ofFn (fun j : Fin tailLen =>
            secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod :
                φ.ker) : FreeGroup (FuchsianGenerator σ)))).prod =
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod := by
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext b
      change
        (((List.ofFn (fun j : Fin tailLen =>
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (List.ofFn (fun j : Fin tailLen =>
            xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod
      rw [ReidemeisterSchreier.Discrete.Presentations.subgroup_list_prod_val]
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext j
      simpa [σ, φ, x, tailGen, xk, kLast] using
        secondReductionCanonicalTailZeroKernelElement_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast
    have hsecondZeroCoe0 :
        ((secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail (0 : Fin q) :
              φ.ker) : FreeGroup (FuchsianGenerator σ)) =
            FreeGroup.of y * xk⁻¹ := by
      simpa [kZero] using hsecondZeroCoe
    have hmiddleZeroVals' :
        (List.ofFn (Subtype.val ∘ fun r : Fin (p - 2) =>
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast)).prod =
            (List.ofFn (fun r : Fin (p - 2) =>
              xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
      simpa only [Function.comp_apply] using hmiddleZeroVals
    have htailZeroVals' :
        (List.ofFn (Subtype.val ∘ fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod =
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod := by
      simpa only [Function.comp_apply] using htailZeroVals
    have hkerEq :
        z =
          secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast *
            secondReductionCanonicalHeadOneKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast *
            secondReductionCanonicalFirstPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail *
            secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero *
            (List.ofFn (fun r : Fin (p - 2) =>
              secondReductionCanonicalMiddleRestZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast)).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                secondReductionCanonicalTailZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * totalRelation σ *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
          (((secondReductionCanonicalHeadZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast *
              secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast *
              secondReductionCanonicalFirstPowerKernel
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail *
              secondReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero *
              (List.ofFn (fun r : Fin (p - 2) =>
                secondReductionCanonicalMiddleRestZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast)).prod *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  secondReductionCanonicalTailZeroKernelElement
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))
      rw [secondReductionCanonicalSource_totalRelation_eq
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail]
      rw [hk]
      simp only [secondReductionCanonicalDistinguishedGenerator, xWord, mul_assoc, Lean.Elab.WF.paramLet,
  Fin.mk_zero', Subgroup.coe_mul, secondReductionCanonicalHeadZeroKernelElement_coe,
  secondReductionCanonicalHeadOneKernelElement_coe, secondReductionCanonicalFirstPowerKernel_coe,
  Subgroup.val_list_prod, List.map_ofFn, inv_mul_cancel_left, mul_right_inj, σ, x, kLast, kZero]
      rw [hsecondZeroCoe0, hmiddleZeroVals', htailZeroVals']
      rw [hmiddleConj, htailConj]
      have hpow :
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ q =
            (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ (q - 1) *
              FreeGroup.of x := by
        have hq' : q = q - 1 + 1 := by omega
        rw [hq', pow_succ]
        have hnat : q - 1 + 1 - 1 = q - 1 := by omega
        rw [hnat]
      rw [hpow]
      simp only [secondReductionCanonicalDistinguishedGenerator, conj_mul, x, y, xk, midGen, tailGen]
      group
    have hwrap :=
      secondReductionCanonicalSchreierToTransportSecondBranch_wrapTotalRelator_image_eq_one
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    rw [hkerEq]
    simp only [map_mul]
    have hEq :
        η ((MulEquiv.symm e)
            (secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast)) *
              η ((MulEquiv.symm e)
                (secondReductionCanonicalHeadOneKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast)) *
            η ((MulEquiv.symm e)
              (secondReductionCanonicalFirstPowerKernel
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) *
          η ((MulEquiv.symm e)
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero)) *
        η ((MulEquiv.symm e)
          (List.ofFn (fun r : Fin (p - 2) =>
            secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast)).prod) *
      η ((MulEquiv.symm e)
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod) =
          1 := by
      simpa [σ, e, η, kLast, kZero, Function.comp_def, map_list_prod, List.map_ofFn]
        using hwrap
    rw [hEq]
    exact Subgroup.one_mem _
  · let knw : Fin (q - 1) := ⟨k.val, by omega⟩
    let k0 : Fin q := ⟨knw.val, by omega⟩
    let k1 : Fin q := ⟨knw.val + 1, by omega⟩
    let xk : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ k.val
    have hk0 : k = k0 := by
      ext
      simp only [knw, k0]
    have hmiddleConj :
        (List.ofFn (fun r : Fin (p - 2) =>
          xk * FreeGroup.of (midGen r) * xk⁻¹)).prod =
            xk * (List.ofFn (fun r : Fin (p - 2) =>
              FreeGroup.of (midGen r))).prod * xk⁻¹ := by
      simpa using
        (ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod xk
          (List.ofFn (fun r : Fin (p - 2) => FreeGroup.of (midGen r)))).symm
    have htailConj :
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod =
            xk *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  FreeGroup.of (tailGen b j))).prod)).prod *
              xk⁻¹ := by
      simpa using
        ReidemeisterSchreier.Discrete.Presentations.nested_conjugate_list_prod xk
          (fun b : Fin p => fun j : Fin tailLen => FreeGroup.of (tailGen b j))
    have hsecondSuccCoe :
        ((secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨k.val + 1, by omega⟩ : φ.ker) :
          FreeGroup (FuchsianGenerator σ)) =
            (FreeGroup.of x) ^ (k.val + 1) * FreeGroup.of y * xk⁻¹ := by
      simpa [σ, φ, x, y, xk, knw] using
        secondReductionCanonicalSecondEdgeKernelElement_succ_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail knw
    have hmiddleZeroVals :
        (List.ofFn (Subtype.val ∘ fun r : Fin (p - 2) =>
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k)).prod =
            (List.ofFn (fun r : Fin (p - 2) =>
              xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext r
      simpa [σ, φ, x, midGen, xk] using
        secondReductionCanonicalMiddleRestZeroKernelElement_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
    have htailZeroVals :
        (List.ofFn (Subtype.val ∘ fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k)).prod)).prod =
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod := by
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext b
      change
        (((List.ofFn (fun j : Fin tailLen =>
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k)).prod :
            φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (List.ofFn (fun j : Fin tailLen =>
            xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod
      rw [ReidemeisterSchreier.Discrete.Presentations.subgroup_list_prod_val]
      apply congrArg List.prod
      apply List.ofFn_inj.2
      funext j
      simpa [σ, φ, x, tailGen, xk] using
        secondReductionCanonicalTailZeroKernelElement_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
    have hkerEq :
          z =
            secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0 *
            secondReductionCanonicalHeadOneKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0 *
            secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1 *
            (List.ofFn (fun r : Fin (p - 2) =>
              secondReductionCanonicalMiddleRestZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0)).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                secondReductionCanonicalTailZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod)).prod := by
      apply Subtype.ext
      change
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val * totalRelation σ *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val)⁻¹ =
          (((secondReductionCanonicalHeadZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0 *
              secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0 *
              secondReductionCanonicalSecondEdgeKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1 *
              (List.ofFn (fun r : Fin (p - 2) =>
                secondReductionCanonicalMiddleRestZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0)).prod *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  secondReductionCanonicalTailZeroKernelElement
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator σ)))
      rw [secondReductionCanonicalSource_totalRelation_eq
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail]
      rw [hk0]
      simp only [secondReductionCanonicalDistinguishedGenerator, xWord, mul_assoc, Lean.Elab.WF.paramLet, Fin.eta,
  Subgroup.coe_mul, secondReductionCanonicalHeadZeroKernelElement_coe,
  secondReductionCanonicalHeadOneKernelElement_coe, Subgroup.val_list_prod, List.map_ofFn, inv_mul_cancel_left,
  mul_right_inj, σ, x, k0, k1, knw]
      rw [hsecondSuccCoe, hmiddleZeroVals, htailZeroVals]
      rw [hmiddleConj, htailConj]
      simp only [secondReductionCanonicalDistinguishedGenerator, conj_mul, x, y, xk, midGen, tailGen]
      group
    have hnonwrap :=
      secondReductionCanonicalSchreierToTransportSecondBranch_nonwrapTotalRelator_image_eq_one
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail knw
    rw [hkerEq]
    simp only [map_mul]
    have hEq :
        η ((MulEquiv.symm e)
            (secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0)) *
            η ((MulEquiv.symm e)
              (secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0)) *
          η ((MulEquiv.symm e)
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1)) *
        η ((MulEquiv.symm e)
          (List.ofFn (fun r : Fin (p - 2) =>
            secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0)).prod) *
      η ((MulEquiv.symm e)
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod)).prod) =
          1 := by
      simpa [σ, e, η, knw, k0, k1, Function.comp_def, map_list_prod, List.map_ofFn]
        using hnonwrap
    rw [hEq]
    exact Subgroup.one_mem _

end FenchelNielsen
