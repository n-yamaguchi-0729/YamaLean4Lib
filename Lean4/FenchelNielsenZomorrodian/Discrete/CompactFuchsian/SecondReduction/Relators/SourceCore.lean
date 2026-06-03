import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.Target

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/Relators/SourceCore.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen

noncomputable def secondReductionCanonicalSecondEdgeForwardWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    Fin q → FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let A :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
      (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)
  let block :=
    secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  intro k
  if h0 : k.val = 0 then
    exact block ⟨q - 1, by omega⟩ * A
  else
    exact block ⟨k.val - 1, by omega⟩
noncomputable def secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage
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
    ↥(schreierGeneratorSet hT) →
      FreeGroup (FuchsianGenerator
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let φ :=
    secondReductionCanonicalSourceFreeQuotientHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let A : FreeGroup (FuchsianGenerator
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)) :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
      (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)
  let secondWord :=
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  intro z
  if hFirst :
      (z : φ.ker) =
        secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail then
    exact A⁻¹
  else if hSecond :
      ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k then
    exact secondWord (Classical.choose hSecond)
  else if hHeadZero :
      ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k then
    let k : Fin q := Classical.choose hHeadZero
    exact
      (targetWord
        (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k))⁻¹
  else if hHeadOne :
      ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k then
    let k : Fin q := Classical.choose hHeadOne
    exact
      (targetWord
        (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k))⁻¹
  else if hMiddleRest :
      ∃ r : Fin (p - 2), ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k then
    let r : Fin (p - 2) := Classical.choose hMiddleRest
    let hk : ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k :=
      Classical.choose_spec hMiddleRest
    let k : Fin q := Classical.choose hk
    exact
      (targetWord
        (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))⁻¹
  else if hTail :
      ∃ b : Fin p, ∃ j : Fin tailLen, ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k then
    let b : Fin p := Classical.choose hTail
    let hj : ∃ j : Fin tailLen, ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k :=
      Classical.choose_spec hTail
    let j : Fin tailLen := Classical.choose hj
    let hk : ∃ k : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k :=
      Classical.choose_spec hj
    let k : Fin q := Classical.choose hk
    exact
      (targetWord
        (secondReductionCanonicalTransportTailIndex tailLen p q b j k))⁻¹
  else
    exact 1
noncomputable def secondReductionCanonicalSchreierToTransportSecondBranchHom
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
    FreeGroup ↥(schreierGeneratorSet hT) →*
      FreeGroup (FuchsianGenerator
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)) :=
  FreeGroup.lift
    (secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_firstPowerWord
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) =
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩) := by
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let A : FreeGroup (FuchsianGenerator
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)) :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
      (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalFirstPowerKernel
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail,
      secondReductionCanonicalFirstPowerKernel_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hzImage : η (FreeGroup.of z) = A⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSchreierToTransportSecondBranchHom,
  secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage, Fin.zero_eta, Fin.isValue, Fin.mk_one,
  dite_eq_ite, id_eq, FreeGroup.lift_apply_of, ↓reduceIte, η, z, A, σ]
  calc
    η
        (e.symm
          (secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ = (A⁻¹)⁻¹ := by rw [hzImage]
    _ = A := by simp only [inv_inv]
theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_headZeroWord
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)) =
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k) := by
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
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
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalHeadZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
      by
        simpa [σ, φ, y, hy, secondReductionCanonicalHeadZeroKernelElement] using
          secondReductionCanonicalHeadZeroKernelElement_mem_schreierGeneratorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hxy : x ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceZeroIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq,
  OfNat.ofNat_ne_zero, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
    intro hEq
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_firstPower
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
        (by simpa [x] using hxy)
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalHeadZeroKernelElement] using hEq)
  have hSecond :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hyne :
        y ≠ FuchsianGenerator.elliptic
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩) := by
      intro hEq'
      simp only [secondReductionCanonicalSourceZeroIndex, secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, OfNat.zero_ne_ofNat, y] at hEq'
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_secondEdge
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k k'
        (by simpa [x] using hxy) hyne
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalHeadZeroKernelElement] using hEq)
  have hHeadZero :
      ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := ⟨k, rfl⟩
  let k' : Fin q := Classical.choose hHeadZero
  have hHeadChoose :
      targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k') =
        targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k) := by
    have hEqHead :
        secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k =
          secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
      simpa [z, k'] using Classical.choose_spec hHeadZero
    have hk : k = k' := by
      exact
        secondReductionCanonicalZeroImageKernelElement_inj
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy
          (by simpa [x] using hxy)
          (by
            simpa [σ, φ, y, hy, secondReductionCanonicalHeadZeroKernelElement] using
              hEqHead)
    simp only [Fin.zero_eta, Fin.isValue, hk]
  have hHeadChoose' :
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k') =
        secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k) := by
    simpa [targetWord] using hHeadChoose
  have hzImage :
      η (FreeGroup.of z) =
        (targetWord
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSchreierToTransportSecondBranchHom,
  secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage, Fin.zero_eta, Fin.isValue, Fin.mk_one,
  dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, hSecond, ↓reduceDIte, hHeadZero, inv_inj, η, z, σ]
    exact hHeadChoose'
  calc
    η
        (e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        ((targetWord
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        targetWord
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k) := by
          simp only [Fin.zero_eta, Fin.isValue, inv_inv]
theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_headOneWord
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)) =
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
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
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalHeadOneKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
      by
        simpa [σ, φ, y, hy, secondReductionCanonicalHeadOneKernelElement] using
          secondReductionCanonicalHeadOneKernelElement_mem_schreierGeneratorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hxy : x ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceOneIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq,
  OfNat.ofNat_ne_one, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
    intro hEq
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_firstPower
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
        (by simpa [x] using hxy)
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalHeadOneKernelElement] using hEq)
  have hSecond :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hyne :
        y ≠ FuchsianGenerator.elliptic
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩) := by
      intro hEq'
      simp only [secondReductionCanonicalSourceOneIndex, secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, OfNat.one_ne_ofNat, y] at hEq'
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_secondEdge
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k k'
        (by simpa [x] using hxy) hyne
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalHeadOneKernelElement] using hEq)
  have hHeadZero :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    let y0 : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    have hy0 : φ (FreeGroup.of y0) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y0]
    have hy0ne : y0 ≠ y := by
      intro hEq'
      simp only [secondReductionCanonicalSourceZeroIndex, secondReductionCanonicalSourceOneIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, zero_ne_one, y0, y] at hEq'
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y y0 hy hy0 k k'
        (by simpa [x] using hxy) hy0ne
        (by
          simpa [z, σ, φ, y, hy, y0, hy0,
            secondReductionCanonicalHeadOneKernelElement,
            secondReductionCanonicalHeadZeroKernelElement] using hEq)
  have hHeadOne :
      ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := ⟨k, rfl⟩
  let k' : Fin q := Classical.choose hHeadOne
  have hHeadChoose :
      targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k') =
        targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
    have hEqHead :
        secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k =
          secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
      simpa [z, k'] using Classical.choose_spec hHeadOne
    have hk : k = k' := by
      exact
        secondReductionCanonicalZeroImageKernelElement_inj
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy
          (by simpa [x] using hxy)
          (by
            simpa [σ, φ, y, hy, secondReductionCanonicalHeadOneKernelElement] using
              hEqHead)
    simp only [Fin.mk_one, Fin.isValue, hk]
  have hHeadChoose' :
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k') =
        secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
    simpa [targetWord] using hHeadChoose
  have hzImage :
      η (FreeGroup.of z) =
        (targetWord
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSchreierToTransportSecondBranchHom,
  secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage, Fin.zero_eta, Fin.isValue, Fin.mk_one,
  dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, hSecond, ↓reduceDIte, hHeadZero, hHeadOne, inv_inj,
  η, z, σ]
    exact hHeadChoose'
  calc
    η
        (e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        ((targetWord
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        targetWord
          (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
          simp only [Fin.mk_one, Fin.isValue, inv_inv]
theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_middleRestWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (r : Fin (p - 2)) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k)) =
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k) := by
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
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
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalMiddleRestZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k,
      by
        simpa [σ, φ, y, hy, secondReductionCanonicalMiddleRestZeroKernelElement] using
          secondReductionCanonicalMiddleZeroKernelElement_mem_schreierGeneratorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hxy : x ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, Nat.left_eq_add, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
  false_and, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
    intro hEq
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_firstPower
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
        (by simpa [x] using hxy)
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalMiddleRestZeroKernelElement] using hEq)
  have hSecond :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hyne :
        y ≠ FuchsianGenerator.elliptic
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩) := by
      intro hEq'
      simp only [secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, FuchsianGenerator.elliptic.injEq,
  Fin.mk.injEq, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_secondEdge
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k k'
        (by simpa [x] using hxy) hyne
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalMiddleRestZeroKernelElement] using hEq)
  have hHeadZero :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    let y0 : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    have hy0 : φ (FreeGroup.of y0) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y0]
    have hy0ne : y0 ≠ y := by
      intro hEq'
      simp only [secondReductionCanonicalSourceZeroIndex, secondReductionCanonicalSourceMiddleIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y0, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y y0 hy hy0 k k'
        (by simpa [x] using hxy) hy0ne
        (by
          simpa [z, σ, φ, y, hy, y0, hy0,
            secondReductionCanonicalMiddleRestZeroKernelElement,
            secondReductionCanonicalHeadZeroKernelElement] using hEq)
  have hHeadOne :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    let y1 : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    have hy1 : φ (FreeGroup.of y1) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, y1]
    have hy1ne : y1 ≠ y := by
      intro hEq'
      simp only [secondReductionCanonicalSourceOneIndex, secondReductionCanonicalSourceMiddleIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y1, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y y1 hy hy1 k k'
        (by simpa [x] using hxy) hy1ne
        (by
          simpa [z, σ, φ, y, hy, y1, hy1,
            secondReductionCanonicalMiddleRestZeroKernelElement,
            secondReductionCanonicalHeadOneKernelElement] using hEq)
  have hMiddleRest :
      ∃ r' : Fin (p - 2), ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r' k' := ⟨r, k, rfl⟩
  let r' : Fin (p - 2) := Classical.choose hMiddleRest
  let hk' : ∃ k' : Fin q,
      (z : φ.ker) =
        secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r' k' :=
    Classical.choose_spec hMiddleRest
  let k' : Fin q := Classical.choose hk'
  have hMiddleChoose :
      targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r' k') =
        targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k) := by
    have hEqMiddle :
        secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k =
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r' k' := by
      simpa [z, r', hk', k'] using Classical.choose_spec hk'
    rcases
      secondReductionCanonicalMiddleRestZeroKernelElement_inj
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail hEqMiddle with
      ⟨hr, hk⟩
    simp only [hr, hk]
  have hMiddleChoose' :
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r' k') =
        secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k) := by
    simpa [targetWord] using hMiddleChoose
  have hzImage :
      η (FreeGroup.of z) =
        (targetWord
          (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSchreierToTransportSecondBranchHom,
  secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage, Fin.zero_eta, Fin.isValue, Fin.mk_one,
  dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, hSecond, ↓reduceDIte, hHeadZero, hHeadOne,
  hMiddleRest, inv_inj, η, z, σ]
    exact hMiddleChoose'
  calc
    η
        (e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        ((targetWord
          (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        targetWord
          (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k) := by
          simp only [inv_inv]
theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_tailWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k)) =
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        (secondReductionCanonicalTransportTailIndex tailLen p q b j k) := by
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
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
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalTailZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k,
      by
        simpa [σ, φ, y, hy, secondReductionCanonicalTailZeroKernelElement] using
          secondReductionCanonicalTailZeroKernelElement_mem_schreierGeneratorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hxy : x ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, secondReductionCanonicalSourceTailIndex, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, x, y] at hEq
    omega
  have hFirst :
      ¬ (z : φ.ker) =
        secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
    intro hEq
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_firstPower
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k
        (by simpa [x] using hxy)
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalTailZeroKernelElement] using hEq)
  have hSecond :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    have hyne :
        y ≠ FuchsianGenerator.elliptic
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩) := by
      intro hEq'
      simp only [secondReductionCanonicalSourceTailIndex, secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_secondEdge
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k k'
        (by simpa [x] using hxy) hyne
        (by simpa [z, σ, φ, y, hy, secondReductionCanonicalTailZeroKernelElement] using hEq)
  have hHeadZero :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    let y0 : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    have hy0 : φ (FreeGroup.of y0) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceZeroIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.zero_ne_ofNat, ↓reduceIte, φ, y0]
    have hy0ne : y0 ≠ y := by
      intro hEq'
      simp only [secondReductionCanonicalSourceZeroIndex, secondReductionCanonicalSourceTailIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y0, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y y0 hy hy0 k k'
        (by simpa [x] using hxy) hy0ne
        (by
          simpa [z, σ, φ, y, hy, y0, hy0,
            secondReductionCanonicalTailZeroKernelElement,
            secondReductionCanonicalHeadZeroKernelElement] using hEq)
  have hHeadOne :
      ¬ ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
    intro h
    rcases h with ⟨k', hEq⟩
    let y1 : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
    have hy1 : φ (FreeGroup.of y1) = 1 := by
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceOneIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, OfNat.one_ne_ofNat, ↓reduceIte, φ, y1]
    have hy1ne : y1 ≠ y := by
      intro hEq'
      simp only [secondReductionCanonicalSourceOneIndex, secondReductionCanonicalSourceTailIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, y1, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y y1 hy hy1 k k'
        (by simpa [x] using hxy) hy1ne
        (by
          simpa [z, σ, φ, y, hy, y1, hy1,
            secondReductionCanonicalTailZeroKernelElement,
            secondReductionCanonicalHeadOneKernelElement] using hEq)
  have hMiddleRest :
      ¬ ∃ r' : Fin (p - 2), ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r' k' := by
    intro h
    rcases h with ⟨r', k', hEq⟩
    let yMid : FuchsianGenerator σ :=
      FuchsianGenerator.elliptic
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r'.val, by omega⟩)
    have hyMid : φ (FreeGroup.of yMid) = 1 := by
      have hnot3 : ¬ 2 + (2 + r'.val) = 3 := by omega
      simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSourceFreeQuotientHom, id_eq,
  secondReductionCanonicalSourceMiddleIndex, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, Nat.add_eq_left, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceIte, hnot3, φ, yMid]
    have hyMidne : yMid ≠ y := by
      intro hEq'
      simp only [secondReductionCanonicalSourceMiddleIndex, secondReductionCanonicalSourceTailIndex,
  FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, yMid, y] at hEq'
      omega
    exact
      secondReductionCanonicalZeroImageKernelElement_ne_of_generator_ne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y yMid hy hyMid k k'
        (by simpa [x] using hxy) hyMidne
        (by
          simpa [z, σ, φ, y, hy, yMid, hyMid,
            secondReductionCanonicalTailZeroKernelElement,
            secondReductionCanonicalMiddleRestZeroKernelElement] using hEq)
  have hTail :
      ∃ b' : Fin p, ∃ j' : Fin tailLen, ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b' j' k' := ⟨b, j, k, rfl⟩
  let b' : Fin p := Classical.choose hTail
  let hj' : ∃ j' : Fin tailLen, ∃ k' : Fin q,
      (z : φ.ker) =
        secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b' j' k' :=
    Classical.choose_spec hTail
  let j' : Fin tailLen := Classical.choose hj'
  let hk' : ∃ k' : Fin q,
      (z : φ.ker) =
        secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b' j' k' :=
    Classical.choose_spec hj'
  let k' : Fin q := Classical.choose hk'
  have hTailChoose :
      targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b' j' k') =
        targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j k) := by
    have hEqTail :
        secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k =
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b' j' k' := by
      simpa [z, b', hj', j', hk', k'] using Classical.choose_spec hk'
    rcases
      secondReductionCanonicalTailZeroKernelElement_inj
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail hEqTail with
      ⟨hb, hj, hk⟩
    simp only [hb, hj, hk]
  have hTailChoose' :
      secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportTailIndex tailLen p q b' j' k') =
        secondReductionCanonicalTransportTargetWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          (secondReductionCanonicalTransportTailIndex tailLen p q b j k) := by
    simpa [targetWord] using hTailChoose
  have hzImage :
      η (FreeGroup.of z) =
        (targetWord
          (secondReductionCanonicalTransportTailIndex tailLen p q b j k))⁻¹ := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSchreierToTransportSecondBranchHom,
  secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage, Fin.zero_eta, Fin.isValue, Fin.mk_one,
  dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, hSecond, ↓reduceDIte, hHeadZero, hHeadOne,
  hMiddleRest, hTail, inv_inj, η, z, σ]
    exact hTailChoose'
  calc
    η
        (e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        ((targetWord
          (secondReductionCanonicalTransportTailIndex tailLen p q b j k))⁻¹)⁻¹ := by
          rw [hzImage]
    _ =
        targetWord
          (secondReductionCanonicalTransportTailIndex tailLen p q b j k) := by
          simp only [inv_inv]
private theorem secondReductionCanonicalSchreierToTransportSecondBranch_toInv_headZero
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
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    η (θ C) = C := by
  classical
  dsimp
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  have hθ :
      θ C =
        e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
    simpa [σ, τ, e, θ, idx, C] using
      secondReductionCanonicalTransportToSchreierHom_headZero
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  change η (θ C) = C
  rw [hθ]
  simpa [C, secondReductionCanonicalTransportTargetWord, idx] using
    secondReductionCanonicalSchreierToTransportSecondBranchHom_headZeroWord
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
private theorem secondReductionCanonicalSchreierToTransportSecondBranch_toInv_headOne
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
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    η (θ C) = C := by
  classical
  dsimp
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  have hθ :
      θ C =
        e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
    simpa [σ, τ, e, θ, idx, C] using
      secondReductionCanonicalTransportToSchreierHom_headOne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  change η (θ C) = C
  rw [hθ]
  simpa [C, secondReductionCanonicalTransportTargetWord, idx] using
    secondReductionCanonicalSchreierToTransportSecondBranchHom_headOneWord
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
private theorem secondReductionCanonicalSchreierToTransportSecondBranch_toInv_middleRest
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (r : Fin (p - 2)) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    η (θ C) = C := by
  classical
  dsimp
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  have hθ :
      θ C =
        e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k) := by
    simpa [σ, τ, e, θ, idx, C] using
      secondReductionCanonicalTransportToSchreierHom_middleRest
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
  change η (θ C) = C
  rw [hθ]
  simpa [C, secondReductionCanonicalTransportTargetWord, idx] using
    secondReductionCanonicalSchreierToTransportSecondBranchHom_middleRestWord
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
private theorem secondReductionCanonicalSchreierToTransportSecondBranch_toInv_tail
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportTailIndex tailLen p q b j k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    η (θ C) = C := by
  classical
  dsimp
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportTailIndex tailLen p q b j k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  have hθ :
      θ C =
        e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k) := by
    simpa [σ, τ, e, θ, idx, C] using
      secondReductionCanonicalTransportToSchreierHom_tail
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
  change η (θ C) = C
  rw [hθ]
  simpa [C, secondReductionCanonicalTransportTargetWord, idx] using
    secondReductionCanonicalSchreierToTransportSecondBranchHom_tailWord
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
private theorem secondReductionCanonicalSchreierToTransportSecondBranch_toInv_positiveDistinguished
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
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩
    let A :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    η (θ A) = A := by
  classical
  dsimp
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩
  let A :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  have hθ :
      θ A =
        e.symm
          (secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalTransportToSchreierHom, xWord,
  secondReductionCanonicalTransportDistinguishedIndex, Fin.zero_eta, Fin.isValue, FreeGroup.lift_apply_of,
  secondReductionCanonicalTransportToSchreierGeneratorImage, secondReductionCanonicalTransportToSchreierGenerator,
  Fin.val_eq_zero_iff, dite_eq_ite, Equiv.symm_apply_apply, id_eq, ↓reduceIte,
  secondReductionCanonicalFirstPowerKernel, θ, A, idx, e]
  change η (θ A) = A
  rw [hθ]
  simpa [A, secondReductionCanonicalTransportTargetWord, idx] using
    secondReductionCanonicalSchreierToTransportSecondBranchHom_firstPowerWord
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
private theorem secondReductionCanonicalSecondBranch_headZero_toInv_eq
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
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let z : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
        secondReductionCanonicalHeadZeroKernelElement_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
    θ (η (FreeGroup.of z)) = FreeGroup.of z := by
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
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalHeadZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
      secondReductionCanonicalHeadZeroKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
  let C :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k))
  have hzWord :
      e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hηinv : η ((FreeGroup.of z)⁻¹) = C := by
    simpa [σ, e, η, C, z, secondReductionCanonicalTransportTargetWord, τ, hzWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_headZeroWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  have hη : η (FreeGroup.of z) = C⁻¹ := by
    have h := congrArg Inv.inv hηinv
    simpa using h
  have hθ : θ C =
      e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
    simpa [σ, τ, e, θ, C] using
      secondReductionCanonicalTransportToSchreierHom_headZero
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  calc
    θ (η (FreeGroup.of z)) = θ C⁻¹ := by rw [hη]
    _ = (θ C)⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        (e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k))⁻¹ := by
          rw [hθ]
    _ = ((FreeGroup.of z)⁻¹)⁻¹ := by rw [hzWord]
    _ = FreeGroup.of z := by simp only [inv_inv]
private theorem secondReductionCanonicalSecondBranch_headOne_toInv_eq
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
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let z : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
        secondReductionCanonicalHeadOneKernelElement_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
    θ (η (FreeGroup.of z)) = FreeGroup.of z := by
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
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalHeadOneKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
      secondReductionCanonicalHeadOneKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
  let C :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k))
  have hzWord :
      e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hηinv : η ((FreeGroup.of z)⁻¹) = C := by
    simpa [σ, e, η, C, z, secondReductionCanonicalTransportTargetWord, τ, hzWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_headOneWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  have hη : η (FreeGroup.of z) = C⁻¹ := by
    have h := congrArg Inv.inv hηinv
    simpa using h
  have hθ : θ C =
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
    simpa [σ, τ, e, θ, C] using
      secondReductionCanonicalTransportToSchreierHom_headOne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  calc
    θ (η (FreeGroup.of z)) = θ C⁻¹ := by rw [hη]
    _ = (θ C)⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        (e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k))⁻¹ := by
          rw [hθ]
    _ = ((FreeGroup.of z)⁻¹)⁻¹ := by rw [hzWord]
    _ = FreeGroup.of z := by simp only [inv_inv]
private theorem secondReductionCanonicalSecondBranch_middleRest_toInv_eq
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
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let z : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k,
        secondReductionCanonicalMiddleZeroKernelElement_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k⟩
    θ (η (FreeGroup.of z)) = FreeGroup.of z := by
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
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalMiddleRestZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k,
      secondReductionCanonicalMiddleZeroKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k⟩
  let C :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))
  have hzWord :
      e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hηinv : η ((FreeGroup.of z)⁻¹) = C := by
    simpa [σ, e, η, C, z, secondReductionCanonicalTransportTargetWord, τ, hzWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_middleRestWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
  have hη : η (FreeGroup.of z) = C⁻¹ := by
    have h := congrArg Inv.inv hηinv
    simpa using h
  have hθ : θ C =
      e.symm
        (secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k) := by
    simpa [σ, τ, e, θ, C] using
      secondReductionCanonicalTransportToSchreierHom_middleRest
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
  calc
    θ (η (FreeGroup.of z)) = θ C⁻¹ := by rw [hη]
    _ = (θ C)⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        (e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k))⁻¹ := by
          rw [hθ]
    _ = ((FreeGroup.of z)⁻¹)⁻¹ := by rw [hzWord]
    _ = FreeGroup.of z := by simp only [inv_inv]
private theorem secondReductionCanonicalSecondBranch_tail_toInv_eq
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
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let z : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k,
        secondReductionCanonicalTailZeroKernelElement_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k⟩
    θ (η (FreeGroup.of z)) = FreeGroup.of z := by
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
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalTailZeroKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k,
      secondReductionCanonicalTailZeroKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k⟩
  let C :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportTailIndex tailLen p q b j k))
  have hzWord :
      e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hηinv : η ((FreeGroup.of z)⁻¹) = C := by
    simpa [σ, e, η, C, z, secondReductionCanonicalTransportTargetWord, τ, hzWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_tailWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
  have hη : η (FreeGroup.of z) = C⁻¹ := by
    have h := congrArg Inv.inv hηinv
    simpa using h
  have hθ : θ C =
      e.symm
        (secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k) := by
    simpa [σ, τ, e, θ, C] using
      secondReductionCanonicalTransportToSchreierHom_tail
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
  calc
    θ (η (FreeGroup.of z)) = θ C⁻¹ := by rw [hη]
    _ = (θ C)⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        (e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))⁻¹ := by
          rw [hθ]
    _ = ((FreeGroup.of z)⁻¹)⁻¹ := by rw [hzWord]
    _ = FreeGroup.of z := by simp only [inv_inv]
theorem secondReductionCanonicalSecondBranch_zeroImage_toInv_mem_normalClosure
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
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ (y : FuchsianGenerator σ) (hy : φ (FreeGroup.of y) = 1)
      (k : Fin q) (hxy : x ≠ y),
      let z : ↥(schreierGeneratorSet hT) :=
        ⟨secondReductionCanonicalZeroImageKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k,
          secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy⟩
      θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
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
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  intro y hy k hxy
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalZeroImageKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k,
      secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy⟩
  change θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
    Subgroup.normalClosure
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := ellipticQuotientGeneratorImage σ
          (secondReductionCanonicalSourceQuotientImage
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
        (rels := relators σ)
        (secondReductionCanonicalSchreierTransversal
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)))
  have hOne_ne_zero : (1 : ZMod q) ≠ 0 := by
    intro hZ
    have hval := congrArg ZMod.val hZ
    letI : Fact (1 < q) := ⟨lt_of_lt_of_le (by decide : 1 < 2) hq⟩
    rw [ZMod.val_one] at hval
    simp only [ZMod.val_zero, one_ne_zero] at hval
  have hy_not_two :
      ¬ ∃ i :
          Fin
            (secondReductionCanonicalSourceSignature
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods,
        y = FuchsianGenerator.elliptic i ∧ i.val = 2 := by
    rintro ⟨i, rfl, hi⟩
    have hy' : (Multiplicative.ofAdd (1 : ZMod q)) = 1 := by
      simpa [φ, σ, secondReductionCanonicalSourceFreeQuotientHom,
        ellipticQuotientGeneratorImage, secondReductionCanonicalSourceQuotientImage, hi]
        using hy
    exact hOne_ne_zero (Multiplicative.ofAdd.injective hy')
  have hy_not_three :
      ¬ ∃ i :
          Fin
            (secondReductionCanonicalSourceSignature
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods,
        y = FuchsianGenerator.elliptic i ∧ i.val = 3 := by
    rintro ⟨i, rfl, hi⟩
    have hy' : (Multiplicative.ofAdd (-1 : ZMod q)) = 1 := by
      simpa [φ, σ, secondReductionCanonicalSourceFreeQuotientHom,
        ellipticQuotientGeneratorImage, secondReductionCanonicalSourceQuotientImage, hi]
        using hy
    have hneg : (-1 : ZMod q) = 0 := Multiplicative.ofAdd.injective hy'
    exact hOne_ne_zero (neg_eq_zero.mp hneg)
  cases y with
  | elliptic i =>
      by_cases h0 : i.val = 0
      · let zHead : ↥(schreierGeneratorSet hT) :=
          ⟨secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
            secondReductionCanonicalHeadZeroKernelElement_mem_schreierGeneratorSet
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
        have hi :
            i =
              secondReductionCanonicalSourceZeroIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
          ext
          simpa [secondReductionCanonicalSourceZeroIndex] using h0
        have hz : z = zHead := by
          apply Subtype.ext
          simp only [hi, secondReductionCanonicalHeadZeroKernelElement, Lean.Elab.WF.paramLet, id_eq, z, zHead]
        have hEq :
            θ (η (FreeGroup.of zHead)) = FreeGroup.of zHead := by
          simpa [σ, hT, θ, η, zHead] using
            secondReductionCanonicalSecondBranch_headZero_toInv_eq
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
        rw [hz, hEq]
        simp only [mul_inv_cancel, one_mem]
      · by_cases h1 : i.val = 1
        · let zHead : ↥(schreierGeneratorSet hT) :=
            ⟨secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
              secondReductionCanonicalHeadOneKernelElement_mem_schreierGeneratorSet
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
          have hi :
              i =
                secondReductionCanonicalSourceOneIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
            ext
            simpa [secondReductionCanonicalSourceOneIndex] using h1
          have hz : z = zHead := by
            apply Subtype.ext
            simp only [hi, secondReductionCanonicalHeadOneKernelElement, Lean.Elab.WF.paramLet, id_eq, z, zHead]
          have hEq :
              θ (η (FreeGroup.of zHead)) = FreeGroup.of zHead := by
            simpa [σ, hT, θ, η, zHead] using
              secondReductionCanonicalSecondBranch_headOne_toInv_eq
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
          rw [hz, hEq]
          simp only [mul_inv_cancel, one_mem]
        · by_cases h2 : i.val = 2
          · exact False.elim (hy_not_two ⟨i, rfl, h2⟩)
          · by_cases h3 : i.val = 3
            · exact False.elim (hy_not_three ⟨i, rfl, h3⟩)
            · by_cases hmid : i.val < 2 + p
              · let r : Fin (p - 2) := ⟨i.val - 4, by omega⟩
                let rSource : Fin p := ⟨2 + r.val, by omega⟩
                let zMiddle : ↥(schreierGeneratorSet hT) :=
                  ⟨secondReductionCanonicalMiddleRestZeroKernelElement
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k,
                    secondReductionCanonicalMiddleZeroKernelElement_mem_schreierGeneratorSet
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k⟩
                have hi :
                    i =
                      secondReductionCanonicalSourceMiddleIndex
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail rSource := by
                  ext
                  simp only [secondReductionCanonicalSourceMiddleIndex, r, rSource]
                  omega
                have hrSource : rSource = ⟨2 + r.val, by omega⟩ := rfl
                have hz : z = zMiddle := by
                  apply Subtype.ext
                  simp only [hi, secondReductionCanonicalMiddleRestZeroKernelElement, Lean.Elab.WF.paramLet, hrSource, id_eq,
  rSource, z, zMiddle]
                have hEq :
                    θ (η (FreeGroup.of zMiddle)) = FreeGroup.of zMiddle := by
                  simpa [σ, hT, θ, η, zMiddle] using
                    secondReductionCanonicalSecondBranch_middleRest_toInv_eq
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
                rw [hz, hEq]
                simp only [mul_inv_cancel, one_mem]
              · have hTailLen : 0 < tailLen := by
                  by_contra hzero
                  have htl : tailLen = 0 := Nat.eq_zero_of_not_pos hzero
                  have hiLt : i.val < 2 + p := by
                    have := i.isLt
                    simp only [secondReductionCanonicalSourceSignature, htl, zero_mul, add_zero] at this
                    omega
                  exact hmid hiLt
                let t : Fin (p * tailLen) := ⟨i.val - (2 + p), by
                  have hiLt : i.val < 2 + p + tailLen * p := by
                    have hi := i.isLt
                    dsimp [σ, secondReductionCanonicalSourceSignature] at hi
                    omega
                  have hbase : 2 + p ≤ i.val := Nat.le_of_not_gt hmid
                  have hbound : i.val - (2 + p) < tailLen * p := by omega
                  simpa [Nat.mul_comm] using hbound⟩
                let b : Fin p := ⟨t.val / tailLen, by
                  exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using t.isLt)⟩
                let j : Fin tailLen := ⟨t.val % tailLen, Nat.mod_lt _ hTailLen⟩
                let zTail : ↥(schreierGeneratorSet hT) :=
                  ⟨secondReductionCanonicalTailZeroKernelElement
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k,
                    secondReductionCanonicalTailZeroKernelElement_mem_schreierGeneratorSet
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k⟩
                have hi :
                    i =
                      secondReductionCanonicalSourceTailIndex
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j := by
                  ext
                  dsimp [b, j, t]
                  change i.val =
                    2 + p + (i.val - (2 + p)) / tailLen * tailLen +
                      (i.val - (2 + p)) % tailLen
                  have hdecomp :
                      (i.val - (2 + p)) / tailLen * tailLen +
                          (i.val - (2 + p)) % tailLen =
                        i.val - (2 + p) :=
                    Nat.div_add_mod' (i.val - (2 + p)) tailLen
                  omega
                have hz : z = zTail := by
                  apply Subtype.ext
                  simp only [hi, secondReductionCanonicalTailZeroKernelElement, Lean.Elab.WF.paramLet, id_eq, zTail, z]
                have hEq :
                    θ (η (FreeGroup.of zTail)) = FreeGroup.of zTail := by
                  simpa [σ, hT, θ, η, zTail] using
                    secondReductionCanonicalSecondBranch_tail_toInv_eq
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
                rw [hz, hEq]
                simp only [mul_inv_cancel, one_mem]
  | surfaceA i =>
      exact Fin.elim0 (by
        simpa [σ, secondReductionCanonicalSourceSignature] using i)
  | surfaceB i =>
      exact Fin.elim0 (by
        simpa [σ, secondReductionCanonicalSourceSignature] using i)
private theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_secondEdgeWord
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)) =
      (secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)⁻¹ := by
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let x : FuchsianGenerator σ :=
    secondReductionCanonicalDistinguishedGenerator
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
      secondReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hxne : x ≠ y := by
    intro hEq
    simp only [secondReductionCanonicalDistinguishedGenerator, secondReductionCanonicalSourceMiddleIndex,
  add_zero, Nat.reduceAdd, FuchsianGenerator.elliptic.injEq, Fin.mk.injEq, Nat.reduceEqDiff, x, y] at hEq
  have hFirst :
      ¬ (z : φ.ker) =
        secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
    intro hEq
    have hval := congrArg
      (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator σ))) hEq
    let r : ℕ := ((k.val : ZMod q) - 1).val
    have hleft :
        ((z : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ k.val * FreeGroup.of y *
            ((FreeGroup.of x) ^ r)⁻¹ := by
      simp only [secondReductionCanonicalSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  secondReductionCanonicalDistinguishedGenerator, id_eq, σ, x, y, r, z]
    have hright :
        ((secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ q := by
      simpa [σ, φ, x] using
        secondReductionCanonicalFirstPowerKernel_coe
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    have hword :
        (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ k.val *
            FreeGroup.of y *
            ((FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ r)⁻¹ =
          (FreeGroup.of x : FreeGroup (FuchsianGenerator σ)) ^ q := by
      simpa [hleft, hright] using hval
    let χ : FuchsianGenerator σ → Multiplicative ℤ :=
      fun u => if u = y then Multiplicative.ofAdd (1 : ℤ) else 1
    have hmap := congrArg (FreeGroup.lift χ) hword
    simp only [map_mul, map_pow, FreeGroup.lift_apply_of, hxne, ↓reduceIte, one_pow, one_mul, map_inv, inv_one,
  mul_one, ofAdd_eq_one, one_ne_zero, χ] at hmap
  have hSecond :
      ∃ k' : Fin q,
        (z : φ.ker) =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := ⟨k, rfl⟩
  let k' : Fin q := Classical.choose hSecond
  have hSecondChoose :
      secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k' =
        secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k := by
    have hEqSecond :
        secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k =
          secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k' := by
      simpa [z, k'] using Classical.choose_spec hSecond
    have hk :=
      secondReductionCanonicalSecondEdgeKernelElement_inj
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail hEqSecond
    simp only [hk]
  have hzImage :
      η (FreeGroup.of z) =
        secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalSchreierToTransportSecondBranchHom,
  secondReductionCanonicalSchreierToTransportSecondBranchGeneratorImage, Fin.zero_eta, Fin.isValue, Fin.mk_one,
  dite_eq_ite, id_eq, FreeGroup.lift_apply_of, hFirst, ↓reduceIte, hSecond, ↓reduceDIte, hSecondChoose, η, z, k', σ]
  calc
    η
        (e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)) =
        η ((FreeGroup.of z)⁻¹) := by rw [hzWord]
    _ = (η (FreeGroup.of z))⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
    _ =
        (secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)⁻¹ := by
          rw [hzImage]
private theorem secondReductionCanonicalSchreierToTransportSecondBranchHom_secondPowerWord
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
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let secondWord :=
      secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
    η
        (e.symm
          (secondReductionCanonicalSecondPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) =
      (secondWord ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩)⁻¹ *
        (List.ofFn (fun i : Fin n =>
          (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod := by
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
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let secondWord :=
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  have hcycle :
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
    simpa [n, σ, e] using
      secondReductionCanonicalSecondDescendingCycle_schreierWord_eq_secondPower
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  rw [← hcycle]
  rw [map_mul]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_secondEdgeWord]
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext i
  simpa [σ, e, η, secondWord] using
    secondReductionCanonicalSchreierToTransportSecondBranchHom_secondEdgeWord
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ⟨n - i.val, by omega⟩
private theorem secondReductionCanonicalSecondEdgeForwardWord_zero
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩ =
      secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
          ⟨q - 1, by omega⟩ *
        xWord τ
          ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
            (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)) := by
  classical
  dsimp [secondReductionCanonicalSecondEdgeForwardWord,
    secondReductionCanonicalTransportTargetWord]
private theorem secondReductionCanonicalSecondEdgeForwardWord_of_ne_zero
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) (h0 : k.val ≠ 0) :
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k =
      secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
        ⟨k.val - 1, by omega⟩ := by
  classical
  dsimp [secondReductionCanonicalSecondEdgeForwardWord]
  rw [if_neg h0]
noncomputable abbrev secondReductionCanonicalSchreierRelatorSet
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
    Set (FreeGroup ↥(schreierGeneratorSet hT)) :=
  by
    classical
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    exact
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet
        (secondReductionCanonicalSchreierBasisEquiv
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
          (f := ellipticQuotientGeneratorImage σ
            (secondReductionCanonicalSourceQuotientImage
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (rels := relators σ)
          (secondReductionCanonicalSchreierTransversal
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
private theorem secondReductionCanonicalTransportToSchreierHom_zeroBlock
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    θ (secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k) =
      (List.ofFn (fun r : Fin (p - 2) =>
        e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k))).prod *
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          e.symm
            (secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))).prod)).prod *
      e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) *
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
  classical
  dsimp
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  have hMiddleMap :
      (List.ofFn (θ ∘ fun r : Fin (p - 2) =>
        targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))).prod =
        (List.ofFn (fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k))).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext r
    simpa [σ, τ, e, θ, targetWord] using
      secondReductionCanonicalTransportToSchreierHom_middleRest
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
  have hTailMap :
      (List.ofFn (θ ∘ fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j k))).prod)).prod =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))).prod)).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext b
    dsimp
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext j
    simpa [σ, τ, e, θ, targetWord] using
      secondReductionCanonicalTransportToSchreierHom_tail
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
  have hHeadZero :
      θ (targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q (0 : Fin 2) k)) =
        e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
    simpa [σ, τ, e, θ, targetWord] using
      secondReductionCanonicalTransportToSchreierHom_headZero
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  have hHeadOne :
      θ (targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q (1 : Fin 2) k)) =
        e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
    simpa [σ, τ, e, θ, targetWord] using
      secondReductionCanonicalTransportToSchreierHom_headOne
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  dsimp [secondReductionCanonicalTransportZeroBlockWord, targetWord]
  simp only [map_mul, map_list_prod, List.map_ofFn]
  rw [hMiddleMap, hTailMap]
  rw [hHeadZero, hHeadOne]
private theorem secondReductionCanonicalSchreier_rotatedBlockTotalProduct_mem_normalClosure
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    e.symm
        (secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
      e.symm
        (secondReductionCanonicalSecondPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
      (List.ofFn (fun k : Fin q =>
        (List.ofFn (fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k))).prod *
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))).prod)).prod *
        e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) *
        e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k))).prod ∈
      Subgroup.normalClosure
        (secondReductionCanonicalSchreierRelatorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
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
  let y : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨1, by omega⟩)
  let h0Gen : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceZeroIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  let h1Gen : FuchsianGenerator σ :=
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceOneIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
  let midGen : Fin (p - 2) → FuchsianGenerator σ := fun r =>
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceMiddleIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨2 + r.val, by omega⟩)
  let tailGen : Fin p → Fin tailLen → FuchsianGenerator σ := fun b j =>
    FuchsianGenerator.elliptic
      (secondReductionCanonicalSourceTailIndex
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j)
  let a :=
    secondReductionCanonicalFirstPowerKernel
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let b :=
    secondReductionCanonicalSecondPowerKernel
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let middle : Fin q → Fin (p - 2) → φ.ker := fun k r =>
    secondReductionCanonicalMiddleRestZeroKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
  let tails : Fin q → Fin p → Fin tailLen → φ.ker := fun k b j =>
    secondReductionCanonicalTailZeroKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
  let h0 : Fin q → φ.ker := fun k =>
    secondReductionCanonicalHeadZeroKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  let h1 : Fin q → φ.ker := fun k =>
    secondReductionCanonicalHeadOneKernelElement
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  let block : Fin q → φ.ker := fun k =>
    (List.ofFn (fun r : Fin (p - 2) => middle k r)).prod *
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen => tails k b j)).prod)).prod *
      h0 k * h1 k
  let kBlock : φ.ker := a * b * (List.ofFn block).prod
  have hrotSource :
      FreeGroup.of x * FreeGroup.of y *
          ((List.ofFn (fun r : Fin (p - 2) => FreeGroup.of (midGen r))).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen b j))).prod)).prod *
            FreeGroup.of h0Gen * FreeGroup.of h1Gen) ∈
        Subgroup.normalClosure (relators σ) := by
    let heads : FreeGroup (FuchsianGenerator σ) :=
      FreeGroup.of h0Gen * FreeGroup.of h1Gen
    let rest : FreeGroup (FuchsianGenerator σ) :=
      FreeGroup.of x * FreeGroup.of y *
        (List.ofFn (fun r : Fin (p - 2) => FreeGroup.of (midGen r))).prod *
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen => FreeGroup.of (tailGen b j))).prod)).prod
    have htotal : heads * rest ∈ Subgroup.normalClosure (relators σ) := by
      have hmem : totalRelation σ ∈ relators σ := Or.inr rfl
      have hmemN : totalRelation σ ∈ Subgroup.normalClosure (relators σ) :=
        Subgroup.subset_normalClosure hmem
      have htotalEq :
          totalRelation σ = heads * rest := by
        simpa [σ, heads, rest, x, y, h0Gen, h1Gen, midGen, tailGen, xWord, mul_assoc] using
          secondReductionCanonicalSource_totalRelation_eq
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      simpa [htotalEq]
        using hmemN
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := relators σ) (a := heads) (b := rest) htotal
    simpa [heads, rest, mul_assoc] using hrot
  have hSourceBlock :
      (FreeGroup.of x) ^ q * (FreeGroup.of y) ^ q *
          (List.ofFn (fun k : Fin q =>
            (List.ofFn (fun r : Fin (p - 2) =>
              (FreeGroup.of x) ^ k.val * FreeGroup.of (midGen r) *
                ((FreeGroup.of x) ^ k.val)⁻¹)).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen b j) *
                  ((FreeGroup.of x) ^ k.val)⁻¹)).prod)).prod *
            ((FreeGroup.of x) ^ k.val * FreeGroup.of h0Gen *
              ((FreeGroup.of x) ^ k.val)⁻¹) *
            ((FreeGroup.of x) ^ k.val * FreeGroup.of h1Gen *
              ((FreeGroup.of x) ^ k.val)⁻¹))).prod ∈
        Subgroup.normalClosure (relators σ) := by
    simpa [mul_assoc] using
      secondReduction_rotatedBlockProduct_mem_normalClosure
        (R := relators σ) (x := FreeGroup.of x) (y := FreeGroup.of y)
        (h₀ := FreeGroup.of h0Gen) (h₁ := FreeGroup.of h1Gen)
        (middle := fun r : Fin (p - 2) => FreeGroup.of (midGen r))
        (tail := fun b : Fin p => fun j : Fin tailLen => FreeGroup.of (tailGen b j))
        (q := q) hrotSource
  have hBlockVal :
      ((kBlock : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
        Subgroup.normalClosure (relators σ) := by
    change
      ((a : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
          ((b : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
        (((List.ofFn block).prod : φ.ker) : FreeGroup (FuchsianGenerator σ)) ∈
        Subgroup.normalClosure (relators σ)
    rw [ReidemeisterSchreier.Discrete.Presentations.subgroup_list_prod_val]
    simp only [block]
    have hblockEach :
        (List.ofFn (fun k : Fin q =>
          (((List.ofFn (fun r : Fin (p - 2) => middle k r)).prod *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen => tails k b j)).prod)).prod *
              h0 k * h1 k : φ.ker) : FreeGroup (FuchsianGenerator σ)))) =
          List.ofFn (fun k : Fin q =>
            (List.ofFn (fun r : Fin (p - 2) =>
              (FreeGroup.of x) ^ k.val * FreeGroup.of (midGen r) *
                ((FreeGroup.of x) ^ k.val)⁻¹)).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen b j) *
                  ((FreeGroup.of x) ^ k.val)⁻¹)).prod)).prod *
            ((FreeGroup.of x) ^ k.val * FreeGroup.of h0Gen *
              ((FreeGroup.of x) ^ k.val)⁻¹) *
            ((FreeGroup.of x) ^ k.val * FreeGroup.of h1Gen *
              ((FreeGroup.of x) ^ k.val)⁻¹)) := by
      apply List.ofFn_inj.2
      funext k
      change
        (((List.ofFn (fun r : Fin (p - 2) => middle k r)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) *
            (((List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen => tails k b j)).prod)).prod : φ.ker) :
              FreeGroup (FuchsianGenerator σ)) *
            ((h0 k : φ.ker) : FreeGroup (FuchsianGenerator σ)) *
            ((h1 k : φ.ker) : FreeGroup (FuchsianGenerator σ)) =
          (List.ofFn (fun r : Fin (p - 2) =>
              (FreeGroup.of x) ^ k.val * FreeGroup.of (midGen r) *
                ((FreeGroup.of x) ^ k.val)⁻¹)).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                (FreeGroup.of x) ^ k.val * FreeGroup.of (tailGen b j) *
                  ((FreeGroup.of x) ^ k.val)⁻¹)).prod)).prod *
            ((FreeGroup.of x) ^ k.val * FreeGroup.of h0Gen *
              ((FreeGroup.of x) ^ k.val)⁻¹) *
            ((FreeGroup.of x) ^ k.val * FreeGroup.of h1Gen *
              ((FreeGroup.of x) ^ k.val)⁻¹)
      rw [ReidemeisterSchreier.Discrete.Presentations.subgroup_list_prod_val]
      rw [ReidemeisterSchreier.Discrete.Presentations.subgroup_nested_list_prod_val]
      simp only [secondReductionCanonicalMiddleRestZeroKernelElement_coe, mul_assoc,
  secondReductionCanonicalTailZeroKernelElement_coe, secondReductionCanonicalHeadZeroKernelElement_coe,
  secondReductionCanonicalHeadOneKernelElement_coe, inv_mul_cancel_left, middle, tails, h0, h1, x, midGen, tailGen,
  h0Gen, h1Gen]
    rw [hblockEach]
    simpa [a, b, x, y, secondReductionCanonicalFirstPowerKernel_coe,
      secondReductionCanonicalSecondPowerKernel_coe, mul_assoc] using hSourceBlock
  have hmem :
      e.symm kBlock ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    exact
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
        hrels hT.1 e hBlockVal
  have hblockMap :
      e.symm ((List.ofFn block).prod) =
        (List.ofFn (fun k : Fin q => e.symm (block k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext k
    rfl
  have hmem' :
      e.symm a * e.symm b *
          e.symm ((List.ofFn block).prod) ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    simpa [kBlock, map_mul] using hmem
  rw [hblockMap] at hmem'
  simpa [a, b, middle, tails, h0, h1, block, map_mul, map_list_prod, List.map_ofFn,
    Function.comp_def, mul_assoc] using hmem'
private theorem secondReductionCanonicalTransportToSchreier_blockTotalWord_mem_normalClosure
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        (secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) ∈
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
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let A :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
  let B :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩))
  let C :=
    (List.ofFn (fun k : Fin q =>
      secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)).prod
  have hA :
      θ A =
        e.symm
          (secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    simpa [σ, τ, e, θ, A] using
      secondReductionCanonicalTransportToSchreierHom_positiveDistinguished
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hB :
      θ B =
        e.symm
          (secondReductionCanonicalSecondPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    simpa [σ, τ, e, θ, B] using
      secondReductionCanonicalTransportToSchreierHom_negativeDistinguished
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hC :
      θ C =
        (List.ofFn (fun k : Fin q =>
          (List.ofFn (fun r : Fin (p - 2) =>
            e.symm
              (secondReductionCanonicalMiddleRestZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k))).prod *
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              e.symm
                (secondReductionCanonicalTailZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))).prod)).prod *
          e.symm
            (secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) *
          e.symm
            (secondReductionCanonicalHeadOneKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k))).prod := by
    dsimp [C]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext k
    simpa [σ, τ, e, θ] using
      secondReductionCanonicalTransportToSchreierHom_zeroBlock
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  have hImage :
      θ (A * B * C) =
        e.symm
            (secondReductionCanonicalFirstPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
          e.symm
            (secondReductionCanonicalSecondPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
          (List.ofFn (fun k : Fin q =>
            (List.ofFn (fun r : Fin (p - 2) =>
              e.symm
                (secondReductionCanonicalMiddleRestZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k))).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                e.symm
                  (secondReductionCanonicalTailZeroKernelElement
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))).prod)).prod *
            e.symm
              (secondReductionCanonicalHeadZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) *
            e.symm
              (secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k))).prod := by
    simp only [Lean.Elab.WF.paramLet, mul_assoc, map_mul, hA, hB, hC]
  have hmem :=
    secondReductionCanonicalSchreier_rotatedBlockTotalProduct_mem_normalClosure
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  change θ (A * B * C) ∈
    Subgroup.normalClosure
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := ellipticQuotientGeneratorImage σ
          (secondReductionCanonicalSourceQuotientImage
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
        (rels := relators σ)
        (secondReductionCanonicalSchreierTransversal
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)))
  rw [hImage]
  simpa [secondReductionCanonicalSchreierRelatorSet, σ, e, hrels] using hmem
theorem secondReductionCanonicalTransportToSchreier_mapsBlockRelators
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ r ∈
        secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail,
      secondReductionCanonicalTransportToSchreierHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r ∈
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
  intro r hr
  change
      ((∃ i : Fin
          (secondReductionTransportSignature (p := p) hq
            m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).numPeriods,
          r =
            ((xWord
                (secondReductionTransportSignature (p := p) hq
                  m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail) i) ^
              ((secondReductionTransportSignature (p := p) hq
                m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).periods i))) ∨
        r =
          secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) at hr
  cases hr with
  | inl hpow =>
    rcases hpow with ⟨i, hi⟩
    rw [hi]
    simpa using
      secondReductionCanonicalTransportToSchreier_powerRelator_mem_normalClosure
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i
  | inr htotal =>
    rw [htotal]
    simpa using
      secondReductionCanonicalTransportToSchreier_blockTotalWord_mem_normalClosure
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
private theorem secondReductionCanonicalSchreier_nonwrapSecondEdgeElimination_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) (h0 : k.val ≠ 0) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let k0 : Fin q := ⟨k.val - 1, by omega⟩
    (List.ofFn (fun r : Fin (p - 2) =>
        e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod *
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          e.symm
            (secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod *
      e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
      e.symm
        (secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
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
  let T :=
    secondReductionCanonicalSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let knw : Fin (q - 1) := ⟨k.val - 1, by
    have hklt := k.isLt
    omega⟩
  let k0 : Fin q := ⟨knw.val, by omega⟩
  let k1 : Fin q := ⟨knw.val + 1, by omega⟩
  have hk0 : k0 = ⟨k.val - 1, by omega⟩ := by
    ext
    simp only [knw, k0]
  have hk1 : k1 = k := by
    ext
    simp only [knw, k1]
    omega
  let xk : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ k0.val
  let t : FreeGroup (FuchsianGenerator σ) := xk
  let r : FreeGroup (FuchsianGenerator σ) := totalRelation σ
  let zRel : φ.ker :=
    ⟨t * r * t⁻¹, by
      change φ (t * r * t⁻¹) = 1
      have hrφ : φ r = 1 := hrels r (Or.inr rfl)
      simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  have ht : t ∈ T := by
    simpa [T, t, xk, k0, secondReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := k0.val) k0.isLt
  have hrel :
      e.symm zRel ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    have h :=
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure
        hrels e ht (Or.inr rfl)
    simpa [secondReductionCanonicalSchreierRelatorSet, T, hT, e, zRel, t, r] using h
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
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1 : φ.ker) :
        FreeGroup (FuchsianGenerator σ)) =
          (FreeGroup.of x) ^ (k0.val + 1) * FreeGroup.of y * xk⁻¹ := by
    simpa [σ, φ, x, y, xk, k0, k1, knw] using
      secondReductionCanonicalSecondEdgeKernelElement_succ_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail knw
  have hmiddleZeroVals :
      (List.ofFn (Subtype.val ∘ fun r : Fin (p - 2) =>
        secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0)).prod =
          (List.ofFn (fun r : Fin (p - 2) =>
            xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext r
    simpa [σ, φ, x, midGen, xk, k0] using
      secondReductionCanonicalMiddleRestZeroKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0
  have htailZeroVals :
      (List.ofFn (Subtype.val ∘ fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod)).prod =
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext b
    change
      (((List.ofFn (fun j : Fin tailLen =>
        secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod :
          φ.ker) : FreeGroup (FuchsianGenerator σ)) =
        (List.ofFn (fun j : Fin tailLen =>
          xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod
    rw [ReidemeisterSchreier.Discrete.Presentations.subgroup_list_prod_val]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext j
    simpa [σ, φ, x, tailGen, xk, k0] using
      secondReductionCanonicalTailZeroKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0
  have hkerEq :
      zRel =
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
      t * r * t⁻¹ =
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
    dsimp [t, r]
    rw [secondReductionCanonicalSource_totalRelation_eq
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail]
    simp only [secondReductionCanonicalDistinguishedGenerator, xWord, mul_assoc,
  secondReductionCanonicalHeadZeroKernelElement_coe, secondReductionCanonicalHeadOneKernelElement_coe,
  inv_mul_cancel_left, Subgroup.val_list_prod, List.map_ofFn, mul_right_inj, σ, xk, x, k0]
    rw [hsecondSuccCoe, hmiddleZeroVals, htailZeroVals]
    rw [hmiddleConj, htailConj]
    simp only [secondReductionCanonicalDistinguishedGenerator, conj_mul, x, y, xk, midGen, tailGen]
    have hk0val : k0.val = knw.val := by
      simp only [k0]
    rw [hk0val]
    group
  have hmiddleMap :
      e.symm
          ((List.ofFn (fun r : Fin (p - 2) =>
            secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0)).prod) =
        (List.ofFn (fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod := by
    simp only [Lean.Elab.WF.paramLet, map_list_prod, List.map_ofFn, Function.comp_def]
  have htailMap :
      e.symm
          ((List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod)).prod) =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod := by
    simp only [Lean.Elab.WF.paramLet, map_list_prod, List.map_ofFn, Function.comp_def]
  have hunrot :
      e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
        e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
        e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1) *
        (List.ofFn (fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod *
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    have hrel' :
        e.symm
            (secondReductionCanonicalHeadZeroKernelElement
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
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0)).prod)).prod) ∈
          Subgroup.normalClosure
            (secondReductionCanonicalSchreierRelatorSet
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
      simpa [hkerEq] using hrel
    simpa [map_mul, hmiddleMap, htailMap, mul_assoc] using hrel'
  let middle :=
    (List.ofFn (fun r : Fin (p - 2) =>
      e.symm
        (secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod
  let tails :=
    (List.ofFn (fun b : Fin p =>
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod
  let headsEdge :=
    e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
      e.symm
        (secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1)
  have hrot :=
    ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
      (R := secondReductionCanonicalSchreierRelatorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (a := headsEdge) (b := middle * tails)
      (by simpa [headsEdge, middle, tails, mul_assoc] using hunrot)
  simpa [k0, hk0, hk1, headsEdge, middle, tails, mul_assoc] using hrot
private theorem secondReductionCanonicalSchreier_wrapSecondEdgeElimination_mem_normalClosure
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let kLast : Fin q := ⟨q - 1, by omega⟩
    let kZero : Fin q := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
    (List.ofFn (fun r : Fin (p - 2) =>
        e.symm
          (secondReductionCanonicalMiddleRestZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod *
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          e.symm
            (secondReductionCanonicalTailZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod *
      e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
      e.symm
        (secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
      e.symm
        (secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero) ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
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
  let T :=
    secondReductionCanonicalSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let kLast : Fin q := ⟨q - 1, by omega⟩
  let kZero : Fin q := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
  let xk : FreeGroup (FuchsianGenerator σ) := (FreeGroup.of x) ^ (q - 1)
  let t : FreeGroup (FuchsianGenerator σ) := xk
  let r : FreeGroup (FuchsianGenerator σ) := totalRelation σ
  let zRel : φ.ker :=
    ⟨t * r * t⁻¹, by
      change φ (t * r * t⁻¹) = 1
      have hrφ : φ r = 1 := hrels r (Or.inr rfl)
      simp only [Lean.Elab.WF.paramLet, map_mul, hrφ, mul_one, map_inv, mul_inv_cancel]⟩
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
  have ht : t ∈ T := by
    simpa [T, t, xk, kLast, secondReductionCanonicalSchreierTransversal, φ, x] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := kLast.val) kLast.isLt
  have hrel :
      e.symm zRel ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    have h :=
      ReidemeisterSchreier.Discrete.Presentations.freeGroupPullback_transversalRelator_mem_normalClosure
        hrels e ht (Or.inr rfl)
    simpa [secondReductionCanonicalSchreierRelatorSet, T, hT, e, zRel, t, r] using h
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
      (List.ofFn (Subtype.val ∘ fun r : Fin (p - 2) =>
        secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast)).prod =
          (List.ofFn (fun r : Fin (p - 2) =>
            xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext r
    simpa [σ, φ, x, midGen, xk, kLast] using
      secondReductionCanonicalMiddleRestZeroKernelElement_coe
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast
  have htailZeroVals :
      (List.ofFn (Subtype.val ∘ fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod =
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
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail (0 : Fin q) : φ.ker) :
        FreeGroup (FuchsianGenerator σ)) =
          FreeGroup.of y * xk⁻¹ := by
    simpa [kZero] using hsecondZeroCoe
  have hmiddleZeroVals' :
      (List.ofFn (fun r : Fin (p - 2) =>
        ((secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast : φ.ker) :
            FreeGroup (FuchsianGenerator σ)))).prod =
          (List.ofFn (fun r : Fin (p - 2) =>
            xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
    simpa only [Function.comp_apply] using hmiddleZeroVals
  have htailZeroVals' :
      (List.ofFn (fun b : Fin p =>
        (((List.ofFn (fun j : Fin tailLen =>
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod :
              φ.ker) : FreeGroup (FuchsianGenerator σ)))).prod =
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod := by
    simpa only [Function.comp_apply] using htailZeroVals
  have hmiddleZeroVals0 :
      (List.ofFn (Subtype.val ∘ fun r : Fin (p - 2) =>
        secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r
          (⟨q - 1, by omega⟩ : Fin q))).prod =
          (List.ofFn (fun r : Fin (p - 2) =>
            xk * FreeGroup.of (midGen r) * xk⁻¹)).prod := by
    simpa [kLast] using hmiddleZeroVals
  have htailZeroVals0 :
      (List.ofFn (Subtype.val ∘ fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j
            (⟨q - 1, by omega⟩ : Fin q))).prod)).prod =
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              xk * FreeGroup.of (tailGen b j) * xk⁻¹)).prod)).prod := by
    simpa [kLast] using htailZeroVals
  have hkerEq :
      zRel =
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
      t * r * t⁻¹ =
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
    dsimp [t, r]
    rw [secondReductionCanonicalSource_totalRelation_eq
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail]
    simp only [secondReductionCanonicalDistinguishedGenerator, xWord, mul_assoc,
  secondReductionCanonicalHeadZeroKernelElement_coe, secondReductionCanonicalHeadOneKernelElement_coe,
  inv_mul_cancel_left, secondReductionCanonicalFirstPowerKernel_coe, Fin.mk_zero', Subgroup.val_list_prod,
  List.map_ofFn, σ, xk, x, kZero]
    rw [hsecondZeroCoe0, hmiddleZeroVals0, htailZeroVals0]
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
    have hkLastVal : kLast.val = q - 1 := by
      simp only [kLast]
    rw [hkLastVal]
    group
  have hmiddleMap :
      e.symm
          ((List.ofFn (fun r : Fin (p - 2) =>
            secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast)).prod) =
        (List.ofFn (fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod := by
    simp only [Lean.Elab.WF.paramLet, map_list_prod, List.map_ofFn, Function.comp_def]
  have htailMap :
      e.symm
          ((List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod) =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod := by
    simp only [Lean.Elab.WF.paramLet, map_list_prod, List.map_ofFn, Function.comp_def]
  have hunrot :
      e.symm
          (secondReductionCanonicalHeadZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
        e.symm
          (secondReductionCanonicalHeadOneKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
        e.symm
          (secondReductionCanonicalFirstPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
        e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero) *
        (List.ofFn (fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod *
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod ∈
        Subgroup.normalClosure
          (secondReductionCanonicalSchreierRelatorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    have hrel' :
        e.symm
            (secondReductionCanonicalHeadZeroKernelElement
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
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast)).prod)).prod) ∈
          Subgroup.normalClosure
            (secondReductionCanonicalSchreierRelatorSet
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
      simpa [hkerEq] using hrel
    simpa [map_mul, hmiddleMap, htailMap, mul_assoc] using hrel'
  let middle :=
    (List.ofFn (fun r : Fin (p - 2) =>
      e.symm
        (secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod
  let tails :=
    (List.ofFn (fun b : Fin p =>
      (List.ofFn (fun j : Fin tailLen =>
        e.symm
          (secondReductionCanonicalTailZeroKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod
  let headsEdge :=
    e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
      e.symm
        (secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
      e.symm
        (secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero)
  have hrot :=
    ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
      (R := secondReductionCanonicalSchreierRelatorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (a := headsEdge) (b := middle * tails)
      (by simpa [headsEdge, middle, tails, mul_assoc] using hunrot)
  simpa [kLast, kZero, headsEdge, middle, tails, mul_assoc] using hrot
theorem secondReductionCanonicalSecondBranch_secondEdge_toInv_mem_normalClosure
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let hT :=
      secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ k : Fin q,
      let z : ↥(schreierGeneratorSet hT) :=
        ⟨secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
          secondReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
      θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
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
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hrels :=
    secondReductionCanonicalSourceFreeQuotientHom_respects_relators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let word :=
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let block :=
    secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let A :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
  intro k
  let z : ↥(schreierGeneratorSet hT) :=
    ⟨secondReductionCanonicalSecondEdgeKernelElement
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
      secondReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
  have hzWord :
      e.symm
          (secondReductionCanonicalSecondEdgeKernelElement
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) =
        (FreeGroup.of z)⁻¹ := by
    simpa [σ, φ, hT, e, z] using
      secondReductionCanonicalSchreierBasisEquiv_symm_apply
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z
  have hηInv :
      η ((FreeGroup.of z)⁻¹) = (word k)⁻¹ := by
    simpa [σ, e, η, word, hzWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_secondEdgeWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  have hη :
      η (FreeGroup.of z) = word k := by
    have h := congrArg Inv.inv hηInv
    simpa using h
  have htarget :
      θ (word k) *
          e.symm
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) ∈
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (secondReductionCanonicalSourceQuotientImage
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
            (rels := relators σ)
            (secondReductionCanonicalSchreierTransversal
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))) := by
    by_cases hk : k.val = 0
    · let kZero : Fin q := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
      let kLast : Fin q := ⟨q - 1, by omega⟩
      have hkZero : k = kZero := by
        ext
        simp only [hk, kZero]
      have hword :
          word k = block kLast * A := by
        simpa [word, block, A, kZero, kLast, hkZero] using
          secondReductionCanonicalSecondEdgeForwardWord_zero
            (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
      have hblock :
          θ (block kLast) =
            (List.ofFn (fun r : Fin (p - 2) =>
              e.symm
                (secondReductionCanonicalMiddleRestZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                e.symm
                  (secondReductionCanonicalTailZeroKernelElement
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod *
            e.symm
              (secondReductionCanonicalHeadZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
            e.symm
              (secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) := by
        simpa [σ, τ, e, θ, block] using
          secondReductionCanonicalTransportToSchreierHom_zeroBlock
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast
      have hA :
          θ A =
            e.symm
              (secondReductionCanonicalFirstPowerKernel
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
        simpa [σ, τ, e, θ, A] using
          secondReductionCanonicalTransportToSchreierHom_positiveDistinguished
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      have h :=
        secondReductionCanonicalSchreier_wrapSecondEdgeElimination_mem_normalClosure
          (p := p) (q := q)
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      rw [hword, map_mul, hblock, hA, hkZero]
      simpa [secondReductionCanonicalSchreierRelatorSet, σ, hT, e, hrels,
        kZero, kLast, mul_assoc] using h
    · let k0 : Fin q := ⟨k.val - 1, by omega⟩
      have hword :
          word k = block k0 := by
        simpa [word, block, k0] using
          secondReductionCanonicalSecondEdgeForwardWord_of_ne_zero
            (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k hk
      have hblock :
          θ (block k0) =
            (List.ofFn (fun r : Fin (p - 2) =>
              e.symm
                (secondReductionCanonicalMiddleRestZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                e.symm
                  (secondReductionCanonicalTailZeroKernelElement
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod *
            e.symm
              (secondReductionCanonicalHeadZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
            e.symm
              (secondReductionCanonicalHeadOneKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) := by
        simpa [σ, τ, e, θ, block] using
          secondReductionCanonicalTransportToSchreierHom_zeroBlock
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0
      have h :=
        secondReductionCanonicalSchreier_nonwrapSecondEdgeElimination_mem_normalClosure
          (p := p) (q := q)
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k hk
      simpa [secondReductionCanonicalSchreierRelatorSet, σ, hT, e, hrels,
        k0, hword, hblock, mul_assoc] using h
  change θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
    Subgroup.normalClosure
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := ellipticQuotientGeneratorImage σ
          (secondReductionCanonicalSourceQuotientImage
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
        (rels := relators σ)
        (secondReductionCanonicalSchreierTransversal
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)))
  simpa [hη, hzWord] using htarget
theorem secondReductionCanonicalSchreierToTransportSecondBranch_nonwrapTotalRelator_image_eq_one
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin (q - 1)) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let k0 : Fin q := ⟨k.val, by omega⟩
    let k1 : Fin q := ⟨k.val + 1, by omega⟩
    η
        (e.symm
            (secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
          e.symm
            (secondReductionCanonicalHeadOneKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k0) *
          e.symm
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k1) *
          (List.ofFn (fun r : Fin (p - 2) =>
            e.symm
              (secondReductionCanonicalMiddleRestZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod *
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              e.symm
                (secondReductionCanonicalTailZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod) = 1 := by
  classical
  dsimp
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
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let block :=
    secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let k0 : Fin q := ⟨k.val, by omega⟩
  let k1 : Fin q := ⟨k.val + 1, by omega⟩
  have hMiddleMap :
      (List.ofFn (η ∘ fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0))).prod =
        (List.ofFn (fun r : Fin (p - 2) =>
          targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k0))).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext r
    simpa [σ, τ, e, η, targetWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_middleRestWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k0
  have hTailMap :
      (List.ofFn (η ∘ fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0))).prod)).prod =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j k0))).prod)).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext b
    dsimp
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext j
    simpa [σ, τ, e, η, targetWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_tailWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k0
  simp only [map_mul, map_list_prod, List.map_ofFn]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_headZeroWord]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_headOneWord]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_secondEdgeWord]
  have hne : k1.val ≠ 0 := by
    dsimp [k1]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true]
  rw [secondReductionCanonicalSecondEdgeForwardWord_of_ne_zero
    m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k1 hne]
  rw [hMiddleMap, hTailMap]
  change
    targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k0) *
      targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k0) *
        (block k0)⁻¹ *
          (List.ofFn (fun r : Fin (p - 2) =>
            targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k0))).prod *
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j k0))).prod)).prod = 1
  dsimp [block, secondReductionCanonicalTransportZeroBlockWord, targetWord]
  group
theorem secondReductionCanonicalSchreierToTransportSecondBranch_wrapTotalRelator_image_eq_one
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
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let kLast : Fin q := ⟨q - 1, by omega⟩
    let kZero : Fin q := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
    η
        (e.symm
            (secondReductionCanonicalHeadZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
          e.symm
            (secondReductionCanonicalHeadOneKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kLast) *
          e.symm
            (secondReductionCanonicalFirstPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
          e.symm
            (secondReductionCanonicalSecondEdgeKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail kZero) *
          (List.ofFn (fun r : Fin (p - 2) =>
            e.symm
              (secondReductionCanonicalMiddleRestZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod *
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              e.symm
                (secondReductionCanonicalTailZeroKernelElement
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod) = 1 := by
  classical
  dsimp
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
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let block :=
    secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let kLast : Fin q := ⟨q - 1, by omega⟩
  let kZero : Fin q := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
  let A :=
    targetWord (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩)
  have hMiddleMap :
      (List.ofFn (η ∘ fun r : Fin (p - 2) =>
          e.symm
            (secondReductionCanonicalMiddleRestZeroKernelElement
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast))).prod =
        (List.ofFn (fun r : Fin (p - 2) =>
          targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r kLast))).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext r
    simpa [σ, τ, e, η, targetWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_middleRestWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r kLast
  have hTailMap :
      (List.ofFn (η ∘ fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            e.symm
              (secondReductionCanonicalTailZeroKernelElement
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast))).prod)).prod =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j kLast))).prod)).prod := by
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext b
    dsimp
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext j
    simpa [σ, τ, e, η, targetWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_tailWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j kLast
  simp only [map_mul, map_list_prod, List.map_ofFn]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_headZeroWord]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_headOneWord]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_firstPowerWord]
  rw [secondReductionCanonicalSchreierToTransportSecondBranchHom_secondEdgeWord]
  rw [secondReductionCanonicalSecondEdgeForwardWord_zero]
  rw [hMiddleMap, hTailMap]
  change
    targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ kLast) *
      targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ kLast) *
        A *
          (block kLast * A)⁻¹ *
            (List.ofFn (fun r : Fin (p - 2) =>
              targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r kLast))).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j kLast))).prod)).prod = 1
  dsimp [block, secondReductionCanonicalTransportZeroBlockWord, targetWord, A]
  group
private theorem secondReductionCanonicalSecondEdgeForward_descendingProduct_eq_targetZeroBlocks_inv
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    let A :=
      xWord τ
        ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
          (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
    let C :=
      (List.ofFn (fun k : Fin q =>
        secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)).prod
    let secondWord :=
      secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
    (secondWord ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩)⁻¹ *
        (List.ofFn (fun i : Fin (q - 1) =>
          (secondWord ⟨q - 1 - i.val, by omega⟩)⁻¹)).prod =
      A⁻¹ * C⁻¹ := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let A :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
  let block :=
    secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let secondWord :=
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  have hq_pos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  have hleft :
      (secondWord ⟨0, hq_pos⟩)⁻¹ *
          (List.ofFn (fun i : Fin (q - 1) =>
            (secondWord ⟨q - 1 - i.val, by omega⟩)⁻¹)).prod =
        (block ⟨q - 1, by omega⟩ * A)⁻¹ *
          (List.ofFn (fun i : Fin (q - 1) =>
            (block ⟨q - 2 - i.val, by omega⟩)⁻¹)).prod := by
    dsimp [secondWord, block, A]
    rw [secondReductionCanonicalSecondEdgeForwardWord_zero]
    congr 1
    apply congrArg List.prod
    apply List.ofFn_inj.2
    funext i
    have hne : (⟨q - 1 - i.val, by omega⟩ : Fin q).val ≠ 0 := by
      simp only [ne_eq]
      omega
    rw [secondReductionCanonicalSecondEdgeForwardWord_of_ne_zero
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
      ⟨q - 1 - i.val, by omega⟩ hne]
    congr 1
    apply congrArg block
    ext
    simp only
    omega
  have hdesc :
      (block ⟨q - 1, by omega⟩ * A)⁻¹ *
          (List.ofFn (fun i : Fin (q - 1) =>
            (block ⟨q - 2 - i.val, by omega⟩)⁻¹)).prod =
        A⁻¹ * (List.ofFn block).prod⁻¹ :=
    descending_block_inv_product_eq hq_pos A block
  calc
    (secondWord ⟨0, hq_pos⟩)⁻¹ *
        (List.ofFn (fun i : Fin (q - 1) =>
          (secondWord ⟨q - 1 - i.val, by omega⟩)⁻¹)).prod
        =
          (block ⟨q - 1, by omega⟩ * A)⁻¹ *
            (List.ofFn (fun i : Fin (q - 1) =>
              (block ⟨q - 2 - i.val, by omega⟩)⁻¹)).prod := hleft
    _ = A⁻¹ * (List.ofFn block).prod⁻¹ := hdesc
private theorem secondReductionCanonicalTransportBlockRelators_inverseRotated_mem_normalClosure
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    let A :=
      xWord τ
        ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
          (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
    let B :=
      xWord τ
        ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
          (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩))
    let C :=
      (List.ofFn (fun k : Fin q =>
        secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)).prod
    A⁻¹ * C⁻¹ * B⁻¹ ∈
      Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let A :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
  let B :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩))
  let C :=
    (List.ofFn (fun k : Fin q =>
      secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)).prod
  let R : Set (FreeGroup (FuchsianGenerator τ)) :=
    secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let N : Subgroup (FreeGroup (FuchsianGenerator τ)) :=
    Subgroup.normalClosure R
  have htotal : A * B * C ∈ N := by
    have hmem :
        secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail ∈ R :=
      secondReductionCanonicalTransport_blockTotalWord_mem_blockRelators
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
    have hmemN : secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail ∈ N :=
      Subgroup.subset_normalClosure hmem
    simpa [R, N, secondReductionCanonicalTransportBlockTotalWord, τ, A, B, C] using hmemN
  have hinv : (A * B * C)⁻¹ ∈ N := N.inv_mem htotal
  have hCBA : C⁻¹ * B⁻¹ * A⁻¹ ∈ N := by
    simpa [N, mul_assoc] using hinv
  have hBA_C : B⁻¹ * A⁻¹ * C⁻¹ ∈ N := by
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := R) (a := C⁻¹) (b := B⁻¹ * A⁻¹)
        (by simpa [N, mul_assoc] using hCBA)
    simpa [N, R, mul_assoc] using hrot
  have hA_CB : A⁻¹ * C⁻¹ * B⁻¹ ∈ N := by
    have hrot :=
      ReidemeisterSchreier.Discrete.Presentations.cyclic_rotation_mem_normalClosure
        (R := R) (a := B⁻¹) (b := A⁻¹ * C⁻¹)
        (by simpa [N, mul_assoc] using hBA_C)
    simpa [N, R, mul_assoc] using hrot
  simpa [N, R, τ, A, B, C, mul_assoc] using hA_CB
theorem secondReductionToTransportSecondBranch_toInv_negDist_mem_blockRelators
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
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩
    let B :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    η (θ B) * B⁻¹ ∈
      Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let n := q - 1
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
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let A :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
  let idx :=
    secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩
  let B :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  let C :=
    (List.ofFn (fun k : Fin q =>
      secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)).prod
  let secondWord :=
    secondReductionCanonicalSecondEdgeForwardWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  have hTheta :
      θ B =
        e.symm
          (secondReductionCanonicalSecondPowerKernel
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
    simpa [σ, τ, e, θ, idx, B] using
      secondReductionCanonicalTransportToSchreierHom_negativeDistinguished
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hImage :
      η
          (e.symm
            (secondReductionCanonicalSecondPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) =
        (secondWord ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩)⁻¹ *
          (List.ofFn (fun i : Fin n =>
            (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod := by
    simpa [n, σ, e, η, secondWord] using
      secondReductionCanonicalSchreierToTransportSecondBranchHom_secondPowerWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hDesc :
      (secondWord ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩)⁻¹ *
          (List.ofFn (fun i : Fin n =>
            (secondWord ⟨n - i.val, by omega⟩)⁻¹)).prod =
        A⁻¹ * C⁻¹ := by
    simpa [n, τ, A, C, secondWord] using
      secondReductionCanonicalSecondEdgeForward_descendingProduct_eq_targetZeroBlocks_inv
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  have hTarget :
      A⁻¹ * C⁻¹ * B⁻¹ ∈
        Subgroup.normalClosure
          (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
    simpa [τ, A, B, C, mul_assoc] using
      secondReductionCanonicalTransportBlockRelators_inverseRotated_mem_normalClosure
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  change η (θ B) * B⁻¹ ∈
    Subgroup.normalClosure
      (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  rw [hTheta, hImage]
  rw [hDesc]
  simpa [mul_assoc] using hTarget
theorem secondReductionCanonicalSchreierToTransportSecondBranch_toInv_mem_blockRelators
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
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let η :=
      secondReductionCanonicalSchreierToTransportSecondBranchHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ y : FreeGroup (FuchsianGenerator τ),
      η (θ y) * y⁻¹ ∈
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
  let R : Set (FreeGroup (FuchsianGenerator τ)) :=
    secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let F : FreeGroup (FuchsianGenerator τ) →* FreeGroup (FuchsianGenerator τ) := η.comp θ
  have hgen :
      ∀ y : FuchsianGenerator τ,
        F (FreeGroup.of y) * (FreeGroup.of y)⁻¹ ∈
          Subgroup.normalClosure R := by
    intro y
    cases y with
    | elliptic i =>
        let idx : SecondReductionTransportIndex tailLen p q :=
          (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)).symm i
        have hi :
            i =
              (Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx := by
          simp only [Equiv.apply_symm_apply, idx]
        rcases idx with ⟨src, k⟩
        cases src with
        | inl head =>
            fin_cases head
            · have hEq :
                  η (θ (FreeGroup.of
                    (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) =
                    FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ) := by
                simpa [τ, xWord, hi, secondReductionCanonicalTransportHeadIndex] using
                  secondReductionCanonicalSchreierToTransportSecondBranch_toInv_headZero
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
              change F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) *
                  (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))⁻¹ ∈
                Subgroup.normalClosure R
              rw [show F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) =
                  η (θ (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) by rfl,
                hEq]
              simp only [mul_inv_cancel, one_mem]
            · have hEq :
                  η (θ (FreeGroup.of
                    (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) =
                    FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ) := by
                simpa [τ, xWord, hi, secondReductionCanonicalTransportHeadIndex] using
                  secondReductionCanonicalSchreierToTransportSecondBranch_toInv_headOne
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
              change F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) *
                  (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))⁻¹ ∈
                Subgroup.normalClosure R
              rw [show F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) =
                  η (θ (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) by rfl,
                hEq]
              simp only [mul_inv_cancel, one_mem]
        | inr rest =>
            cases rest with
            | inl distinguished =>
                fin_cases k
                fin_cases distinguished
                · have hEq :
                      η (θ (FreeGroup.of
                        (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) =
                        FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ) := by
                    simpa [τ, xWord, hi, secondReductionCanonicalTransportDistinguishedIndex] using
                      secondReductionCanonicalSchreierToTransportSecondBranch_toInv_positiveDistinguished
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  change F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) *
                      (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))⁻¹ ∈
                    Subgroup.normalClosure R
                  rw [show F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) =
                      η (θ (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) by rfl,
                    hEq]
                  simp only [mul_inv_cancel, one_mem]
                · simpa [R, τ, xWord, hi, secondReductionCanonicalTransportDistinguishedIndex,
                    F, θ, η] using
                    secondReductionToTransportSecondBranch_toInv_negDist_mem_blockRelators
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            | inr rest =>
                cases rest with
                | inl r =>
                    have hEq :
                        η (θ (FreeGroup.of
                          (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) =
                          FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ) := by
                      simpa [τ, xWord, hi, secondReductionCanonicalTransportMiddleRestIndex] using
                        secondReductionCanonicalSchreierToTransportSecondBranch_toInv_middleRest
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k
                    change F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) *
                        (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))⁻¹ ∈
                      Subgroup.normalClosure R
                    rw [show F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) =
                        η (θ (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) by rfl,
                      hEq]
                    simp only [mul_inv_cancel, one_mem]
                | inr jk =>
                    rcases jk with ⟨j, b⟩
                    have hEq :
                        η (θ (FreeGroup.of
                          (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) =
                          FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ) := by
                      simpa [τ, xWord, hi, secondReductionCanonicalTransportTailIndex] using
                        secondReductionCanonicalSchreierToTransportSecondBranch_toInv_tail
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k
                    change F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) *
                        (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))⁻¹ ∈
                      Subgroup.normalClosure R
                    rw [show F (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ)) =
                        η (θ (FreeGroup.of (FuchsianGenerator.elliptic i : FuchsianGenerator τ))) by rfl,
                      hEq]
                    simp only [mul_inv_cancel, one_mem]
    | surfaceA i =>
        exact Fin.elim0 (by
          simpa [τ, secondReductionTransportSignature, familyFuchsianSignature] using i)
    | surfaceB i =>
        exact Fin.elim0 (by
          simpa [τ, secondReductionTransportSignature, familyFuchsianSignature] using i)
  intro y
  simpa [R, F] using
    ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv
      R F hgen y

end FenchelNielsen
