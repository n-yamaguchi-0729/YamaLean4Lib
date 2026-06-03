import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.RelatorProofs
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceHead
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceMiddleTail
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceTotal

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/KernelEquivalence.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen
private def SecondReductionCanonicalTransportBlockForwardMapData
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) : Type :=
  (letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
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
    ReidemeisterSchreier.Discrete.Presentations.RelatorQuotientForwardMapData
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
        (f := ellipticQuotientGeneratorImage σ
          (secondReductionCanonicalSourceQuotientImage
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
        (rels := relators σ)
        (secondReductionCanonicalSchreierTransversal
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)))
      (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
      (secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
private noncomputable def secondReductionCanonicalTransportForwardMapData_of_secondBranch_allGenerators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (hMapsRelators :
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
      ∀ r ∈
          ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (secondReductionCanonicalSourceQuotientImage
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
            (rels := relators σ)
            (secondReductionCanonicalSchreierTransversal
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)),
        η r ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail))
    (hInvGenerators :
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
      let η :=
        secondReductionCanonicalSchreierToTransportSecondBranchHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      ∀ z : ↥(schreierGeneratorSet
          (secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)),
        θ (η (FreeGroup.of z)) * (FreeGroup.of z)⁻¹ ∈
          Subgroup.normalClosure
            (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
              (f := ellipticQuotientGeneratorImage σ
                (secondReductionCanonicalSourceQuotientImage
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
              (rels := relators σ)
              (secondReductionCanonicalSchreierTransversal
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))))
    :
    SecondReductionCanonicalTransportBlockForwardMapData
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
  classical
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
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
      (f := ellipticQuotientGeneratorImage σ
        (secondReductionCanonicalSourceQuotientImage
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
      (rels := relators σ)
      (secondReductionCanonicalSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
  let F : FreeGroup ↥(schreierGeneratorSet
      (secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) →*
      FreeGroup ↥(schreierGeneratorSet
        (secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) :=
    θ.comp η
  refine
    { toHom := η
      mapsRelators := ?_
      inv_toHom := ?_
      to_invHom := ?_ }
  · intro r hr
    simpa [SecondReductionCanonicalTransportBlockForwardMapData, σ, τ, e, hrels, η] using
      hMapsRelators r hr
  · intro x
    simpa [SecondReductionCanonicalTransportBlockForwardMapData, R, F, σ, τ, e, hrels, θ, η] using
      ReidemeisterSchreier.Discrete.Presentations.freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv
        R F
        (by
          intro z
          simpa [R, F, σ, e, hrels, θ, η] using hInvGenerators z)
        x
  · intro y
    simpa [SecondReductionCanonicalTransportBlockForwardMapData, σ, τ, θ, η] using
      secondReductionCanonicalSchreierToTransportSecondBranch_toInv_mem_blockRelators
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y
private noncomputable def secondReductionCanonicalTransportForwardMapData_of_secondBranch_of_mapsRelators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (hMapsRelators :
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
      ∀ r ∈
          ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
            (f := ellipticQuotientGeneratorImage σ
              (secondReductionCanonicalSourceQuotientImage
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
            (rels := relators σ)
            (secondReductionCanonicalSchreierTransversal
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)),
        η r ∈ Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail))
    :
    SecondReductionCanonicalTransportBlockForwardMapData
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail := by
  classical
  refine
    secondReductionCanonicalTransportForwardMapData_of_secondBranch_allGenerators
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      hMapsRelators ?_
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
  let hT :=
    secondReductionCanonicalSchreierTransversal_isRightSchreierTransversal
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let η :=
    secondReductionCanonicalSchreierToTransportSecondBranchHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
      (f := ellipticQuotientGeneratorImage σ
        (secondReductionCanonicalSourceQuotientImage
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
      (rels := relators σ)
      (secondReductionCanonicalSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
  intro z
  rcases
    secondReductionCanonical_schreierGeneratorSet_cases
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail z with
    hFirst | hSecond | hZero
  · let zFirst : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail,
        secondReductionCanonicalFirstPowerKernel_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail⟩
    have hz : z = zFirst := Subtype.ext hFirst
    subst z
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    let A :=
      xWord τ
        ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
          (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
    have hzWord :
        e.symm
            (secondReductionCanonicalFirstPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) =
          (FreeGroup.of zFirst)⁻¹ := by
      simpa [σ, φ, hT, e, zFirst] using
        secondReductionCanonicalSchreierBasisEquiv_symm_apply
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail zFirst
    have hηA : η (FreeGroup.of zFirst) = A⁻¹ := by
      have h :=
        secondReductionCanonicalSchreierToTransportSecondBranchHom_firstPowerWord
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      have h' := congrArg Inv.inv h
      simpa [σ, e, η, A, hzWord] using h'
    have hθA :
        θ A =
          e.symm
            (secondReductionCanonicalFirstPowerKernel
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
      simpa [σ, τ, e, θ, A] using
        secondReductionCanonicalTransportToSchreierHom_positiveDistinguished
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    have hθ : θ (η (FreeGroup.of zFirst)) = FreeGroup.of zFirst := by
      calc
        θ (η (FreeGroup.of zFirst)) = θ A⁻¹ := by rw [hηA]
        _ = (θ A)⁻¹ := by simp only [Lean.Elab.WF.paramLet, map_inv]
        _ =
            (e.symm
              (secondReductionCanonicalFirstPowerKernel
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))⁻¹ := by
              rw [hθA]
        _ = ((FreeGroup.of zFirst)⁻¹)⁻¹ := by rw [hzWord]
        _ = FreeGroup.of zFirst := by simp only [inv_inv]
    rw [hθ]
    simp only [mul_inv_cancel, one_mem]
  · rcases hSecond with ⟨k, hz⟩
    let zSecond : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalSecondEdgeKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k,
        secondReductionCanonicalSecondEdgeKernelElement_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k⟩
    have hz' : z = zSecond := Subtype.ext hz
    subst z
    simpa [R, σ, e, hrels, hT, θ, η, zSecond] using
      secondReductionCanonicalSecondBranch_secondEdge_toInv_mem_normalClosure
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  · rcases hZero with ⟨y, hy, k, hz⟩
    let x : FuchsianGenerator σ :=
      secondReductionCanonicalDistinguishedGenerator
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    have hxy : x ≠ y := by
      intro hEq
      have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod q) := by
        simp only [Lean.Elab.WF.paramLet, secondReductionCanonicalDistinguishedGenerator,
  secondReductionCanonicalSourceFreeQuotientHom_firstDistinguished m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail, φ, x]
      have hyx : φ (FreeGroup.of x) = 1 := by
        simpa [hEq] using hy
      have hOne : (Multiplicative.ofAdd (1 : ZMod q)) = 1 := hx.symm.trans hyx
      have hZ : (1 : ZMod q) = 0 := Multiplicative.ofAdd.injective hOne
      have hval := congrArg ZMod.val hZ
      letI : Fact (1 < q) := ⟨lt_of_lt_of_le (by decide : 1 < 2) hq⟩
      rw [ZMod.val_one] at hval
      simp only [ZMod.val_zero, one_ne_zero] at hval
    let zZero : ↥(schreierGeneratorSet hT) :=
      ⟨secondReductionCanonicalZeroImageKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k,
        secondReductionCanonicalZeroImageKernelElement_mem_schreierGeneratorSet
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy⟩
    have hz' : z = zZero := Subtype.ext hz
    subst z
    simpa [R, σ, φ, e, hrels, x, hT, θ, η, zZero] using
      secondReductionCanonicalSecondBranch_zeroImage_toInv_mem_normalClosure
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail y hy k hxy
private noncomputable def secondReductionCanonicalTransportBlockKernelEquivOfForwardMapData
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (D :
      SecondReductionCanonicalTransportBlockForwardMapData
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) :
    (secondReductionCanonicalSourceQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).ker ≃*
      PresentedGroup
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let ξ :=
    secondReductionCanonicalSourceQuotientImage
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hpow : ∀ i, ξ i ^ σ.periods i = 1 :=
    secondReductionCanonicalSourceQuotientImage_pow
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let hprod : ∏ i : Fin σ.numPeriods, ξ i = 1 :=
    secondReductionCanonicalSourceQuotientImage_prod
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let i₀ : Fin σ.numPeriods :=
    secondReductionCanonicalSourceMiddleIndex
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩
  have hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod q) := by
    simp only [secondReductionCanonicalSourceMiddleIndex, add_zero, secondReductionCanonicalSourceQuotientImage,
  ↓reduceIte, ξ, i₀]
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let R :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet
      (f := ellipticQuotientGeneratorImage σ
        (secondReductionCanonicalSourceQuotientImage
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
      (rels := relators σ)
      (secondReductionCanonicalSchreierTransversal
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
  let S : Set (FreeGroup (FuchsianGenerator τ)) :=
    secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hTarget :
      ∀ s ∈ S, θ s ∈ Subgroup.normalClosure R := by
    intro s hs
    simpa [S, R, σ, τ, e, θ] using
      secondReductionCanonicalTransportToSchreier_mapsBlockRelators
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail s hs
  let data :
      FuchsianEllipticCyclicRelatorData σ ξ i₀ hi₀ S := by
    simpa [FuchsianEllipticCyclicRelatorData, CyclicSchreierRelatorData,
      σ, τ, ξ, i₀, hi₀, e, R, S, θ,
      secondReductionCanonicalSourceFreeQuotientHom,
      secondReductionCanonicalDistinguishedGenerator,
      SecondReductionCanonicalTransportBlockForwardMapData] using
      (ReidemeisterSchreier.Discrete.Presentations.relatorQuotientMutualMapDataOfForwardMapData
        (R := R) (S := S) (invHom := θ) hTarget D)
  simpa [secondReductionCanonicalSourceQuotientHom, ellipticQuotientHom,
    σ, τ, ξ, hpow, hprod, S] using
    fuchsianEllipticCyclicKernelEquivPresentedGroupOfRelatorData
      σ ξ hpow hprod i₀ hi₀ S data
theorem secondReductionCanonicalTransportKernelEquiv_of_secondBranch
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Nonempty
      ((secondReductionCanonicalSourceQuotientHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).ker ≃*
        FuchsianPresentedGroup
          (secondReductionTransportSignature (p := p) hq
            m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)) := by
    let D :=
      secondReductionCanonicalTransportForwardMapData_of_secondBranch_of_mapsRelators
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        (secondReductionToTransportSecondBranch_mapsRelators_of_sourceCases
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          (by
            classical
            have hNegative :=
              secondReductionCanonicalSecondBranchNegativeMiddleSourceCase_mem_blockRelators
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            have hTotal :=
              secondReductionCanonicalSecondBranchSourceTotalCase_mem_normalClosure
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            dsimp [SecondReductionCanonicalSecondBranchSourceRelatorCases,
              SecondReductionCanonicalSecondBranchNegativeMiddleSourceCase,
              SecondReductionCanonicalSecondBranchSourceTotalCase] at hNegative hTotal ⊢
            refine ⟨?_, ?_, ?_, ?_, hTotal⟩
            · intro k
              simpa using
                secondReductionToTransportSecondBranch_headZero_sourceCase_mem_normalClosure
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
            · intro k
              simpa using
                secondReductionToTransportSecondBranch_headOne_sourceCase_mem_normalClosure
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
            · intro r k
              by_cases h0 : r.val = 0
              · have hr : r = ⟨0, by omega⟩ := Fin.ext h0
                rw [hr]
                simpa using
                  secondReductionToTransportSecondBranch_posMiddle_sourceCase_mem_normalClosure
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
              · by_cases h1 : r.val = 1
                · have hr : r = ⟨1, by omega⟩ := Fin.ext h1
                  rw [hr]
                  simpa using hNegative k
                · let rRest : Fin (p - 2) := ⟨r.val - 2, by omega⟩
                  have hr : r = (⟨2 + rRest.val, by omega⟩ : Fin p) := by
                    ext
                    simp only [rRest]
                    omega
                  rw [hr]
                  simpa [rRest] using
                    secondReductionToTransportSecondBranch_middleRest_sourceCase_mem_normalClosure
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail rRest k
            · intro b j k
              simpa using
                secondReductionToTransportSecondBranch_tail_sourceCase_mem_normalClosure
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k))
    let eBlock :=
      secondReductionCanonicalTransportBlockKernelEquivOfForwardMapData
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail D
    let eBlockOrdered :=
      secondReductionCanonicalTransportBlockRelatorsEquivOrderedTarget
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    rcases
      secondReductionCanonicalOrderedTarget_mulEquiv_transportSignature_exists
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail with
      ⟨eOrderedTransport⟩
    exact ⟨eBlock.trans (eBlockOrdered.trans eOrderedTransport)⟩
end FenchelNielsen
