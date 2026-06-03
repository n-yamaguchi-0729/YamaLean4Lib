import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Relators.SourceCore

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/RelatorProofs.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen

def SecondReductionCanonicalSecondBranchSourceRelatorCases
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
  let hZero :=
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
        Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  let hOne :=
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
        Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  let hMiddle :=
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
        Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  let hTail :=
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
        Subgroup.normalClosure
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
  let hTotal :=
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
  hZero ∧ hOne ∧ hMiddle ∧ hTail ∧ hTotal
theorem secondReductionToTransportSecondBranch_mapsRelators_of_sourceCases
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (hCases :
      SecondReductionCanonicalSecondBranchSourceRelatorCases
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) :
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
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp [SecondReductionCanonicalSecondBranchSourceRelatorCases] at hCases
  rcases hCases with ⟨hZero, hOne, hMiddle, hTail, hTotal⟩
  simpa [secondReductionCanonicalSchreierTransversal,
    secondReductionCanonicalSchreierBasisEquiv] using
    secondReductionCanonicalSchreierToTarget_mapsRelators_of_source_cases
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)
        (secondReductionCanonicalSchreierToTransportSecondBranchHom
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
        hZero hOne hMiddle hTail hTotal

end FenchelNielsen
