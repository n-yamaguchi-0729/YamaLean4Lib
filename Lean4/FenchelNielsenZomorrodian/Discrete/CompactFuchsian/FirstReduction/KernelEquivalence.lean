import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.ActualTransport
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.RelatorProofs

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/FirstReduction/KernelEquivalence.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# First compact zero-genus reduction

The first explicit finite quotient reduction for compact zero-genus Fuchsian presentations, including quotient maps, basis transport, signatures, and relator verification.
-/

namespace FenchelNielsen
def originalFirstReductionIndexEquivCanonicalSourceFin
    (tailLen : ℕ) :
    OriginalFirstReductionIndex tailLen ≃ Fin (2 + tailLen) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.refl (Fin tailLen))).trans
    finSumFinEquiv
theorem firstReductionSourceSignature_mulEquiv_canonicalSourceSignature_exists
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    Nonempty
      (FuchsianPresentedGroup
          (firstReductionSourceSignature m₁' m₂' tail hp
            (lt_of_lt_of_le (by decide : 0 < 2) hm₁')
            (lt_of_lt_of_le (by decide : 0 < 2) hm₂') htail hTailLen)
        ≃*
        FuchsianPresentedGroup
          (firstReductionCanonicalSourceSignature
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) := by
  classical
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
      (firstReductionSourceSignature m₁' m₂' tail hp
        (lt_of_lt_of_le (by decide : 0 < 2) hm₁')
        (lt_of_lt_of_le (by decide : 0 < 2) hm₂') htail hTailLen)
      (firstReductionCanonicalSourceSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      ?_ ?_
      (originalFirstReductionOrderedIndexEquiv tailLen)
      (originalFirstReductionIndexEquivCanonicalSourceFin tailLen) ?_
  · simp only [firstReductionSourceSignature, originalFirstReductionSignature]
  · simp only [firstReductionCanonicalSourceSignature]
  · intro x
    cases x using Sum.casesOn <;> rename_i x
    · fin_cases x
      · calc
          (firstReductionSourceSignature m₁' m₂' tail hp
              (lt_of_lt_of_le (by decide : 0 < 2) hm₁')
              (lt_of_lt_of_le (by decide : 0 < 2) hm₂') htail hTailLen).periods
              (originalFirstReductionOrderedIndexEquiv tailLen (.inl (0 : Fin 2))) =
            p * m₁' := by
              rw [originalFirstReductionOrderedIndexEquiv_left_zero]
              simp only [originalFirstReductionSignature, originalFirstReductionSignaturePeriod, Fin.coe_ofNat_eq_mod,
  Nat.zero_mod, ↓reduceDIte]
          _ =
            (firstReductionCanonicalSourceSignature
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
              (originalFirstReductionIndexEquivCanonicalSourceFin tailLen (.inl (0 : Fin 2))) := by
              simpa [firstReductionCanonicalSourceZeroIndex] using
                (firstReductionCanonicalSourceSignature_period_zero
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).symm
      · calc
          (firstReductionSourceSignature m₁' m₂' tail hp
              (lt_of_lt_of_le (by decide : 0 < 2) hm₁')
              (lt_of_lt_of_le (by decide : 0 < 2) hm₂') htail hTailLen).periods
              (originalFirstReductionOrderedIndexEquiv tailLen (.inl (1 : Fin 2))) =
            p * m₂' := by
              rw [originalFirstReductionOrderedIndexEquiv_left_one]
              have hOneFin : (1 : Fin (2 + tailLen)) = ⟨1, by omega⟩ := by
                apply Fin.ext
                simp only [Fin.coe_ofNat_eq_mod]
                rw [Nat.mod_eq_of_lt (by omega : 1 < 2 + tailLen)]
              rw [hOneFin]
              simp only [originalFirstReductionSignature, originalFirstReductionSignaturePeriod, one_ne_zero, ↓reduceDIte]
          _ =
            (firstReductionCanonicalSourceSignature
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
              (originalFirstReductionIndexEquivCanonicalSourceFin tailLen (.inl (1 : Fin 2))) := by
              simpa [firstReductionCanonicalSourceOneIndex] using
                (firstReductionCanonicalSourceSignature_period_one
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).symm
    · calc
        (firstReductionSourceSignature m₁' m₂' tail hp
            (lt_of_lt_of_le (by decide : 0 < 2) hm₁')
            (lt_of_lt_of_le (by decide : 0 < 2) hm₂') htail hTailLen).periods
            (originalFirstReductionOrderedIndexEquiv tailLen (.inr x)) =
          tail x := by
            rw [originalFirstReductionOrderedIndexEquiv_right]
            simp only [originalFirstReductionSignature, originalFirstReductionSignaturePeriod, Nat.add_eq_zero_iff,
  OfNat.ofNat_ne_zero, false_and, ↓reduceDIte, add_tsub_cancel_left, Fin.eta, dite_eq_ite, ite_eq_right_iff]
            omega
        _ =
          (firstReductionCanonicalSourceSignature
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
            (originalFirstReductionIndexEquivCanonicalSourceFin tailLen (.inr x)) := by
            simpa [firstReductionCanonicalSourceTailIndex] using
              (firstReductionCanonicalSourceSignature_period_tail
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen x).symm
noncomputable def firstReductionCanonicalSourceQuotientHom
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianPresentedGroup
      (firstReductionCanonicalSourceSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) →*
      Multiplicative (ZMod p) := by
  classical
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let ξ :=
    firstReductionCanonicalSourceQuotientImage
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  exact ellipticQuotientHom σ ξ
    (firstReductionCanonicalSourceQuotientImage_pow
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
    (firstReductionCanonicalSourceQuotientImage_prod
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
noncomputable def firstReductionCanonicalSourceKernelEquiv_targetSignature
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    (firstReductionCanonicalSourceQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).ker ≃*
      FuchsianPresentedGroup
        (firstReductionCanonicalTargetSignature
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) := by
  simpa [firstReductionCanonicalSourceQuotientHom] using
    firstReductionCanonicalKernelEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
def firstReductionIndexEquivCanonicalTargetFin
    (tailLen p : ℕ) :
    FirstReductionIndex tailLen p ≃ Fin (2 + p * tailLen) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2))
      ((Equiv.prodComm (Fin tailLen) (Fin p)).trans finProdFinEquiv)).trans
    finSumFinEquiv
private theorem firstReductionCanonicalTargetSignature_mulEquiv_transportSignature_exists
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    Nonempty
      (FuchsianPresentedGroup
          (firstReductionCanonicalTargetSignature
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
        ≃*
        FuchsianPresentedGroup
          (firstReductionTransportSignature
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)) := by
  classical
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
      (firstReductionCanonicalTargetSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      (firstReductionTransportSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)
      ?_ ?_
      (firstReductionIndexEquivCanonicalTargetFin tailLen p)
      (Fintype.equivFin (FirstReductionIndex tailLen p)) ?_
  · simp only [firstReductionCanonicalTargetSignature]
  · simp only [firstReductionTransportSignature, familyFuchsianSignature]
  · intro x
    cases x using Sum.casesOn <;> rename_i x
    · fin_cases x
      · calc
          (firstReductionCanonicalTargetSignature
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
            (firstReductionIndexEquivCanonicalTargetFin tailLen p (.inl (0 : Fin 2))) =
            m₁' := by
              simpa [firstReductionCanonicalTargetZeroIndex,
                firstReductionIndexEquivCanonicalTargetFin] using
                firstReductionCanonicalTargetSignature_period_zero
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          _ =
            (firstReductionTransportSignature
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
              ((Fintype.equivFin (FirstReductionIndex tailLen p)) (.inl (0 : Fin 2))) := by
              simp only [firstReductionTransportSignature, Fin.isValue, familyFuchsianSignature_periods,
  firstReductionPeriods, twoPeriods, Nat.reduceAdd, Fin.cases_zero]
      · calc
          (firstReductionCanonicalTargetSignature
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
            (firstReductionIndexEquivCanonicalTargetFin tailLen p (.inl (1 : Fin 2))) =
            m₂' := by
              simpa [firstReductionCanonicalTargetOneIndex,
                firstReductionIndexEquivCanonicalTargetFin] using
                firstReductionCanonicalTargetSignature_period_one
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
          _ =
            (firstReductionTransportSignature
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
              ((Fintype.equivFin (FirstReductionIndex tailLen p)) (.inl (1 : Fin 2))) := by
              simp only [firstReductionTransportSignature, Fin.isValue, familyFuchsianSignature_periods,
  firstReductionPeriods, twoPeriods, Nat.reduceAdd, fin_cases_const_one]
    · rcases x with ⟨j, k⟩
      calc
        (firstReductionCanonicalTargetSignature
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
            (firstReductionIndexEquivCanonicalTargetFin tailLen p (.inr (j, k))) =
          tail j := by
            simpa [firstReductionCanonicalTargetTailIndex,
              firstReductionIndexEquivCanonicalTargetFin, finProdFinEquiv,
              Nat.add_assoc, Nat.add_comm, Nat.mul_comm] using
              firstReductionCanonicalTargetSignature_period_tail
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j
        _ =
          (firstReductionTransportSignature
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
            ((Fintype.equivFin (FirstReductionIndex tailLen p)) (.inr (j, k))) := by
            simp only [firstReductionTransportSignature, familyFuchsianSignature_periods, firstReductionPeriods]
private theorem firstReductionCanonicalTargetSignature_mulEquiv_secondReductionSourceSignature_exists
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 0 < m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Nonempty
      (FuchsianPresentedGroup
          (firstReductionCanonicalTargetSignature m₁' m₂'
            (firstReductionTailIncludingThird (q := q) m₃' tail)
            hp hm₁' hm₂'
            (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
            (Nat.succ_pos _))
        ≃*
        FuchsianPresentedGroup
          (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
            hm₃' htail)) := by
  rcases firstReductionCanonicalTargetSignature_mulEquiv_transportSignature_exists
      m₁' m₂' (firstReductionTailIncludingThird (q := q) m₃' tail)
      hp hm₁' hm₂' (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
      (Nat.succ_pos _) with ⟨e₁⟩
  rcases firstReductionTransportSignature_mulEquiv_secondReductionSourceSignature_exists
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩
noncomputable def firstReductionCanonicalKernelEquiv_secondReductionSourceSignature
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 0 < m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    (firstReductionCanonicalSourceQuotientHom m₁' m₂'
        (firstReductionTailIncludingThird (q := q) m₃' tail)
        hp hm₁' hm₂'
        (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
        (Nat.succ_pos _)).ker ≃*
      FuchsianPresentedGroup
        (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
          hm₃' htail) :=
  (firstReductionCanonicalSourceKernelEquiv_targetSignature
      m₁' m₂' (firstReductionTailIncludingThird (q := q) m₃' tail)
      hp hm₁' hm₂'
      (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
      (Nat.succ_pos _)).trans
    (Classical.choice
      (firstReductionCanonicalTargetSignature_mulEquiv_secondReductionSourceSignature_exists
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
