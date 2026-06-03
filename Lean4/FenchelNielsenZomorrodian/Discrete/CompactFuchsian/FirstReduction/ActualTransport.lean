import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.Reductions

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/FirstReduction/ActualTransport.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# First compact zero-genus reduction

The first explicit finite quotient reduction for compact zero-genus Fuchsian presentations, including quotient maps, basis transport, signatures, and relator verification.
-/

namespace FenchelNielsen
private theorem firstReductionIndex_card_ge_three
    {tailLen p : ℕ} (hp : 2 ≤ p) (hTailLen : 0 < tailLen) :
    3 ≤ Fintype.card (FirstReductionIndex tailLen p) := by
  simp only [FirstReductionIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  nlinarith [Nat.succ_le_iff.mpr hTailLen, hp]
private theorem firstReductionPeriods_ge_two
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j)
    (x : FirstReductionIndex tailLen p) :
    2 ≤ firstReductionPeriods (p := p) m₁' m₂' tail x := by
  cases x using Sum.casesOn <;> rename_i x
  · fin_cases x
    · simpa [firstReductionPeriods, twoPeriods] using hm₁'
    · simpa [firstReductionPeriods, twoPeriods] using hm₂'
  · simpa [firstReductionPeriods] using htail x.1
noncomputable def firstReductionTransportSignature
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianSignature :=
  familyFuchsianSignature
    (firstReductionPeriods (p := p) m₁' m₂' tail)
    (firstReductionPeriods_ge_two m₁' m₂' tail hm₁' hm₂' htail)
    (firstReductionIndex_card_ge_three hp hTailLen)
def firstReductionTailSuccEquivFirstSecondTail
    (tailLen p : ℕ) :
    Fin (tailLen + 1) × Fin p ≃ Sum (Fin p) (Fin tailLen × Fin p) where
  toFun jk :=
    Fin.cases (motive := fun _ => Sum (Fin p) (Fin tailLen × Fin p))
      (.inl jk.2)
      (fun j => .inr (j, jk.2))
      jk.1
  invFun
    | .inl k => (0, k)
    | .inr jk => (jk.1.succ, jk.2)
  left_inv := by
    intro jk
    rcases jk with ⟨j, k⟩
    cases j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv := by
    intro s
    cases s with
    | inl k => rfl
    | inr jk =>
        rcases jk with ⟨j, k⟩
        rfl
def firstReductionIndexSuccEquivFirstSecondInputIndex
    (tailLen p : ℕ) :
    FirstReductionIndex (tailLen + 1) p ≃ FirstSecondInputIndex tailLen p :=
  Equiv.sumCongr (Equiv.refl (Fin 2))
    (firstReductionTailSuccEquivFirstSecondTail tailLen p)
def finTwoRestEquiv {p : ℕ} (hp : 2 ≤ p) : Fin p ≃ Sum (Fin 2) (Fin (p - 2)) :=
  (finCongr (by omega : p = 2 + (p - 2))).trans finSumFinEquiv.symm
def firstSecondInputIndexEquivSecondReductionSourceIndex
    {tailLen p : ℕ} (hp : 2 ≤ p) :
    FirstSecondInputIndex tailLen p ≃ SecondReductionSourceIndex tailLen p :=
  Equiv.sumCongr (Equiv.refl (Fin 2))
    ((Equiv.sumCongr (finTwoRestEquiv hp) (Equiv.refl (Fin tailLen × Fin p))).trans
      (Equiv.sumAssoc (Fin 2) (Fin (p - 2)) (Fin tailLen × Fin p)))
def firstReductionIndexSuccEquivSecondReductionSourceIndex
    {tailLen p : ℕ} (hp : 2 ≤ p) :
    FirstReductionIndex (tailLen + 1) p ≃ SecondReductionSourceIndex tailLen p :=
  (firstReductionIndexSuccEquivFirstSecondInputIndex tailLen p).trans
    (firstSecondInputIndexEquivSecondReductionSourceIndex hp)
private theorem firstReductionTailIncludingThird_transportPeriods_reindexed
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) (hp : 2 ≤ p)
    (x : FirstReductionIndex (tailLen + 1) p) :
    firstReductionPeriods (p := p) m₁' m₂'
        (firstReductionTailIncludingThird (q := q) m₃' tail) x =
      secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail
        (firstReductionIndexSuccEquivSecondReductionSourceIndex hp x) := by
  cases x using Sum.casesOn <;> rename_i x
  · fin_cases x <;> rfl
  · rcases x with ⟨j, k⟩
    cases j using Fin.cases with
    | zero =>
        change q * m₃' =
          secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail
            (firstSecondInputIndexEquivSecondReductionSourceIndex hp (.inr (.inl k)))
        unfold firstSecondInputIndexEquivSecondReductionSourceIndex
        cases h : finTwoRestEquiv hp k with
        | inl i =>
            simp only [secondReductionSourcePeriods, Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr,
  Function.comp_apply, Sum.map_inl, h, Equiv.sumAssoc_apply_inl_inl]
        | inr i =>
            simp only [secondReductionSourcePeriods, Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr,
  Function.comp_apply, Sum.map_inl, h, Equiv.sumAssoc_apply_inl_inr]
    | succ j =>
        rfl
theorem firstReductionTransportSignature_mulEquiv_secondReductionSourceSignature_exists
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 0 < m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Nonempty
      (FuchsianPresentedGroup
          (firstReductionTransportSignature m₁' m₂'
            (firstReductionTailIncludingThird (q := q) m₃' tail)
            hp hm₁' hm₂'
            (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
            (Nat.succ_pos _))
        ≃*
        FuchsianPresentedGroup
          (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
            hm₃' htail)) := by
  classical
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
        (firstReductionTransportSignature m₁' m₂'
          (firstReductionTailIncludingThird (q := q) m₃' tail)
          hp hm₁' hm₂'
          (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
          (Nat.succ_pos _))
      (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
        hm₃' htail)
      ?_ ?_
      (Fintype.equivFin (FirstReductionIndex (tailLen + 1) p))
      ((firstReductionIndexSuccEquivSecondReductionSourceIndex hp).trans
        (Fintype.equivFin (SecondReductionSourceIndex tailLen p))) ?_
  · simp only [firstReductionTransportSignature, familyFuchsianSignature]
  · simp only [secondReductionSourceSignature, familyFuchsianSignature]
  · intro x
    calc
      (firstReductionTransportSignature m₁' m₂'
          (firstReductionTailIncludingThird (q := q) m₃' tail)
          hp hm₁' hm₂'
          (firstReductionTailIncludingThird_ge_two_of_pos hq m₃' tail hm₃' htail)
          (Nat.succ_pos _)).periods
          ((Fintype.equivFin (FirstReductionIndex (tailLen + 1) p)) x)
          =
            firstReductionPeriods (p := p) m₁' m₂'
              (firstReductionTailIncludingThird (q := q) m₃' tail) x := by
            simp only [firstReductionTransportSignature, familyFuchsianSignature_periods]
      _ =
          secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail
            (firstReductionIndexSuccEquivSecondReductionSourceIndex hp x) :=
            firstReductionTailIncludingThird_transportPeriods_reindexed
              m₁' m₂' m₃' tail hp x
      _ =
        (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
            hm₃' htail).periods
          ((Fintype.equivFin (SecondReductionSourceIndex tailLen p))
            (firstReductionIndexSuccEquivSecondReductionSourceIndex hp x)) := by
            simp only [secondReductionSourceSignature, familyFuchsianSignature_periods]
end FenchelNielsen
