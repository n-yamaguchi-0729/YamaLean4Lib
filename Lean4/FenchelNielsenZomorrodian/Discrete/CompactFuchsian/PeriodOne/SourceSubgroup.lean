import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.Quotients
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.KernelEquivalence
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.LowCardDihedral
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.KernelEquivalence

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/SourceSubgroup.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Period-one cleanup step

Handles the cleanup of period-one target entries using quotient maps, kernel equivalences, low-cardinality dihedral cases, source subgroups, and relator proofs.
-/

namespace FenchelNielsen

theorem SecondStageCleanupPeriodData.periodOne_of_not_strict
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime)
    (hNonStrict : ¬ (2 ≤ D.m₁' ∧ 2 ≤ D.m₂' ∧ 2 ≤ E.m₃')) :
    D.m₁' = 1 ∨ D.m₂' = 1 ∨ E.m₃' = 1 := by
  by_cases hm₁ : 2 ≤ D.m₁'
  · by_cases hm₂ : 2 ≤ D.m₂'
    · by_cases hm₃ : 2 ≤ E.m₃'
      · exact False.elim (hNonStrict ⟨hm₁, hm₂, hm₃⟩)
      · right
        right
        have hpos : 0 < E.m₃' := E.hm₃'
        omega
    · right
      left
      have hpos : 0 < D.m₂' := D.hm₂'
      omega
  · left
    have hpos : 0 < D.m₁' := D.hm₁'
    omega

private theorem originalFirstReduction_doublePeriodOne_sourceSubgroup_exists
    {tailLen p : ℕ} (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    ∃ L : Subgroup
        (FuchsianPresentedGroup
          (originalFirstReductionSignature 1 1 tail hp (by norm_num) (by norm_num)
            htail hTailLen)),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 2 := by
  classical
  let source :=
    originalFirstReductionSignature 1 1 tail hp (by norm_num) (by norm_num)
      htail hTailLen
  by_cases hHigh : 3 ≤ p * tailLen
  · let target := doublePeriodOneTailReplicatedSignature tail htail hHigh
    have hTargetSubgroup :
        ∃ L : Subgroup (FuchsianPresentedGroup target),
          L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
            SubgroupQuotientHasDerivedLengthAtMost L 1 :=
      sourceSubgroup_exists_of_lcmCondition
        target (m := 1) (by norm_num)
        (doublePeriodOneTailReplicatedSignature_lcmCondition tail htail hHigh hp)
    let eIdx := originalFirstReductionOrderedIndexEquiv tailLen
    have hperiods :
        ∀ x : OriginalFirstReductionIndex tailLen,
          source.periods (eIdx x) =
            originalFirstReductionPeriods (p := p) 1 1 tail x := by
      intro x
      simpa [source, eIdx] using
        originalFirstReduction_canonical_periods_eq
          1 1 tail hp (by norm_num) (by norm_num) htail hTailLen x
    let φ :=
      originalFirstReductionPeriodOneQuotientHom
        1 1 tail hp (by norm_num) (by norm_num) htail hTailLen
    let eKernel :
        φ.ker ≃* FuchsianPresentedGroup target := by
      simpa [φ, source, target, eIdx, originalFirstReductionPeriodOneQuotientHom] using
        doublePeriodOneKernelEquivOfForwardMapData
          1 1 tail hp (by norm_num) (by norm_num) htail hTailLen
          hHigh eIdx hperiods rfl rfl rfl
          (doublePeriodOneForwardMapData
            1 1 tail hp (by norm_num) (by norm_num) htail hTailLen
            hHigh eIdx hperiods rfl rfl rfl)
    letI : NeZero p :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    letI : Fintype (ZMod p) := ZMod.fintype p
    letI : Fintype (Multiplicative (ZMod p)) := inferInstance
    haveI : Finite (Multiplicative (ZMod p)) :=
      Finite.of_fintype (Multiplicative (ZMod p))
    simpa [source, φ] using
      sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
        φ eKernel hTargetSubgroup
  · have hMin : p = 2 ∧ tailLen = 1 :=
      firstReductionTransportPeriodsFin_tail_low_card_eq_two hp hTailLen hHigh
    let k : Fin tailLen := ⟨0, by omega⟩
    let n := tail k
    have hn : 2 ≤ n := htail k
    let τ := twoTwoTailSignature n hn
    let eTarget : OriginalFirstReductionIndex tailLen ≃ Fin τ.numPeriods :=
      (originalFirstReductionIndexEquivCanonicalSourceFin tailLen).trans
        (finCongr (by simp only [twoTwoTailSignature, τ]; omega))
    have hSourceEquiv :
        Nonempty (FuchsianPresentedGroup source ≃* FuchsianPresentedGroup τ) := by
      refine
        zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
          source τ
          (by simp only [originalFirstReductionSignature, source])
          (by simp only [twoTwoTailSignature, τ])
          (originalFirstReductionOrderedIndexEquiv tailLen)
          eTarget ?_
      intro x
      cases x using Sum.casesOn with
      | inl i =>
          fin_cases i
          · have hSource :
              source.periods
                  ((originalFirstReductionOrderedIndexEquiv tailLen) (.inl 0)) = 2 := by
              simp only [originalFirstReductionSignature, Fin.isValue, originalFirstReductionOrderedIndexEquiv_left_zero,
  hMin.1, originalFirstReductionSignaturePeriod_zero_fin, mul_one, source]
            have hTarget :
                τ.periods (eTarget (.inl 0)) = 2 := by
              simp only [twoTwoTailSignature, originalFirstReductionIndexEquivCanonicalSourceFin, Equiv.sumCongr_refl,
  Equiv.refl_trans, Fin.isValue, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, twoTwoTailPeriods,
  Fin.val_cast, Fin.val_castAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, eTarget, τ]
            exact hSource.trans hTarget.symm
          · have hSource :
              source.periods
                  ((originalFirstReductionOrderedIndexEquiv tailLen) (.inl 1)) = 2 := by
              simp only [originalFirstReductionSignature, Fin.isValue, originalFirstReductionOrderedIndexEquiv_left_one,
  hMin.1, originalFirstReductionSignaturePeriod_one_fin, mul_one, source]
            have hTarget :
                τ.periods (eTarget (.inl 1)) = 2 := by
              simp only [twoTwoTailSignature, originalFirstReductionIndexEquivCanonicalSourceFin, Equiv.sumCongr_refl,
  Equiv.refl_trans, Fin.isValue, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, twoTwoTailPeriods,
  Fin.val_cast, Fin.val_castAdd, Fin.coe_ofNat_eq_mod, Nat.mod_succ, one_ne_zero, ↓reduceIte, eTarget, τ]
            exact hSource.trans hTarget.symm
      | inr j =>
          have hj : j = k := by
            ext
            omega
          rw [hj]
          have hSource :
            source.periods
                ((originalFirstReductionOrderedIndexEquiv tailLen) (.inr k)) = n := by
            rw [originalFirstReductionOrderedIndexEquiv_right]
            simpa [source, originalFirstReductionSignature, k, n] using
              originalFirstReductionSignaturePeriod_tail
                (p := p) 1 1 tail k
          have hTarget :
              τ.periods (eTarget (.inr k)) = n := by
            simp only [twoTwoTailSignature, originalFirstReductionIndexEquivCanonicalSourceFin, Equiv.sumCongr_refl,
  Equiv.refl_trans, Equiv.trans_apply, finSumFinEquiv_apply_right, Fin.natAdd_mk, add_zero, finCongr_apply,
  Fin.cast_mk, Fin.reduceFinMk, twoTwoTailPeriods, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
  OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, n, k, eTarget, τ]
          exact hSource.trans hTarget.symm
    have hτ :
        ∃ L : Subgroup (FuchsianPresentedGroup τ),
          L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
            SubgroupQuotientHasDerivedLengthAtMost L 2 :=
      (finiteSolvableSmoothQuotientData_two_of_twoTwoTail hn).sourceSubgroup_exists_classical
    exact sourceSubgroup_exists_of_mulEquiv (Classical.choice hSourceEquiv) hτ

private theorem oneHeadPeriodOneTarget_sourceSubgroup_exists_by_tailPair
    {tailLen p : ℕ} (m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₂' : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j)
    (hTailLen : 0 < tailLen) :
    ∃ L : Subgroup
        (FuchsianPresentedGroup
          (oneHeadPeriodOneTargetSignature m₂' tail hp hm₂' htail hTailLen)),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 2 := by
  classical
  let target := oneHeadPeriodOneTargetSignature m₂' tail hp hm₂' htail hTailLen
  let idx := OneHeadPeriodOneTargetIndex tailLen p
  let j₀ : Fin tailLen := ⟨0, hTailLen⟩
  let k₀ : Fin p := finZeroOfTwoLe hp
  let k₁ : Fin p := finPartner hp k₀
  let pos : idx := .inr (k₀, j₀)
  let neg : idx := .inr (k₁, j₀)
  have hposneg : pos ≠ neg := by
    intro h
    have hk : k₁ = k₀ := by
      exact (congrArg Prod.fst (Sum.inr.inj h)).symm
    exact finPartner_ne hp k₀ hk
  let restSubtype := {x : idx // x ≠ pos ∧ x ≠ neg}
  let restLen := Fintype.card restSubtype
  let reidx : OriginalFirstReductionIndex restLen ≃ idx :=
    originalFirstReductionReindex pos neg hposneg
  let restPeriods : Fin restLen → ℕ := fun r =>
    oneHeadPeriodOneTargetPeriods (p := p) m₂' tail (reidx (.inr r))
  have hRestLen : 0 < restLen := by
    have hnePos : (Sum.inl (0 : Fin 1) : idx) ≠ pos := by
      change (Sum.inl (0 : Fin 1) : idx) ≠ Sum.inr (k₀, j₀)
      intro h
      cases h
    have hneNeg : (Sum.inl (0 : Fin 1) : idx) ≠ neg := by
      change (Sum.inl (0 : Fin 1) : idx) ≠ Sum.inr (k₁, j₀)
      intro h
      cases h
    have hnonempty : Nonempty restSubtype :=
      ⟨⟨(Sum.inl (0 : Fin 1) : idx), hnePos, hneNeg⟩⟩
    simpa [restLen] using (Fintype.card_pos_iff.mpr hnonempty)
  have hrest : ∀ r : Fin restLen, 2 ≤ restPeriods r := by
    intro r
    dsimp [restPeriods]
    cases h : reidx (.inr r) with
    | inl head =>
        fin_cases head
        simpa [oneHeadPeriodOneTargetPeriods] using hm₂'
    | inr kj =>
        simpa [oneHeadPeriodOneTargetPeriods] using htail kj.2
  let q := tail j₀
  have hq : 2 ≤ q := htail j₀
  let source :=
    originalFirstReductionSignature 1 1 restPeriods hq (by norm_num) (by norm_num)
      hrest hRestLen
  have hSourceSubgroup :
      ∃ L : Subgroup (FuchsianPresentedGroup source),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 2 :=
    originalFirstReduction_doublePeriodOne_sourceSubgroup_exists
      restPeriods hq hrest hRestLen
  have hTargetEquiv :
      Nonempty (FuchsianPresentedGroup target ≃* FuchsianPresentedGroup source) := by
    refine
      zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
        target source
        (by simp only [oneHeadPeriodOneTargetSignature, target])
        (by simp only [originalFirstReductionSignature, source])
        (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p)
        (reidx.symm.trans (originalFirstReductionOrderedIndexEquiv restLen)) ?_
    intro x
    have hsourcePeriod :
        source.periods
            ((reidx.symm.trans (originalFirstReductionOrderedIndexEquiv restLen)) x) =
          originalFirstReductionPeriods (p := q) 1 1 restPeriods (reidx.symm x) := by
      simpa [source] using
        originalFirstReduction_canonical_periods_eq
          1 1 restPeriods hq (by norm_num) (by norm_num) hrest hRestLen
          (reidx.symm x)
    calc
      target.periods ((oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p) x) =
          originalFirstReductionPeriods (p := q) 1 1 restPeriods (reidx.symm x) := by
        generalize hy : reidx.symm x = y
        have hx : x = reidx y := by
          rw [← hy]
          simp only [Equiv.apply_symm_apply]
        cases y using Sum.casesOn with
        | inl head =>
            fin_cases head
            · subst hx
              have htarget :
                  target.periods (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p pos) = q := by
                simp only [oneHeadPeriodOneTargetSignature, oneHeadPeriodOneTargetPeriods, Equiv.symm_apply_apply, pos, q,
  target]
              simpa [originalFirstReductionPeriods, twoPeriods] using htarget
            · subst hx
              have htarget :
                  target.periods (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p neg) = q := by
                simp only [oneHeadPeriodOneTargetSignature, oneHeadPeriodOneTargetPeriods, Equiv.symm_apply_apply, neg, q,
  target]
              simpa [originalFirstReductionPeriods, twoPeriods] using htarget
        | inr r =>
            subst hx
            have htarget :
                target.periods (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p (reidx (.inr r))) =
                  restPeriods r := by
              simp only [oneHeadPeriodOneTargetSignature, Equiv.symm_apply_apply, restPeriods, target]
            simpa [originalFirstReductionPeriods] using htarget
      _ = source.periods
          ((reidx.symm.trans (originalFirstReductionOrderedIndexEquiv restLen)) x) :=
        hsourcePeriod.symm
  exact sourceSubgroup_exists_of_mulEquiv (Classical.choice hTargetEquiv) hSourceSubgroup

private theorem firstReductionCanonicalTarget_periods_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (x : FirstReductionIndex tailLen p) :
    (firstReductionCanonicalTargetSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
      (firstReductionIndexEquivCanonicalTargetFin tailLen p x) =
        firstReductionPeriods (p := p) m₁' m₂' tail x := by
  classical
  cases x using Sum.casesOn with
  | inl head =>
      fin_cases head
      · simpa [firstReductionCanonicalTargetZeroIndex,
          firstReductionIndexEquivCanonicalTargetFin,
          firstReductionPeriods, twoPeriods] using
          firstReductionCanonicalTargetSignature_period_zero
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      · simpa [firstReductionCanonicalTargetOneIndex,
          firstReductionIndexEquivCanonicalTargetFin,
          firstReductionPeriods, twoPeriods] using
          firstReductionCanonicalTargetSignature_period_one
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  | inr jk =>
      rcases jk with ⟨j, k⟩
      simpa [firstReductionCanonicalTargetTailIndex,
        firstReductionIndexEquivCanonicalTargetFin, finProdFinEquiv,
        Nat.add_assoc, Nat.add_comm, Nat.mul_comm,
        firstReductionPeriods] using
        firstReductionCanonicalTargetSignature_period_tail
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j

private theorem firstReductionCanonicalTarget_sourceSubgroup_exists_by_tailPair
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    ∃ L : Subgroup
        (FuchsianPresentedGroup
          (firstReductionCanonicalTargetSignature
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen)),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 2 := by
  classical
  let target :=
    firstReductionCanonicalTargetSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let idx := FirstReductionIndex tailLen p
  let j₀ : Fin tailLen := ⟨0, hTailLen⟩
  let k₀ : Fin p := finZeroOfTwoLe hp
  let k₁ : Fin p := finPartner hp k₀
  let pos : idx := .inr (j₀, k₀)
  let neg : idx := .inr (j₀, k₁)
  have hposneg : pos ≠ neg := by
    intro h
    have hk : k₁ = k₀ := by
      exact (congrArg Prod.snd (Sum.inr.inj h)).symm
    exact finPartner_ne hp k₀ hk
  let restSubtype := {x : idx // x ≠ pos ∧ x ≠ neg}
  let restLen := Fintype.card restSubtype
  let reidx : OriginalFirstReductionIndex restLen ≃ idx :=
    originalFirstReductionReindex pos neg hposneg
  let restPeriods : Fin restLen → ℕ := fun r =>
    firstReductionPeriods (p := p) m₁' m₂' tail (reidx (.inr r))
  have hRestLen : 0 < restLen := by
    have hnePos : (Sum.inl (0 : Fin 2) : idx) ≠ pos := by
      change (Sum.inl (0 : Fin 2) : idx) ≠ Sum.inr (j₀, k₀)
      intro h
      cases h
    have hneNeg : (Sum.inl (0 : Fin 2) : idx) ≠ neg := by
      change (Sum.inl (0 : Fin 2) : idx) ≠ Sum.inr (j₀, k₁)
      intro h
      cases h
    have hnonempty : Nonempty restSubtype :=
      ⟨⟨(Sum.inl (0 : Fin 2) : idx), hnePos, hneNeg⟩⟩
    simpa [restLen] using (Fintype.card_pos_iff.mpr hnonempty)
  have hrest : ∀ r : Fin restLen, 2 ≤ restPeriods r := by
    intro r
    dsimp [restPeriods]
    cases h : reidx (.inr r) with
    | inl head =>
        fin_cases head
        · simpa [firstReductionPeriods, twoPeriods] using hm₁'
        · simpa [firstReductionPeriods, twoPeriods] using hm₂'
    | inr jk =>
        simpa [firstReductionPeriods] using htail jk.1
  let q := tail j₀
  have hq : 2 ≤ q := htail j₀
  let source :=
    originalFirstReductionSignature 1 1 restPeriods hq (by norm_num) (by norm_num)
      hrest hRestLen
  have hSourceSubgroup :
      ∃ L : Subgroup (FuchsianPresentedGroup source),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 2 :=
    originalFirstReduction_doublePeriodOne_sourceSubgroup_exists
      restPeriods hq hrest hRestLen
  have hTargetEquiv :
      Nonempty (FuchsianPresentedGroup target ≃* FuchsianPresentedGroup source) := by
    refine
      zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
        target source
        (by simp only [firstReductionCanonicalTargetSignature, target])
        (by simp only [originalFirstReductionSignature, source])
        (firstReductionIndexEquivCanonicalTargetFin tailLen p)
        (reidx.symm.trans (originalFirstReductionOrderedIndexEquiv restLen)) ?_
    intro x
    have hsourcePeriod :
        source.periods
            ((reidx.symm.trans (originalFirstReductionOrderedIndexEquiv restLen)) x) =
          originalFirstReductionPeriods (p := q) 1 1 restPeriods (reidx.symm x) := by
      simpa [source] using
        originalFirstReduction_canonical_periods_eq
          1 1 restPeriods hq (by norm_num) (by norm_num) hrest hRestLen
          (reidx.symm x)
    calc
      target.periods (firstReductionIndexEquivCanonicalTargetFin tailLen p x) =
          originalFirstReductionPeriods (p := q) 1 1 restPeriods (reidx.symm x) := by
        generalize hy : reidx.symm x = y
        have hx : x = reidx y := by
          rw [← hy]
          simp only [Equiv.apply_symm_apply]
        cases y using Sum.casesOn with
        | inl head =>
            fin_cases head
            · subst hx
              have htarget :
                  target.periods (firstReductionIndexEquivCanonicalTargetFin tailLen p pos) = q := by
                simpa [target, q, pos] using
                  firstReductionCanonicalTarget_periods_eq
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen pos
              simpa [originalFirstReductionPeriods, twoPeriods] using htarget
            · subst hx
              have htarget :
                  target.periods (firstReductionIndexEquivCanonicalTargetFin tailLen p neg) = q := by
                simpa [target, q, neg] using
                  firstReductionCanonicalTarget_periods_eq
                    m₁' m₂' tail hp hm₁' hm₂' htail hTailLen neg
              simpa [originalFirstReductionPeriods, twoPeriods] using htarget
        | inr r =>
            subst hx
            have htarget :
                target.periods
                    (firstReductionIndexEquivCanonicalTargetFin tailLen p (reidx (.inr r))) =
                  restPeriods r := by
              simpa [target, restPeriods] using
                firstReductionCanonicalTarget_periods_eq
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen (reidx (.inr r))
            simpa [originalFirstReductionPeriods] using htarget
      _ = source.periods
          ((reidx.symm.trans (originalFirstReductionOrderedIndexEquiv restLen)) x) :=
        hsourcePeriod.symm
  exact sourceSubgroup_exists_of_mulEquiv (Classical.choice hTargetEquiv) hSourceSubgroup

theorem firstReductionSourceSubgroup_leftPeriodOne_exists
    {σ : FuchsianSignature}
    (D : FirstReductionPeriodData σ)
    (hm₁' : D.m₁' = 1) :
    ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 3 := by
  classical
  by_cases hSourceBoundTwo :
      ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 2
  · exact
      hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
        (G := FuchsianPresentedGroup D.sourceSignature) (m := 2) (n := 3)
        (by norm_num) hSourceBoundTwo
  · have hSourceNotLCM : ¬ LCMCondition D.sourceSignature.toFenchelSignature := by
      intro hLCM
      exact hSourceBoundTwo
        (sourceSubgroup_exists_of_lcmCondition
          D.sourceSignature (m := 2) (by norm_num) hLCM)
    have hPeriodOneQuotientData :
        ∃ φ : FuchsianPresentedGroup D.sourceSignature →* Multiplicative (ZMod D.p),
          φ.ker.FiniteIndex ∧
            φ (ellipticElement D.sourceSignature
                ((originalFirstReductionOrderedIndexEquiv D.tailLen)
                  (.inl (0 : Fin 2)))) =
              Multiplicative.ofAdd (1 : ZMod D.p) ∧
            φ (ellipticElement D.sourceSignature
                ((originalFirstReductionOrderedIndexEquiv D.tailLen)
                  (.inl (1 : Fin 2)))) =
              Multiplicative.ofAdd (-1 : ZMod D.p) ∧
            (∀ j : Fin D.tailLen,
              φ (ellipticElement D.sourceSignature
                  ((originalFirstReductionOrderedIndexEquiv D.tailLen)
                    (.inr j))) = 1) := by
      let φ₀ :=
        originalFirstReductionPeriodOneQuotientHom
          D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
      let φ : FuchsianPresentedGroup D.sourceSignature →* Multiplicative (ZMod D.p) := by
        simpa [FirstReductionPeriodData.sourceSignature] using φ₀
      refine ⟨φ, ?_, ?_, ?_, ?_⟩
      letI : NeZero D.p :=
        ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.hp)⟩
      letI : Fintype (ZMod D.p) := ZMod.fintype D.p
      letI : Fintype (Multiplicative (ZMod D.p)) := inferInstance
      haveI : Finite (Multiplicative (ZMod D.p)) :=
        Finite.of_fintype (Multiplicative (ZMod D.p))
      · exact Subgroup.finiteIndex_ker φ
      · simpa [φ, FirstReductionPeriodData.sourceSignature] using
          originalFirstReductionPeriodOneQuotientHom_head_zero
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
      · simpa [φ, FirstReductionPeriodData.sourceSignature] using
          originalFirstReductionPeriodOneQuotientHom_head_one
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
      · intro j
        simpa [φ, FirstReductionPeriodData.sourceSignature] using
          originalFirstReductionPeriodOneQuotientHom_tail
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen j
    have hSecondHeadShape : D.m₂' = 1 ∨ 2 ≤ D.m₂' := by
      by_cases hm₂one : D.m₂' = 1
      · exact Or.inl hm₂one
      · have hpos : 0 < D.m₂' := D.hm₂'
        exact Or.inr (by omega)
    rcases hSecondHeadShape with hm₂one | hm₂ge
    · by_cases hHighDouble : 3 ≤ D.p * D.tailLen
      · have hSourceLCMObstruction :=
          exists_lcm_obstruction_of_not_lcmCondition
            D.sourceSignature.toFenchelSignature hSourceNotLCM
        have hDroppedDoubleTargetSubgroup :
            ∃ L : Subgroup
                (FuchsianPresentedGroup
                  (doublePeriodOneTailReplicatedSignature
                    D.tail D.htail hHighDouble)),
              L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
                SubgroupQuotientHasDerivedLengthAtMost L 1 :=
          sourceSubgroup_exists_of_lcmCondition
            (doublePeriodOneTailReplicatedSignature D.tail D.htail hHighDouble)
            (m := 1) (by norm_num)
            (doublePeriodOneTailReplicatedSignature_lcmCondition
              D.tail D.htail hHighDouble D.hp)
        -- FRONTIER(period-one-left-high-double-residual): both divided heads
        -- are period one, the double-period-one tail has high cardinality,
        -- the exact `≤ 2` source-subgroup route has failed, and the source-LCM
        -- smooth quotient route is impossible by `hSourceNotLCM`.  The repeated
        -- tail target produced by dropping the period-one heads is now closed by
        -- the LCM smooth quotient route, while the source itself carries the
        -- displayed LCM obstruction `hSourceLCMObstruction`; what remains is the cyclic kernel
        -- transport from this repeated-tail target back to `D.sourceSignature`.
        -- The remaining task is the public `≤ 3` source-subgroup statement, not
        -- a cleaned presentation theorem.
        let source :=
          originalFirstReductionSignature
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
        let target :=
          doublePeriodOneTailReplicatedSignature D.tail D.htail hHighDouble
        let eIdx := originalFirstReductionOrderedIndexEquiv D.tailLen
        have hperiods :
            ∀ x : OriginalFirstReductionIndex D.tailLen,
              source.periods (eIdx x) =
                originalFirstReductionPeriods (p := D.p) D.m₁' D.m₂' D.tail x := by
          intro x
          simpa [source, eIdx] using
            originalFirstReduction_canonical_periods_eq
              D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen x
        let φ :=
          originalFirstReductionPeriodOneQuotientHom
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
        let eKernel :
            φ.ker ≃* FuchsianPresentedGroup target := by
          simpa [φ, source, target, eIdx, originalFirstReductionPeriodOneQuotientHom] using
            doublePeriodOneKernelEquivOfForwardMapData
              D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
              hHighDouble eIdx hperiods rfl hm₁' hm₂one
              (doublePeriodOneForwardMapData
                D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
                hHighDouble eIdx hperiods rfl hm₁' hm₂one)
        letI : NeZero D.p :=
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.hp)⟩
        letI : Fintype (ZMod D.p) := ZMod.fintype D.p
        letI : Fintype (Multiplicative (ZMod D.p)) := inferInstance
        haveI : Finite (Multiplicative (ZMod D.p)) :=
          Finite.of_fintype (Multiplicative (ZMod D.p))
        have hSourceBoundTwo' :
            ∃ L : Subgroup (FuchsianPresentedGroup source),
              L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
                SubgroupQuotientHasDerivedLengthAtMost L 2 := by
          simpa [target, φ] using
            sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
              φ eKernel hDroppedDoubleTargetSubgroup
        have hSourceBoundThree' :
            ∃ L : Subgroup (FuchsianPresentedGroup source),
              L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
                SubgroupQuotientHasDerivedLengthAtMost L 3 :=
          hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
            (G := FuchsianPresentedGroup source) (m := 2) (n := 3)
            (by norm_num) hSourceBoundTwo'
        simpa [source, FirstReductionPeriodData.sourceSignature] using hSourceBoundThree'
      · have hMin : D.p = 2 ∧ D.tailLen = 1 :=
          firstReductionTransportPeriodsFin_tail_low_card_eq_two
            D.hp D.hTailLen hHighDouble
        have hLowSubgroupTwo :
            ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
              L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
                SubgroupQuotientHasDerivedLengthAtMost L 2 :=
          D.sourceSubgroup_exists_of_two_two_tail_two hm₁' hm₂one hMin.1 hMin.2
        exact
          hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
            (G := FuchsianPresentedGroup D.sourceSignature) (m := 2) (n := 3)
            (by norm_num) hLowSubgroupTwo
    · have hSourceLCMObstruction :=
        exists_lcm_obstruction_of_not_lcmCondition
          D.sourceSignature.toFenchelSignature hSourceNotLCM
      let droppedHeadTarget :=
        oneHeadPeriodOneTargetSignature D.m₂' D.tail D.hp hm₂ge D.htail D.hTailLen
      have hDroppedHeadTargetSubgroup :
          ∃ L : Subgroup (FuchsianPresentedGroup droppedHeadTarget),
            L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
              SubgroupQuotientHasDerivedLengthAtMost L 2 := by
        simpa [droppedHeadTarget] using
          oneHeadPeriodOneTarget_sourceSubgroup_exists_by_tailPair
            D.m₂' D.tail D.hp hm₂ge D.htail D.hTailLen
      let source :=
        originalFirstReductionSignature
          D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
      let target :=
        oneHeadPeriodOneTargetSignature D.m₂' D.tail D.hp hm₂ge D.htail D.hTailLen
      let eIdx := originalFirstReductionOrderedIndexEquiv D.tailLen
      have hperiods :
          ∀ x : OriginalFirstReductionIndex D.tailLen,
            source.periods (eIdx x) =
              originalFirstReductionPeriods (p := D.p) D.m₁' D.m₂' D.tail x := by
        intro x
        simpa [source, eIdx] using
          originalFirstReduction_canonical_periods_eq
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen x
      let φ :=
        originalFirstReductionPeriodOneQuotientHom
          D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail D.hTailLen
      let eKernel :
          φ.ker ≃* FuchsianPresentedGroup target := by
        simpa [φ, source, target, eIdx, originalFirstReductionPeriodOneQuotientHom] using
          oneHeadPeriodOneKernelEquivOfForwardMapData
            D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' hm₂ge D.htail D.hTailLen
            eIdx hperiods rfl hm₁'
            (oneHeadPeriodOneForwardMapData
              D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' hm₂ge D.htail D.hTailLen
              eIdx hperiods rfl hm₁')
      letI : NeZero D.p :=
        ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.hp)⟩
      letI : Fintype (ZMod D.p) := ZMod.fintype D.p
      letI : Fintype (Multiplicative (ZMod D.p)) := inferInstance
      haveI : Finite (Multiplicative (ZMod D.p)) :=
        Finite.of_fintype (Multiplicative (ZMod D.p))
      have hSourceBoundThree' :
          ∃ L : Subgroup (FuchsianPresentedGroup source),
            L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
              SubgroupQuotientHasDerivedLengthAtMost L 3 := by
        simpa [target, φ, droppedHeadTarget] using
          sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
            φ eKernel hDroppedHeadTargetSubgroup
      simpa [source, FirstReductionPeriodData.sourceSignature] using hSourceBoundThree'
theorem firstReductionSourceSubgroup_rightPeriodOne_exists
    {σ : FuchsianSignature}
    (D : FirstReductionPeriodData σ)
    (hm₂' : D.m₂' = 1) :
    ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 3 := by
  classical
  let headSwap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let sourceSwap : OriginalFirstReductionIndex D.tailLen ≃
      OriginalFirstReductionIndex D.tailLen :=
    Equiv.sumCongr headSwap (Equiv.refl (Fin D.tailLen))
  let Dswap : FirstReductionPeriodData D.sourceSignature :=
    { p := D.p
      hpPrime := D.hpPrime
      hp := D.hp
      tailLen := D.tailLen
      m₁' := D.m₂'
      m₂' := D.m₁'
      tail := D.tail
      hm₁' := D.hm₂'
      hm₂' := D.hm₁'
      htail := D.htail
      hTailLen := D.hTailLen
      reindex := sourceSwap.trans (originalFirstReductionOrderedIndexEquiv D.tailLen)
      periods_eq := by
        intro x
        cases x using Sum.casesOn with
        | inl i =>
            fin_cases i
            · simp [originalFirstReductionPeriods, twoPeriods,
                FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature,
                Equiv.trans_apply, sourceSwap, headSwap]
            · simp [originalFirstReductionPeriods, twoPeriods,
                FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature,
                Equiv.trans_apply, sourceSwap, headSwap]
        | inr j =>
            simp only [originalFirstReductionPeriods, FirstReductionPeriodData.sourceSignature,
  originalFirstReductionSignature, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq,
  originalFirstReductionOrderedIndexEquiv_right, originalFirstReductionSignaturePeriod_tail, sourceSwap]}
  let e :
      FuchsianPresentedGroup D.sourceSignature ≃*
        FuchsianPresentedGroup Dswap.sourceSignature :=
    Classical.choice
      (firstReductionSourceMulEquiv_exists Dswap (by
        simp only [FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature]))
  exact
    sourceSubgroup_exists_of_mulEquiv e
      (firstReductionSourceSubgroup_leftPeriodOne_exists Dswap hm₂')

private theorem SecondStageCleanupPeriodData.sourceSubgroup_exists_of_tailPair
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime)
    (hm₁' : 2 ≤ D.m₁') (hm₂' : 2 ≤ D.m₂') :
    ∃ L : Subgroup (FuchsianPresentedGroup E.sourceSignature),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 3 := by
  let sourceTail :=
    firstReductionTailIncludingThird_ge_two_of_pos
      secondPrime.hqPrime.two_le E.m₃' E.tail E.hm₃' E.htail
  let canonicalSource :=
    firstReductionCanonicalSourceSignature D.m₁' D.m₂'
      (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
      D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
  have hCanonicalSubgroup :
      ∃ L : Subgroup (FuchsianPresentedGroup canonicalSource),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 3 := by
    by_cases hCanonicalBoundTwo :
        ∃ L : Subgroup (FuchsianPresentedGroup canonicalSource),
          L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
            SubgroupQuotientHasDerivedLengthAtMost L 2
    · exact
        hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
          (G := FuchsianPresentedGroup canonicalSource) (m := 2) (n := 3)
          (by norm_num) hCanonicalBoundTwo
    · by_cases hCanonicalLCM : LCMCondition canonicalSource.toFenchelSignature
      · exact
          sourceSubgroup_exists_of_lcmCondition
            canonicalSource (m := 3) (by norm_num) hCanonicalLCM
      · let target :=
          firstReductionCanonicalTargetSignature D.m₁' D.m₂'
            (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
            D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
        have hTargetSubgroup :
            ∃ L : Subgroup (FuchsianPresentedGroup target),
              L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
                SubgroupQuotientHasDerivedLengthAtMost L 2 :=
          firstReductionCanonicalTarget_sourceSubgroup_exists_by_tailPair
            D.m₁' D.m₂'
            (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
            D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
        let φ :=
          firstReductionCanonicalSourceQuotientHom D.m₁' D.m₂'
            (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
            D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
        let eKernel :
            φ.ker ≃* FuchsianPresentedGroup target := by
          simpa [φ, target] using
            firstReductionCanonicalSourceKernelEquiv_targetSignature
              D.m₁' D.m₂'
              (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
              D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
        letI : NeZero D.p :=
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.hp)⟩
        letI : Fintype (ZMod D.p) := ZMod.fintype D.p
        letI : Fintype (Multiplicative (ZMod D.p)) := inferInstance
        haveI : Finite (Multiplicative (ZMod D.p)) :=
          Finite.of_fintype (Multiplicative (ZMod D.p))
        simpa [canonicalSource, φ, target] using
          sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
            φ eKernel hTargetSubgroup
  let eSourceCanonical :
      FuchsianPresentedGroup E.sourceSignature ≃*
        FuchsianPresentedGroup canonicalSource := by
    simpa [canonicalSource, sourceTail, SecondStageCleanupPeriodData.sourceSignature,
      firstReductionSourceSignature] using
      (Classical.choice
        (firstReductionSourceSignature_mulEquiv_canonicalSourceSignature_exists
          D.m₁' D.m₂'
          (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
          D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)))
  exact sourceSubgroup_exists_of_mulEquiv eSourceCanonical hCanonicalSubgroup

theorem firstReductionSourceSubgroup_tailPrimeQuotientOne_exists
    {σ : FuchsianSignature}
    (D : FirstReductionPeriodData σ)
    (_hquot : D.tail D.tailPrimeDivisorData.k / D.tailPrimeDivisorData.q = 1) :
    ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 3 := by
  classical
  let secondPrime : FirstKernelTailPrimeDivisorData D := D.tailPrimeDivisorData
  by_cases hSourceBoundTwo :
      ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 2
  · exact
      hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
        (G := FuchsianPresentedGroup D.sourceSignature) (m := 2) (n := 3)
        (by norm_num) hSourceBoundTwo
  · have hSourceNotLCM : ¬ LCMCondition D.sourceSignature.toFenchelSignature := by
      intro hLCM
      exact hSourceBoundTwo
        (sourceSubgroup_exists_of_lcmCondition
          D.sourceSignature (m := 2) (by norm_num) hLCM)
    by_cases hm₁' : D.m₁' = 1
    · exact firstReductionSourceSubgroup_leftPeriodOne_exists D hm₁'
    · by_cases hm₂' : D.m₂' = 1
      · exact firstReductionSourceSubgroup_rightPeriodOne_exists D hm₂'
      · have hm₁'ge : 2 ≤ D.m₁' := by
          have hpos : 0 < D.m₁' := D.hm₁'
          omega
        have hm₂'ge : 2 ≤ D.m₂' := by
          have hpos : 0 < D.m₂' := D.hm₂'
          omega
        let E : SecondStageCleanupPeriodData D secondPrime :=
          secondStageCleanupPeriodDataOfTailPrime D secondPrime
        have hESourceSubgroup :
            ∃ L : Subgroup (FuchsianPresentedGroup E.sourceSignature),
              L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
                SubgroupQuotientHasDerivedLengthAtMost L 3 :=
          SecondStageCleanupPeriodData.sourceSubgroup_exists_of_tailPair E hm₁'ge hm₂'ge
        let eOuter :
            FuchsianPresentedGroup D.sourceSignature ≃*
              FuchsianPresentedGroup E.sourceSignature :=
          Classical.choice (secondStageCleanupSourceMulEquiv_exists E)
        exact sourceSubgroup_exists_of_mulEquiv eOuter hESourceSubgroup


/-- Source-subgroup form of the strict two-stage branch.  This is the form
    actually needed before the final paper-facing normal core is taken: the
    two cyclic extensions only require finite-index torsion-free source
    subgroups, not local normality. -/
theorem SecondStageCleanupPeriodData.sourceSubgroup_exists_of_canonicalReductions
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime)
    (hm₁' : 2 ≤ D.m₁') (hm₂' : 2 ≤ D.m₂') (hm₃' : 2 ≤ E.m₃') :
    ∃ L : Subgroup (FuchsianPresentedGroup E.sourceSignature),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 3 := by
  let sourceTail :=
    firstReductionTailIncludingThird_ge_two_of_pos
      secondPrime.hqPrime.two_le E.m₃' E.tail E.hm₃' E.htail
  let canonicalSource :=
    firstReductionCanonicalSourceSignature D.m₁' D.m₂'
      (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
      D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
  have hCanonicalSubgroup :
      ∃ L : Subgroup (FuchsianPresentedGroup canonicalSource),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 3 := by
    let target :=
      secondReductionTransportSignature (p := D.p) secondPrime.hqPrime.two_le
        D.m₁' D.m₂' E.m₃' E.tail hm₁' hm₂' hm₃' E.htail
    rcases
      secondReductionCanonicalTransportKernelEquiv_of_secondBranch
        D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
        hm₁' hm₂' hm₃' E.htail with
      ⟨eΨ⟩
    have hMiddleSubgroup :
        ∃ L : Subgroup
          (FuchsianPresentedGroup
            (secondReductionCanonicalSourceSignature
              D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
              hm₁' hm₂' hm₃' E.htail)),
          L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
            SubgroupQuotientHasDerivedLengthAtMost L 2 := by
      let ψ :=
        secondReductionCanonicalSourceQuotientHom
          D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
          hm₁' hm₂' hm₃' E.htail
      let QD := finiteSolvableSmoothQuotientData_one_of_lcmCondition
        target
        (secondReductionTransportSignature_lcmCondition
          (p := D.p) secondPrime.hqPrime.two_le
          D.m₁' D.m₂' E.m₃' E.tail hm₁' hm₂' hm₃' E.htail)
      letI : NeZero secondPrime.q :=
        ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) secondPrime.hqPrime.two_le)⟩
      letI : Fintype (ZMod secondPrime.q) := ZMod.fintype secondPrime.q
      letI : Fintype (Multiplicative (ZMod secondPrime.q)) := inferInstance
      haveI : Finite (Multiplicative (ZMod secondPrime.q)) :=
        Finite.of_fintype (Multiplicative (ZMod secondPrime.q))
      haveI : ψ.ker.FiniteIndex := Subgroup.finiteIndex_ker ψ
      exact
        sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
          ψ eΨ QD.sourceSubgroup_exists_classical
    let φ :=
      firstReductionCanonicalSourceQuotientHom D.m₁' D.m₂'
        (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
        D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)
    let eSource :
        FuchsianPresentedGroup
            (secondReductionSourceSignature (p := D.p) D.m₁' D.m₂' E.m₃' E.tail secondPrime.hqPrime.two_le hm₁' hm₂'
              (lt_of_lt_of_le (by decide : 0 < 2) hm₃') E.htail)
          ≃*
          FuchsianPresentedGroup
            (secondReductionCanonicalSourceSignature
              D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
              hm₁' hm₂' hm₃' E.htail) :=
      Classical.choice
        (secondReductionSourceSignature_mulEquiv_canonicalSourceSignature_exists
          D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
          hm₁' hm₂' hm₃' E.htail)
    let eΦ :
        φ.ker ≃*
          FuchsianPresentedGroup
            (secondReductionCanonicalSourceSignature
              D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
              hm₁' hm₂' hm₃' E.htail) :=
      (firstReductionCanonicalKernelEquiv_secondReductionSourceSignature
        D.m₁' D.m₂' E.m₃' E.tail D.hp secondPrime.hqPrime.two_le
        hm₁' hm₂' (lt_of_lt_of_le (by decide : 0 < 2) hm₃') E.htail).trans
        eSource
    letI : NeZero D.p :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.hp)⟩
    letI : Fintype (ZMod D.p) := ZMod.fintype D.p
    letI : Fintype (Multiplicative (ZMod D.p)) := inferInstance
    haveI : Finite (Multiplicative (ZMod D.p)) :=
      Finite.of_fintype (Multiplicative (ZMod D.p))
    simpa [canonicalSource, φ] using
      sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
        φ eΦ hMiddleSubgroup
  let eSource :
      FuchsianPresentedGroup E.sourceSignature ≃*
        FuchsianPresentedGroup canonicalSource :=
    by
      simpa [canonicalSource, sourceTail, SecondStageCleanupPeriodData.sourceSignature,
        firstReductionSourceSignature] using
        (Classical.choice
          (firstReductionSourceSignature_mulEquiv_canonicalSourceSignature_exists
            D.m₁' D.m₂'
            (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
            D.hp hm₁' hm₂' sourceTail (Nat.succ_pos _)))
  exact sourceSubgroup_exists_of_mulEquiv eSource hCanonicalSubgroup

end FenchelNielsen
