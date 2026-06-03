import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.Perfectness
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.SecondReductionData

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/ZeroGenus/CleanupData.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact zero-genus three-step proof data

Organizes first and second reduction data, perfectness numerics, reindexing, cleanup data, and the final zero-genus three-step finite-index theorem.
-/

namespace FenchelNielsen
private theorem secondReductionTransportIndex_card_ge_three
    {tailLen p q : ℕ} (hq : 2 ≤ q) :
    3 ≤ Fintype.card (SecondReductionTransportIndex tailLen p q) := by
  have hcard :
      Fintype.card (SecondReductionTransportIndex tailLen p q) =
        2 * q + 2 + q * (p - 2) + tailLen * p * q := by
    simp only [SecondReductionTransportIndex, secondReductionSourceCycleCount, Fintype.card_sigma,
  Fintype.card_fin, Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm, mul_one,
  Fintype.card_prod, Nat.mul_left_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  rw [hcard]
  omega
private theorem secondReductionTransportPeriods_ge_two
    {tailLen p q : ℕ} (hq : 2 ≤ q)
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃') (htail : ∀ j, 2 ≤ tail j)
    (x : SecondReductionTransportIndex tailLen p q) :
    2 ≤ secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail x := by
  rcases x with ⟨i, k⟩
  cases i with
  | inl i =>
      fin_cases i
      · simpa [secondReductionTransportPeriods, secondReductionSourceTransportPeriods, twoPeriods]
          using hm₁'
      · simpa [secondReductionTransportPeriods, secondReductionSourceTransportPeriods, twoPeriods]
          using hm₂'
  | inr s =>
      cases s with
      | inl j =>
          fin_cases j
          · simpa [secondReductionTransportPeriods, secondReductionSourceTransportPeriods]
              using hm₃'
          · simpa [secondReductionTransportPeriods, secondReductionSourceTransportPeriods]
              using hm₃'
      | inr s =>
          cases s with
          | inl j =>
              exact le_trans hq
                (Nat.le_mul_of_pos_right q (lt_of_lt_of_le (by decide : 0 < 2) hm₃'))
          | inr jk =>
              simpa [secondReductionTransportPeriods, secondReductionSourceTransportPeriods]
                using htail jk.1
noncomputable def secondReductionTransportSignature
    {tailLen p q : ℕ} (hq : 2 ≤ q)
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃') (htail : ∀ j, 2 ≤ tail j) :
    FuchsianSignature :=
  familyFuchsianSignature
    (secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail)
    (secondReductionTransportPeriods_ge_two hq m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)
    (secondReductionTransportIndex_card_ge_three hq)
theorem secondReductionTransportSignature_lcmCondition
    {tailLen p q : ℕ} (hq : 2 ≤ q)
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃') (htail : ∀ j, 2 ≤ tail j) :
    LCMCondition
      (secondReductionTransportSignature (p := p) hq m₁' m₂' m₃' tail
        hm₁' hm₂' hm₃' htail).toFenchelSignature :=
  by
    simpa [secondReductionTransportSignature] using
      familyFuchsianSignature_lcmCondition_of_lcmConditionFamily
        (secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail)
        (secondReductionTransportPeriods_ge_two hq m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)
        (secondReductionTransportIndex_card_ge_three hq)
        (lcmConditionFamily_of_hasEqualPartnerFamily
          (secondReductionTransport_hasEqualPartnerFamily hq m₁' m₂' m₃' tail))

private theorem secondReductionSourcePeriods_pos
    {tailLen p q : ℕ} (hq : 2 ≤ q)
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₁' : 0 < m₁') (hm₂' : 0 < m₂') (hm₃' : 0 < m₃')
    (htail : ∀ j, 0 < tail j) :
    ∀ i : SecondReductionSourceIndex tailLen p, 0 < secondReductionSourcePeriods
      (p := p) (q := q) m₁' m₂' m₃' tail i := by
  intro i
  cases i with
  | inl h =>
      fin_cases h <;> simpa [secondReductionSourcePeriods, twoPeriods]
  | inr rest =>
      cases rest with
      | inl _ =>
          exact Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hq) hm₃'
      | inr rest =>
          cases rest with
          | inl _ =>
              exact Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hq) hm₃'
          | inr jk =>
              exact htail jk.1

theorem secondReductionSource_nonOne_periods_ge_two
    {tailLen p q : ℕ} (hq : 2 ≤ q)
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₁' : 0 < m₁') (hm₂' : 0 < m₂') (hm₃' : 0 < m₃')
    (htail : ∀ j, 0 < tail j) :
    ∀ i : NonOneSubfamilyIndex
        (secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail),
      2 ≤ nonOneSubfamilyPeriods
        (secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail) i :=
  nonOneSubfamilyPeriods_ge_two
    (secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail)
    (secondReductionSourcePeriods_pos hq m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail)

def firstReductionTailIncludingThird
    {tailLen q : ℕ} (m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    Fin (tailLen + 1) → ℕ :=
  Fin.cases (q * m₃') tail
theorem firstReductionTailIncludingThird_ge_two_of_pos
    {tailLen q : ℕ} (hq : 2 ≤ q) (m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hm₃' : 0 < m₃') (htail : ∀ j, 2 ≤ tail j) :
    ∀ j : Fin (tailLen + 1), 2 ≤ firstReductionTailIncludingThird (q := q) m₃' tail j := by
  intro j
  refine Fin.cases ?_ (fun k => htail k) j
  exact le_trans hq (Nat.le_mul_of_pos_right q hm₃')
noncomputable def finHeadInsertionEquiv {n : ℕ} (k : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.ofBijective (Fin.cases k k.succAbove) <| by
    constructor
    · intro a b h
      cases a using Fin.cases with
      | zero =>
          cases b using Fin.cases with
          | zero => rfl
          | succ j =>
              exfalso
              exact Fin.ne_succAbove k j h
      | succ i =>
          cases b using Fin.cases with
          | zero =>
              exfalso
              exact Fin.succAbove_ne k i h
          | succ j =>
              exact congrArg Fin.succ (Fin.succAbove_right_inj.mp h)
    · intro y
      rcases Fin.eq_self_or_eq_succAbove k y with rfl | ⟨j, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨j.succ, rfl⟩
noncomputable def twoPointSubtypeEquiv {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) : Fin 2 ≃ {k : ι // k = i ∨ k = j} where
  toFun k :=
    match k with
    | ⟨0, _⟩ => ⟨i, Or.inl rfl⟩
    | ⟨1, _⟩ => ⟨j, Or.inr rfl⟩
    | ⟨n + 2, h⟩ => by omega
  invFun k := if _h : (k : ι) = i then 0 else 1
  left_inv := by
    intro k
    fin_cases k
    · simp only [↓reduceDIte, Fin.isValue, Fin.zero_eta]
    · simp only [hij.symm, ↓reduceDIte, Fin.isValue, Fin.mk_one]
  right_inv := by
    intro k
    apply Subtype.ext
    rcases k with ⟨k, hk | hk⟩
    · subst hk
      simp only [↓reduceDIte, Fin.isValue]
    · subst hk
      simp only [hij.symm, ↓reduceDIte, Fin.isValue]
noncomputable def notTwoSubtypeEquiv {ι : Type*}
    (i j : ι) : {k : ι // k ≠ i ∧ k ≠ j} ≃ {k : ι // ¬ (k = i ∨ k = j)} :=
  Equiv.subtypeEquivRight (fun _ => by simp only [ne_eq, not_or])
noncomputable def originalFirstReductionReindex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    OriginalFirstReductionIndex (Fintype.card {k : ι // k ≠ i ∧ k ≠ j}) ≃ ι :=
  (Equiv.sumCongr
      (twoPointSubtypeEquiv i j hij)
      ((Fintype.equivFin {k : ι // k ≠ i ∧ k ≠ j}).symm.trans
        (notTwoSubtypeEquiv i j))).trans
    (Equiv.sumCompl (fun k : ι => k = i ∨ k = j))
@[simp 900] theorem originalFirstReductionReindex_left_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    originalFirstReductionReindex i j hij (.inl 0) = i := by
  simp only [ne_eq, originalFirstReductionReindex, twoPointSubtypeEquiv, Fin.isValue, dite_eq_ite,
  Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_fn_mk, Equiv.coe_trans, Sum.map_inl, Equiv.sumCompl_apply_inl]
@[simp 900] theorem originalFirstReductionReindex_left_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    originalFirstReductionReindex i j hij (.inl 1) = j := by
  simp only [ne_eq, originalFirstReductionReindex, twoPointSubtypeEquiv, Fin.isValue, dite_eq_ite,
  Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_fn_mk, Equiv.coe_trans, Sum.map_inl, Equiv.sumCompl_apply_inl]
@[simp 900] theorem originalFirstReductionReindex_right
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j)
    (k : Fin (Fintype.card {k : ι // k ≠ i ∧ k ≠ j})) :
    originalFirstReductionReindex i j hij (.inr k) =
      ((Fintype.equivFin {k : ι // k ≠ i ∧ k ≠ j}).symm k :
        {k : ι // k ≠ i ∧ k ≠ j}).1 := by
  simp only [ne_eq, originalFirstReductionReindex, notTwoSubtypeEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_trans, Sum.map_inr, Function.comp_apply, Equiv.sumCompl_apply_inr, Equiv.subtypeEquivRight_apply_coe]
structure FirstReductionPeriodData (σ : FuchsianSignature) where
  p : ℕ
  hpPrime : p.Prime
  hp : 2 ≤ p
  tailLen : ℕ
  m₁' : ℕ
  m₂' : ℕ
  tail : Fin tailLen → ℕ
  hm₁' : 0 < m₁'
  hm₂' : 0 < m₂'
  htail : ∀ j, 2 ≤ tail j
  hTailLen : 0 < tailLen
  reindex : OriginalFirstReductionIndex tailLen ≃ Fin σ.numPeriods
  periods_eq :
    ∀ x, originalFirstReductionPeriods (p := p) m₁' m₂' tail x = σ.periods (reindex x)
noncomputable def firstReductionPeriodDataOfPrimePair
    (σ : FuchsianSignature) {p : ℕ} (hpPrime : p.Prime)
    {i j : Fin σ.numPeriods} (hij : i ≠ j)
    (hpi : p ∣ σ.periods i) (hpj : p ∣ σ.periods j) :
    FirstReductionPeriodData σ := by
  classical
  let tailSubtype := {k : Fin σ.numPeriods // k ≠ i ∧ k ≠ j}
  let tailLen := Fintype.card tailSubtype
  let tailEquiv : Fin tailLen ≃ tailSubtype := (Fintype.equivFin tailSubtype).symm
  let tail : Fin tailLen → ℕ := fun k => σ.periods ((tailEquiv k).1)
  have hpPos : 0 < p := hpPrime.pos
  have hpi_period_pos : 0 < σ.periods i :=
    lt_of_lt_of_le (by decide : 0 < 2) (σ.period_ge_two i)
  have hpj_period_pos : 0 < σ.periods j :=
    lt_of_lt_of_le (by decide : 0 < 2) (σ.period_ge_two j)
  have hm₁pos : 0 < σ.periods i / p :=
    Nat.div_pos (Nat.le_of_dvd hpi_period_pos hpi) hpPos
  have hm₂pos : 0 < σ.periods j / p :=
    Nat.div_pos (Nat.le_of_dvd hpj_period_pos hpj) hpPos
  have hmul₁ : p * (σ.periods i / p) = σ.periods i := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hpi
  have hmul₂ : p * (σ.periods j / p) = σ.periods j := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hpj
  have htailLen : 0 < tailLen := by
    have hcard0 := Fintype.card_congr (originalFirstReductionReindex i j hij)
    have hcard : 2 + tailLen = σ.numPeriods := by
      simpa [OriginalFirstReductionIndex, tailLen] using hcard0
    have hsig : 3 ≤ σ.numPeriods := σ.numPeriods_ge_three
    omega
  exact
    { p := p
      hpPrime := hpPrime
      hp := hpPrime.two_le
      tailLen := tailLen
      m₁' := σ.periods i / p
      m₂' := σ.periods j / p
      tail := tail
      hm₁' := hm₁pos
      hm₂' := hm₂pos
      htail := by
        intro k
        exact σ.period_ge_two ((tailEquiv k).1)
      hTailLen := htailLen
      reindex := originalFirstReductionReindex i j hij
      periods_eq := by
        intro x
        cases x using Sum.casesOn with
        | inl a =>
            fin_cases a
            · simpa [originalFirstReductionPeriods, twoPeriods,
                originalFirstReductionReindex_left_zero] using hmul₁
            · simpa [originalFirstReductionPeriods, twoPeriods,
                originalFirstReductionReindex_left_one] using hmul₂
        | inr k =>
            change σ.periods ((tailEquiv k).1) =
              σ.periods (originalFirstReductionReindex i j hij (.inr k))
            rw [originalFirstReductionReindex_right] }
noncomputable def FirstReductionPeriodData.sourceSignature
    {σ : FuchsianSignature} (D : FirstReductionPeriodData σ) : FuchsianSignature :=
  originalFirstReductionSignature D.m₁' D.m₂' D.tail D.hp D.hm₁' D.hm₂' D.htail
    D.hTailLen

end FenchelNielsen
