import FenchelNielsenZomorrodian.Discrete.Singerman.FreeGroupWords
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.FirstReductionData

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/FirstReduction/Signatures.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# First compact zero-genus reduction

The first explicit finite quotient reduction for compact zero-genus Fuchsian presentations, including quotient maps, basis transport, signatures, and relator verification.
-/

namespace FenchelNielsen
noncomputable abbrev firstReductionSourceSignature
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianSignature :=
  originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen

theorem list_prod_ofFn_mul_blocks {α : Type*} [Monoid α] {p n : ℕ}
    (f : Fin (p * n) → α) :
    (List.ofFn f).prod =
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin n =>
          f ⟨k.val * n + j.val, by
            calc
              k.val * n + j.val < (k.val + 1) * n := by
                calc
                  k.val * n + j.val < k.val * n + n :=
                    Nat.add_lt_add_left j.isLt _
                  _ = (k.val + 1) * n := by rw [Nat.add_mul, one_mul]
              _ ≤ p * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt k.isLt)⟩)).prod)).prod := by
  rw [List.ofFn_mul]
  rw [List.prod_flatten]
  rw [List.map_ofFn]
  congr
def firstReductionCanonicalSourcePeriod
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (i : Fin (2 + tailLen)) : ℕ :=
  if h0 : i.val = 0 then
    p * m₁'
  else if h1 : i.val = 1 then
    p * m₂'
  else
    tail ⟨i.val - 2, by omega⟩
@[local simp]
theorem firstReductionCanonicalSourcePeriod_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    firstReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        ⟨0, by omega⟩ = p * m₁' := by
  simp only [firstReductionCanonicalSourcePeriod, ↓reduceDIte]
@[local simp]
theorem firstReductionCanonicalSourcePeriod_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    firstReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        ⟨1, by omega⟩ = p * m₂' := by
  simp only [firstReductionCanonicalSourcePeriod, one_ne_zero, ↓reduceDIte]
@[local simp]
theorem firstReductionCanonicalSourcePeriod_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (j : Fin tailLen) :
    firstReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        ⟨2 + j.val, by omega⟩ = tail j := by
  unfold firstReductionCanonicalSourcePeriod
  have h0 : 2 + j.val ≠ 0 := by omega
  have h1 : 2 + j.val ≠ 1 := by omega
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceDIte, h1, add_tsub_cancel_left,
  Fin.eta]
def firstReductionCanonicalSourceSignature
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := 2 + tailLen
  periods := firstReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
  period_ge_two := by
    intro i
    unfold firstReductionCanonicalSourcePeriod
    by_cases h0 : i.val = 0
    · rw [dif_pos h0]
      exact le_trans hp (Nat.le_mul_of_pos_right p (lt_of_lt_of_le (by decide) hm₁'))
    · by_cases h1 : i.val = 1
      · rw [dif_neg h0, dif_pos h1]
        exact le_trans hp (Nat.le_mul_of_pos_right p (lt_of_lt_of_le (by decide) hm₂'))
      · rw [dif_neg h0, dif_neg h1]
        exact htail ⟨i.val - 2, by omega⟩
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by omega
def firstReductionCanonicalSourceZeroIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    Fin
      (firstReductionCanonicalSourceSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨0, by simp only [firstReductionCanonicalSourceSignature, add_pos_iff, Nat.ofNat_pos, true_or]⟩
def firstReductionCanonicalSourceOneIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    Fin
      (firstReductionCanonicalSourceSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨1, by simp only [firstReductionCanonicalSourceSignature]; omega⟩
def firstReductionCanonicalSourceTailIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) (j : Fin tailLen) :
    Fin
      (firstReductionCanonicalSourceSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨2 + j.val, by
    simp only [firstReductionCanonicalSourceSignature, add_lt_add_iff_left, Fin.is_lt]⟩
@[simp 900] theorem firstReductionCanonicalSourceSignature_period_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    (firstReductionCanonicalSourceSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) =
      p * m₁' := by
  simp only [firstReductionCanonicalSourceSignature, firstReductionCanonicalSourceZeroIndex, Fin.mk_zero',
  firstReductionCanonicalSourcePeriod, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceDIte]
@[simp 900] theorem firstReductionCanonicalSourceSignature_period_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    (firstReductionCanonicalSourceSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) =
      p * m₂' := by
  simp only [firstReductionCanonicalSourceSignature, firstReductionCanonicalSourceOneIndex,
  firstReductionCanonicalSourcePeriod, one_ne_zero, ↓reduceDIte]
@[simp 900] theorem firstReductionCanonicalSourceSignature_period_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) (j : Fin tailLen) :
    (firstReductionCanonicalSourceSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalSourceTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j) =
      tail j := by
  simp only [firstReductionCanonicalSourceSignature, firstReductionCanonicalSourceTailIndex,
  firstReductionCanonicalSourcePeriod_tail]
theorem firstReductionCanonicalSource_totalRelation_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let σ :=
      firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    totalRelation σ =
      xWord σ
          (firstReductionCanonicalSourceZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
        xWord σ
          (firstReductionCanonicalSourceOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
          (List.ofFn (fun j : Fin tailLen =>
            xWord σ
              (firstReductionCanonicalSourceTailIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j))).prod := by
  classical
  let σ :=
    firstReductionCanonicalSourceSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change totalRelation σ =
    xWord σ
        (firstReductionCanonicalSourceZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
      xWord σ
        (firstReductionCanonicalSourceOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
        (List.ofFn (fun j : Fin tailLen =>
          xWord σ
            (firstReductionCanonicalSourceTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen j))).prod
  rw [totalRelation]
  simpa [σ, firstReductionCanonicalSourceSignature, firstReductionCanonicalSourceZeroIndex,
    firstReductionCanonicalSourceOneIndex, firstReductionCanonicalSourceTailIndex,
    List.ofFn_eq_map, List.prod_cons, mul_assoc] using
      congrArg List.prod
        (list_ofFn_two_add (fun i : Fin (2 + tailLen) => xWord σ i))
def firstReductionCanonicalTargetPeriod
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (hTailLen : 0 < tailLen)
    (i : Fin (2 + p * tailLen)) : ℕ :=
  if i.val = 0 then
    m₁'
  else if i.val = 1 then
    m₂'
  else
    tail ⟨(i.val - 2) % tailLen, Nat.mod_lt _ hTailLen⟩
@[local simp]
theorem firstReductionCanonicalTargetPeriod_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (hTailLen : 0 < tailLen) :
    firstReductionCanonicalTargetPeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        hTailLen ⟨0, by omega⟩ = m₁' := by
  simp only [firstReductionCanonicalTargetPeriod, ↓reduceIte]
@[local simp]
theorem firstReductionCanonicalTargetPeriod_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (hTailLen : 0 < tailLen) :
    firstReductionCanonicalTargetPeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        hTailLen ⟨1, by omega⟩ = m₂' := by
  simp only [firstReductionCanonicalTargetPeriod, one_ne_zero, ↓reduceIte]
@[local simp]
theorem firstReductionCanonicalTargetPeriod_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
    firstReductionCanonicalTargetPeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        hTailLen
        ⟨2 + k.val * tailLen + j.val, by
          have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
            calc
              k.val * tailLen + j.val < k.val * tailLen + tailLen :=
                Nat.add_lt_add_left j.isLt _
              _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
          have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
            Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
          have hmain : k.val * tailLen + j.val < p * tailLen :=
            lt_of_lt_of_le hblock hle
          omega⟩ = tail j := by
  unfold firstReductionCanonicalTargetPeriod
  have h0 : 2 + k.val * tailLen + j.val ≠ 0 := by omega
  have h1 : 2 + k.val * tailLen + j.val ≠ 1 := by omega
  rw [if_neg h0, if_neg h1]
  have hsub :
      2 + k.val * tailLen + j.val - 2 = k.val * tailLen + j.val := by
    omega
  have hmod : (2 + k.val * tailLen + j.val - 2) % tailLen = j.val := by
    rw [hsub, Nat.mul_comm k.val tailLen, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  exact congrArg tail (Fin.ext hmod)
def firstReductionCanonicalTargetSignature
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := 2 + p * tailLen
  periods :=
    firstReductionCanonicalTargetPeriod (tailLen := tailLen) (p := p) m₁' m₂' tail hTailLen
  period_ge_two := by
    intro i
    unfold firstReductionCanonicalTargetPeriod
    by_cases h0 : i.val = 0
    · rw [if_pos h0]
      exact hm₁'
    · by_cases h1 : i.val = 1
      · rw [if_neg h0, if_pos h1]
        exact hm₂'
      · rw [if_neg h0, if_neg h1]
        exact htail ⟨(i.val - 2) % tailLen, Nat.mod_lt _ hTailLen⟩
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by
    have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
    nlinarith [Nat.mul_pos hp_pos hTailLen]
def firstReductionCanonicalTargetZeroIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    Fin
      (firstReductionCanonicalTargetSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨0, by simp only [firstReductionCanonicalTargetSignature, add_pos_iff, Nat.ofNat_pos, CanonicallyOrderedAdd.mul_pos,
  true_or]⟩
def firstReductionCanonicalTargetOneIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    Fin
      (firstReductionCanonicalTargetSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨1, by
    have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
    have hprod : 0 < p * tailLen := Nat.mul_pos hp_pos hTailLen
    simp only [firstReductionCanonicalTargetSignature, gt_iff_lt]
    omega⟩
def firstReductionCanonicalTargetFlatTailIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (r : Fin (p * tailLen)) :
    Fin
      (firstReductionCanonicalTargetSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨2 + r.val, by
    simp only [firstReductionCanonicalTargetSignature, add_lt_add_iff_left, Fin.is_lt]⟩
@[local simp]
theorem firstReductionCanonicalTargetSignature_period_flatTail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (r : Fin (p * tailLen)) :
    (firstReductionCanonicalTargetSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalTargetFlatTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r) =
      tail ⟨r.val % tailLen, Nat.mod_lt _ hTailLen⟩ := by
  change
    firstReductionCanonicalTargetPeriod (tailLen := tailLen) (p := p)
      m₁' m₂' tail hTailLen ⟨2 + r.val, by simp only [add_lt_add_iff_left, Fin.is_lt]⟩ =
        tail ⟨r.val % tailLen, Nat.mod_lt _ hTailLen⟩
  unfold firstReductionCanonicalTargetPeriod
  have h0 : 2 + r.val ≠ 0 := by omega
  have h1 : 2 + r.val ≠ 1 := by omega
  rw [if_neg h0, if_neg h1]
  apply congrArg tail
  ext
  simp only [add_tsub_cancel_left]
def firstReductionCanonicalTargetTailIndex
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
    Fin
      (firstReductionCanonicalTargetSignature
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods :=
  ⟨2 + k.val * tailLen + j.val, by
    have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
      calc
        k.val * tailLen + j.val < k.val * tailLen + tailLen :=
          Nat.add_lt_add_left j.isLt _
        _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
    have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
      Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
    have hmain : k.val * tailLen + j.val < p * tailLen :=
      lt_of_lt_of_le hblock hle
    simp only [firstReductionCanonicalTargetSignature, gt_iff_lt]
    omega⟩
theorem firstReductionCanonicalTargetIndex_eq_tailIndex_of_ne_zero_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (i :
      Fin
        (firstReductionCanonicalTargetSignature
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).numPeriods)
    (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) :
    let r : Fin (p * tailLen) := ⟨i.val - 2, by
      have hi : i.val < 2 + p * tailLen := by
        simp only [firstReductionCanonicalTargetSignature] at i
        exact i.isLt
      omega⟩
    let k : Fin p := ⟨r.val / tailLen, by
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using r.isLt)⟩
    let j : Fin tailLen := ⟨r.val % tailLen, Nat.mod_lt _ hTailLen⟩
    i =
      firstReductionCanonicalTargetTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j := by
  dsimp
  ext
  change i.val = 2 + (i.val - 2) / tailLen * tailLen + (i.val - 2) % tailLen
  have hige2 : 2 ≤ i.val := by omega
  have hdecomp :
      (i.val - 2) / tailLen * tailLen + (i.val - 2) % tailLen = i.val - 2 :=
    Nat.div_add_mod' (i.val - 2) tailLen
  omega
@[simp 900] theorem firstReductionCanonicalTargetFlatTailIndex_block
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
    firstReductionCanonicalTargetFlatTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        ⟨k.val * tailLen + j.val, by
          have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
            calc
              k.val * tailLen + j.val < k.val * tailLen + tailLen :=
                Nat.add_lt_add_left j.isLt _
              _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
          have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
            Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
          exact lt_of_lt_of_le hblock hle⟩ =
      firstReductionCanonicalTargetTailIndex
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j := by
  ext
  simp only [firstReductionCanonicalTargetFlatTailIndex, firstReductionCanonicalTargetTailIndex]
  omega
private theorem firstReductionCanonicalTarget_flatTailProduct_eq_blocks
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    (List.ofFn (fun r : Fin (p * tailLen) =>
      xWord τ
        (firstReductionCanonicalTargetFlatTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r))).prod =
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod)).prod := by
  classical
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change
    (List.ofFn (fun r : Fin (p * tailLen) =>
      xWord τ
        (firstReductionCanonicalTargetFlatTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r))).prod =
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          xWord τ
            (firstReductionCanonicalTargetTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod)).prod
  rw [list_prod_ofFn_mul_blocks]
  congr
  funext k
  congr
  funext j
  rw [firstReductionCanonicalTargetFlatTailIndex_block]
private theorem firstReductionCanonicalTarget_totalRelation_eq_flat
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    totalRelation τ =
      xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
        xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
          (List.ofFn (fun r : Fin (p * tailLen) =>
            xWord τ
              (firstReductionCanonicalTargetFlatTailIndex
                m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r))).prod := by
  classical
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change totalRelation τ =
    xWord τ
        (firstReductionCanonicalTargetZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
      xWord τ
        (firstReductionCanonicalTargetOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
        (List.ofFn (fun r : Fin (p * tailLen) =>
          xWord τ
            (firstReductionCanonicalTargetFlatTailIndex
              m₁' m₂' tail hp hm₁' hm₂' htail hTailLen r))).prod
  rw [totalRelation]
  simpa [τ, firstReductionCanonicalTargetSignature, firstReductionCanonicalTargetZeroIndex,
    firstReductionCanonicalTargetOneIndex, firstReductionCanonicalTargetFlatTailIndex,
    List.ofFn_eq_map, List.prod_cons, mul_assoc] using
      congrArg List.prod
        (list_ofFn_two_add (fun i : Fin (2 + p * tailLen) => xWord τ i))
theorem firstReductionCanonicalTarget_totalRelation_eq_blocks
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let τ :=
      firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    totalRelation τ =
      xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
        xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              xWord τ
                (firstReductionCanonicalTargetTailIndex
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod)).prod := by
  classical
  let τ :=
    firstReductionCanonicalTargetSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  change totalRelation τ =
      xWord τ
          (firstReductionCanonicalTargetZeroIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
        xWord τ
          (firstReductionCanonicalTargetOneIndex
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              xWord τ
                (firstReductionCanonicalTargetTailIndex
                  m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j))).prod)).prod
  rw [firstReductionCanonicalTarget_totalRelation_eq_flat]
  rw [firstReductionCanonicalTarget_flatTailProduct_eq_blocks]
@[simp 900] theorem firstReductionCanonicalTargetSignature_period_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    (firstReductionCanonicalTargetSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalTargetZeroIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) =
      m₁' := by
  simp only [firstReductionCanonicalTargetSignature, firstReductionCanonicalTargetZeroIndex, Fin.mk_zero',
  firstReductionCanonicalTargetPeriod, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte]
@[simp 900] theorem firstReductionCanonicalTargetSignature_period_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    (firstReductionCanonicalTargetSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalTargetOneIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) =
      m₂' := by
  simp only [firstReductionCanonicalTargetSignature, firstReductionCanonicalTargetOneIndex,
  firstReductionCanonicalTargetPeriod, one_ne_zero, ↓reduceIte]
@[simp 900] theorem firstReductionCanonicalTargetSignature_period_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (k : Fin p) (j : Fin tailLen) :
    (firstReductionCanonicalTargetSignature
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen).periods
        (firstReductionCanonicalTargetTailIndex
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen k j) =
      tail j := by
  simp only [firstReductionCanonicalTargetSignature, firstReductionCanonicalTargetTailIndex,
  firstReductionCanonicalTargetPeriod_tail]
end FenchelNielsen
