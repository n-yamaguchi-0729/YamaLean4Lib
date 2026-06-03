import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.Signatures

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/OrderedTargetSignature.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen
def secondReductionCanonicalOrderedTargetBlockLen (tailLen p : ℕ) : ℕ :=
  2 + ((p - 2) + p * tailLen)
def secondReductionCanonicalOrderedTargetNumPeriods (tailLen p q : ℕ) : ℕ :=
  2 + q * secondReductionCanonicalOrderedTargetBlockLen tailLen p
def secondReductionCanonicalOrderedTargetDistinguishedIndex
    (tailLen p q : ℕ) (d : Fin 2) :
    Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  ⟨d.val, by
    have hd := d.isLt
    simp only [secondReductionCanonicalOrderedTargetNumPeriods, secondReductionCanonicalOrderedTargetBlockLen,
  gt_iff_lt]
    omega⟩
def secondReductionCanonicalOrderedTargetHeadIndex
    (tailLen p q : ℕ) (h : Fin 2) (k : Fin q) :
    Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  ⟨2 + k.val * secondReductionCanonicalOrderedTargetBlockLen tailLen p +
      (p - 2) + p * tailLen + h.val, by
    let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
    have hpos : (p - 2) + p * tailLen + h.val < L := by
      have hh := h.isLt
      dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
      omega
    have hblock :
        k.val * L + ((p - 2) + p * tailLen + h.val) < (k.val + 1) * L := by
      calc
        k.val * L + ((p - 2) + p * tailLen + h.val) < k.val * L + L :=
          Nat.add_lt_add_left hpos _
        _ = (k.val + 1) * L := by rw [Nat.add_mul, one_mul]
    have hle : (k.val + 1) * L ≤ q * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt k.isLt)
    have hlt' : 2 + (k.val * L + ((p - 2) + p * tailLen + h.val)) < 2 + q * L :=
      Nat.add_lt_add_left (lt_of_lt_of_le hblock hle) 2
    have hlt : 2 + k.val * L + ((p - 2) + p * tailLen + h.val) < 2 + q * L := by
      simpa [Nat.add_assoc] using hlt'
    simpa [secondReductionCanonicalOrderedTargetNumPeriods, L, Nat.add_assoc] using hlt⟩
def secondReductionCanonicalOrderedTargetMiddleRestIndex
    (tailLen p q : ℕ) (r : Fin (p - 2)) (k : Fin q) :
    Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  ⟨2 + k.val * secondReductionCanonicalOrderedTargetBlockLen tailLen p + r.val, by
    let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
    have hrL : r.val < L := by
      have hr := r.isLt
      dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
      omega
    have hblock :
        k.val * L + r.val < (k.val + 1) * L := by
      calc
        k.val * L + r.val < k.val * L + L :=
          Nat.add_lt_add_left hrL _
        _ = (k.val + 1) * L := by rw [Nat.add_mul, one_mul]
    have hle : (k.val + 1) * L ≤ q * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt k.isLt)
    have hlt' : 2 + (k.val * L + r.val) < 2 + q * L :=
      Nat.add_lt_add_left (lt_of_lt_of_le hblock hle) 2
    have hlt : 2 + k.val * L + r.val < 2 + q * L := by
      simpa [Nat.add_assoc] using hlt'
    simpa [secondReductionCanonicalOrderedTargetNumPeriods, L, Nat.add_assoc] using hlt⟩
def secondReductionCanonicalOrderedTargetTailIndex
    (tailLen p q : ℕ) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  ⟨2 + k.val * secondReductionCanonicalOrderedTargetBlockLen tailLen p +
      (p - 2) + b.val * tailLen + j.val, by
    let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
    have htailLen : 0 < tailLen := lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have hbj :
        b.val * tailLen + j.val < p * tailLen := by
      have hblock : b.val * tailLen + j.val < (b.val + 1) * tailLen := by
        calc
          b.val * tailLen + j.val < b.val * tailLen + tailLen :=
            Nat.add_lt_add_left j.isLt _
          _ = (b.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
      have hle : (b.val + 1) * tailLen ≤ p * tailLen :=
        Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt b.isLt)
      exact lt_of_lt_of_le hblock hle
    have hpos :
        (p - 2) + (b.val * tailLen + j.val) < L := by
      dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
      omega
    have hblock :
        k.val * L + ((p - 2) + b.val * tailLen + j.val) <
          (k.val + 1) * L := by
      calc
        k.val * L + ((p - 2) + b.val * tailLen + j.val) =
            k.val * L + ((p - 2) + (b.val * tailLen + j.val)) := by omega
        _ < k.val * L + L := Nat.add_lt_add_left hpos _
        _ = (k.val + 1) * L := by rw [Nat.add_mul, one_mul]
    have hle : (k.val + 1) * L ≤ q * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt k.isLt)
    have hlt' :
        2 + (k.val * L + ((p - 2) + b.val * tailLen + j.val)) <
          2 + q * L :=
      Nat.add_lt_add_left (lt_of_lt_of_le hblock hle) 2
    have hlt :
        2 + k.val * L + ((p - 2) + b.val * tailLen + j.val) <
          2 + q * L := by
      simpa [Nat.add_assoc] using hlt'
    simpa [secondReductionCanonicalOrderedTargetNumPeriods, L, Nat.add_assoc] using hlt⟩
def secondReductionCanonicalOrderedTargetPeriod
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (i : Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q)) : ℕ :=
  if _h0 : i.val = 0 then
    m₃'
  else if _h1 : i.val = 1 then
    m₃'
  else
    let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
    let r := (i.val - 2) % L
    if _hrMid : r < p - 2 then
      q * m₃'
    else if _hrTail : r < (p - 2) + p * tailLen then
      if hTailLen : 0 < tailLen then
        tail ⟨(r - (p - 2)) % tailLen, Nat.mod_lt _ hTailLen⟩
      else
        m₁'
    else if _hrHead0 : r = (p - 2) + p * tailLen then
      m₁'
    else
      m₂'
def secondReductionCanonicalOrderedTargetSignature
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := secondReductionCanonicalOrderedTargetNumPeriods tailLen p q
  periods :=
    secondReductionCanonicalOrderedTargetPeriod (tailLen := tailLen) (p := p) (q := q)
      m₁' m₂' m₃' tail
  period_ge_two := by
    intro i
    by_cases h0 : i.val = 0
    · simpa [secondReductionCanonicalOrderedTargetPeriod, h0] using hm₃'
    by_cases h1 : i.val = 1
    · simpa [secondReductionCanonicalOrderedTargetPeriod, h0, h1] using hm₃'
    let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
    let r := (i.val - 2) % L
    by_cases hrMid : r < p - 2
    · have hm₃mul : 2 ≤ q * m₃' :=
        le_trans hq
          (Nat.le_mul_of_pos_right q (lt_of_lt_of_le (by decide : 0 < 2) hm₃'))
      simpa [secondReductionCanonicalOrderedTargetPeriod, h0, h1, L, r, hrMid] using hm₃mul
    by_cases hrTail : r < (p - 2) + p * tailLen
    · by_cases hTailLen : 0 < tailLen
      · have htail' :
            2 ≤ tail ⟨(r - (p - 2)) % tailLen, Nat.mod_lt _ hTailLen⟩ :=
          htail _
        simpa [secondReductionCanonicalOrderedTargetPeriod, h0, h1, L, r, hrMid,
          hrTail, hTailLen] using htail'
      · simpa [secondReductionCanonicalOrderedTargetPeriod, h0, h1, L, r, hrMid,
          hrTail, hTailLen] using hm₁'
    · by_cases hrHead0 : r = (p - 2) + p * tailLen
      · simpa [secondReductionCanonicalOrderedTargetPeriod, h0, h1, L, r, hrMid,
          hrTail, hrHead0] using hm₁'
      · simpa [secondReductionCanonicalOrderedTargetPeriod, h0, h1, L, r, hrMid,
          hrTail, hrHead0] using hm₂'
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by
    have _hp0 : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
    have hq0 : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
    have hL0 : 0 < secondReductionCanonicalOrderedTargetBlockLen tailLen p := by
      simp only [secondReductionCanonicalOrderedTargetBlockLen, add_pos_iff, Nat.ofNat_pos, tsub_pos_iff_lt,
  CanonicallyOrderedAdd.mul_pos, true_or]
    have hprod : 0 < q * secondReductionCanonicalOrderedTargetBlockLen tailLen p :=
      Nat.mul_pos hq0 hL0
    dsimp [secondReductionCanonicalOrderedTargetNumPeriods]
    omega
@[simp 900] theorem secondReductionCanonicalOrderedTargetSignature_period_distinguished
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (d : Fin 2) :
    (secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q d) =
      m₃' := by
  fin_cases d <;>
    simp only [secondReductionCanonicalOrderedTargetSignature,
  secondReductionCanonicalOrderedTargetDistinguishedIndex, secondReductionCanonicalOrderedTargetPeriod, one_ne_zero,
  ↓reduceDIte]
@[simp 900] theorem secondReductionCanonicalOrderedTargetSignature_period_middleRest
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (r : Fin (p - 2)) (k : Fin q) :
    (secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k) =
      q * m₃' := by
  let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
  have hrL : r.val < L := by
    have hr := r.isLt
    dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
    omega
  have hmod : (2 + k.val * L + r.val - 2) % L = r.val := by
    have hsub : 2 + k.val * L + r.val - 2 = k.val * L + r.val := by omega
    rw [hsub, Nat.mul_comm k.val L, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrL]
  have hnot0 : ¬ 2 + k.val * L + r.val = 0 := by omega
  have hnot1 : ¬ 2 + k.val * L + r.val = 1 := by omega
  have hrMid : r.val < p - 2 := r.isLt
  simp only [secondReductionCanonicalOrderedTargetSignature,
  secondReductionCanonicalOrderedTargetMiddleRestIndex, secondReductionCanonicalOrderedTargetPeriod,
  Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, mul_eq_zero, false_and, ↓reduceDIte, hnot1, hmod, hrMid, L]
@[simp 900] theorem secondReductionCanonicalOrderedTargetSignature_period_tail
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    (secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k) =
      tail j := by
  let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
  have htailLen : 0 < tailLen := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hbj : b.val * tailLen + j.val < p * tailLen := by
    have hblock : b.val * tailLen + j.val < (b.val + 1) * tailLen := by
      calc
        b.val * tailLen + j.val < b.val * tailLen + tailLen :=
          Nat.add_lt_add_left j.isLt _
        _ = (b.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
    have hle : (b.val + 1) * tailLen ≤ p * tailLen :=
      Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt b.isLt)
    exact lt_of_lt_of_le hblock hle
  have hpos : (p - 2) + b.val * tailLen + j.val < L := by
    dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
    omega
  have hmod :
      (2 + k.val * L + ((p - 2) + b.val * tailLen + j.val) - 2) % L =
        (p - 2) + b.val * tailLen + j.val := by
    have hsub :
        2 + k.val * L + ((p - 2) + b.val * tailLen + j.val) - 2 =
          k.val * L + ((p - 2) + b.val * tailLen + j.val) := by omega
    rw [hsub, Nat.mul_comm k.val L, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hpos]
  have hnot0 : ¬ 2 + k.val * L + ((p - 2) + b.val * tailLen + j.val) = 0 := by omega
  have hnot1 : ¬ 2 + k.val * L + ((p - 2) + b.val * tailLen + j.val) = 1 := by omega
  have hnotMid : ¬ (p - 2) + b.val * tailLen + j.val < p - 2 := by omega
  have hTail : (p - 2) + b.val * tailLen + j.val < (p - 2) + p * tailLen := by
    omega
  have htailIndex :
      ((p - 2) + b.val * tailLen + j.val - (p - 2)) % tailLen = j.val := by
    have hsub : (p - 2) + b.val * tailLen + j.val - (p - 2) =
        b.val * tailLen + j.val := by omega
    rw [hsub, Nat.mul_comm b.val tailLen, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  have hnot1Actual :
      ¬ 2 + k.val * L + (p - 2) + b.val * tailLen + j.val = 1 := by omega
  have hmodActual :
      (2 + k.val * L + (p - 2) + b.val * tailLen + j.val - 2) % L =
        (p - 2) + b.val * tailLen + j.val := by
    rw [show 2 + k.val * L + (p - 2) + b.val * tailLen + j.val - 2 =
        2 + k.val * L + ((p - 2) + b.val * tailLen + j.val) - 2 by omega]
    exact hmod
  have htailIndexActual :
      ((2 + k.val * L + (p - 2) + b.val * tailLen + j.val - 2) % L -
          (p - 2)) % tailLen = j.val := by
    rw [hmodActual]
    exact htailIndex
  simpa [secondReductionCanonicalOrderedTargetSignature,
    secondReductionCanonicalOrderedTargetTailIndex,
    secondReductionCanonicalOrderedTargetPeriod, L, hnot1Actual, hmodActual, hnotMid,
    hTail, htailLen, htailIndexActual] using congrArg tail (Fin.ext htailIndex)
@[simp 900] theorem secondReductionCanonicalOrderedTargetSignature_period_head_zero
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    (secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨0, by decide⟩ k) =
      m₁' := by
  let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
  have hpos : (p - 2) + p * tailLen < L := by
    dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
    omega
  have hmod :
      (2 + k.val * L + ((p - 2) + p * tailLen) - 2) % L =
        (p - 2) + p * tailLen := by
    have hsub :
        2 + k.val * L + ((p - 2) + p * tailLen) - 2 =
          k.val * L + ((p - 2) + p * tailLen) := by omega
    rw [hsub, Nat.mul_comm k.val L, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hpos]
  have hnot1Actual : ¬ 2 + k.val * L + (p - 2) + p * tailLen = 1 := by omega
  have hmodActual :
      (2 + k.val * L + (p - 2) + p * tailLen - 2) % L =
        (p - 2) + p * tailLen := by
    rw [show 2 + k.val * L + (p - 2) + p * tailLen - 2 =
        2 + k.val * L + ((p - 2) + p * tailLen) - 2 by omega]
    exact hmod
  have hnotMid : ¬ (p - 2) + p * tailLen < p - 2 := by omega
  have hnotTail : ¬ (p - 2) + p * tailLen < (p - 2) + p * tailLen := by omega
  simp only [secondReductionCanonicalOrderedTargetSignature, secondReductionCanonicalOrderedTargetHeadIndex,
  add_zero, secondReductionCanonicalOrderedTargetPeriod, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, mul_eq_zero,
  false_and, ↓reduceDIte, hnot1Actual, hmodActual, hnotMid, lt_self_iff_false, L]
@[simp 900] theorem secondReductionCanonicalOrderedTargetSignature_period_head_one
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    (secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨1, by decide⟩ k) =
      m₂' := by
  let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
  have hpos : (p - 2) + p * tailLen + (1 : ℕ) < L := by
    dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
    omega
  have hmod :
      (2 + k.val * L + ((p - 2) + p * tailLen + (1 : ℕ)) - 2) % L =
        (p - 2) + p * tailLen + 1 := by
    have hsub :
        2 + k.val * L + ((p - 2) + p * tailLen + (1 : ℕ)) - 2 =
          k.val * L + ((p - 2) + p * tailLen + 1) := by omega
    rw [hsub, Nat.mul_comm k.val L, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hpos]
  have hnot0 : ¬ 2 + k.val * L + ((p - 2) + p * tailLen + (1 : ℕ)) = 0 := by omega
  have hnot1 : ¬ 2 + k.val * L + ((p - 2) + p * tailLen + (1 : ℕ)) = 1 := by omega
  have hnotMid : ¬ (p - 2) + p * tailLen + 1 < p - 2 := by omega
  have hnotTail : ¬ (p - 2) + p * tailLen + 1 < (p - 2) + p * tailLen := by omega
  have hnotHead0 : ¬ (p - 2) + p * tailLen + 1 = (p - 2) + p * tailLen := by omega
  have hmodActual :
      (2 + k.val * L + (p - 2) + p * tailLen - 1) % L =
        (p - 2) + p * tailLen + 1 := by
    rw [show 2 + k.val * L + (p - 2) + p * tailLen - 1 =
        2 + k.val * L + ((p - 2) + p * tailLen + 1) - 2 by omega]
    exact hmod
  simp only [secondReductionCanonicalOrderedTargetSignature, secondReductionCanonicalOrderedTargetHeadIndex,
  secondReductionCanonicalOrderedTargetPeriod, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, mul_eq_zero, false_and,
  one_ne_zero, and_self, ↓reduceDIte, Nat.add_eq_right, Nat.reduceSubDiff, hmodActual, hnotMid, hnotTail,
  Nat.add_eq_left, L]
def secondReductionCanonicalOrderedTargetFlatBlockIndex
    (tailLen p q : ℕ)
    (r : Fin (q * secondReductionCanonicalOrderedTargetBlockLen tailLen p)) :
    Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  ⟨2 + r.val, by
    dsimp [secondReductionCanonicalOrderedTargetNumPeriods]
    omega⟩
def secondReductionCanonicalOrderedTargetBlockIndex
    (tailLen p q : ℕ) (k : Fin q)
    (r : Fin (secondReductionCanonicalOrderedTargetBlockLen tailLen p)) :
    Fin (secondReductionCanonicalOrderedTargetNumPeriods tailLen p q) :=
  secondReductionCanonicalOrderedTargetFlatBlockIndex tailLen p q
    ⟨k.val * secondReductionCanonicalOrderedTargetBlockLen tailLen p + r.val, by
      let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
      have hblock : k.val * L + r.val < (k.val + 1) * L := by
        calc
          k.val * L + r.val < k.val * L + L :=
            Nat.add_lt_add_left r.isLt _
          _ = (k.val + 1) * L := by rw [Nat.add_mul, one_mul]
      have hle : (k.val + 1) * L ≤ q * L :=
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt k.isLt)
      simpa [L] using lt_of_lt_of_le hblock hle⟩
noncomputable def secondReductionCanonicalOrderedTargetZeroBlockWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    Fin q → FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  intro k
  exact
    (List.ofFn (fun r : Fin (secondReductionCanonicalOrderedTargetBlockLen tailLen p) =>
      xWord τ (secondReductionCanonicalOrderedTargetBlockIndex tailLen p q k r))).prod
private theorem secondReduction_list_prod_ofFn_add
    {α : Type*} [Monoid α] {m n : ℕ} (f : Fin (m + n) → α) :
    (List.ofFn f).prod =
      (List.ofFn (fun i : Fin m => f (Fin.castAdd n i))).prod *
        (List.ofFn (fun j : Fin n => f (Fin.natAdd m j))).prod := by
  rw [← List.prod_append, ← List.ofFn_fin_append]
  congr
  funext i
  cases i using Fin.addCases with
  | left a =>
      simp only [Fin.append_left]
  | right b =>
      simp only [Fin.append_right]
private theorem secondReduction_list_prod_ofFn_cast_add
    {α : Type*} [Monoid α] {l m n : ℕ} (h : l = m + n) (f : Fin l → α) :
    (List.ofFn f).prod =
      (List.ofFn (fun i : Fin m => f (Fin.cast h.symm (Fin.castAdd n i)))).prod *
        (List.ofFn (fun j : Fin n => f (Fin.cast h.symm (Fin.natAdd m j)))).prod := by
  rw [List.ofFn_congr h f]
  exact secondReduction_list_prod_ofFn_add
    (fun i : Fin (m + n) => f (Fin.cast h.symm i))
private theorem secondReductionCanonicalOrderedTargetBlockIndex_middleRest
    (tailLen p q : ℕ) (k : Fin q) (r : Fin (p - 2)) :
    secondReductionCanonicalOrderedTargetBlockIndex tailLen p q k
        ⟨r.val, by
          have hr := r.isLt
          simp only [secondReductionCanonicalOrderedTargetBlockLen, gt_iff_lt]
          omega⟩ =
      secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k := by
  ext
  simp only [secondReductionCanonicalOrderedTargetBlockIndex,
  secondReductionCanonicalOrderedTargetFlatBlockIndex, secondReductionCanonicalOrderedTargetMiddleRestIndex]
  omega
private theorem secondReductionCanonicalOrderedTargetBlockIndex_tail
    (tailLen p q : ℕ) (k : Fin q) (b : Fin p) (j : Fin tailLen) :
    secondReductionCanonicalOrderedTargetBlockIndex tailLen p q k
        ⟨(p - 2) + (b.val * tailLen + j.val), by
          let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
          have hbj : b.val * tailLen + j.val < p * tailLen := by
            have hblock : b.val * tailLen + j.val < (b.val + 1) * tailLen := by
              calc
                b.val * tailLen + j.val < b.val * tailLen + tailLen :=
                  Nat.add_lt_add_left j.isLt _
                _ = (b.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
            have hle : (b.val + 1) * tailLen ≤ p * tailLen :=
              Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt b.isLt)
            exact lt_of_lt_of_le hblock hle
          dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
          omega⟩ =
      secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k := by
  ext
  simp only [secondReductionCanonicalOrderedTargetBlockIndex,
  secondReductionCanonicalOrderedTargetFlatBlockIndex, secondReductionCanonicalOrderedTargetTailIndex]
  omega
theorem secondReductionCanonicalOrderedTargetZeroBlockWord_eq_nested
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin q) :
    let τ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    secondReductionCanonicalOrderedTargetZeroBlockWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k =
      (List.ofFn (fun r : Fin (p - 2) =>
        xWord τ (secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k))).prod *
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            xWord τ (secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k))).prod)).prod *
        xWord τ (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨0, by decide⟩ k) *
        xWord τ (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
  classical
  dsimp
  let τ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
  let f : Fin L → FreeGroup (FuchsianGenerator τ) := fun r =>
    xWord τ (secondReductionCanonicalOrderedTargetBlockIndex tailLen p q k r)
  change (List.ofFn f).prod = _
  have hL : L = (p - 2) + (p * tailLen + 2) := by
    dsimp [L, secondReductionCanonicalOrderedTargetBlockLen]
    omega
  rw [secondReduction_list_prod_ofFn_cast_add hL f]
  have hmiddle :
      (List.ofFn (fun i : Fin (p - 2) =>
          f (Fin.cast hL.symm (Fin.castAdd (p * tailLen + 2) i)))).prod =
        (List.ofFn (fun r : Fin (p - 2) =>
          xWord τ (secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k))).prod := by
    congr
    funext r
    dsimp [f]
    congr
    exact secondReductionCanonicalOrderedTargetBlockIndex_middleRest tailLen p q k r
  let g : Fin (p * tailLen + 2) → FreeGroup (FuchsianGenerator τ) := fun s =>
    f (Fin.cast hL.symm (Fin.natAdd (p - 2) s))
  have hrest :
      (List.ofFn (fun j : Fin (p * tailLen + 2) =>
          f (Fin.cast hL.symm (Fin.natAdd (p - 2) j)))).prod =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            xWord τ (secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k))).prod)).prod *
          xWord τ (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨0, by decide⟩ k) *
          xWord τ (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
    change (List.ofFn g).prod = _
    rw [secondReduction_list_prod_ofFn_add g]
    have htailFlat :
        (List.ofFn (fun i : Fin (p * tailLen) => g (Fin.castAdd 2 i))).prod =
          (List.ofFn (fun b : Fin p =>
            (List.ofFn (fun j : Fin tailLen =>
              xWord τ (secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k))).prod)).prod := by
      rw [list_prod_ofFn_mul_blocks]
      congr
      funext b
      congr
      funext j
      dsimp [g, f]
      congr
      exact secondReductionCanonicalOrderedTargetBlockIndex_tail tailLen p q k b j
    have hheads :
        (List.ofFn (fun j : Fin 2 => g (Fin.natAdd (p * tailLen) j))).prod =
          xWord τ (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨0, by decide⟩ k) *
            xWord τ (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
      rw [List.ofFn_succ]
      rw [List.ofFn_succ]
      have hhead :
          ∀ h : Fin 2,
            secondReductionCanonicalOrderedTargetBlockIndex tailLen p q k
                (Fin.cast hL.symm (Fin.natAdd (p - 2) (Fin.natAdd (p * tailLen) h))) =
              secondReductionCanonicalOrderedTargetHeadIndex tailLen p q h k := by
        intro h
        ext
        simp only [secondReductionCanonicalOrderedTargetBlockIndex,
  secondReductionCanonicalOrderedTargetFlatBlockIndex, secondReductionCanonicalOrderedTargetBlockLen, Fin.val_cast,
  Fin.val_natAdd, secondReductionCanonicalOrderedTargetHeadIndex, L]
        omega
      simp only [Fin.isValue, hhead, Fin.succ_zero_eq_one, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
  Fin.zero_eta, Fin.mk_one, g, f]
    rw [htailFlat, hheads]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_assoc]
  rw [hmiddle, hrest]
  simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_assoc, τ]
theorem secondReductionCanonicalOrderedTarget_totalRelation_eq_blocks
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let A :=
      xWord τ (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q
        ⟨0, by decide⟩)
    let B :=
      xWord τ (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q
        ⟨1, by decide⟩)
    let C :=
      (List.ofFn (fun k : Fin q =>
        secondReductionCanonicalOrderedTargetZeroBlockWord
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)).prod
    totalRelation τ = A * B * C := by
  classical
  let τ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let L := secondReductionCanonicalOrderedTargetBlockLen tailLen p
  let flat :=
    (List.ofFn (fun r : Fin (q * L) =>
      xWord τ (secondReductionCanonicalOrderedTargetFlatBlockIndex tailLen p q r))).prod
  let blocks :=
    (List.ofFn (fun k : Fin q =>
      secondReductionCanonicalOrderedTargetZeroBlockWord
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)).prod
  have hflat_blocks : flat = blocks := by
    dsimp [flat, blocks, secondReductionCanonicalOrderedTargetZeroBlockWord]
    rw [list_prod_ofFn_mul_blocks]
    congr
  have htwo :
      totalRelation τ =
        xWord τ (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q
          ⟨0, by decide⟩) *
          xWord τ (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q
            ⟨1, by decide⟩) *
            flat := by
    rw [totalRelation]
    simpa [τ, flat, L, secondReductionCanonicalOrderedTargetSignature,
      secondReductionCanonicalOrderedTargetDistinguishedIndex,
      secondReductionCanonicalOrderedTargetFlatBlockIndex, List.ofFn_eq_map,
      List.prod_cons, mul_assoc] using
        congrArg List.prod
          (list_ofFn_two_add
            (fun i : Fin (2 + q * L) => xWord τ i))
  simpa [τ, blocks, flat, hflat_blocks, mul_assoc] using htwo
end FenchelNielsen
