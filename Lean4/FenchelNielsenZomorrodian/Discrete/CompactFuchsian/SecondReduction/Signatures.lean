import FenchelNielsenZomorrodian.Discrete.Core.EllipticQuotientHom
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.ActualTransport
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.Signatures

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/Signatures.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

open scoped BigOperators
namespace FenchelNielsen
def secondReductionCanonicalSourcePeriod
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (i : Fin (2 + (p + tailLen * p))) : ℕ :=
  if _h0 : i.val = 0 then
    m₁'
  else if _h1 : i.val = 1 then
    m₂'
  else if _hmid : i.val < 2 + p then
    q * m₃'
  else if hTailLen : 0 < tailLen then
    tail ⟨(i.val - (2 + p)) % tailLen, Nat.mod_lt _ hTailLen⟩
  else
    m₁'
@[local simp]
theorem secondReductionCanonicalSourcePeriod_zero
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    secondReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) (q := q)
        m₁' m₂' m₃' tail ⟨0, by omega⟩ = m₁' := by
  simp only [secondReductionCanonicalSourcePeriod, ↓reduceDIte]
@[local simp]
theorem secondReductionCanonicalSourcePeriod_one
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    secondReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) (q := q)
        m₁' m₂' m₃' tail ⟨1, by omega⟩ = m₂' := by
  simp only [secondReductionCanonicalSourcePeriod, one_ne_zero, ↓reduceDIte]
@[local simp]
theorem secondReductionCanonicalSourcePeriod_middle
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) (r : Fin p) :
    secondReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) (q := q)
        m₁' m₂' m₃' tail ⟨2 + r.val, by omega⟩ = q * m₃' := by
  unfold secondReductionCanonicalSourcePeriod
  have h0 : 2 + r.val ≠ 0 := by omega
  have h1 : 2 + r.val ≠ 1 := by omega
  have hmid : 2 + r.val < 2 + p := by omega
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceDIte, h1, hmid]
@[local simp]
theorem secondReductionCanonicalSourcePeriod_tail
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (k : Fin p) (j : Fin tailLen) :
    secondReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) (q := q)
        m₁' m₂' m₃' tail
        ⟨2 + p + k.val * tailLen + j.val, by
          have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
            calc
              k.val * tailLen + j.val < k.val * tailLen + tailLen :=
                Nat.add_lt_add_left j.isLt _
              _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
          have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
            Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
          have hmain : k.val * tailLen + j.val < p * tailLen :=
            lt_of_lt_of_le hblock hle
          have hcomm : p * tailLen = tailLen * p := Nat.mul_comm p tailLen
          omega⟩ = tail j := by
  unfold secondReductionCanonicalSourcePeriod
  have h0 : 2 + p + k.val * tailLen + j.val ≠ 0 := by omega
  have h1 : 2 + p + k.val * tailLen + j.val ≠ 1 := by omega
  have hmid : ¬ 2 + p + k.val * tailLen + j.val < 2 + p := by omega
  have hTailLen : 0 < tailLen := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, mul_eq_zero, ↓reduceDIte, h1, hmid, hTailLen]
  have hsub :
      2 + p + k.val * tailLen + j.val - (2 + p) =
        k.val * tailLen + j.val := by
    omega
  have hmod :
      (2 + p + k.val * tailLen + j.val - (2 + p)) % tailLen = j.val := by
    rw [hsub, Nat.mul_comm k.val tailLen, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  exact congrArg tail (Fin.ext hmod)
def secondReductionCanonicalSourceSignature
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := 2 + (p + tailLen * p)
  periods :=
    secondReductionCanonicalSourcePeriod (tailLen := tailLen) (p := p) (q := q)
      m₁' m₂' m₃' tail
  period_ge_two := by
    intro i
    unfold secondReductionCanonicalSourcePeriod
    by_cases h0 : i.val = 0
    · rw [dif_pos h0]
      exact hm₁'
    · by_cases h1 : i.val = 1
      · rw [dif_neg h0, dif_pos h1]
        exact hm₂'
      · by_cases hmid : i.val < 2 + p
        · rw [dif_neg h0, dif_neg h1, dif_pos hmid]
          exact le_trans hq
            (Nat.le_mul_of_pos_right q (lt_of_lt_of_le (by decide : 0 < 2) hm₃'))
        · by_cases hTailLen : 0 < tailLen
          · rw [dif_neg h0, dif_neg h1, dif_neg hmid, dif_pos hTailLen]
            exact htail ⟨(i.val - (2 + p)) % tailLen, Nat.mod_lt _ hTailLen⟩
          · rw [dif_neg h0, dif_neg h1, dif_neg hmid, dif_neg hTailLen]
            exact hm₁'
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by omega
def secondReductionCanonicalSourceZeroIndex
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Fin
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods :=
  ⟨0, by simp only [secondReductionCanonicalSourceSignature, add_pos_iff, Nat.ofNat_pos, CanonicallyOrderedAdd.mul_pos,
  true_or]⟩
def secondReductionCanonicalSourceOneIndex
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Fin
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods :=
  ⟨1, by simp only [secondReductionCanonicalSourceSignature]; omega⟩
def secondReductionCanonicalSourceMiddleIndex
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (r : Fin p) :
    Fin
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods :=
  ⟨2 + r.val, by simp only [secondReductionCanonicalSourceSignature, add_lt_add_iff_left]; omega⟩
def secondReductionCanonicalSourceTailIndex
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin p) (j : Fin tailLen) :
    Fin
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).numPeriods :=
  ⟨2 + p + k.val * tailLen + j.val, by
    have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
      calc
        k.val * tailLen + j.val < k.val * tailLen + tailLen :=
          Nat.add_lt_add_left j.isLt _
        _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
    have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
      Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
    have hmain : k.val * tailLen + j.val < p * tailLen :=
      lt_of_lt_of_le hblock hle
    have hcomm : p * tailLen = tailLen * p := Nat.mul_comm p tailLen
    simp only [secondReductionCanonicalSourceSignature, gt_iff_lt]
    omega⟩
@[simp 900] theorem secondReductionCanonicalSourceSignature_period_zero
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    (secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) =
      m₁' := by
  simp only [secondReductionCanonicalSourceSignature, secondReductionCanonicalSourceZeroIndex, Fin.mk_zero',
  secondReductionCanonicalSourcePeriod, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceDIte]
@[simp 900] theorem secondReductionCanonicalSourceSignature_period_one
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    (secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) =
      m₂' := by
  simp only [secondReductionCanonicalSourceSignature, secondReductionCanonicalSourceOneIndex,
  secondReductionCanonicalSourcePeriod, one_ne_zero, ↓reduceDIte]
@[simp 900] theorem secondReductionCanonicalSourceSignature_period_middle
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (r : Fin p) :
    (secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r) =
      q * m₃' := by
  simp only [secondReductionCanonicalSourceSignature, secondReductionCanonicalSourceMiddleIndex,
  secondReductionCanonicalSourcePeriod_middle]
@[simp 900] theorem secondReductionCanonicalSourceSignature_period_tail
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) (k : Fin p) (j : Fin tailLen) :
    (secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
        (secondReductionCanonicalSourceTailIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k j) =
      tail j := by
  simp only [secondReductionCanonicalSourceSignature, secondReductionCanonicalSourceTailIndex,
  secondReductionCanonicalSourcePeriod_tail]
theorem secondReductionCanonicalSource_totalRelation_eq
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    totalRelation σ =
      xWord σ
          (secondReductionCanonicalSourceZeroIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
        xWord σ
          (secondReductionCanonicalSourceOneIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
          xWord σ
            (secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨0, by omega⟩) *
            xWord σ
              (secondReductionCanonicalSourceMiddleIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ⟨1, by omega⟩) *
              (List.ofFn (fun r : Fin (p - 2) =>
                xWord σ
                  (secondReductionCanonicalSourceMiddleIndex
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                    ⟨2 + r.val, by omega⟩))).prod *
                (List.ofFn (fun b : Fin p =>
                  (List.ofFn (fun j : Fin tailLen =>
                    xWord σ
                      (secondReductionCanonicalSourceTailIndex
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j))).prod)).prod := by
  classical
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let f : Fin (2 + (p + tailLen * p)) → FreeGroup (FuchsianGenerator σ) :=
    fun i => xWord σ i
  let middle : Fin p → FreeGroup (FuchsianGenerator σ) :=
    fun r =>
      xWord σ
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r)
  let tailFlat : Fin (tailLen * p) → FreeGroup (FuchsianGenerator σ) :=
    fun t =>
      xWord σ
        ⟨2 + p + t.val, by
          have ht : t.val < tailLen * p := t.isLt
          simp only [secondReductionCanonicalSourceSignature, gt_iff_lt, σ]
          omega⟩
  let tailFlat' : Fin (p * tailLen) → FreeGroup (FuchsianGenerator σ) :=
    fun t =>
      xWord σ
        ⟨2 + p + t.val, by
          have ht : t.val < p * tailLen := t.isLt
          have hcomm : p * tailLen = tailLen * p := Nat.mul_comm p tailLen
          simp only [secondReductionCanonicalSourceSignature, gt_iff_lt, σ]
          omega⟩
  have hafter :
      (List.ofFn (fun j : Fin (p + tailLen * p) => f ⟨2 + j.val, by omega⟩)).prod =
        (List.ofFn middle).prod * (List.ofFn tailFlat).prod := by
    have hlist :
        List.ofFn (fun j : Fin (p + tailLen * p) => f ⟨2 + j.val, by omega⟩) =
          List.ofFn middle ++ List.ofFn tailFlat := by
      rw [← List.ofFn_fin_append middle tailFlat]
      apply List.ofFn_inj.2
      funext i
      cases i using Fin.addCases with
      | left r =>
          dsimp [f, middle, tailFlat]
          rw [Fin.append_left]
          rfl
      | right t =>
          dsimp [f, middle, tailFlat]
          rw [Fin.append_right]
          congr 1
          ext
          simp only
          omega
    rw [hlist, List.prod_append]
  have hmiddle :
      (List.ofFn middle).prod =
        xWord σ
            (secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨0, by omega⟩) *
          xWord σ
            (secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨1, by omega⟩) *
            (List.ofFn (fun r : Fin (p - 2) =>
              xWord σ
                (secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  ⟨2 + r.val, by omega⟩))).prod := by
    have hcast :
        List.ofFn middle =
          List.ofFn (fun i : Fin (2 + (p - 2)) =>
            middle ⟨i.val, by omega⟩) := by
      rw [List.ofFn_congr (show p = 2 + (p - 2) by omega)]
      rfl
    rw [hcast]
    simpa [middle, List.prod_cons, mul_assoc] using
      congrArg List.prod
        (list_ofFn_two_add (fun i : Fin (2 + (p - 2)) =>
          middle ⟨i.val, by omega⟩))
  have htailCast :
      (List.ofFn tailFlat).prod = (List.ofFn tailFlat').prod := by
    have hlist :
        List.ofFn tailFlat = List.ofFn tailFlat' := by
      rw [List.ofFn_congr (show tailLen * p = p * tailLen by rw [Nat.mul_comm])]
      rfl
    rw [hlist]
  have htailBlocks :
      (List.ofFn tailFlat').prod =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin tailLen =>
            xWord σ
              (secondReductionCanonicalSourceTailIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j))).prod)).prod := by
    rw [list_prod_ofFn_mul_blocks tailFlat']
    congr
    funext b
    congr
    funext j
    dsimp [tailFlat']
    congr 1
    ext
    simp only [secondReductionCanonicalSourceTailIndex]
    omega
  change totalRelation σ =
    xWord σ
        (secondReductionCanonicalSourceZeroIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
      xWord σ
        (secondReductionCanonicalSourceOneIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
        xWord σ
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨0, by omega⟩) *
          xWord σ
            (secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨1, by omega⟩) *
            (List.ofFn (fun r : Fin (p - 2) =>
              xWord σ
                (secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  ⟨2 + r.val, by omega⟩))).prod *
              (List.ofFn (fun b : Fin p =>
                (List.ofFn (fun j : Fin tailLen =>
                  xWord σ
                    (secondReductionCanonicalSourceTailIndex
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j))).prod)).prod
  have htwo :=
    congrArg List.prod
      (list_ofFn_two_add (fun i : Fin (2 + (p + tailLen * p)) => f i))
  dsimp [f] at htwo
  have hprod :
      (List.ofFn (fun i : Fin (2 + (p + tailLen * p)) => xWord σ i)).prod =
        xWord σ
            (secondReductionCanonicalSourceZeroIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
          xWord σ
            (secondReductionCanonicalSourceOneIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) *
            xWord σ
              (secondReductionCanonicalSourceMiddleIndex
                m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                ⟨0, by omega⟩) *
              xWord σ
                (secondReductionCanonicalSourceMiddleIndex
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                  ⟨1, by omega⟩) *
                (List.ofFn (fun r : Fin (p - 2) =>
                  xWord σ
                    (secondReductionCanonicalSourceMiddleIndex
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                      ⟨2 + r.val, by omega⟩))).prod *
                  (List.ofFn (fun b : Fin p =>
                    (List.ofFn (fun j : Fin tailLen =>
                      xWord σ
                        (secondReductionCanonicalSourceTailIndex
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j))).prod)).prod := by
    rw [htwo, hafter, hmiddle, htailCast, htailBlocks]
    simp only [mul_assoc, secondReductionCanonicalSourceZeroIndex, secondReductionCanonicalSourceOneIndex,
  mul_left_inj, σ]
    congr 1
  rw [totalRelation]
  simpa [σ, secondReductionCanonicalSourceSignature, List.ofFn_eq_map,
    List.prod_cons, mul_assoc] using hprod
def firstSecondInputIndexEquivCanonicalSecondSourceFin
    (tailLen p : ℕ) :
    FirstSecondInputIndex tailLen p ≃ Fin (2 + (p + tailLen * p)) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2))
    ((Equiv.sumCongr (Equiv.refl (Fin p))
        ((Equiv.prodComm (Fin tailLen) (Fin p)).trans finProdFinEquiv)).trans
      (finSumFinEquiv.trans (finCongr (by rw [Nat.mul_comm p tailLen]))))).trans
    finSumFinEquiv
@[local simp]
theorem firstSecondInputIndexEquivCanonicalSecondSourceFin_inl_zero
    (tailLen p : ℕ) :
    firstSecondInputIndexEquivCanonicalSecondSourceFin tailLen p (.inl (0 : Fin 2)) =
      (⟨0, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [firstSecondInputIndexEquivCanonicalSecondSourceFin, Fin.isValue, Equiv.trans_apply,
  Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inl, id_eq, finSumFinEquiv_apply_left,
  Fin.val_castAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
@[local simp]
theorem firstSecondInputIndexEquivCanonicalSecondSourceFin_inl_one
    (tailLen p : ℕ) :
    firstSecondInputIndexEquivCanonicalSecondSourceFin tailLen p (.inl (1 : Fin 2)) =
      (⟨1, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [firstSecondInputIndexEquivCanonicalSecondSourceFin, Fin.isValue, Equiv.trans_apply,
  Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inl, id_eq, finSumFinEquiv_apply_left,
  Fin.val_castAdd, Fin.coe_ofNat_eq_mod, Nat.mod_succ]
@[local simp]
theorem firstSecondInputIndexEquivCanonicalSecondSourceFin_middle
    {tailLen p : ℕ} (r : Fin p) :
    firstSecondInputIndexEquivCanonicalSecondSourceFin tailLen p (.inr (.inl r)) =
      (⟨2 + r.val, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [firstSecondInputIndexEquivCanonicalSecondSourceFin, Equiv.trans_apply, Equiv.sumCongr_apply,
  Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr, Function.comp_apply, Equiv.coe_prodComm, Sum.map_inl, id_eq,
  finSumFinEquiv_apply_left, finCongr_apply, Fin.cast_castAdd_right, finSumFinEquiv_apply_right, Fin.val_natAdd,
  Fin.val_castAdd]
@[local simp]
theorem firstSecondInputIndexEquivCanonicalSecondSourceFin_tail
    {tailLen p : ℕ} (j : Fin tailLen) (k : Fin p) :
    firstSecondInputIndexEquivCanonicalSecondSourceFin tailLen p (.inr (.inr (j, k))) =
      (⟨2 + p + k.val * tailLen + j.val, by
        have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
          calc
            k.val * tailLen + j.val < k.val * tailLen + tailLen :=
              Nat.add_lt_add_left j.isLt _
            _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
        have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
          Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
        have hmain : k.val * tailLen + j.val < p * tailLen :=
          lt_of_lt_of_le hblock hle
        have hcomm : p * tailLen = tailLen * p := Nat.mul_comm p tailLen
        omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [firstSecondInputIndexEquivCanonicalSecondSourceFin, finProdFinEquiv, Equiv.trans_apply,
  Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr, Function.comp_apply, Equiv.coe_fn_mk,
  Equiv.coe_prodComm, Prod.swap_prod_mk, finSumFinEquiv_apply_right, Fin.natAdd_mk, finCongr_apply, Fin.cast_mk,
  Nat.mul_comm]
  omega
def secondReductionSourceIndexEquivCanonicalSourceFin
    {tailLen p : ℕ} (hp : 2 ≤ p) :
    SecondReductionSourceIndex tailLen p ≃ Fin (2 + (p + tailLen * p)) :=
  (firstSecondInputIndexEquivSecondReductionSourceIndex (tailLen := tailLen) hp).symm.trans
    (firstSecondInputIndexEquivCanonicalSecondSourceFin tailLen p)
@[local simp]
theorem secondReductionSourceIndexEquivCanonicalSourceFin_inl_zero
    {tailLen p : ℕ} (hp : 2 ≤ p) :
    secondReductionSourceIndexEquivCanonicalSourceFin (tailLen := tailLen) hp (.inl (0 : Fin 2)) =
      (⟨0, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [secondReductionSourceIndexEquivCanonicalSourceFin,
  firstSecondInputIndexEquivSecondReductionSourceIndex, Equiv.sumCongr_symm, Equiv.refl_symm, Fin.isValue,
  Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl, id_eq,
  firstSecondInputIndexEquivCanonicalSecondSourceFin_inl_zero, Fin.mk_zero', Fin.coe_ofNat_eq_mod, Nat.zero_mod]
@[local simp]
theorem secondReductionSourceIndexEquivCanonicalSourceFin_inl_one
    {tailLen p : ℕ} (hp : 2 ≤ p) :
    secondReductionSourceIndexEquivCanonicalSourceFin (tailLen := tailLen) hp (.inl (1 : Fin 2)) =
      (⟨1, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [secondReductionSourceIndexEquivCanonicalSourceFin,
  firstSecondInputIndexEquivSecondReductionSourceIndex, Equiv.sumCongr_symm, Equiv.refl_symm, Fin.isValue,
  Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl, id_eq,
  firstSecondInputIndexEquivCanonicalSecondSourceFin_inl_one]
@[local simp]
theorem secondReductionSourceIndexEquivCanonicalSourceFin_distinguished
    {tailLen p : ℕ} (hp : 2 ≤ p) (i : Fin 2) :
    secondReductionSourceIndexEquivCanonicalSourceFin (tailLen := tailLen) hp (.inr (.inl i)) =
      (⟨2 + i.val, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  fin_cases i <;>
    simp only [secondReductionSourceIndexEquivCanonicalSourceFin,
  firstSecondInputIndexEquivSecondReductionSourceIndex, finTwoRestEquiv, Equiv.sumCongr_symm, Equiv.refl_symm,
  Fin.mk_one, Fin.isValue, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr,
  Equiv.symm_trans_apply, Equiv.sumAssoc_symm_apply_inl, Sum.map_inl, finCongr_symm, Equiv.symm_symm,
  finSumFinEquiv_apply_left, finCongr_apply, firstSecondInputIndexEquivCanonicalSecondSourceFin_middle, Fin.val_cast,
  Fin.val_castAdd, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.reduceAdd]
@[local simp]
theorem secondReductionSourceIndexEquivCanonicalSourceFin_rest
    {tailLen p : ℕ} (hp : 2 ≤ p) (r : Fin (p - 2)) :
    secondReductionSourceIndexEquivCanonicalSourceFin
        (tailLen := tailLen) hp (.inr (.inr (.inl r))) =
      (⟨4 + r.val, by omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [secondReductionSourceIndexEquivCanonicalSourceFin,
  firstSecondInputIndexEquivSecondReductionSourceIndex, finTwoRestEquiv, Equiv.sumCongr_symm, Equiv.refl_symm,
  Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, Equiv.symm_trans_apply,
  Equiv.sumAssoc_symm_apply_inr_inl, Sum.map_inl, finCongr_symm, Equiv.symm_symm, finSumFinEquiv_apply_right,
  finCongr_apply, firstSecondInputIndexEquivCanonicalSecondSourceFin_middle, Fin.val_cast, Fin.val_natAdd]
  omega
@[local simp]
theorem secondReductionSourceIndexEquivCanonicalSourceFin_tail
    {tailLen p : ℕ} (hp : 2 ≤ p) (j : Fin tailLen) (k : Fin p) :
    secondReductionSourceIndexEquivCanonicalSourceFin
        (tailLen := tailLen) hp (.inr (.inr (.inr (j, k)))) =
      (⟨2 + p + k.val * tailLen + j.val, by
        have hblock : k.val * tailLen + j.val < (k.val + 1) * tailLen := by
          calc
            k.val * tailLen + j.val < k.val * tailLen + tailLen :=
              Nat.add_lt_add_left j.isLt _
            _ = (k.val + 1) * tailLen := by rw [Nat.add_mul, one_mul]
        have hle : (k.val + 1) * tailLen ≤ p * tailLen :=
          Nat.mul_le_mul_right tailLen (Nat.succ_le_of_lt k.isLt)
        have hmain : k.val * tailLen + j.val < p * tailLen :=
          lt_of_lt_of_le hblock hle
        have hcomm : p * tailLen = tailLen * p := Nat.mul_comm p tailLen
        omega⟩ : Fin (2 + (p + tailLen * p))) := by
  ext
  simp only [secondReductionSourceIndexEquivCanonicalSourceFin,
  firstSecondInputIndexEquivSecondReductionSourceIndex, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.trans_apply,
  Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, Equiv.symm_trans_apply, Equiv.sumAssoc_symm_apply_inr_inr, id_eq,
  firstSecondInputIndexEquivCanonicalSecondSourceFin_tail, Nat.mul_comm]
theorem secondReductionSourceSignature_mulEquiv_canonicalSourceSignature_exists
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    Nonempty
      (FuchsianPresentedGroup
          (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
            (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail)
        ≃*
        FuchsianPresentedGroup
          (secondReductionCanonicalSourceSignature
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)) := by
  classical
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
      (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
        (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail)
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      ?_ ?_
      (Fintype.equivFin (SecondReductionSourceIndex tailLen p))
      (secondReductionSourceIndexEquivCanonicalSourceFin (tailLen := tailLen) hp) ?_
  · simp only [secondReductionSourceSignature, familyFuchsianSignature]
  · simp only [secondReductionCanonicalSourceSignature]
  · intro x
    cases x with
    | inl i =>
        fin_cases i
        · calc
            (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
                (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail).periods
                ((Fintype.equivFin (SecondReductionSourceIndex tailLen p)) (.inl (0 : Fin 2))) =
              m₁' := by
                simp only [secondReductionSourceSignature, familyFuchsianSignature, secondReductionSourcePeriods, twoPeriods,
  Nat.reduceAdd, Fin.isValue, Equiv.symm_apply_apply, Fin.cases_zero]
            _ =
              (secondReductionCanonicalSourceSignature
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
                (secondReductionSourceIndexEquivCanonicalSourceFin
                  (tailLen := tailLen) hp (.inl (0 : Fin 2))) := by
                simpa [secondReductionCanonicalSourceZeroIndex] using
                  (secondReductionCanonicalSourceSignature_period_zero
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm
        · calc
            (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
                (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail).periods
                ((Fintype.equivFin (SecondReductionSourceIndex tailLen p)) (.inl (1 : Fin 2))) =
              m₂' := by
                simp only [secondReductionSourceSignature, familyFuchsianSignature, secondReductionSourcePeriods, twoPeriods,
  Nat.reduceAdd, Fin.isValue, Equiv.symm_apply_apply, fin_cases_const_one]
            _ =
              (secondReductionCanonicalSourceSignature
                  m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
                (secondReductionSourceIndexEquivCanonicalSourceFin
                  (tailLen := tailLen) hp (.inl (1 : Fin 2))) := by
                simpa [secondReductionCanonicalSourceOneIndex] using
                  (secondReductionCanonicalSourceSignature_period_one
                    m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).symm
    | inr s =>
        cases s with
        | inl i =>
            fin_cases i
            · calc
                (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
                    (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail).periods
                    ((Fintype.equivFin (SecondReductionSourceIndex tailLen p))
                      (.inr (.inl (0 : Fin 2)))) =
                  q * m₃' := by
                    simp only [secondReductionSourceSignature, familyFuchsianSignature, secondReductionSourcePeriods, Fin.isValue,
  Equiv.symm_apply_apply]
                _ =
                  (secondReductionCanonicalSourceSignature
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
                    (secondReductionSourceIndexEquivCanonicalSourceFin
                      (tailLen := tailLen) hp (.inr (.inl (0 : Fin 2)))) := by
                    simpa [secondReductionCanonicalSourceMiddleIndex] using
                      (secondReductionCanonicalSourceSignature_period_middle
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                        ⟨0, by omega⟩).symm
            · calc
                (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
                    (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail).periods
                    ((Fintype.equivFin (SecondReductionSourceIndex tailLen p))
                      (.inr (.inl (1 : Fin 2)))) =
                  q * m₃' := by
                    simp only [secondReductionSourceSignature, familyFuchsianSignature, secondReductionSourcePeriods, Fin.isValue,
  Equiv.symm_apply_apply]
                _ =
                  (secondReductionCanonicalSourceSignature
                      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
                    (secondReductionSourceIndexEquivCanonicalSourceFin
                      (tailLen := tailLen) hp (.inr (.inl (1 : Fin 2)))) := by
                    simpa [secondReductionCanonicalSourceMiddleIndex] using
                      (secondReductionCanonicalSourceSignature_period_middle
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                        ⟨1, by omega⟩).symm
        | inr s =>
            cases s with
            | inl r =>
                calc
                  (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
                      (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail).periods
                      ((Fintype.equivFin (SecondReductionSourceIndex tailLen p))
                        (.inr (.inr (.inl r)))) =
                    q * m₃' := by
                      simp only [secondReductionSourceSignature, familyFuchsianSignature, secondReductionSourcePeriods,
  Equiv.symm_apply_apply]
                  _ =
                    (secondReductionCanonicalSourceSignature
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
                      (secondReductionSourceIndexEquivCanonicalSourceFin
                        (tailLen := tailLen) hp (.inr (.inr (.inl r)))) := by
                      simpa [secondReductionCanonicalSourceMiddleIndex, Nat.add_assoc,
                        Nat.add_comm, Nat.add_left_comm] using
                        (secondReductionCanonicalSourceSignature_period_middle
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
                          ⟨2 + r.val, by omega⟩).symm
            | inr jk =>
                rcases jk with ⟨j, k⟩
                calc
                  (secondReductionSourceSignature (p := p) m₁' m₂' m₃' tail hq hm₁' hm₂'
                      (lt_of_lt_of_le (by decide : 0 < 2) hm₃') htail).periods
                      ((Fintype.equivFin (SecondReductionSourceIndex tailLen p))
                        (.inr (.inr (.inr (j, k))))) =
                    tail j := by
                      simp only [secondReductionSourceSignature, familyFuchsianSignature, secondReductionSourcePeriods,
  Equiv.symm_apply_apply]
                  _ =
                    (secondReductionCanonicalSourceSignature
                        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail).periods
                      (secondReductionSourceIndexEquivCanonicalSourceFin
                        (tailLen := tailLen) hp (.inr (.inr (.inr (j, k))))) := by
                      simpa [secondReductionCanonicalSourceTailIndex] using
                        (secondReductionCanonicalSourceSignature_period_tail
                          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k j).symm
noncomputable def secondReductionCanonicalSourceQuotientImage
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    (let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
     Fin σ.numPeriods → Multiplicative (ZMod q)) :=
  fun i =>
    if i.val = 2 then Multiplicative.ofAdd (1 : ZMod q)
    else if i.val = 3 then Multiplicative.ofAdd (-1 : ZMod q)
    else 1
theorem secondReductionCanonicalSourceQuotientImage_pow
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∀ i : Fin σ.numPeriods,
      secondReductionCanonicalSourceQuotientImage
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i ^
        σ.periods i = 1 := by
  classical
  dsimp
  intro i
  by_cases h2 : i.val = 2
  · have hi :
        i =
          secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨0, by omega⟩ := by
      ext
      simpa [secondReductionCanonicalSourceMiddleIndex] using h2
    rw [hi]
    have hval :
        (secondReductionCanonicalSourceMiddleIndex
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
          ⟨0, by omega⟩).val = 2 := by
      simp only [secondReductionCanonicalSourceMiddleIndex, add_zero]
    rw [secondReductionCanonicalSourceQuotientImage, if_pos hval]
    apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
    simp only [secondReductionCanonicalSourceSignature_period_middle, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
  Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_one, toAdd_one]
  · by_cases h3 : i.val = 3
    · have hp1 : 1 < p := by omega
      have hi :
          i =
            secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
              ⟨1, hp1⟩ := by
        ext
        simpa [secondReductionCanonicalSourceMiddleIndex] using h3
      rw [hi]
      have hnot2 :
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨1, hp1⟩).val ≠ 2 := by
        simp only [secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd, ne_eq, Nat.succ_ne_self,
  not_false_eq_true]
      have hval :
          (secondReductionCanonicalSourceMiddleIndex
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
            ⟨1, hp1⟩).val = 3 := by
        simp only [secondReductionCanonicalSourceMiddleIndex, Nat.reduceAdd]
      rw [secondReductionCanonicalSourceQuotientImage, if_neg hnot2, if_pos hval]
      apply (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q).injective
      simp only [ofAdd_neg, secondReductionCanonicalSourceSignature_period_middle, inv_pow, toAdd_inv, toAdd_pow,
  toAdd_ofAdd, nsmul_eq_mul, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_one, neg_zero, toAdd_one]
    · simp only [secondReductionCanonicalSourceQuotientImage, h2, ↓reduceIte, h3, one_pow]
theorem secondReductionCanonicalSourceQuotientImage_prod
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let σ :=
      secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    ∏ i : Fin σ.numPeriods,
      secondReductionCanonicalSourceQuotientImage
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i = 1 := by
  classical
  dsimp
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let ξ : Fin σ.numPeriods → Multiplicative (ZMod q) :=
    secondReductionCanonicalSourceQuotientImage
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  change ∏ i : Fin σ.numPeriods, ξ i = 1
  have hnum : σ.numPeriods = 2 + (p + tailLen * p) := by
    simp only [secondReductionCanonicalSourceSignature, σ]
  let n := 2 + (p + tailLen * p)
  let f : Fin n → Multiplicative (ZMod q) := fun i =>
    if i.val = 2 then Multiplicative.ofAdd (1 : ZMod q)
    else if i.val = 3 then Multiplicative.ofAdd (-1 : ZMod q)
    else 1
  change ∏ i : Fin n, f i = 1
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i2)]
  have hprod3 : (∏ x ∈ Finset.univ.erase i2, f x) = f i3 := by
    refine Finset.prod_eq_single_of_mem i3 ?hmem ?hone
    · simp only [Finset.mem_erase, ne_eq, Fin.mk.injEq, Nat.succ_ne_self, not_false_eq_true, Finset.mem_univ,
  and_self, i2, i3]
    · intro b hb hbne
      have hb_ne_i2 : b ≠ i2 := (Finset.mem_erase.mp hb).1
      have hb2 : b.val ≠ 2 := by
        intro h
        apply hb_ne_i2
        ext
        simpa [i2] using h
      have hb3 : b.val ≠ 3 := by
        intro h
        apply hbne
        ext
        simpa [i3] using h
      simp only [ofAdd_neg, hb2, ↓reduceIte, hb3, f]
  rw [hprod3]
  simp only [ofAdd_neg, ↓reduceIte, Nat.succ_ne_self, mul_inv_cancel, f, i2, i3]
noncomputable def secondReductionCanonicalSourceQuotientHom
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    FuchsianPresentedGroup
      (secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) →*
        Multiplicative (ZMod q) := by
  classical
  let σ :=
    secondReductionCanonicalSourceSignature m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  exact
    ellipticQuotientHom σ
      (secondReductionCanonicalSourceQuotientImage
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (secondReductionCanonicalSourceQuotientImage_pow
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
      (secondReductionCanonicalSourceQuotientImage_prod
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
@[local simp]
theorem secondReductionCanonicalSourceQuotientHom_firstDistinguished
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    secondReductionCanonicalSourceQuotientHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
        (PresentedGroup.of
          (rels := relators
            (secondReductionCanonicalSourceSignature
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail))
          (FuchsianGenerator.elliptic
            (secondReductionCanonicalSourceMiddleIndex
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail ⟨0, by omega⟩))) =
      Multiplicative.ofAdd (1 : ZMod q) := by
  classical
  simp only [secondReductionCanonicalSourceQuotientHom, ellipticQuotientHom,
  secondReductionCanonicalSourceMiddleIndex, add_zero, PresentedGroup.toGroup.of, ellipticQuotientGeneratorImage,
  secondReductionCanonicalSourceQuotientImage, ↓reduceIte]
