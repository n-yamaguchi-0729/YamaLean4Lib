import FenchelNielsenZomorrodian.Discrete.Core.FamilySignature
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodFamilies
import Mathlib.Tactic.FinCases

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/ZeroGenus/FirstReductionData.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact zero-genus three-step proof data

Organizes first and second reduction data, perfectness numerics, reindexing, cleanup data, and the final zero-genus three-step finite-index theorem.
-/

namespace FenchelNielsen

def originalFirstReductionSignaturePeriod
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (i : Fin (2 + tailLen)) : ℕ :=
  if h0 : i.val = 0 then
    p * m₁'
  else if h1 : i.val = 1 then
    p * m₂'
  else
    tail ⟨i.val - 2, by omega⟩

@[simp 900] theorem originalFirstReductionSignaturePeriod_zero
    {tailLen p : ℕ} (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    originalFirstReductionSignaturePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        ⟨0, by omega⟩ = p * m₁' := by
  simp only [originalFirstReductionSignaturePeriod, ↓reduceDIte]

@[simp 900] theorem originalFirstReductionSignaturePeriod_zero_fin
    {tailLen p : ℕ} (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    originalFirstReductionSignaturePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        (0 : Fin (2 + tailLen)) = p * m₁' := by
  rfl

@[simp 900] theorem originalFirstReductionSignaturePeriod_one
    {tailLen p : ℕ} (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    originalFirstReductionSignaturePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        ⟨1, by omega⟩ = p * m₂' := by
  simp only [originalFirstReductionSignaturePeriod, one_ne_zero, ↓reduceDIte]

@[simp 900] theorem originalFirstReductionSignaturePeriod_one_fin
    {tailLen p : ℕ} (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    originalFirstReductionSignaturePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        (1 : Fin (2 + tailLen)) = p * m₂' := by
  have hOne : (1 : Fin (2 + tailLen)) = ⟨1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.coe_ofNat_eq_mod]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 + tailLen)]
  rw [hOne]
  simp only [originalFirstReductionSignaturePeriod_one]

@[simp 900] theorem originalFirstReductionSignaturePeriod_tail
    {tailLen p : ℕ} (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) (j : Fin tailLen) :
    originalFirstReductionSignaturePeriod (tailLen := tailLen) (p := p) m₁' m₂' tail
        ⟨2 + j.val, by omega⟩ = tail j := by
  unfold originalFirstReductionSignaturePeriod
  have h0 : 2 + j.val ≠ 0 := by omega
  have h1 : 2 + j.val ≠ 1 := by omega
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceDIte, h1, add_tsub_cancel_left,
  Fin.eta]

def originalFirstReductionOrderedIndexEquiv (tailLen : ℕ) :
    OriginalFirstReductionIndex tailLen ≃ Fin (2 + tailLen) where
  toFun := fun
    | .inl i => ⟨i.val, by omega⟩
    | .inr j => ⟨2 + j.val, by omega⟩
  invFun := fun i =>
    if h0 : i.val = 0 then
      .inl (0 : Fin 2)
    else if h1 : i.val = 1 then
      .inl (1 : Fin 2)
    else
      .inr ⟨i.val - 2, by omega⟩
  left_inv := by
    intro x
    cases x using Sum.casesOn with
    | inl i =>
        fin_cases i <;> rfl
    | inr j =>
        simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, ↓reduceDIte, Fin.isValue,
  add_tsub_cancel_left, Fin.eta, dite_eq_ite, ite_eq_right_iff, reduceCtorEq, imp_false]
        omega
  right_inv := by
    intro i
    by_cases h0 : i.val = 0
    · ext
      simp only [h0, ↓reduceDIte, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.mk_zero']
    · by_cases h1 : i.val = 1
      · ext
        simp only [h1, one_ne_zero, ↓reduceDIte, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ]
      · ext
        simp only [h0, ↓reduceDIte, h1]
        omega

@[simp 900] theorem originalFirstReductionOrderedIndexEquiv_left_zero
    (tailLen : ℕ) :
    originalFirstReductionOrderedIndexEquiv tailLen (.inl (0 : Fin 2)) =
      (0 : Fin (2 + tailLen)) := rfl

@[simp 900] theorem originalFirstReductionOrderedIndexEquiv_left_one
    (tailLen : ℕ) :
    originalFirstReductionOrderedIndexEquiv tailLen (.inl (1 : Fin 2)) =
      (1 : Fin (2 + tailLen)) := by
  apply Fin.ext
  simp only [originalFirstReductionOrderedIndexEquiv, Fin.val_eq_zero_iff, Fin.isValue, Equiv.coe_fn_mk,
  Fin.coe_ofNat_eq_mod, Nat.mod_succ]
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2 + tailLen)]

@[simp 900] theorem originalFirstReductionOrderedIndexEquiv_right
    {tailLen : ℕ} (j : Fin tailLen) :
    originalFirstReductionOrderedIndexEquiv tailLen (.inr j) =
      ⟨2 + j.val, by omega⟩ := rfl

@[simp 900] theorem originalFirstReductionOrderedIndexEquiv_symm_zero
    (tailLen : ℕ) :
    (originalFirstReductionOrderedIndexEquiv tailLen).symm (0 : Fin (2 + tailLen)) =
      .inl (0 : Fin 2) := by
  apply (originalFirstReductionOrderedIndexEquiv tailLen).injective
  simp only [Equiv.apply_symm_apply, Fin.isValue, originalFirstReductionOrderedIndexEquiv_left_zero]

@[simp 900] theorem originalFirstReductionOrderedIndexEquiv_symm_one
    (tailLen : ℕ) :
    (originalFirstReductionOrderedIndexEquiv tailLen).symm (1 : Fin (2 + tailLen)) =
      .inl (1 : Fin 2) := by
  apply (originalFirstReductionOrderedIndexEquiv tailLen).injective
  simp only [Equiv.apply_symm_apply, Fin.isValue, originalFirstReductionOrderedIndexEquiv_left_one]

@[simp 900] theorem originalFirstReductionOrderedIndexEquiv_symm_right
    {tailLen : ℕ} (j : Fin tailLen) :
    (originalFirstReductionOrderedIndexEquiv tailLen).symm ⟨2 + j.val, by omega⟩ =
      .inr j := by
  apply (originalFirstReductionOrderedIndexEquiv tailLen).injective
  simp only [Equiv.apply_symm_apply, originalFirstReductionOrderedIndexEquiv_right]

noncomputable def originalFirstReductionSignature
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := 2 + tailLen
  periods := originalFirstReductionSignaturePeriod (p := p) m₁' m₂' tail
  period_ge_two := by
    intro i
    unfold originalFirstReductionSignaturePeriod
    by_cases h0 : i.val = 0
    · simp only [h0, ↓reduceDIte]
      exact le_trans hp (Nat.le_mul_of_pos_right p hm₁')
    · by_cases h1 : i.val = 1
      · simp only [h1, one_ne_zero, ↓reduceDIte]
        exact le_trans hp (Nat.le_mul_of_pos_right p hm₂')
      · simp only [h0, ↓reduceDIte, h1]
        exact htail ⟨i.val - 2, by omega⟩
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by
    omega

end FenchelNielsen
