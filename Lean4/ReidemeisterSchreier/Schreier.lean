import Mathlib.Data.Nat.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Schreier.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Schreier rank transform

Numerical rank-transform formulas for finite-index subgroups of free groups.
-/

namespace ReidemeisterSchreier
namespace Schreier

/-- The Schreier rank transform `T(r, i) = 1 + i * (r - 1)`, with the rank-zero convention. -/
def rankTransform (r i : ℕ) : ℕ :=
  if r = 0 then 0 else 1 + i * (r - 1)

@[simp] theorem rankTransform_zero_left (i : ℕ) : rankTransform 0 i = 0 := by
  simp only [rankTransform, ↓reduceIte]

@[simp] theorem rankTransform_succ (r i : ℕ) : rankTransform (r + 1) i = 1 + i * r := by
  simp only [rankTransform, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, ↓reduceIte,
    Nat.add_one_sub_one]

@[simp] theorem rankTransform_one_left (i : ℕ) : rankTransform 1 i = 1 := by
  simp only [rankTransform, Nat.succ_ne_self, ↓reduceIte, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

theorem rankTransform_eq_one_add {r i : ℕ} (hr : r ≠ 0) :
    rankTransform r i = 1 + i * (r - 1) := by
  simp only [rankTransform, hr, ↓reduceIte]

/-- Multiplying subgroup indices composes the Schreier rank transform. -/
theorem rankTransform_mul_index (r i j : ℕ) :
    rankTransform (rankTransform r i) j = rankTransform r (i * j) := by
  cases r with
  | zero =>
      simp only [rankTransform, ↓reduceIte]
  | succ r =>
      simp only [rankTransform, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, ↓reduceIte,
        Nat.add_one_sub_one, false_and, Nat.add_sub_cancel_left, Nat.mul_left_comm, Nat.mul_comm]

/-- The Schreier rank transform is monotone in the rank variable. -/
theorem rankTransform_mono_left {r s i : ℕ} (hrs : r ≤ s) :
    rankTransform r i ≤ rankTransform s i := by
  cases s with
  | zero =>
      have hr : r = 0 := Nat.eq_zero_of_le_zero hrs
      subst hr
      simp only [rankTransform_zero_left, le_refl]
  | succ s =>
      cases r with
      | zero =>
          simp only [rankTransform_zero_left, rankTransform_succ, Nat.zero_le]
      | succ r =>
          simpa only [rankTransform_succ] using
            Nat.add_le_add_left (Nat.mul_le_mul_left i (Nat.succ_le_succ_iff.mp hrs)) 1

end Schreier
end ReidemeisterSchreier
