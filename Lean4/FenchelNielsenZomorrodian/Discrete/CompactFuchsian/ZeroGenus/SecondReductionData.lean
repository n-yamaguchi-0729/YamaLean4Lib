import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.FirstReductionData
import Mathlib.Data.Fintype.Prod

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/ZeroGenus/SecondReductionData.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact zero-genus three-step proof data

Organizes first and second reduction data, perfectness numerics, reindexing, cleanup data, and the final zero-genus three-step finite-index theorem.
-/

namespace FenchelNielsen

noncomputable def secondReductionSourceSignature
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 0 < m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    FuchsianSignature :=
  familyFuchsianSignature
    (secondReductionSourcePeriods (p := p) (q := q) m₁' m₂' m₃' tail)
    (by
      intro i
      cases i using Sum.casesOn <;> rename_i i
      · fin_cases i
        · simpa [secondReductionSourcePeriods, twoPeriods] using hm₁'
        · simpa [secondReductionSourcePeriods, twoPeriods] using hm₂'
      · cases i using Sum.casesOn <;> rename_i i
        · exact le_trans hq (Nat.le_mul_of_pos_right q hm₃')
        · cases i using Sum.casesOn <;> rename_i i
          · exact le_trans hq (Nat.le_mul_of_pos_right q hm₃')
          · exact htail i.1)
    (by
      have hcard :
          Fintype.card (SecondReductionSourceIndex tailLen p)
            = 2 + 2 + (p - 2) + tailLen * p := by
        simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Nat.reduceAdd]
        omega
      rw [hcard]
      omega)

end FenchelNielsen
