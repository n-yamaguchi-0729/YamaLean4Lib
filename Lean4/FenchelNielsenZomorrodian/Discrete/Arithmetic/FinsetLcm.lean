import FenchelNielsenZomorrodian.Discrete.Arithmetic.FamilyLcm

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Arithmetic/FinsetLcm.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Arithmetic of period families

GCD, LCM, prime-divisor, replicated-family, and abelian-period numerical lemmas used in compact zero-genus reductions.
-/

open scoped BigOperators

namespace Finset

theorem two_mul_lcm_le_prod_of_equal_pair
    {ι : Type*} {periods : ι → ℕ} {s : Finset ι}
    (hge : ∀ i ∈ s, 2 ≤ periods i)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hji : j ≠ i) (hjEq : periods j = periods i) :
    2 * s.lcm periods ≤ s.prod periods := by
  classical
  have hjmem : j ∈ s.erase i := by
    exact Finset.mem_erase.mpr ⟨hji, hj⟩
  have hlcmDivProdErase :
      s.lcm periods ∣ (s.erase i).prod periods := by
    apply Finset.lcm_dvd
    intro k hk
    by_cases hki : k = i
    · subst hki
      rw [← hjEq]
      exact Finset.dvd_prod_of_mem periods hjmem
    · have hkmem : k ∈ s.erase i := by
        exact Finset.mem_erase.mpr ⟨hki, hk⟩
      exact Finset.dvd_prod_of_mem periods hkmem
  have hProdErasePos : 0 < (s.erase i).prod periods := by
    exact Finset.prod_pos
      (fun k hk => lt_of_lt_of_le (by decide : 0 < 2)
        (hge k (Finset.mem_of_mem_erase hk)))
  have hlcmLeProdErase : s.lcm periods ≤ (s.erase i).prod periods :=
    Nat.le_of_dvd hProdErasePos hlcmDivProdErase
  calc
    2 * s.lcm periods
        ≤ periods i * (s.erase i).prod periods :=
          Nat.mul_le_mul (hge i hi) hlcmLeProdErase
    _ = s.prod periods := by
          rw [mul_comm]
          exact Finset.prod_erase_mul (s := s) (f := periods) (a := i) hi

end Finset
