import Mathlib.Data.Nat.Prime.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Arithmetic/PrimeDivisors.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Arithmetic of period families

GCD, LCM, prime-divisor, replicated-family, and abelian-period numerical lemmas used in compact zero-genus reductions.
-/

namespace FenchelNielsen

theorem not_pairwiseCoprimeFamily_iff_exists_prime_dvd_two
    {ι : Type*} {periods : ι → ℕ} :
    (¬ ∀ i j, i ≠ j → Nat.Coprime (periods i) (periods j)) ↔
      ∃ p : ℕ, p.Prime ∧
        ∃ i j : ι, i ≠ j ∧ p ∣ periods i ∧ p ∣ periods j := by
  constructor
  · intro hNot
    by_contra hPrime
    apply hNot
    intro i j hij
    by_contra hCoprime
    rcases Nat.Prime.not_coprime_iff_dvd.mp hCoprime with ⟨p, hp, hpi, hpj⟩
    exact hPrime ⟨p, hp, i, j, hij, hpi, hpj⟩
  · rintro ⟨p, hp, i, j, hij, hpi, hpj⟩
    intro hPair
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpi, hpj⟩) (hPair i j hij)

end FenchelNielsen
