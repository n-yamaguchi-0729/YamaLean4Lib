import FenchelNielsenZomorrodian.Discrete.Abelianization.EllipticAbelianization
import FenchelNielsenZomorrodian.Discrete.Arithmetic.PrimeDivisors
import FenchelNielsenZomorrodian.Discrete.GroupTheory.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/ZeroGenus/Perfectness.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact zero-genus three-step proof data

Organizes first and second reduction data, perfectness numerics, reindexing, cleanup data, and the final zero-genus three-step finite-index theorem.
-/

open scoped BigOperators

namespace FenchelNielsen

private theorem hom_trivial_of_zeroGenus_pairwiseCoprime
    (σ : FuchsianSignature) (hZero : σ.orbitGenus = 0)
    (hPair :
      ∀ i j : Fin σ.numPeriods, i ≠ j → Nat.Coprime (σ.periods i) (σ.periods j))
    {A : Type*} [CommGroup A] (φ : FuchsianPresentedGroup σ →* A) :
    φ = 1 := by
  apply PresentedGroup.ext
  intro x
  cases x with
  | elliptic i =>
      let ξ : Fin σ.numPeriods → A := fun j => φ (ellipticElement σ j)
      have hpow : ∀ j : Fin σ.numPeriods, ξ j ^ σ.periods j = 1 := by
        intro j
        simpa [ξ, ellipticElement, xWord, MonoidHom.map_pow] using
          congrArg φ
            (PresentedGroup.one_of_mem (rels := relators σ)
              (x := (xWord σ j) ^ σ.periods j) (Or.inl ⟨j, rfl⟩))
      let L := otherPeriodsLcm σ.toFenchelSignature i
      have hPow : ξ i ^ L = 1 := by
        simpa [ξ, L] using
          commHom_ellipticElement_pow_otherPeriodsLcm_eq_one σ φ i
      have hCoprimeProd :
          Nat.Coprime (σ.periods i)
            ((Finset.univ.erase i : Finset (Fin σ.numPeriods)).prod σ.periods) := by
        rw [Nat.coprime_prod_right_iff]
        intro j hj
        exact hPair i j (Finset.mem_erase.mp hj).1.symm
      have hLDiv :
          L ∣ (Finset.univ.erase i : Finset (Fin σ.numPeriods)).prod σ.periods := by
        dsimp [L, otherPeriodsLcm]
        exact Finset.lcm_dvd (fun j hj => Finset.dvd_prod_of_mem _ hj)
      have hCoprime : Nat.Coprime (σ.periods i) L := hCoprimeProd.of_dvd_right hLDiv
      have hOrder :
          orderOf (ξ i) = 1 := by
        exact Nat.eq_one_of_dvd_coprimes hCoprime
          (orderOf_dvd_of_pow_eq_one (hpow i))
          (orderOf_dvd_of_pow_eq_one hPow)
      exact orderOf_eq_one_iff.mp hOrder
  | surfaceA j =>
      exfalso
      rw [hZero] at j
      exact Nat.not_lt_zero _ j.2
  | surfaceB j =>
      exfalso
      rw [hZero] at j
      exact Nat.not_lt_zero _ j.2

theorem FuchsianSignature.isPerfect_of_zeroGenus_pairwiseCoprime
    (σ : FuchsianSignature) (hZero : σ.orbitGenus = 0)
    (hPair :
      ∀ i j : Fin σ.numPeriods, i ≠ j → Nat.Coprime (σ.periods i) (σ.periods j)) :
    IsPerfectGroup (FuchsianPresentedGroup σ) := by
  rw [IsPerfectGroup, derivedSeries_one]
  apply top_le_iff.mp
  intro g hg
  rw [← Abelianization.ker_of (G := FuchsianPresentedGroup σ), MonoidHom.mem_ker]
  have htriv :
      (Abelianization.of :
          FuchsianPresentedGroup σ →* Abelianization (FuchsianPresentedGroup σ)) = 1 :=
    hom_trivial_of_zeroGenus_pairwiseCoprime σ hZero hPair Abelianization.of
  simpa using congrArg
    (fun f : FuchsianPresentedGroup σ →* Abelianization (FuchsianPresentedGroup σ) => f g) htriv

theorem exists_prime_dvd_two_periods_of_zeroGenus_notPerfect
    (σ : FuchsianSignature) (hZero : σ.orbitGenus = 0)
    (hNonperfect : ¬ IsPerfectGroup (FuchsianPresentedGroup σ)) :
    ∃ p : ℕ, p.Prime ∧
      ∃ i j : Fin σ.numPeriods, i ≠ j ∧ p ∣ σ.periods i ∧ p ∣ σ.periods j := by
  exact (not_pairwiseCoprimeFamily_iff_exists_prime_dvd_two (periods := σ.periods)).mp <| by
    intro hPair
    exact hNonperfect (FuchsianSignature.isPerfect_of_zeroGenus_pairwiseCoprime σ hZero hPair)

end FenchelNielsen
