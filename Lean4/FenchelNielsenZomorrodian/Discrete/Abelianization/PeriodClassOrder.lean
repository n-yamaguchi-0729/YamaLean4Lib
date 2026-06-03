import FenchelNielsenZomorrodian.Discrete.Abelianization.PeriodCoordinate

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Abelianization/PeriodClassOrder.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abelianization of compact Fuchsian presentations

Finite cyclic coordinate calculations for elliptic generators, period classes, period quotients, and order formulas in compact Fuchsian abelianizations.
-/

namespace FenchelNielsen

theorem gcd_period_otherLcm_dvd_of_nsmul_periodClass_eq_zero
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) {n : ℕ}
    (hzero : n • periodClass σ i = 0) :
    Nat.gcd (σ.periods i) (otherPeriodsLcm σ.toFenchelSignature i) ∣ n := by
  classical
  let L := otherPeriodsLcm σ.toFenchelSignature i
  let d := Nat.gcd (σ.periods i) L
  have hmem : n • periodBasisVector σ i ∈ periodRelation σ := by
    simpa using
      (QuotientAddGroup.eq_iff_sub_mem (N := periodRelation σ)
        (x := n • periodBasisVector σ i) (y := 0)).1 <| by
          simpa [periodClass] using hzero
  change n • periodBasisVector σ i ∈ AddSubgroup.zmultiples (periodDiagonal σ) at hmem
  rcases hmem with ⟨z, hz⟩
  have hOthers :
      ∀ j ∈ (Finset.univ.erase i : Finset (Fin σ.numPeriods)),
        σ.periods j ∣ Int.natAbs z := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hcoord : (z : ZMod (σ.periods j)) = 0 := by
      have := congrArg (fun v : PeriodCoordinate σ => v j) hz
      simpa [periodDiagonal, periodBasisVector, zmodBasisVector, hji] using this
    have hzdiv : (σ.periods j : ℤ) ∣ z := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd z (σ.periods j)).mp hcoord
    exact Int.natCast_dvd.mp hzdiv
  have hLzNat : L ∣ Int.natAbs z := by
    exact Finset.lcm_dvd hOthers
  have hdzNat : d ∣ Int.natAbs z :=
    (Nat.gcd_dvd_right (σ.periods i) L).trans hLzNat
  have hdzInt : (d : ℤ) ∣ z := by
    exact Int.natCast_dvd.mpr hdzNat
  have hdaNat : d ∣ σ.periods i := Nat.gcd_dvd_left (σ.periods i) L
  have hdaInt : (d : ℤ) ∣ (σ.periods i : ℤ) := by
    exact Int.natCast_dvd_natCast.mpr hdaNat
  have hcoordi :
      ((n : ℤ) : ZMod (σ.periods i)) = (z : ZMod (σ.periods i)) := by
    have := congrArg (fun v : PeriodCoordinate σ => v i) hz
    simpa [periodDiagonal, periodBasisVector, zmodBasisVector] using this.symm
  have hdiff : (σ.periods i : ℤ) ∣ z - (n : ℤ) := by
    exact
      (ZMod.intCast_eq_intCast_iff_dvd_sub (n : ℤ) z (σ.periods i)).mp hcoordi
  have hdDiff : (d : ℤ) ∣ z - (n : ℤ) := hdaInt.trans hdiff
  have hdNInt : (d : ℤ) ∣ (n : ℤ) := by
    have hsub : (d : ℤ) ∣ z - (z - (n : ℤ)) := dvd_sub hdzInt hdDiff
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  exact Int.natCast_dvd_natCast.mp hdNInt

theorem periodClass_addOrderOf_eq_gcd
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    addOrderOf (periodClass σ i) =
      Nat.gcd (σ.periods i) (otherPeriodsLcm σ.toFenchelSignature i) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd
      ((addOrderOf_dvd_iff_nsmul_eq_zero).2 (periodClass_nsmul_eq_zero σ i))
      ((addOrderOf_dvd_iff_nsmul_eq_zero).2
        (otherPeriodsLcm_nsmul_periodClass_eq_zero σ i))
  · exact gcd_period_otherLcm_dvd_of_nsmul_periodClass_eq_zero σ i (by simp only [addOrderOf_nsmul_eq_zero])

theorem periodClass_addOrderOf_eq_period_iff
    {σ : FuchsianSignature} {i : Fin σ.numPeriods} :
    addOrderOf (periodClass σ i) = σ.periods i ↔
      σ.periods i ∣ otherPeriodsLcm σ.toFenchelSignature i := by
  rw [periodClass_addOrderOf_eq_gcd]
  exact Nat.gcd_eq_left_iff_dvd

theorem periodClass_orderOf_eq_period_iff
    {σ : FuchsianSignature} {i : Fin σ.numPeriods} :
    orderOf (Multiplicative.ofAdd (periodClass σ i)) = σ.periods i ↔
      σ.periods i ∣ otherPeriodsLcm σ.toFenchelSignature i := by
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact periodClass_addOrderOf_eq_period_iff (σ := σ) (i := i)

theorem periodClass_addOrderOf_eq_period
  (σ : FuchsianSignature) (hLCM : LCMCondition σ.toFenchelSignature)
  (i : Fin σ.numPeriods) :
  addOrderOf (periodClass σ i) = σ.periods i :=
  (periodClass_addOrderOf_eq_period_iff (σ := σ) (i := i)).2 (hLCM i)

theorem periodClass_orderOf_eq_period
  (σ : FuchsianSignature) (hLCM : LCMCondition σ.toFenchelSignature)
  (i : Fin σ.numPeriods) :
  orderOf (Multiplicative.ofAdd (periodClass σ i)) = σ.periods i :=
  (periodClass_orderOf_eq_period_iff (σ := σ) (i := i)).2 (hLCM i)

end FenchelNielsen
