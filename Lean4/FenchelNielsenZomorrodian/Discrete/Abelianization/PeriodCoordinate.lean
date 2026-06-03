import FenchelNielsenZomorrodian.Discrete.Coordinates.ZModFamily
import FenchelNielsenZomorrodian.Discrete.Core.CompactFuchsianPresentation
import Mathlib.Algebra.BigOperators.Pi

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Abelianization/PeriodCoordinate.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abelianization of compact Fuchsian presentations

Finite cyclic coordinate calculations for elliptic generators, period classes, period quotients, and order formulas in compact Fuchsian abelianizations.
-/

open scoped BigOperators

namespace FenchelNielsen

abbrev PeriodCoordinate (σ : FuchsianSignature) :=
  ZModCoordinateFamily σ.periods

def periodDiagonal (σ : FuchsianSignature) : PeriodCoordinate σ :=
  fun _ => 1

def periodRelation (σ : FuchsianSignature) : AddSubgroup (PeriodCoordinate σ) :=
  AddSubgroup.zmultiples (periodDiagonal σ)

abbrev PeriodAbelianization (σ : FuchsianSignature) :=
  PeriodCoordinate σ ⧸ periodRelation σ

def periodBasisVector (σ : FuchsianSignature) (i : Fin σ.numPeriods) : PeriodCoordinate σ :=
  zmodBasisVector σ.periods i

def periodClass (σ : FuchsianSignature) (i : Fin σ.numPeriods) : PeriodAbelianization σ :=
  (periodBasisVector σ i : PeriodCoordinate σ)

theorem sum_periodBasisVector_eq_periodDiagonal (σ : FuchsianSignature) :
    (∑ i : Fin σ.numPeriods, periodBasisVector σ i) = periodDiagonal σ := by
  simpa [periodBasisVector, zmodBasisVector, periodDiagonal] using
    (Finset.univ_sum_single (fun i : Fin σ.numPeriods => (1 : ZMod (σ.periods i))))

theorem sum_periodClass_eq_zero (σ : FuchsianSignature) :
    (∑ i : Fin σ.numPeriods, periodClass σ i) = 0 := by
  have hsum :
      (((∑ i : Fin σ.numPeriods, periodBasisVector σ i) : PeriodCoordinate σ) :
          PeriodAbelianization σ) = (periodDiagonal σ : PeriodAbelianization σ) := by
    exact congrArg (fun v : PeriodCoordinate σ => (v : PeriodAbelianization σ))
      (sum_periodBasisVector_eq_periodDiagonal σ)
  have hdiag : (periodDiagonal σ : PeriodAbelianization σ) = 0 := by
    have hmem : periodDiagonal σ ∈ periodRelation σ := by
      change periodDiagonal σ ∈ AddSubgroup.zmultiples (periodDiagonal σ)
      exact ⟨1, by simp only [one_smul]⟩
    exact (QuotientAddGroup.eq_iff_sub_mem (N := periodRelation σ)
      (x := periodDiagonal σ) (y := 0)).2 <| by simpa using hmem
  simpa [periodClass] using hsum.trans hdiag

theorem periodClass_nsmul_eq_zero (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    σ.periods i • periodClass σ i = 0 := by
  have hvec : σ.periods i • periodBasisVector σ i = 0 :=
    zmodBasisVector_nsmul_eq_zero σ.periods i
  simpa [periodClass] using
    congrArg (fun v : PeriodCoordinate σ => (v : PeriodAbelianization σ)) hvec

theorem otherPeriodsLcm_nsmul_periodClass_eq_zero
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    otherPeriodsLcm σ.toFenchelSignature i • periodClass σ i = 0 := by
  classical
  let L := otherPeriodsLcm σ.toFenchelSignature i
  have hmem : L • periodBasisVector σ i ∈ periodRelation σ := by
    change L • periodBasisVector σ i ∈ AddSubgroup.zmultiples (periodDiagonal σ)
    refine ⟨(L : ℤ), ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji
      simp only [Pi.smul_apply, periodDiagonal, zsmul_eq_mul, Int.cast_natCast, mul_one, periodBasisVector,
  zmodBasisVector, Pi.single_eq_same, nsmul_eq_mul, L]
    · have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin σ.numPeriods)) := by
        exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
      have hjdvd : σ.periods j ∣ L := by
        exact Finset.dvd_lcm (s := Finset.univ.erase i) (f := σ.periods) hjmem
      have hLzero : (L : ZMod (σ.periods j)) = 0 :=
        (ZMod.natCast_eq_zero_iff L (σ.periods j)).2 hjdvd
      simp only [Pi.smul_apply, periodDiagonal, zsmul_eq_mul, Int.cast_natCast, hLzero, mul_one, periodBasisVector,
  zmodBasisVector, ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, nsmul_zero, L]
  exact
    (QuotientAddGroup.eq_iff_sub_mem
      (N := periodRelation σ)
      (x := otherPeriodsLcm σ.toFenchelSignature i • periodBasisVector σ i)
      (y := 0)).2 (by
        simpa [periodClass, L] using hmem)

end FenchelNielsen
