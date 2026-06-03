import Mathlib.Data.ZMod.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Coordinates/ZModFamily.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite coordinate systems for Fenchel periods

ZMod coordinate families and Fenchel period-coordinate sums used to define finite quotient maps on period generators.
-/

namespace FenchelNielsen

abbrev ZModCoordinateFamily {ι : Type*} (periods : ι → ℕ) :=
  ∀ i : ι, ZMod (periods i)

def zmodBasisVector {ι : Type*} [DecidableEq ι] (periods : ι → ℕ) (i : ι) :
    ZModCoordinateFamily periods :=
  Pi.single i (1 : ZMod (periods i))

theorem zmodBasisVector_nsmul_eq_zero
    {ι : Type*} [DecidableEq ι] (periods : ι → ℕ) (i : ι) :
    periods i • zmodBasisVector periods i = 0 := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp only [zmodBasisVector, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  Pi.zero_apply]
  · simp only [zmodBasisVector, Pi.smul_apply, ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, nsmul_zero,
  Pi.zero_apply]

theorem zmodBasisVector_addOrderOf
    {ι : Type*} [DecidableEq ι] (periods : ι → ℕ) (i : ι) :
    addOrderOf (zmodBasisVector periods i) = periods i := by
  apply Nat.dvd_antisymm
  · exact (addOrderOf_dvd_iff_nsmul_eq_zero).2
      (zmodBasisVector_nsmul_eq_zero periods i)
  · let π : ZModCoordinateFamily periods →+ ZMod (periods i) :=
      { toFun := fun v => v i
        map_zero' := rfl
        map_add' := by
          intro x y
          rfl }
    have hmap :
        π (zmodBasisVector periods i) = (1 : ZMod (periods i)) := by
      simp only [zmodBasisVector, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_eq_same, π]
    have hdiv := addOrderOf_map_dvd π (zmodBasisVector periods i)
    rw [hmap, ZMod.addOrderOf_one] at hdiv
    exact hdiv

theorem zmodBasisVector_pair_neg_addOrderOf
    {ι : Type*} [DecidableEq ι] (periods : ι → ℕ) (i : ι) :
    addOrderOf (zmodBasisVector periods i, -zmodBasisVector periods i) =
      periods i := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    ext j
    · exact congrFun (zmodBasisVector_nsmul_eq_zero periods i) j
    · simp only [Prod.smul_mk, smul_neg, Pi.neg_apply, congrFun (zmodBasisVector_nsmul_eq_zero periods i) j,
  Pi.zero_apply, neg_zero, Prod.snd_zero]
  · let π : (ZModCoordinateFamily periods × ZModCoordinateFamily periods) →+
        ZMod (periods i) :=
      { toFun := fun v => (v.1 : ZModCoordinateFamily periods) i
        map_zero' := rfl
        map_add' := by
          intro x y
          rfl }
    have hmap :
        π (zmodBasisVector periods i, -zmodBasisVector periods i) =
          (1 : ZMod (periods i)) := by
      simp only [zmodBasisVector, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_eq_same, π]
    have hdiv := addOrderOf_map_dvd π
      (zmodBasisVector periods i, -zmodBasisVector periods i)
    rw [hmap, ZMod.addOrderOf_one] at hdiv
    exact hdiv

noncomputable def zmodCoordinateFamily_finite
    {ι : Type*} [Fintype ι] (periods : ι → ℕ) (hpos : ∀ i, 0 < periods i) :
    Finite (ZModCoordinateFamily periods) := by
  classical
  letI (i : ι) : NeZero (periods i) := ⟨ne_of_gt (hpos i)⟩
  letI (i : ι) : Fintype (ZMod (periods i)) := ZMod.fintype (periods i)
  exact Finite.of_fintype (ZModCoordinateFamily periods)

end FenchelNielsen
