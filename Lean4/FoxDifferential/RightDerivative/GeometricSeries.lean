import FoxDifferential.Discrete.GroupRing
import Mathlib.Algebra.Ring.GeomSum

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/RightDerivative/GeometricSeries.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Right Fox derivatives

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable def geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    FoxDifferential.GroupRing A :=
  ∑ k ∈ Finset.range n, MonoidAlgebra.of ℤ A (a ^ k)

theorem geomSeries_eq_sum_pow {A : Type*} [Group A] (a : A) (n : ℕ) :
    geomSeries a n = ∑ k ∈ Finset.range n,
      (MonoidAlgebra.of ℤ A a : FoxDifferential.GroupRing A) ^ k := by
  simp only [geomSeries, map_pow, MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, one_pow]

@[simp]
theorem geomSeries_zero {A : Type*} [Group A] (a : A) :
    geomSeries a 0 = 0 := by
  simp only [geomSeries, Finset.range_zero, MonoidAlgebra.of_apply, Finset.sum_empty]

@[simp]
theorem geomSeries_one {A : Type*} [Group A] (a : A) :
    geomSeries a 1 = 1 := by
  simpa [geomSeries] using (FoxDifferential.groupRing_of_one (H := A))

@[simp]
theorem augmentation_geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    FoxDifferential.augmentation A (geomSeries a n) = n := by
  simp only [augmentation, augmentationAlgHom, AlgHom.toRingHom_eq_coe, geomSeries, MonoidAlgebra.of_apply,
  map_sum, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, Int.zsmul_eq_mul, mul_one,
  Finset.sum_const, Finset.card_range, Int.nsmul_eq_mul]

theorem geomSeries_ne_zero_of_nat_ne_zero {A : Type*} [Group A]
    (a : A) {n : ℕ} (hn : n ≠ 0) :
    geomSeries a n ≠ 0 := by
  intro hzero
  have haug := congrArg (FoxDifferential.augmentation A) hzero
  rw [augmentation_geomSeries] at haug
  simp only [map_zero, Int.natCast_eq_zero] at haug
  exact hn haug

theorem geomSeries_succ_eq_add_pow {A : Type*} [Group A] (a : A) (n : ℕ) :
    geomSeries a (n + 1) =
      geomSeries a n + MonoidAlgebra.of ℤ A (a ^ n) := by
  simp only [geomSeries, Finset.range_add_one, MonoidAlgebra.of_apply, Finset.mem_range, lt_self_iff_false,
  not_false_eq_true, Finset.sum_insert, add_comm]

theorem geomSeries_add {A : Type*} [CommGroup A] (a : A) (m n : ℕ) :
    geomSeries a (m + n) =
      geomSeries a m + MonoidAlgebra.of ℤ A (a ^ m) * geomSeries a n := by
  induction n with
  | zero =>
      simp only [add_zero, MonoidAlgebra.of_apply, geomSeries_zero, mul_zero]
  | succ n ih =>
      rw [Nat.add_succ, geomSeries_succ_eq_add_pow, ih, geomSeries_succ_eq_add_pow]
      rw [mul_add]
      simp only [MonoidAlgebra.of_apply, pow_add, MonoidAlgebra.single_mul_single, mul_one]
      ring

theorem geomSeries_succ_eq_mul_add_one {A : Type*} [Group A] (a : A) (n : ℕ) :
    geomSeries a (n + 1) =
      geomSeries a n * MonoidAlgebra.of ℤ A a + 1 := by
  rw [geomSeries_eq_sum_pow, geomSeries_eq_sum_pow]
  let x : FoxDifferential.GroupRing A := MonoidAlgebra.of ℤ A a
  have h := geom_sum_succ (x := MulOpposite.op x) (n := n)
  have h2 := congrArg MulOpposite.unop h
  dsimp [x] at h2
  simpa using h2

theorem one_sub_pow_eq_one_sub_mul_geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    (1 - MonoidAlgebra.of ℤ A (a ^ n) : FoxDifferential.GroupRing A) =
      (1 - MonoidAlgebra.of ℤ A a) * geomSeries a n := by
  rw [geomSeries_eq_sum_pow]
  simpa [map_pow] using
    (mul_neg_geom_sum (MonoidAlgebra.of ℤ A a : FoxDifferential.GroupRing A) n).symm

theorem pow_sub_one_eq_sub_one_mul_geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    (MonoidAlgebra.of ℤ A (a ^ n) - 1 : FoxDifferential.GroupRing A) =
      (MonoidAlgebra.of ℤ A a - 1) * geomSeries a n := by
  rw [geomSeries_eq_sum_pow]
  simpa [map_pow] using
    (mul_geom_sum (MonoidAlgebra.of ℤ A a : FoxDifferential.GroupRing A) n).symm

end FoxDifferential
