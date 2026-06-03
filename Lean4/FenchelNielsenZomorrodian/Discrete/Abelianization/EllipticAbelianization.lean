import FenchelNielsenZomorrodian.Discrete.Abelianization.PeriodClassOrder
import FenchelNielsenZomorrodian.Discrete.Core.EllipticCompact
import FenchelNielsenZomorrodian.Discrete.Core.EllipticQuotientHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Abelianization/EllipticAbelianization.lean
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

def ellipticAbelianizationHom (σ : FuchsianSignature) :
    FuchsianPresentedGroup σ →* Multiplicative (PeriodAbelianization σ) :=
  ellipticQuotientHom σ
    (fun i => Multiplicative.ofAdd (periodClass σ i))
    (by
      intro i
      simpa using congrArg Multiplicative.ofAdd (periodClass_nsmul_eq_zero σ i))
    (by
      simpa using congrArg Multiplicative.ofAdd (sum_periodClass_eq_zero σ))

@[simp] theorem ellipticAbelianizationHom_elliptic
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    ellipticAbelianizationHom σ (ellipticElement σ i) =
      Multiplicative.ofAdd (periodClass σ i) := by
  simp only [ellipticAbelianizationHom, ellipticElement, ellipticQuotientHom_elliptic]

theorem ellipticAbelianizationHom_elliptic_order_eq_period_iff
    {σ : FuchsianSignature} {i : Fin σ.numPeriods} :
    orderOf (ellipticAbelianizationHom σ (ellipticElement σ i)) = σ.periods i ↔
      σ.periods i ∣ otherPeriodsLcm σ.toFenchelSignature i := by
  rw [ellipticAbelianizationHom_elliptic]
  exact periodClass_orderOf_eq_period_iff (σ := σ) (i := i)

theorem ellipticAbelianizationHom_elliptic_orders_eq_periods_iff_lcmCondition
    {σ : FuchsianSignature} :
    (∀ i : Fin σ.numPeriods,
      orderOf (ellipticAbelianizationHom σ (ellipticElement σ i)) = σ.periods i) ↔
      LCMCondition σ.toFenchelSignature := by
  constructor
  · intro h i
    exact (ellipticAbelianizationHom_elliptic_order_eq_period_iff (σ := σ) (i := i)).1 (h i)
  · intro h i
    exact (ellipticAbelianizationHom_elliptic_order_eq_period_iff (σ := σ) (i := i)).2 (h i)

theorem commHom_ellipticElement_pow_otherPeriodsLcm_eq_one
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (φ : FuchsianPresentedGroup σ →* A) (i : Fin σ.numPeriods) :
    φ (ellipticElement σ i) ^ otherPeriodsLcm σ.toFenchelSignature i = 1 := by
  let ξ : Fin σ.numPeriods → A := fun j => φ (ellipticElement σ j)
  have hpow : ∀ j : Fin σ.numPeriods, ξ j ^ σ.periods j = 1 := by
    intro j
    change φ (ellipticElement σ j) ^ σ.periods j = 1
    rw [← map_pow, ellipticElement_pow_period_eq_one, map_one]
  have hprod : ∏ j : Fin σ.numPeriods, ξ j = 1 := by
    have hrel :
        (∏ j : Fin σ.numPeriods, ξ j) *
            (∏ j : Fin σ.orbitGenus,
              φ ⁅PresentedGroup.of (rels := relators σ) (FuchsianGenerator.surfaceA j),
                PresentedGroup.of (rels := relators σ) (FuchsianGenerator.surfaceB j)⁆)
          = 1 := by
      simpa [ξ, totalRelation, xWord, aWord, bWord, ellipticElement,
        Fin.prod_univ_def, MonoidHom.map_mul, MonoidHom.map_list_prod] using
        congrArg φ
          (PresentedGroup.one_of_mem (rels := relators σ)
            (x := totalRelation σ) (Or.inr rfl))
    have hcomm :
        ∏ j : Fin σ.orbitGenus,
            φ ⁅PresentedGroup.of (rels := relators σ) (FuchsianGenerator.surfaceA j),
              PresentedGroup.of (rels := relators σ) (FuchsianGenerator.surfaceB j)⁆
          = 1 := by
      refine Finset.prod_eq_one ?_
      intro j hj
      simpa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] using
        (mul_comm
          (φ (PresentedGroup.of (rels := relators σ) (FuchsianGenerator.surfaceA j)))
          (φ (PresentedGroup.of (rels := relators σ) (FuchsianGenerator.surfaceB j))))
    rw [hcomm, mul_one] at hrel
    exact hrel
  let L := otherPeriodsLcm σ.toFenchelSignature i
  have hsplit' : ((Finset.univ.erase i).prod ξ) * ξ i = 1 := by
    calc
      ((Finset.univ.erase i).prod ξ) * ξ i = ∏ j, ξ j := by
        exact Finset.prod_erase_mul (s := Finset.univ) (f := ξ) (a := i) (Finset.mem_univ i)
      _ = 1 := hprod
  have hsplit : ξ i * ((Finset.univ.erase i).prod ξ) = 1 := by
    simpa [mul_comm] using hsplit'
  have hOthers :
      ((Finset.univ.erase i).prod ξ) ^ L = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one ?_
    intro j hj
    obtain ⟨m, hm⟩ := Finset.dvd_lcm (s := Finset.univ.erase i) (f := σ.periods) hj
    rw [show L = σ.periods j * m by simpa [L, otherPeriodsLcm] using hm,
      pow_mul, hpow j, one_pow]
  have hPow : ξ i ^ L = 1 := by
    have hsplitPow := congrArg (fun a : A => a ^ L) hsplit
    simp only at hsplitPow
    rw [mul_pow, hOthers, mul_one] at hsplitPow
    simpa [L] using hsplitPow
  simpa [ξ, L] using hPow

theorem orderOf_commHom_ellipticElement_dvd_otherPeriodsLcm
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (φ : FuchsianPresentedGroup σ →* A) (i : Fin σ.numPeriods) :
    orderOf (φ (ellipticElement σ i)) ∣
      otherPeriodsLcm σ.toFenchelSignature i :=
  orderOf_dvd_of_pow_eq_one
    (commHom_ellipticElement_pow_otherPeriodsLcm_eq_one σ φ i)

theorem lcmCondition_of_commHom_elliptic_exact
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (φ : FuchsianPresentedGroup σ →* A)
    (hell : ∀ i : Fin σ.numPeriods,
      orderOf (φ (ellipticElement σ i)) = σ.periods i) :
    LCMCondition σ.toFenchelSignature := by
  intro i
  simpa [hell i] using
    orderOf_commHom_ellipticElement_dvd_otherPeriodsLcm σ φ i

end FenchelNielsen
