import FenchelNielsenZomorrodian.Discrete.Abelianization.EllipticAbelianization
import FenchelNielsenZomorrodian.Discrete.Abelianization.PeriodQuotient
import FenchelNielsenZomorrodian.Discrete.FiniteIndex.SmoothQuotientData

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/Quotients.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact Fuchsian quotient constructions

Finite quotient constructions under abelian-period conditions for compact Fuchsian presentations.
-/

namespace FenchelNielsen

noncomputable def finiteSolvableSmoothQuotientData_one_of_lcmCondition
    (σ : FuchsianSignature)
    (hLCM : LCMCondition σ.toFenchelSignature) :
    FiniteSolvableSmoothQuotientData σ 1 where
  Q := Multiplicative (PeriodAbelianization σ)
  finite := by
    letI : Finite (PeriodAbelianization σ) := periodAbelianization_finite σ
    infer_instance
  φ := ellipticAbelianizationHom σ
  derived_length := by
    exact derivedSeries_one_eq_bot_of_commGroup
      (Multiplicative (PeriodAbelianization σ))
  elliptic_exact := by
    intro i
    simpa [ellipticAbelianizationHom_elliptic] using
      periodClass_orderOf_eq_period σ hLCM i

theorem sourceSubgroup_exists_of_lcmCondition
    (σ : FuchsianSignature) {m : ℕ} (hm : 1 ≤ m)
    (hLCM : LCMCondition σ.toFenchelSignature) :
    ∃ L : Subgroup (FuchsianPresentedGroup σ),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L m := by
  have hSubgroupOne :
      ∃ L : Subgroup (FuchsianPresentedGroup σ),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 1 :=
    (finiteSolvableSmoothQuotientData_one_of_lcmCondition σ hLCM).sourceSubgroup_exists_classical
  exact
    hasFiniteIndexTorsionFreeSubgroupWithDerivedLengthAtMost_mono
      (G := FuchsianPresentedGroup σ) (m := 1) (n := m) hm hSubgroupOne

end FenchelNielsen
