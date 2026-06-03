import FenchelNielsenZomorrodian.Discrete.FiniteIndex.Smooth
import FenchelNielsenZomorrodian.Discrete.Torsion.CompactFiniteOrder

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/FiniteIndex/SmoothQuotientData.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Smooth quotient data for finite-index compact Fuchsian constructions

Abbreviates the generic smooth quotient package for compact Fuchsian presentations and records the
source-subgroup existence theorem consumed by the profinite Fenchel-Nielsen bridge.
-/

namespace FenchelNielsen

/-!
# Smooth quotient data for compact Fuchsian presentations

The compact specialization keeps only the abbreviation and the source-subgroup existence theorem
that is actually consumed downstream.  Generic kernel, finite-index, and torsion-free wrappers are
available from `SmoothQuotientData` and are no longer repeated here.
-/

abbrev FiniteSolvableSmoothQuotientData
    (σ : FuchsianSignature) (m : ℕ) :=
  SmoothQuotientData
    (FuchsianPresentedGroup σ)
    (Fin σ.numPeriods)
    σ.periods
    (ellipticElement σ)
    m

namespace FiniteSolvableSmoothQuotientData

/-- The finite smooth quotient kernel gives the finite-index torsion-free subgroup consumed by the
compact proof route.  The only nonlocal input is the approved finite-subgroup torsion frontier. -/
theorem sourceSubgroup_exists_classical
    {σ : FuchsianSignature} {m : ℕ}
    (D : FiniteSolvableSmoothQuotientData σ m) :
    ∃ L : Subgroup (FuchsianPresentedGroup σ),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L m :=
  SmoothQuotientData.sourceSubgroup_exists_of_finiteOrderClassification
    D
    (fun i _n hdiv => ellipticElement_zpow_eq_one_of_period_int_dvd σ i hdiv)
    (finiteOrder_eq_one_or_isConj_elliptic_zpow σ)

end FiniteSolvableSmoothQuotientData

end FenchelNielsen
