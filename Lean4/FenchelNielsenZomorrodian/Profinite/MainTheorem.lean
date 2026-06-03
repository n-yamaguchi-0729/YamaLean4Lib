import FenchelNielsenZomorrodian.Profinite.CharacteristicClosure
import FenchelNielsenZomorrodian.Profinite.CuspedQuotient
import FenchelNielsenZomorrodian.Profinite.DiscreteBridge
import FenchelNielsenZomorrodian.Profinite.LowPeriodQuotient
import FenchelNielsenZomorrodian.Profinite.PositiveGenusQuotient
import FenchelNielsenZomorrodian.Profinite.TorsionFrontier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/MainTheorem.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite Fenchel-Nielsen main theorems

This file is the public theorem entry point for the profinite Fenchel-Nielsen-Zomorrodian
formalization.
-/

namespace FenchelNielsen

universe u

namespace ProfiniteFGroup

/-- Profinite Fenchel-Nielsen existence theorem, normal-subgroup form.

Every profinite Fenchel group has a torsion-free open normal subgroup.  This theorem is not
restricted to non-perfect groups. -/
theorem exists_torsionFree_openNormalSubgroup
    (Δ : ProfiniteFGroup.{u}) :
    ∃ U : OpenNormalSubgroup Δ.carrier,
      ProfiniteOpenNormalSubgroupTorsionFree Δ.carrier U :=
  exists_torsionFreeOpenNormalSubgroup Δ

/-- Profinite Fenchel-Nielsen existence theorem, characteristic-subgroup form.

Every profinite Fenchel group has a torsion-free open characteristic subgroup.  This is the
existence-only theorem and does not assume non-perfectness. -/
theorem exists_torsionFree_openCharacteristicSubgroup
    (Δ : ProfiniteFGroup.{u}) :
    ∃ U : ProfiniteOpenCharacteristicSubgroup Δ.carrier,
      ProfiniteOpenNormalSubgroupTorsionFree Δ.carrier U.toOpenNormalSubgroup := by
  letI : CompactSpace Δ.carrier := Δ.isProfinite.compactSpace
  exact
    exists_torsionFree_openCharacteristicSubgroup_of_exists_torsionFree_openNormalSubgroup
      (G := Δ.carrier) Δ.finiteOpenSubgroupsOfIndex
      (exists_torsionFree_openNormalSubgroup Δ)

private theorem threeStep_normal_of_isNonPerfect
    (Δ : ProfiniteFGroup.{u}) :
    Δ.IsNonPerfect →
      HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost
        Δ.carrier 3 := by
  intro hNonPerfect
  by_cases hCusps : Δ.signature.HasCusps
  · exact
      ProfiniteSmoothQuotientData.has_torsionFreeOpenNormal_quotient_derivedLength_le
        (cuspedSmoothQuotientData Δ hCusps) (by decide : 1 ≤ 3)
  · have hCompact : Δ.signature.IsCompact := by
      dsimp [FenchelSignature.HasCusps, FenchelSignature.IsCompact] at hCusps ⊢
      omega
    by_cases hGenus : 1 ≤ Δ.signature.orbitGenus
    · exact
        ProfiniteSmoothQuotientData.has_torsionFreeOpenNormal_quotient_derivedLength_le
          (positiveGenusSmoothQuotientData Δ hGenus) (by decide : 2 ≤ 3)
    · have hZero : Δ.signature.orbitGenus = 0 := by omega
      by_cases hPeriods : 3 ≤ Δ.signature.numPeriods
      · exact
          compactDiscreteBridge_threeStep_normal_of_isNonPerfect
            Δ hNonPerfect hCompact hZero hPeriods
      · have hTwo :
            Δ.signature.numPeriods = 2 :=
          numPeriods_eq_two_of_isNonPerfect_zeroGenus_noCusps_not_three
            Δ hNonPerfect hZero hCompact hPeriods
        exact
          ProfiniteSmoothQuotientData.has_torsionFreeOpenNormal_quotient_derivedLength_le
            (twoPeriodCyclicSmoothQuotientData Δ hCompact hZero hTwo) (by decide : 1 ≤ 3)

/-- Normal-subgroup form of the non-perfect three-step Fenchel-Nielsen theorem. -/
theorem exists_openNormal_torsionFree_dl_le_three_of_nonperfect
    (Δ : ProfiniteFGroup.{u}) :
    Δ.IsNonPerfect →
      HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost
        Δ.carrier 3 :=
  threeStep_normal_of_isNonPerfect Δ

/-- Characteristic-subgroup form of the non-perfect three-step Fenchel-Nielsen theorem. -/
theorem exists_openChar_torsionFree_dl_le_three_of_nonperfect
    (Δ : ProfiniteFGroup.{u}) :
    Δ.IsNonPerfect →
      HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost
        Δ.carrier 3 := by
  intro hNonPerfect
  letI : CompactSpace Δ.carrier := Δ.isProfinite.compactSpace
  exact
    hasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost_of_normal
      (G := Δ.carrier) Δ.finiteOpenSubgroupsOfIndex
      (threeStep_normal_of_isNonPerfect Δ hNonPerfect)

end ProfiniteFGroup

end FenchelNielsen
