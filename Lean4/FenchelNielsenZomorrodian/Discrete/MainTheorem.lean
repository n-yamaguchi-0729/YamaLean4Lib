import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.PeriodOne.SourceSubgroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/MainTheorem.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Fenchel-Nielsen main theorem

This file is the public theorem entry point for the discrete compact Fuchsian part used by the
profinite Fenchel-Nielsen bridge.
-/

namespace FenchelNielsen

/-- Zero-genus compact three-step construction from explicit period data.

This is the proof-carrying discrete main theorem used by the profinite bridge.  It avoids
re-running the perfectness-to-period-data conversion when the profinite side has already produced
the required shared-prime pair. -/
theorem threeStep_sourceSubgroup_exists_of_zeroGenus_periodData
    (σ : FuchsianSignature)
    (hZero : σ.orbitGenus = 0)
    (D : FirstReductionPeriodData σ) :
    ∃ L : Subgroup (FuchsianPresentedGroup σ),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 3 := by
  classical
  let secondPrime : FirstKernelTailPrimeDivisorData D := D.tailPrimeDivisorData
  let E : SecondStageCleanupPeriodData D secondPrime :=
    secondStageCleanupPeriodDataOfTailPrime D secondPrime
  let sourceEquiv₀ :
      FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup D.sourceSignature :=
    Classical.choice (firstReductionSourceMulEquiv_exists D hZero)
  by_cases hStrict : 2 ≤ D.m₁' ∧ 2 ≤ D.m₂' ∧ 2 ≤ E.m₃'
  · have hStrictSubgroup :
        ∃ L : Subgroup (FuchsianPresentedGroup E.sourceSignature),
          L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
            SubgroupQuotientHasDerivedLengthAtMost L 3 :=
      E.sourceSubgroup_exists_of_canonicalReductions
        hStrict.1 hStrict.2.1 hStrict.2.2
    let sourceEquiv₁ :
        FuchsianPresentedGroup D.sourceSignature ≃*
          FuchsianPresentedGroup E.sourceSignature :=
      Classical.choice (secondStageCleanupSourceMulEquiv_exists E)
    let sourceEquiv :
        FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup E.sourceSignature :=
      sourceEquiv₀.trans sourceEquiv₁
    exact sourceSubgroup_exists_of_mulEquiv sourceEquiv hStrictSubgroup
  · have hPeriodOne :
        D.m₁' = 1 ∨ D.m₂' = 1 ∨ E.m₃' = 1 :=
      E.periodOne_of_not_strict hStrict
    have hSubgroup :
        ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
          L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
            SubgroupQuotientHasDerivedLengthAtMost L 3 := by
      rcases hPeriodOne with hm₁' | hm₂' | hm₃'
      · exact
          firstReductionSourceSubgroup_leftPeriodOne_exists
            D hm₁'
      · exact
          firstReductionSourceSubgroup_rightPeriodOne_exists
            D hm₂'
      · have hquot : D.tail secondPrime.k / secondPrime.q = 1 := by
          simpa [E, secondStageCleanupPeriodDataOfTailPrime] using hm₃'
        exact
          firstReductionSourceSubgroup_tailPrimeQuotientOne_exists
            D (by simpa [secondPrime] using hquot)
    exact sourceSubgroup_exists_of_mulEquiv sourceEquiv₀ hSubgroup

end FenchelNielsen
