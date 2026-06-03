import CrowellExactSequence.Profinite.BlanchfieldLyndon

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/MainTheorem.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite Crowell main theorems

This file is the paper-facing entry point for the profinite main statements.  The conclusions
are packaged as four-term exact sequences for the separated completed Crowell sequence and its
finite-coordinate Blanchfield--Lyndon forms.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {ProC : ProCGroupPredicate.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass]

/-- The separated completed Crowell exact sequence over pro-`C` integer coefficients, packaged
as the full four-term exact sequence
`N^ab(C) -> A_psi(C) -> Z_C[[H]] -> Z_C`. -/
theorem profiniteSeparatedCrowellExactSequence
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    IsFourTermExactSequence
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi)
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
        (ProCGroupPredicate.finiteQuotientHereditary ProC) psi)
      (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) := by
  exact
    freeProC_presentedSepCrowellZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi

/-- The separated completed Blanchfield--Lyndon exact sequence in the universe-lifted finite
coordinate basis, packaged as the full four-term exact sequence. -/
theorem profiniteSeparatedBlanchfieldLyndonExactSequence
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    IsFourTermExactSequence
      (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
            ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
      (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) := by
  exact
    freeProC_presentedSepBLZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi

/-- The separated completed Blanchfield--Lyndon exact sequence in the concrete `Fin r`
coordinate basis, packaged as the full four-term exact sequence. -/
theorem profiniteSeparatedBlanchfieldLyndonFinExactSequence
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    IsFourTermExactSequence
      (freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun i : Fin r =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
            ((freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
      (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) := by
  exact
    freeProC_presentedSepBLFinZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi

end

end CrowellExactSequence
