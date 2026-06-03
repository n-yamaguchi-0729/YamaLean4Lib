import CrowellExactSequence.Profinite.FreeExactness

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/BlanchfieldLyndon.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C Blanchfield--Lyndon over pro-C integer coefficients

BL is only the finite-basis coordinate expression of the displayed Crowell sequence

```text
N^ab(C) -> A_psi(C) -> Z_C[[H]] -> Z_C.
```

This file transports exactness through the chosen finite basis of `A_psi(C)`.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {ProC : ProCGroupPredicate.{u}}

/-- The BL first map: take the genuine `d_N : N^ab(C) -> A_psi(C)` and read it in the chosen
finite basis coordinates of `A_psi(C)`. -/
def freeProCBlanchfieldLyndonBoundaryProCInteger
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
        (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis))
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi) :
    ProCKernelAbelianizationAdd ProC psi →
      Fin r → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H :=
  fun x =>
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
      (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) hbasis_A
      (profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi hwell_dN x)

/-- Exactness at the Crowell middle term is equivalent to exactness at the finite
Blanchfield--Lyndon coordinate middle term, once the chosen family is a basis of
`A_psi(C)`.

In paper language, this is only the change of coordinates
`A_psi(C) ≃ Z_C[[H]]^r`; it does not change the kernel/image statement. -/
theorem freeProC_exactAtA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
        (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis))
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi) :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi hwell_dN)
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi) ↔
      Function.Exact
        (freeProCBlanchfieldLyndonBoundaryProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi hbasis_A hwell_dN)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
          (fun i : Fin r =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
              ((freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i))) := by
  let family : Fin r → sourceData.carrier :=
    freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi hwell_dN
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi family hbasis_A
  let delta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun i : Fin r =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi (family i))
  have hblDelta_comp : delta.comp coords.symm.toLinearMap = blDelta := by
    rw [presentedCompletedDifferentialFamilyCoordinatesProCInteger_symm_toLinearMap]
    exact
      presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi family
  have hblDelta_apply (y) : blDelta y = delta (coords.symm y) := by
    have h := congrArg (fun f => f y) hblDelta_comp
    simpa [LinearMap.comp_apply] using h.symm
  change
    Function.Exact dN delta ↔
      Function.Exact (fun x => coords (dN x)) blDelta
  constructor
  · intro hexact_A y
    constructor
    · intro hy
      have hy_delta : delta (coords.symm y) = 0 := by
        simpa [hblDelta_apply y] using hy
      rcases (hexact_A (coords.symm y)).1 hy_delta with ⟨x, hx⟩
      exact ⟨x, by simpa using congrArg coords hx⟩
    · rintro ⟨x, rfl⟩
      have hker : delta (dN x) = 0 :=
        (hexact_A (dN x)).2 ⟨x, rfl⟩
      calc
        blDelta (coords (dN x)) = delta (coords.symm (coords (dN x))) :=
          hblDelta_apply (coords (dN x))
        _ = delta (dN x) := by rw [coords.symm_apply_apply]
        _ = 0 := hker
  · intro hexact_BL y
    constructor
    · intro hy
      have hy_bl : blDelta (coords y) = 0 := by
        calc
          blDelta (coords y) = delta (coords.symm (coords y)) :=
            hblDelta_apply (coords y)
          _ = delta y := by rw [coords.symm_apply_apply]
          _ = 0 := hy
      rcases (hexact_BL (coords y)).1 hy_bl with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply coords.injective
      simpa using hx
    · rintro ⟨x, rfl⟩
      have hbl : blDelta (coords (dN x)) = 0 :=
        (hexact_BL (coords (dN x))).2 ⟨x, rfl⟩
      calc
        delta (dN x) = delta (coords.symm (coords (dN x))) := by
          rw [coords.symm_apply_apply]
        _ = blDelta (coords (dN x)) := by
          rw [hblDelta_apply]
        _ = 0 := hbl

/-- The separated BL first map: take `d_N^sep` and read it in the separated chosen coordinates. -/
def freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProCKernelAbelianizationAdd ProC psi →
      ZCFreeFoxCoordinates ProC.finiteQuotientClass
        (X := ULift.{u} (Fin r)) (H := H) :=
  fun x =>
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi x)

/-- Exactness at the separated Crowell middle term is equivalent to exactness at the finite
Blanchfield--Lyndon coordinate middle term for the separated coordinate equivalence. -/
theorem freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
          (ProCGroupPredicate.finiteQuotientHereditary ProC) psi) ↔
      Function.Exact
        (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
          (fun i : ULift.{u} (Fin r) =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
              ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i))) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
      (ProCGroupPredicate.finiteQuotientHereditary ProC) psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi (family i))
  have hcoords_symm :
      coords.symm.toLinearMap =
        freeProCChosenULift_sepFamilyMap
          (H := H) (ProC := ProC) sourceData hbasis psi := by
    rfl
  have hblDelta_comp : delta.comp coords.symm.toLinearMap = blDelta := by
    rw [hcoords_symm]
    exact
      presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
        (ProCGroupPredicate.finiteQuotientHereditary ProC) psi family
  have hblDelta_apply (y) : blDelta y = delta (coords.symm y) := by
    have h := congrArg (fun f => f y) hblDelta_comp
    simpa [LinearMap.comp_apply] using h.symm
  change
    Function.Exact dN delta ↔
      Function.Exact (fun x => coords (dN x)) blDelta
  constructor
  · intro hexact_A y
    constructor
    · intro hy
      have hy_delta : delta (coords.symm y) = 0 := by
        simpa [hblDelta_apply y] using hy
      rcases (hexact_A (coords.symm y)).1 hy_delta with ⟨x, hx⟩
      exact ⟨x, by simpa using congrArg coords hx⟩
    · rintro ⟨x, rfl⟩
      have hker : delta (dN x) = 0 :=
        (hexact_A (dN x)).2 ⟨x, rfl⟩
      calc
        blDelta (coords (dN x)) = delta (coords.symm (coords (dN x))) :=
          hblDelta_apply (coords (dN x))
        _ = delta (dN x) := by rw [coords.symm_apply_apply]
        _ = 0 := hker
  · intro hexact_BL y
    constructor
    · intro hy
      have hy_bl : blDelta (coords y) = 0 := by
        calc
          blDelta (coords y) = delta (coords.symm (coords y)) :=
            hblDelta_apply (coords y)
          _ = delta y := by rw [coords.symm_apply_apply]
          _ = 0 := hy
      rcases (hexact_BL (coords y)).1 hy_bl with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply coords.injective
      simpa using hx
    · rintro ⟨x, rfl⟩
      have hbl : blDelta (coords (dN x)) = 0 :=
        (hexact_BL (coords (dN x))).2 ⟨x, rfl⟩
      calc
        delta (dN x) = delta (coords.symm (coords (dN x))) := by
          rw [coords.symm_apply_apply]
        _ = blDelta (coords (dN x)) := (hblDelta_apply (coords (dN x))).symm
        _ = 0 := hbl

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass]

/-- BL exactness at `Z_C[[H]]`, supplied by a finite free basis and surjectivity of `psi`. -/
theorem freeProC_presentedBlanchfieldLyndonGAExactZC_of_psi_surj
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun i : Fin r =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
            ((freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
      (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass) :=
    ⟨by
      intro Q _ hQ
      exact ProCGroupPredicate.finiteQuotientFinite ProC hQ⟩
  let family : Fin r → sourceData.carrier :=
    freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  have htargetGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : Fin r => psi (family i))) := by
    simpa [family] using
      freeProCChosenFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  simpa [family] using
    exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
      (ProCGroupPredicate.finiteQuotientFormation ProC) psi family htargetGen

/-- Separated-coordinate BL exactness at `Z_C[[H]]`, supplied by a finite free basis and
surjectivity of `psi`. -/
theorem freeProC_presentedSepBlanchfieldLyndonGAExactZC_of_psi_surj
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
            ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
      (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass) :=
    ⟨by
      intro Q _ hQ
      exact ProCGroupPredicate.finiteQuotientFinite ProC hQ⟩
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  have htargetGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : ULift.{u} (Fin r) => psi (family i))) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  simpa [family] using
    exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
      (ProCGroupPredicate.finiteQuotientFormation ProC) psi family htargetGen

/-- Separated-coordinate BL exactness from the standard all-finite-quotient stage family and
surjectivity of `psi`.

This is the public separated Blanchfield-Lyndon assembly theorem.  The separated Crowell
middle-exactness input is proved internally from the all-finite stage family. -/
theorem freeProC_presentedSepBLZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    IsBlanchfieldLyndonExactSequence
        (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
          (fun i : ULift.{u} (Fin r) =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
              ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
        (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) :=
by
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
          ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i))
  have hinj_dN :
      Function.Injective dN :=
    freeProC_profKerAbBoundaryAddZCSep_inj_of_continuousMagnus
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  have hexact_A :
      Function.Exact dN
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
          (ProCGroupPredicate.finiteQuotientHereditary ProC) psi) :=
    freeProC_exactAtSepA_of_continuousMagnus_zcBifilteredAllFiniteQuotientStages
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  have hexact_BL_A :
      Function.Exact
          (fun x : ProCKernelAbelianizationAdd ProC psi => coords (dN x))
          blDelta :=
    (freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi).1 hexact_A
  change
    IsBlanchfieldLyndonExactSequence
      (fun x : ProCKernelAbelianizationAdd ProC psi => coords (dN x)) blDelta
      (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H)
  refine ⟨?_, hexact_BL_A, ?_, ?_⟩
  · intro x y hxy
    exact hinj_dN (coords.injective hxy)
  · exact
      freeProC_presentedSepBlanchfieldLyndonGAExactZC_of_psi_surj
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  · exact
      zcCompletedGroupAlgebraAugmentation_surjective
        (C := ProC.finiteQuotientClass) (H := H)

/-- The canonical equivalence from concrete finite coordinates to the universe-lifted copy used by
the free pro-`C` universal property. -/
def finULiftEquiv (r : Nat) : Fin r ≃ ULift.{u} (Fin r) where
  toFun i := ULift.up i
  invFun i := i.down
  left_inv := by
    intro i
    rfl
  right_inv := by
    intro i
    cases i
    rfl

/-- The separated BL first map in the concrete `Fin r` basis.  It is the public separated
coordinate map reindexed back from the universe-lifted finite basis. -/
def freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProCKernelAbelianizationAdd ProC psi →
      Fin r → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H :=
  let e : Fin r ≃ ULift.{u} (Fin r) := finULiftEquiv r
  fun x =>
    (piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) e).symm
      (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi x)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- Exactness at the separated Crowell middle term is equivalent to exactness at the concrete
`Fin r` Blanchfield--Lyndon coordinate middle term. -/
theorem freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtFinCoordinatesProCInteger
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
          (ProCGroupPredicate.finiteQuotientHereditary ProC) psi) ↔
      Function.Exact
        (freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
          (fun i : Fin r =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
              ((freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i))) := by
  let e : Fin r ≃ ULift.{u} (Fin r) := finULiftEquiv r
  let L :
      (Fin r → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) ≃ₗ[
        ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
        (ULift.{u} (Fin r) →
          ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) :=
    piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) e
  let blULift :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
          ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i))
  let blFin :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun i : Fin r =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
          ((freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i))
  have hblFin :
      blFin = blULift.comp L.toLinearMap := by
    simpa [blFin, blULift, L, e, finULiftEquiv, freeProCChosenULiftFamilyOfBasisCard] using
      (finiteFamilyLinearMap_reindex
        (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        e
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
            ((freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
  have hULiftIff :=
    freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  have htransport :
      Function.Exact
          (fun x : ProCKernelAbelianizationAdd ProC psi =>
            L.symm
              (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
                (H := H) (ProC := ProC) sourceData hbasis psi hpsi x))
          (fun y : Fin r → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H =>
            blULift (L y)) ↔
        Function.Exact
          (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
            (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
          blULift :=
    Function.Exact.linearEquiv_symm_comp_comp_iff
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) L
  change
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
          (ProCGroupPredicate.finiteQuotientHereditary ProC) psi) ↔
      Function.Exact
        (fun x : ProCKernelAbelianizationAdd ProC psi =>
          L.symm
            (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
              (H := H) (ProC := ProC) sourceData hbasis psi hpsi x))
        blFin
  rw [hblFin]
  exact hULiftIff.trans htransport.symm

/-- Concrete `Fin r` separated-coordinate BL exactness from the standard all-finite-quotient stage
family and surjectivity of `psi`.

This is the same theorem as
`freeProC_presentedSepBLZC_of_continuousMagnus_zcBiAllStages_of_psi_surj`,
transported through the finite reindexing equivalence `Fin r ≃ ULift (Fin r)`.  It leaves no
closedness, coordinate-injectivity, algebraic-basis, `d_N` well-definedness, or middle-exactness
inputs in the statement. -/
theorem freeProC_presentedSepBLFinZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    IsBlanchfieldLyndonExactSequence
        (freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi hpsi)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
          (fun i : Fin r =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
              ((freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) i)))
        (zcCompletedGroupAlgebraAugmentation ProC.finiteQuotientClass H) :=
by
  let e : Fin r ≃ ULift.{u} (Fin r) := finULiftEquiv r
  let L :
      (Fin r → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) ≃ₗ[
        ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
        (ULift.{u} (Fin r) →
          ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) :=
    piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) e
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  have hinj_dN :
      Function.Injective dN :=
    freeProC_profKerAbBoundaryAddZCSep_inj_of_continuousMagnus
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  have hexact_A :
      Function.Exact dN
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass
          (ProCGroupPredicate.finiteQuotientHereditary ProC) psi) :=
    freeProC_exactAtSepA_of_continuousMagnus_zcBifilteredAllFiniteQuotientStages
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    change L.symm (coords (dN x)) = L.symm (coords (dN y)) at hxy
    exact hinj_dN (coords.injective (L.symm.injective hxy))
  · exact
      (freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtFinCoordinatesProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi).1 hexact_A
  · exact
      freeProC_presentedBlanchfieldLyndonGAExactZC_of_psi_surj
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi
  · exact
      zcCompletedGroupAlgebraAugmentation_surjective
        (C := ProC.finiteQuotientClass) (H := H)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- The `ULift (Fin r)` display of the chosen free basis has the completed differential basis
property whenever the concrete `Fin r` display does. -/
theorem freeProCChosenULiftFamilyOfBasisCard_hbasis_A_of_chosenFamily_hbasis_A
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
        (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis)) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
      (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) := by
  let e : ULift.{u} (Fin r) ≃ Fin r :=
    { toFun := fun i => i.down
      invFun := fun i => ULift.up i
      left_inv := by
        intro i
        cases i
        rfl
      right_inv := by
        intro i
        rfl }
  change
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
      (fun i : ULift.{u} (Fin r) =>
        freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis (e i))
  exact
    isPresentedCompletedDifferentialFamilyBasisProCInteger_reindex
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi e
      (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis)
      hbasis_A

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- The finite `Fin r` display inherits the `A_psi(C)` basis from the universe-lifted chosen
family. -/
theorem freeProCChosenFamilyOfBasisCard_hbasis_A_of_chosenULiftFamily_hbasis_A
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
        (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis)) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
      (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) := by
  let e : Fin r ≃ ULift.{u} (Fin r) :=
    { toFun := fun i => ULift.up i
      invFun := fun i => i.down
      left_inv := by
        intro i
        rfl
      right_inv := by
        intro i
        cases i
        rfl }
  change
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi
      (fun i : Fin r =>
        freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis (e i))
  exact
    isPresentedCompletedDifferentialFamilyBasisProCInteger_reindex
      (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi e
      (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis)
      hbasis_A

end

end CrowellExactSequence
