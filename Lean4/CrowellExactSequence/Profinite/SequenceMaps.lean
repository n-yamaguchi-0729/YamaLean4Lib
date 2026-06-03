import CrowellExactSequence.FiniteFamilyExactness
import FoxDifferential.Completed.Continuous.TopologicalGeneration
import FoxDifferential.Completed.Continuous.TailExactness
import FoxDifferential.Completed.Continuous.Universal.NaturalTopology

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/SequenceMaps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Crowell maps over pro-C integer coefficients

This file names the maps in the paper sequence
`A_psi(C) -> Z_C[[H]] -> Z_C` and the finite-family BL coordinate map.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

universe u v w

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The value of `A_psi(C) -> Z_C[[H]]` on a displayed generator, `dg |-> psi(g)-1`. -/
def presentedCompletedDifferentialBoundaryProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) (g : G) :
    ZCCompletedGroupAlgebra C H :=
  zcCompletedGroupAlgebraBoundary C psi.toMonoidHom g

/-- The displayed Crowell map `A_psi(C) -> Z_C[[H]]`. -/
def presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  zcToCompletedGroupAlgebra C psi.toMonoidHom

/-- The displayed Crowell boundary from the separated completed middle term
`A_psi(C)_sep -> Z_C[[H]]`. -/
def presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra C hC psi

omit [IsTopologicalGroup G] in
@[simp]
theorem presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) (g : G) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
        (zcUniversalDifferential C psi.toMonoidHom g) =
      presentedCompletedDifferentialBoundaryProCInteger (G := G) (H := H) C psi g := by
  exact zcToCompletedGroupAlgebra_universal C psi.toMonoidHom g

omit [IsTopologicalGroup G] in
@[simp]
theorem presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (g : G) :
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (zcSeparatedUniversalDifferential C psi.toMonoidHom g) =
      presentedCompletedDifferentialBoundaryProCInteger (G := G) (H := H) C psi g := by
  exact zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_universal
    (G := G) (H := H) C hC psi g

omit [IsTopologicalGroup G] in
theorem presentedSepToZC_comp_toSep
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi).comp
      (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) =
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C psi := by
  exact zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_comp_toSeparated
    (G := G) (H := H) C hC psi

variable (C : ProCGroups.FiniteGroupClass.{u})

/-- The `Z_C[[H]]`-linear family map sending the standard coordinate vector `e_i` to
`d(family i)`. -/
def presentedCompletedDifferentialFamilyMapProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) :
    (X -> ZCCompletedGroupAlgebra C H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModule C psi.toMonoidHom :=
  blanchfieldLyndonFiniteFamilyMap
    (R := ZCCompletedGroupAlgebra C H)
    (fun i : X => zcUniversalDifferential C psi.toMonoidHom (family i))

omit [IsTopologicalGroup G] in
@[simp]
theorem presentedCompletedDifferentialFamilyMapProCInteger_single
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) (i : X) :
    presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family (Pi.single i 1) =
      zcUniversalDifferential C psi.toMonoidHom (family i) := by
  exact
    blanchfieldLyndonFiniteFamilyMap_single
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X => zcUniversalDifferential C psi.toMonoidHom (family i)) i

/-- The finite-family map into the separated completed differential module. -/
def presentedSeparatedDifferentialFamilyMapProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  blanchfieldLyndonFiniteFamilyMap
    (R := ZCCompletedGroupAlgebra C H)
    (fun i : X => zcSeparatedUniversalDifferential C psi.toMonoidHom (family i))

omit [IsTopologicalGroup G] in
@[simp]
theorem presentedSeparatedDifferentialFamilyMapProCInteger_single
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) (i : X) :
    presentedSeparatedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family (Pi.single i 1) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom (family i) := by
  exact
    blanchfieldLyndonFiniteFamilyMap_single
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X => zcSeparatedUniversalDifferential C psi.toMonoidHom (family i)) i

omit [IsTopologicalGroup G] in
/-- Projecting the separated finite-family map to a finite stage agrees with projecting the
algebraic finite-family map to the same finite stage. -/
theorem zcSepDiffModuleStageProj_comp_presentedSepFamilyMap
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :
    (zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i).comp
        (presentedSeparatedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i).comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) := by
  apply linearMap_ext_pi_single
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    presentedSeparatedDifferentialFamilyMapProCInteger_single,
    presentedCompletedDifferentialFamilyMapProCInteger_single,
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal,
    zcCompletedDifferentialModuleStageProjection_universal]

omit [IsTopologicalGroup G] in
/-- The finite-family map into `A_psi(C)` is continuous for the finite-stage completed topology on
`A_psi(C)`. -/
theorem continuous_presentedCompletedDifferentialFamilyMapProCInteger_naturalTopology
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) :
    @Continuous
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family) := by
  rw [continuous_induced_rng]
  change Continuous
    (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
      fun i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom =>
        zcCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family x))
  refine continuous_pi fun i => ?_
  letI : TopologicalSpace (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i) :=
    inferInstance
  letI : DiscreteTopology (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i) :=
    inferInstance
  have hstageAction :
      Continuous (fun p : zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i ×
          ZCCompletedDifferentialModuleStage C psi.toMonoidHom i => p.1 • p.2) :=
    continuous_of_discreteTopology
  have hsum :
      Continuous
        (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          ∑ k, x k •
            zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i (family k)) := by
    refine continuous_finset_sum _ fun k _ => ?_
    have hcoeff :
        Continuous (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          zcCompletedGroupAlgebraProjectionRingHom C H i.target (x k)) :=
      (continuous_zcCompletedGroupAlgebraProjectionRingHom (C := C) (G := H) i.target).comp
        (continuous_apply k)
    have hconst :
        Continuous (fun _ : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i (family k)) :=
      continuous_const
    have hterm := hstageAction.comp (hcoeff.prodMk hconst)
    simpa [zcCompletedDifferentialModuleStage_completed_smul] using hterm
  simpa [presentedCompletedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap, finiteFamilyLinearMap_apply, map_sum]
    using hsum

/-- The basis property for a finite family in the Fox completed differential module. -/
def IsPresentedCompletedDifferentialFamilyBasisProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) : Prop :=
  Function.Bijective
    (presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family)

omit [IsTopologicalGroup G] in
/-- The completed differential basis property is invariant under reindexing a finite family. -/
theorem isPresentedCompletedDifferentialFamilyBasisProCInteger_reindex
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X]
    {Y : Type w} [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (family : Y -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := G) (H := H) C psi (fun x : X => family (e x)) := by
  dsimp [IsPresentedCompletedDifferentialFamilyBasisProCInteger]
  have hmap :
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi (fun x : X => family (e x)) =
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family).comp
          (piReindexLinearEquiv
            (R := ZCCompletedGroupAlgebra C H) e).toLinearMap := by
    simpa [presentedCompletedDifferentialFamilyMapProCInteger,
      blanchfieldLyndonFiniteFamilyMap] using
      (finiteFamilyLinearMap_reindex
        (R := ZCCompletedGroupAlgebra C H)
        (M := ZCCompletedDifferentialModule C psi.toMonoidHom)
        e (fun y : Y => zcUniversalDifferential C psi.toMonoidHom (family y)))
  rw [hmap]
  exact hbasis_A.comp
    (piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra C H) e).bijective

/-- Coordinates associated to a basis family in `A_psi(C)`. -/
def presentedCompletedDifferentialFamilyCoordinatesProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    ZCCompletedDifferentialModule C psi.toMonoidHom ≃ₗ[ZCCompletedGroupAlgebra C H]
      (X -> ZCCompletedGroupAlgebra C H) :=
  (LinearEquiv.ofBijective
    (presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family)
    hbasis_A).symm

omit [IsTopologicalGroup G] in
theorem presentedCompletedDifferentialFamilyCoordinatesProCInteger_symm_toLinearMap
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    (presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A).symm.toLinearMap =
      presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family :=
  rfl

omit [IsTopologicalGroup G] in
@[simp 900]
theorem presentedCompletedDifferentialFamilyCoordinatesProCInteger_d_family
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) (i : X) :
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
        (G := G) (H := H) C psi family hbasis_A
        (zcUniversalDifferential C psi.toMonoidHom (family i)) =
      Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A
  have hsingle :
      coords.symm (Pi.single i (1 : ZCCompletedGroupAlgebra C H)) =
        zcUniversalDifferential C psi.toMonoidHom (family i) := by
    change
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family (Pi.single i 1) =
        zcUniversalDifferential C psi.toMonoidHom (family i)
    exact presentedCompletedDifferentialFamilyMapProCInteger_single
      (G := G) (H := H) C psi family i
  calc
    coords (zcUniversalDifferential C psi.toMonoidHom (family i)) =
        coords (coords.symm (Pi.single i (1 : ZCCompletedGroupAlgebra C H))) := by
          rw [hsingle]
    _ = Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
          exact coords.apply_symm_apply (Pi.single i (1 : ZCCompletedGroupAlgebra C H))

section ClosedGeneratedCoordinates

variable (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
variable (psi : ContinuousMonoidHom G H)
variable {X : Type u} [Fintype X] [DecidableEq X]
variable (family : X → G)
variable
  (hfree :
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X G family)
variable
  (htarget :
    ProC
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
variable
  (hφconv :
    ProCGroups.FreeProC.FamilyConvergesToOne
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
      (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
        (ProC := ProC) (fun i : X => psi (family i))))

/-- The closed-generated expansion into `A_psi(C)` is continuous for the finite-stage completed
topology on `A_psi(C)`. -/
theorem continuous_closedGenerated_module_expansion_naturalTopology :
    @Continuous G
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (zcCompletedDifferentialModuleNaturalTopology
        ProC.finiteQuotientClass psi.toMonoidHom)
      (fun g : G =>
        presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)) := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology ProC.finiteQuotientClass psi.toMonoidHom
  change Continuous
    (fun g : G =>
      presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family
        (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g))
  exact
    (continuous_presentedCompletedDifferentialFamilyMapProCInteger_naturalTopology
      (G := G) (H := H) ProC.finiteQuotientClass psi family).comp
      (continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) X H hfree (fun i : X => psi (family i)) htarget hφconv)

/-- The closed-generated Fox vector, read as a crossed differential with the intended scalar
`psi`, gives a linear map from `A_psi(C)` to finite completed Fox coordinates. -/
def closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
    (hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom) :
    ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
  let Dclosed : G → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g
  have hclosed_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass psi.toMonoidHom)
        Dclosed := by
    have hraw :=
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv
    simpa [Dclosed, hright] using hraw
  zcCompletedDifferentialModuleLift
    (A := ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    ProC.finiteQuotientClass psi.toMonoidHom Dclosed hclosed_cross

omit [Fintype X] in
/-- Evaluation of the closed-generated coordinate lift on universal differentials. -/
@[simp]
theorem closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal
    (hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom)
    (g : G) :
    closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
        (G := G) (H := H) ProC psi family hfree htarget hφconv hright
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  exact
    zcCompletedDifferentialModuleLift_universal
      (A := ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      ProC.finiteQuotientClass psi.toMonoidHom
      (fun g : G =>
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)
      (by
        have hraw :=
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv
        simpa [hright] using hraw)
      g
/-- The closed-generated coordinate lift is a left inverse to the family map. -/
theorem closedGenDerivativeCoordinatesLinearMapZCOfRightHom_comp_familyMap
    (hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom) :
    (closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
        (G := G) (H := H) ProC psi family hfree htarget hφconv hright).comp
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family) =
    LinearMap.id := by
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
      (G := G) (H := H) ProC psi family hfree htarget hφconv hright
  have hL_family :
      ∀ i : X,
        L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom (family i)) =
          Pi.single i (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) := by
    intro i
    calc
      L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom (family i)) =
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv
            (family i) := by
            simpa [L] using
              closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal
                (G := G) (H := H) ProC psi family hfree htarget hφconv hright
                (family i)
      _ = Pi.single i (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) := by
          simp only [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator]
  simpa [L, presentedCompletedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap] using
    (finiteFamilyLinearMap_leftInverse_of_mapsToSingle
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (generators := fun i : X =>
        zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom (family i))
      L hL_family)

/-- Closed-generated coordinates with the right component identified by the free pro-`C`
universal property. -/
def closedGeneratedDerivativeCoordinatesLinearMapProCInteger
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
  closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
    (G := G) (H := H) ProC psi family hfree htarget hφconv
    (freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (ProC := ProC) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl))

omit [Fintype X] in
/-- Evaluation formula for `closedGeneratedDerivativeCoordinatesLinearMapProCInteger`. -/
@[simp]
theorem closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (g : G) :
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  unfold closedGeneratedDerivativeCoordinatesLinearMapProCInteger
  exact
    closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      (freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (ProC := ProC) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
        hφHconv hφHgen psi (by intro i; rfl))
      g
omit [Fintype X] in
/-- A finite-stage factorization criterion for continuity of the closed-generated coordinate
lift.

To prove the coordinate map `A_psi(C) -> Z_C[[H]]^X` is continuous for the natural finite-stage
topology, it is enough to show that every finite coefficient coordinate of the map factors
through some finite source/target/coefficient stage of `A_psi(C)`.  This is the formal
finite-stage compatibility statement left by the paper definition of `A_psi(C)`. -/
theorem continuous_closedGenDerivCoordsZC_of_stageFactorization
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfactor :
      ∀ (x : X) (j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H),
        ∃ i : ZCCompletedDifferentialModuleIndex
            ProC.finiteQuotientClass psi.toMonoidHom,
          ∃ stageCoord :
            ZCCompletedDifferentialModuleStage
                ProC.finiteQuotientClass psi.toMonoidHom i →
              ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j,
            ∀ a :
              ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom,
              zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j
                  (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
                    (G := G) (H := H) ProC psi family hfree htarget hφconv
                    hH hφHconv hφHgen a x) =
                stageCoord
                  (zcCompletedDifferentialModuleStageProjection
                    ProC.finiteQuotientClass psi.toMonoidHom i a)) :
    @Continuous
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (zcCompletedDifferentialModuleNaturalTopology
        ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen) := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology
      ProC.finiteQuotientClass psi.toMonoidHom
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
  change @Continuous
    (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
    (X → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
    (zcCompletedDifferentialModuleNaturalTopology
      ProC.finiteQuotientClass psi.toMonoidHom)
    inferInstance L
  refine continuous_pi fun x => ?_
  refine Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible
    ProC.finiteQuotientClass H) ?_ (fun a => (L a x).property)
  refine continuous_pi fun j => ?_
  rcases hfactor x j with ⟨i, stageCoord, hstageCoord⟩
  letI : TopologicalSpace
      (ZCCompletedDifferentialModuleStage
        ProC.finiteQuotientClass psi.toMonoidHom i) := inferInstance
  letI : DiscreteTopology
      (ZCCompletedDifferentialModuleStage
        ProC.finiteQuotientClass psi.toMonoidHom i) := inferInstance
  have hstage : Continuous stageCoord := continuous_of_discreteTopology
  have hproj :
      @Continuous
        (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
        (ZCCompletedDifferentialModuleStage
          ProC.finiteQuotientClass psi.toMonoidHom i)
        (zcCompletedDifferentialModuleNaturalTopology
          ProC.finiteQuotientClass psi.toMonoidHom)
        inferInstance
        (zcCompletedDifferentialModuleStageProjection
          ProC.finiteQuotientClass psi.toMonoidHom i) :=
    continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
      ProC.finiteQuotientClass psi.toMonoidHom i
  have hcomp : Continuous
      (fun a :
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
        stageCoord
          (zcCompletedDifferentialModuleStageProjection
            ProC.finiteQuotientClass psi.toMonoidHom i a)) :=
    hstage.comp hproj
  have hfun :
      (fun a :
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
        zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j (L a x)) =
      (fun a :
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
        stageCoord
          (zcCompletedDifferentialModuleStageProjection
            ProC.finiteQuotientClass psi.toMonoidHom i a)) := by
    funext a
    simpa [L] using hstageCoord a
  change Continuous
    (fun a :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
      zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j (L a x))
  rw [hfun]
  exact hcomp

omit [Fintype X] in
/-- Concrete finite-stage factorization of each closed-generated coordinate.

For a fixed coordinate `x` and finite coefficient/target stage `j`, the scalar-valued
closed-generated Fox derivative is locally unchanged at `1` after intersecting with the target
kernel.  The pro-`C` open-normal basis supplies a source quotient in the same finite quotient
class, and the crossed-differential rule descends the coordinate to that quotient. -/
theorem closedGenDerivativeCoordinatesLinearMapZC_stage_factorization_of_isProCGroup
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (x : X) (j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) :
    ∃ i : ZCCompletedDifferentialModuleIndex
        ProC.finiteQuotientClass psi.toMonoidHom,
      ∃ stageCoord :
        ZCCompletedDifferentialModuleStage
            ProC.finiteQuotientClass psi.toMonoidHom i →
          ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j,
        ∀ a :
          ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom,
          zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j
              (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
                (G := G) (H := H) ProC psi family hfree htarget hφconv
                hH hφHconv hφHgen a x) =
            stageCoord
              (zcCompletedDifferentialModuleStageProjection
                ProC.finiteQuotientClass psi.toMonoidHom i a) := by
  let C := ProC.finiteQuotientClass
  let φ : X → H := fun i => psi (family i)
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
  let coordStage :
      ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
        ZCCompletedGroupAlgebraStage C H j :=
    {
    toFun v := zcCompletedGroupAlgebraProjection C H j (v x)
    map_add' v w := by
      simp only [Pi.add_apply, zcCompletedGroupAlgebraProjection_add]
    map_smul' r v := by
      change zcCompletedGroupAlgebraProjection C H j (r * v x) =
        zcCompletedGroupAlgebraProjection C H j r *
          zcCompletedGroupAlgebraProjection C H j (v x)
      exact zcCompletedGroupAlgebraProjection_mul C H j r (v x)
    }
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree φ htarget hφconv g
  let D : G → ZCCompletedGroupAlgebraStage C H j := fun g => coordStage (Dclosed g)
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    exact
      freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (ProC := ProC) X H hfree hH φ htarget hφconv hφHconv hφHgen psi
        (by intro i; rfl)
  have hclosed_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
        Dclosed := by
    have hraw :=
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
        (ProC := ProC) hfree φ htarget hφconv
    simpa [C, Dclosed, φ, hright] using hraw
  have hDcross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
        D := by
    exact IsCrossedDifferential.map_linear hclosed_cross coordStage
  have hDcont : Continuous D := by
    have hvec :
        Continuous Dclosed := by
      simpa [C, Dclosed, φ] using
        (continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (ProC := ProC) X H hfree φ htarget hφconv)
    have hcoord : Continuous (fun g : G => Dclosed g x) :=
      (continuous_apply x).comp hvec
    have hproj :
        Continuous (fun a : ZCCompletedGroupAlgebra C H =>
          zcCompletedGroupAlgebraProjection C H j a) :=
      continuous_zcCompletedGroupAlgebraProjection C H j
    simpa [D, coordStage] using hproj.comp hcoord
  let Utarget : OpenNormalSubgroup H := (OrderDual.ofDual j.2).1
  let W : Set G :=
    {g : G | D g = 0 ∧ psi.toMonoidHom g ∈ (Utarget : Subgroup H)}
  have hDzero_open : IsOpen {g : G | D g = 0} := by
    change IsOpen (D ⁻¹' ({0} : Set (ZCCompletedGroupAlgebraStage C H j)))
    exact (isOpen_discrete _).preimage hDcont
  have htarget_open :
      IsOpen {g : G | psi.toMonoidHom g ∈ (Utarget : Subgroup H)} := by
    change IsOpen (psi ⁻¹' (((Utarget : Subgroup H) : Set H)))
    exact (ProCGroups.openNormalSubgroup_isOpen (G := H) Utarget).preimage
      psi.continuous_toFun
  have hWopen : IsOpen W := hDzero_open.inter htarget_open
  have h1W : (1 : G) ∈ W := by
    constructor
    · simpa [D] using IsCrossedDifferential.one hDcross
    · simp only [ContinuousMonoidHom.coe_toMonoidHom, map_one, one_mem, Utarget]
  rcases hGproC.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hWopen h1W with
    ⟨V, hVW⟩
  let i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom :=
    { source := V
      target := j
      compatible := by
        intro g hg
        exact (hVW hg).2 }
  have hD_eq_of_mem :
      ∀ a b : G, a⁻¹ * b ∈ (V.1 : Subgroup G) → D a = D b := by
    intro a b hab
    have hzero : D (a⁻¹ * b) = 0 := (hVW hab).1
    have hmul := hDcross a (a⁻¹ * b)
    have habmul : a * (a⁻¹ * b) = b := by simp only [mul_inv_cancel_left]
    symm
    calc
      D b = D (a * (a⁻¹ * b)) := by rw [habmul]
      _ = D a + zcCompletedGroupAlgebraScalar C psi.toMonoidHom a •
            D (a⁻¹ * b) := hmul
      _ = D a := by rw [hzero, smul_zero, add_zero]
  let Dstage : zcCompletedDifferentialModuleStageSource C psi.toMonoidHom i →
      ZCCompletedGroupAlgebraStage C H j :=
    fun q => Quotient.liftOn' q D (by
      intro a b hab
      have habi : a⁻¹ * b ∈ (i.source.1 : Subgroup G) := by
        have hq : (a : G ⧸ (i.source.1 : Subgroup G)) = b := Quotient.sound' hab
        exact QuotientGroup.eq.1 hq
      exact hD_eq_of_mem a b (by simpa [i] using habi))
  have hDstage_cross :
      IsCrossedDifferential
        (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i)
        Dstage := by
    intro q r
    refine QuotientGroup.induction_on q ?_
    intro a
    refine QuotientGroup.induction_on r ?_
    intro b
    change D (a * b) =
      D a + zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i
        (QuotientGroup.mk' (i.source.1 : Subgroup G) a) • D b
    have hscalar :
        zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i
            (QuotientGroup.mk' (i.source.1 : Subgroup G) a) =
          zcCompletedGroupAlgebraProjectionRingHom C H j
            (zcCompletedGroupAlgebraScalar C psi.toMonoidHom a) := by
      dsimp [i, C, zcCompletedGroupAlgebraScalar]
      rfl
    have h := hDcross a b
    change D (a * b) =
      D a + zcCompletedGroupAlgebraProjectionRingHom C H j
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom a) • D b at h
    rw [hscalar]
    exact h
  let stageCoordFinite :
      ZCCompletedDifferentialModuleStage C psi.toMonoidHom i →ₗ[
        zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i]
        ZCCompletedGroupAlgebraStage C H j :=
    crossedDifferentialModuleLift
      (A := ZCCompletedGroupAlgebraStage C H j)
      (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i)
      Dstage hDstage_cross
  letI : Module (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i) :=
    Module.compHom _ (zcCompletedGroupAlgebraProjectionRingHom C H i.target)
  let stageCoordLinear :
      ZCCompletedDifferentialModuleStage C psi.toMonoidHom i →ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCCompletedGroupAlgebraStage C H j :=
    {
    toFun := stageCoordFinite
    map_add' m n := by
      exact map_add stageCoordFinite m n
    map_smul' r m := by
      change stageCoordFinite
          ((zcCompletedGroupAlgebraProjectionRingHom C H i.target r) • m) =
        (zcCompletedGroupAlgebraProjectionRingHom C H i.target r) • stageCoordFinite m
      exact map_smul stageCoordFinite
        (zcCompletedGroupAlgebraProjectionRingHom C H i.target r) m
    }
  have hcomp :
      stageCoordLinear.comp
          (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i) =
        coordStage.comp L := by
    apply zcCompletedDifferentialModuleHom_ext C psi.toMonoidHom
    intro g
    change stageCoordLinear
        (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
          (zcUniversalDifferential C psi.toMonoidHom g)) =
      coordStage (L (zcUniversalDifferential C psi.toMonoidHom g))
    calc
      stageCoordLinear
          (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (zcUniversalDifferential C psi.toMonoidHom g)) =
          stageCoordFinite
            (zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i g) := by
            rw [zcCompletedDifferentialModuleStageProjection_universal]
            rfl
      _ = Dstage (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom i g) := by
            simp only [ContinuousMonoidHom.coe_toMonoidHom, zcCompletedDifferentialModuleStageDifferential,
  zcCompletedDifferentialModuleStageSourceProj_apply, QuotientGroup.mk'_apply,
  crossedDifferentialModuleLift_universal, stageCoordFinite]
      _ = D g := by
            rfl
      _ = coordStage (Dclosed g) := rfl
      _ = coordStage (L (zcUniversalDifferential C psi.toMonoidHom g)) := by
            rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
              (G := G) (H := H) ProC psi family hfree htarget hφconv
              hH hφHconv hφHgen g]
  refine ⟨i, fun m => stageCoordLinear m, ?_⟩
  intro a
  have h := congrArg (fun f => f a) hcomp
  simpa [LinearMap.comp_apply, coordStage, L] using h.symm

omit [Fintype X] in
/-- The closed-generated coordinate lift is continuous for the natural finite-stage topology once
the source is a concrete pro-`C` group. -/
theorem continuous_closedGenDerivativeCoordinatesLinearMapZC_naturalTopology_of_isProCGroup
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    @Continuous
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (zcCompletedDifferentialModuleNaturalTopology
        ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen) :=
  continuous_closedGenDerivCoordsZC_of_stageFactorization
    (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen
    (fun x j =>
      closedGenDerivativeCoordinatesLinearMapZC_stage_factorization_of_isProCGroup
        (G := G) (H := H) ProC psi family hfree htarget hφconv hGproC
        hH hφHconv hφHgen x j)

omit [Fintype X] in
/-- The pre-quotient closed-generated coordinate lift is continuous for the finite-stage
pre-module topology once the source is a concrete pro-`C` group. -/
theorem continuous_closedGenDerivativeCoordinatesPreliftZC_naturalTopology_of_isProCGroup
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    @Continuous
      (CrossedDifferentialPreModule
        (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) G)
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (zcCompletedDifferentialPreModuleNaturalTopology
        ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun g : G =>
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)) := by
  let C := ProC.finiteQuotientClass
  letI : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom
  letI : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen
  let q :
      CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G →ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H) :=
    L.comp
      (crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ
  have hqcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (ZCFreeFoxCoordinates C (X := X) (H := H))
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance q := by
    have hLcont :=
      continuous_closedGenDerivativeCoordinatesLinearMapZC_naturalTopology_of_isProCGroup
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hGproC hH hφHconv hφHgen
    have hmk :=
      continuous_zcCompletedDifferentialModule_mkQ_naturalTopology
        C psi.toMonoidHom
    exact hLcont.comp hmk
  have hq :
      q =
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) Dclosed := by
    apply Finsupp.lhom_ext
    intro g r
    have hsingle :
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ
            (Finsupp.single g r) :
          ZCCompletedDifferentialModule C psi.toMonoidHom) =
          r • zcUniversalDifferential C psi.toMonoidHom g := by
      rw [← Finsupp.smul_single_one]
      rfl
    calc
      q (Finsupp.single g r) =
          L ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ
              (Finsupp.single g r)) := rfl
      _ = L (r • zcUniversalDifferential C psi.toMonoidHom g) := by
            rw [hsingle]
      _ = r • L (zcUniversalDifferential C psi.toMonoidHom g) := by
            rw [map_smul]
      _ = r • Dclosed g := by
            rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal]
      _ =
          crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H) Dclosed (Finsupp.single g r) := by
            rw [crossedDifferentialModuleLiftLinear_single]
  rw [hq] at hqcont
  simpa [C, Dclosed] using hqcont

omit [Fintype X] in
/-- Closed-generated coordinates as a map out of the separated completed differential module. -/
def separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ZCSeparatedCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) := by
  let C := ProC.finiteQuotientClass
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom :=
    freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (ProC := ProC) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl)
  have hclosed_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom) Dclosed := by
    have hraw :=
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv
    simpa [C, Dclosed, hright] using hraw
  exact
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
      C psi.toMonoidHom hdir Dclosed hclosed_cross
      (by
        simpa [C, Dclosed] using
          continuous_closedGenDerivativeCoordinatesPreliftZC_naturalTopology_of_isProCGroup
            (G := G) (H := H) ProC psi family hfree htarget hφconv
            hGproC hH hφHconv hφHgen)

omit [Fintype X] in
@[simp 900]
theorem separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (g : G) :
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hdir hGproC hH hφHconv hφHgen
        (zcSeparatedUniversalDifferential
          ProC.finiteQuotientClass psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  simp only [ContinuousMonoidHom.coe_toMonoidHom,
  separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger,
  zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_universal]

/-- The separated closed-generated coordinate lift is a left inverse to the separated finite family
map. -/
theorem separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hdir hGproC hH hφHconv hφHgen).comp
      (presentedSeparatedDifferentialFamilyMapProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family) =
    LinearMap.id := by
  let L :=
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen
  have hL_family :
      ∀ i : X,
        L (zcSeparatedUniversalDifferential
            ProC.finiteQuotientClass psi.toMonoidHom (family i)) =
          Pi.single i (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) := by
    intro i
    calc
      L (zcSeparatedUniversalDifferential
          ProC.finiteQuotientClass psi.toMonoidHom (family i)) =
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv
            (family i) := by
            simpa [L] using
              separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
                (G := G) (H := H) ProC psi family hfree htarget hφconv
                hdir hGproC hH hφHconv hφHgen (family i)
      _ = Pi.single i (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) := by
          simp only [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator]
  simpa [L, presentedSeparatedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap] using
    (finiteFamilyLinearMap_leftInverse_of_mapsToSingle
      (R := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (generators := fun i : X =>
        zcSeparatedUniversalDifferential
          ProC.finiteQuotientClass psi.toMonoidHom (family i))
      L hL_family)

/-- The closed-generated coordinate lift is a left inverse to the finite family map. -/
theorem closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen).comp
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family) =
    LinearMap.id := by
  unfold closedGeneratedDerivativeCoordinatesLinearMapProCInteger
  exact
    closedGenDerivativeCoordinatesLinearMapZCOfRightHom_comp_familyMap
      (G := G) (H := H) ProC psi family hfree htarget hφconv
    (freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (ProC := ProC) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl))

/-- The closed-generated fundamental formula after projection to any finite
source/target/coefficient stage.

This is the non-circular finite-stage form: both sides are continuous crossed differentials into
a finite discrete stage and agree on the topological free generators.  It does not assume that the
finite-stage projections of `A_psi(C)` separate points. -/
theorem closedGenerated_fundamental_formula_stageProj
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (i : ZCCompletedDifferentialModuleIndex
        ProC.finiteQuotientClass psi.toMonoidHom)
    (g : G) :
    zcCompletedDifferentialModuleStageProjection
        ProC.finiteQuotientClass psi.toMonoidHom i
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
      zcCompletedDifferentialModuleStageProjection
        ProC.finiteQuotientClass psi.toMonoidHom i
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
  let C := ProC.finiteQuotientClass
  let φ : X → H := fun i => psi (family i)
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let P := zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree φ htarget hφconv g
  let Dstage : G → ZCCompletedDifferentialModuleStage C psi.toMonoidHom i :=
    fun g => P (M (Dclosed g))
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    exact
      freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (ProC := ProC) X H hfree hH φ htarget hφconv hφHconv hφHgen psi
        (by intro i; rfl)
  have hclosed_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
        Dclosed := by
    have hraw :=
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
        (ProC := ProC) hfree φ htarget hφconv
    simpa [C, Dclosed, φ, hright] using hraw
  have hstage_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
        Dstage := by
    exact IsCrossedDifferential.map_linear hclosed_cross (P.comp M)
  have huniv_stage_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
        (zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i) :=
    zcCompletedDifferentialModuleStageDifferential_isCrossedDifferential C psi.toMonoidHom i
  have hstage_continuous : Continuous Dstage := by
    letI : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    have hmodule :
        @Continuous G
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          inferInstance
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          (fun g : G => M (Dclosed g)) := by
      simpa [C, φ, M, Dclosed] using
        (continuous_closedGenerated_module_expansion_naturalTopology
          (G := G) (H := H) ProC psi family hfree htarget hφconv)
    have hP :
        @Continuous
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i)
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          inferInstance P := by
      simpa [C, P] using
        (continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
          C psi.toMonoidHom i)
    simpa [Dstage, P] using hP.comp hmodule
  have huniv_stage_continuous :
      Continuous (zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i) := by
    letI : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    have huniv :
        @Continuous G
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          inferInstance
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          (zcUniversalDifferential C psi.toMonoidHom) :=
      continuous_zcUniversalDifferential_naturalTopology C psi.toMonoidHom
    have hP :
        @Continuous
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i)
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          inferInstance P := by
      simpa [C, P] using
        (continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
          C psi.toMonoidHom i)
    have hcomp : Continuous (fun g : G => P (zcUniversalDifferential C psi.toMonoidHom g)) :=
      hP.comp huniv
    have hfun :
        (fun g : G => P (zcUniversalDifferential C psi.toMonoidHom g)) =
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i := by
      funext g
      simp only [ContinuousMonoidHom.coe_toMonoidHom, zcCompletedDifferentialModuleStageProjection_universal, P]
    rw [← hfun]
    exact hcomp
  have hEq :
      Dstage =
        zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i := by
    refine
      IsCrossedDifferential.eq_of_continuous_of_topologicallyGenerates
        hstage_cross huniv_stage_cross hstage_continuous huniv_stage_continuous hfree.generates_range ?_
    rintro _ ⟨x, rfl⟩
    have hDclosed :
        Dclosed (family x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
      simp only [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator, Dclosed, φ]
    calc
      Dstage (family x) =
          P (M (Pi.single x (1 : ZCCompletedGroupAlgebra C H))) := by
            simp only [ContinuousMonoidHom.coe_toMonoidHom, hDclosed, Dstage]
      _ =
          P (zcUniversalDifferential C psi.toMonoidHom (family x)) := by
            simpa [M] using congrArg P
              (presentedCompletedDifferentialFamilyMapProCInteger_single
                (G := G) (H := H) C psi family x)
      _ =
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i
            (family x) := by
            simp only [ContinuousMonoidHom.coe_toMonoidHom, zcCompletedDifferentialModuleStageProjection_universal, P]
  simpa [Dstage, Dclosed, M, P, C, φ,
    zcCompletedDifferentialModuleStageProjection_universal] using congrFun hEq g

/-- The separated finite family map is a left inverse to the separated closed-generated coordinate
lift.  The proof uses only the finite-stage fundamental formula and separated finite-stage
projections. -/
theorem presentedSepDifferentialFamilyMapZC_comp_sepClosedGenDerivativeCoordinatesLinearMapZC
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (presentedSeparatedDifferentialFamilyMapProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family).comp
      (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hdir hGproC hH hφHconv hφHgen) =
    LinearMap.id := by
  let C := ProC.finiteQuotientClass
  let Msep :=
    presentedSeparatedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let Lsep :=
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen
  apply zcSeparatedCompletedDifferentialModuleHom_ext C psi.toMonoidHom
  intro g
  rw [LinearMap.comp_apply]
  change Msep (Lsep (zcSeparatedUniversalDifferential C psi.toMonoidHom g)) =
    zcSeparatedUniversalDifferential C psi.toMonoidHom g
  rw [separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal]
  have hzero :
      Msep
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) -
        zcSeparatedUniversalDifferential C psi.toMonoidHom g = 0 := by
    apply zcSeparatedCompletedDifferentialModuleStageProjectionsSeparate C psi.toMonoidHom
    intro i
    rw [map_sub, sub_eq_zero]
    calc
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (Msep
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
          zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (M
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)) := by
            have hstage :=
              zcSepDiffModuleStageProj_comp_presentedSepFamilyMap
                (G := G) (H := H) C psi family i
            simpa [LinearMap.comp_apply, C, Msep, M] using
              congrArg
                (fun L : ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[
                    ZCCompletedGroupAlgebra C H]
                    ZCCompletedDifferentialModuleStage C psi.toMonoidHom i =>
                  L
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g))
                hstage
      _ =
          zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (zcUniversalDifferential C psi.toMonoidHom g) := by
            exact
              closedGenerated_fundamental_formula_stageProj
                (G := G) (H := H) ProC psi family hfree htarget hφconv
                hH hφHconv hφHgen i g
      _ =
          zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
            (zcSeparatedUniversalDifferential C psi.toMonoidHom g) := by
            simp only [ContinuousMonoidHom.coe_toMonoidHom, zcCompletedDifferentialModuleStageProjection_universal,
  zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal]
  exact sub_eq_zero.mp hzero

/-- Coordinate equivalence for the separated completed differential module, obtained from the
closed-generated Fox coordinates without assuming algebraic relation-submodule closedness. -/
def separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ZCSeparatedCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom
      ≃ₗ[ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
  LinearEquiv.ofLinear
    (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen)
    (presentedSeparatedDifferentialFamilyMapProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family)
    (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen)
    (presentedSepDifferentialFamilyMapZC_comp_sepClosedGenDerivativeCoordinatesLinearMapZC
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen)

theorem separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_toLinearMap
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen).toLinearMap =
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen :=
  rfl

@[simp 900]
theorem separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_universal
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (g : G) :
    separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hdir hGproC hH hφHconv hφHgen
        (zcSeparatedUniversalDifferential
          ProC.finiteQuotientClass psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  change
    (separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hdir hGproC hH hφHconv hφHgen).toLinearMap
      (zcSeparatedUniversalDifferential
        ProC.finiteQuotientClass psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g
  rw [separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_toLinearMap]
  exact
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hdir hGproC hH hφHconv hφHgen g

/-- Every finite stage projection of `A_psi(C)` factors through the closed-generated coordinate
lift.

This is a stagewise replacement for the completed fundamental formula: the equality is proved
after applying an arbitrary finite stage projection, so no finite-stage separation or closedness
of the relation submodule is used. -/
theorem zcDiffModuleStageProj_eq_familyMap_comp_closedGenCoord
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (i : ZCCompletedDifferentialModuleIndex
        ProC.finiteQuotientClass psi.toMonoidHom) :
    zcCompletedDifferentialModuleStageProjection
        ProC.finiteQuotientClass psi.toMonoidHom i =
      ((zcCompletedDifferentialModuleStageProjection
            ProC.finiteQuotientClass psi.toMonoidHom i).comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family)).comp
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen) := by
  apply zcCompletedDifferentialModuleHom_ext
    ProC.finiteQuotientClass psi.toMonoidHom
  intro g
  simp only [LinearMap.comp_apply]
  rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
    (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen g]
  exact
    (closedGenerated_fundamental_formula_stageProj
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen i g).symm

/-- Equality of closed-generated coordinates implies equality after every finite stage
projection. -/
theorem zcCompletedDifferentialModuleStageProjection_eq_of_closedGeneratedCoordinate_eq
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    {a b : ZCCompletedDifferentialModule
        ProC.finiteQuotientClass psi.toMonoidHom}
    (hab :
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen a =
        closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen b)
    (i : ZCCompletedDifferentialModuleIndex
        ProC.finiteQuotientClass psi.toMonoidHom) :
    zcCompletedDifferentialModuleStageProjection
        ProC.finiteQuotientClass psi.toMonoidHom i a =
      zcCompletedDifferentialModuleStageProjection
        ProC.finiteQuotientClass psi.toMonoidHom i b := by
  let P :=
    zcCompletedDifferentialModuleStageProjection
      ProC.finiteQuotientClass psi.toMonoidHom i
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hfactor :=
    zcDiffModuleStageProj_eq_familyMap_comp_closedGenCoord
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen i
  have hfactor' : P = (P.comp M).comp L := by
    simpa [P, M, L] using hfactor
  calc
    zcCompletedDifferentialModuleStageProjection
        ProC.finiteQuotientClass psi.toMonoidHom i a = ((P.comp M).comp L) a := by
          simpa [P, M, L] using congrArg (fun f => f a) hfactor'
    _ = ((P.comp M).comp L) b := by
          exact congrArg (fun x => (P.comp M) x) (by simpa [L] using hab)
    _ =
        zcCompletedDifferentialModuleStageProjection
          ProC.finiteQuotientClass psi.toMonoidHom i b := by
          simpa [P, M, L] using (congrArg (fun f => f b) hfactor').symm

/-- If finite stage projections already separate points, then the closed-generated coordinate lift
is injective.  The proof uses only the finite-stage fundamental formula above. -/
theorem closedGenDerivativeCoordinatesLinearMapZC_inj_of_stageProjsSeparate
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hsep :
      zcCompletedDifferentialModuleStageProjectionsSeparate
        ProC.finiteQuotientClass psi.toMonoidHom) :
    Function.Injective
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen) := by
  intro a b hab
  apply hsep
  funext i
  simpa [zcCompletedDifferentialModuleStageProjectionProduct,
    zcCompletedDifferentialModuleStageProjectionAdd] using
    zcCompletedDifferentialModuleStageProjection_eq_of_closedGeneratedCoordinate_eq
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hab i

/-- The completed fundamental formula for the closed-generated Fox coordinates is equivalent to
injectivity of the closed-generated coordinate lift `A_psi(C) -> Z_C[[H]]^X`.

The forward direction says that the family map and the coordinate lift are inverse linear maps.
The reverse direction is the non-circular reduction used in the Morishita-aligned route: since the
coordinate lift is already a left inverse to the family map, injectivity forces the formula
`Σ_i D_i(g) d x_i = d g` in the algebraic Crowell module. -/
theorem closedGenerated_fundamental_formula_iff_closedGeneratedCoordinate_injective
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (∀ g : G,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
        zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) ↔
      Function.Injective
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen) := by
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hLM : L.comp M = LinearMap.id := by
    simpa [L, M] using
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen
  constructor
  · intro hfundamental
    have hML : M.comp L = LinearMap.id := by
      apply zcCompletedDifferentialModuleHom_ext
        ProC.finiteQuotientClass psi.toMonoidHom
      intro g
      calc
        (M.comp L)
            (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) =
            M
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) := by
              change
                M (L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) =
                  M
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)
              rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
                (G := G) (H := H) ProC psi family hfree htarget hφconv
                hH hφHconv hφHgen g]
        _ = zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g :=
            hfundamental g
        _ = LinearMap.id
            (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := rfl
    intro a b hab
    calc
      a = (M.comp L) a := by rw [hML]; rfl
      _ = M (L a) := rfl
      _ = M (L b) := by rw [hab]
      _ = (M.comp L) b := rfl
      _ = b := by rw [hML]; rfl
  · intro hLinj g
    apply hLinj
    calc
      L
          (presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
          (L.comp M)
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) := rfl
      _ = freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
            rw [hLM]
            rfl
      _ = L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
            rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
              (G := G) (H := H) ProC psi family hfree htarget hφconv
              hH hφHconv hφHgen g]

omit [Fintype X] in
/-- A direct non-circular closedness criterion through the closed-generated coordinate lift.

For a pro-`C` source the coordinate lift is continuous for the finite-stage natural topology.
Thus injectivity of this lift gives closedness of the defining crossed-differential relation
submodule by the general Hausdorff target reflection criterion. -/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_isProCGroup_of_inj
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hcoord_inj :
      Function.Injective
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen)) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      ProC.finiteQuotientClass psi.toMonoidHom := by
  exact
    zcDiffModuleRelSubmoduleClosed_of_inj_continuous_naturalTopology
      ProC.finiteQuotientClass psi.toMonoidHom
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen)
      hcoord_inj
      (continuous_closedGenDerivativeCoordinatesLinearMapZC_naturalTopology_of_isProCGroup
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hGproC hH hφHconv hφHgen)

/-- On the genuine `A_psi(C)`, the Crowell boundary is obtained by first reading the
closed-generated Fox coordinates and then applying the completed Fox boundary. -/
theorem presentedCompletedToZC_eq_boundary_comp_closedGenCoords
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi =
      (freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass
        (fun i : X => psi (family i))).comp
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen) := by
  apply
    crossedDifferentialModuleHom_ext
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass psi.toMonoidHom)
  intro g
  change
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) =
      ((freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass
        (fun i : X => psi (family i))).comp
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen))
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)
  rw [presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d,
    LinearMap.comp_apply,
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal]
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom :=
    freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (ProC := ProC) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl)
  exact
    (freeProCZCBoundary_of_topologicalGeneration
      ProC.finiteQuotientClass hfree.generates_range psi.toMonoidHom
      (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv)
      (by
        have hraw :=
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv
        simpa [hright] using hraw)
      (continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) X H hfree (fun i : X => psi (family i)) htarget hφconv)
      psi.continuous_toFun
      (by intro i; simp only [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator])
      g).symm

/-- Closed-generated module-valued fundamental formula from topological uniqueness of continuous
crossed differentials.

The extra continuity hypotheses are the precise topological input not supplied by the algebraic
definition of `ZCCompletedDifferentialModule`: they say that the displayed closed-generated
expansion and the universal differential are continuous into a Hausdorff topology on `A_psi(C)`. -/
theorem closedGenerated_fundamental_formula_of_continuous
    [TopologicalSpace (ZCCompletedDifferentialModule
      ProC.finiteQuotientClass psi.toMonoidHom)]
    [T2Space (ZCCompletedDifferentialModule
      ProC.finiteQuotientClass psi.toMonoidHom)]
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hmodule_continuous :
      Continuous
        (fun g : G =>
          presentedCompletedDifferentialFamilyMapProCInteger
              (G := G) (H := H) ProC.finiteQuotientClass psi family
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)))
    (huniv_continuous :
      Continuous
        (fun g : G =>
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) :
    ∀ g : G,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
        zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g := by
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family
  let φ : X → H := fun i => psi (family i)
  let Dclosed : G → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
    fun g => freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (ProC := ProC) hfree φ htarget hφconv g
  let Dmodule : G → ZCCompletedDifferentialModule
      ProC.finiteQuotientClass psi.toMonoidHom :=
    fun g => M (Dclosed g)
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    exact
      freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (ProC := ProC) X H hfree hH φ htarget hφconv hφHconv hφHgen psi
        (by intro i; rfl)
  have hclosed_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass psi.toMonoidHom)
        Dclosed := by
    have hraw :=
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
        (ProC := ProC) hfree φ htarget hφconv
    simpa [Dclosed, hright] using hraw
  have hmodule_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass psi.toMonoidHom)
        Dmodule := by
    exact IsCrossedDifferential.map_linear hclosed_cross M
  have huniv_cross :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass psi.toMonoidHom)
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom) :=
    zcUniversalDifferential_isCrossedDifferential
      ProC.finiteQuotientClass psi.toMonoidHom
  have hEq :
      Dmodule =
        (fun g : G =>
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
    refine
      IsCrossedDifferential.eq_of_continuous_of_topologicallyGenerates
        hmodule_cross huniv_cross ?_ ?_ hfree.generates_range ?_
    · simpa [Dmodule, Dclosed, M, φ] using hmodule_continuous
    · simpa using huniv_continuous
    · rintro _ ⟨i, rfl⟩
      calc
        Dmodule (family i) =
            M (Pi.single i
              (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) := by
              simp only [ContinuousMonoidHom.coe_toMonoidHom,
  freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator, Dmodule, M, Dclosed, φ]
        _ = zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom
              (family i) := by
              simpa [M] using
                presentedCompletedDifferentialFamilyMapProCInteger_single
                  (G := G) (H := H) ProC.finiteQuotientClass psi family i
  intro g
  exact congrFun hEq g

/-- Natural-topology form of the closed-generated fundamental formula, assuming the finite-stage
projections separate points of `A_psi(C)`. -/
theorem closedGenerated_fundamental_formula_naturalTopology_of_separating
    (hsep :
      zcCompletedDifferentialModuleStageProjectionsSeparate
        ProC.finiteQuotientClass psi.toMonoidHom)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ∀ g : G,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
        zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology ProC.finiteQuotientClass psi.toMonoidHom
  letI : T2Space
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating
      ProC.finiteQuotientClass psi.toMonoidHom hsep
  exact
    closedGenerated_fundamental_formula_of_continuous
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
      (by
        simpa using
          continuous_closedGenerated_module_expansion_naturalTopology
            (G := G) (H := H) ProC psi family hfree htarget hφconv)
      (by
        simpa using
          continuous_zcUniversalDifferential_naturalTopology
            ProC.finiteQuotientClass psi.toMonoidHom)

/-- For a pro-`C` source, closedness of the algebraic crossed-differential relation submodule is
equivalent to injectivity of the closed-generated coordinate lift.

This is the precise non-circular frontier left by the Morishita-aligned route.  The implication
from closedness to injectivity goes through finite-stage separation and the completed fundamental
formula.  The converse uses only continuity of the coordinate lift for the finite-stage natural
topology and the Hausdorff target reflection criterion. -/
theorem zcDiffModuleRelSubmoduleClosed_iff_closedGenCoord_inj_of_isProCGroup
    [Nonempty
      (ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex ProC.finiteQuotientClass psi.toMonoidHom))
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
        ProC.finiteQuotientClass psi.toMonoidHom ↔
      Function.Injective
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen) := by
  constructor
  · intro hclosed
    have hsep :
        zcCompletedDifferentialModuleStageProjectionsSeparate
          ProC.finiteQuotientClass psi.toMonoidHom :=
      (zcDiffModuleRelSubmoduleClosed_iff_stageProjsSeparate
        ProC.finiteQuotientClass psi.toMonoidHom hdir).1 hclosed
    exact
      closedGenDerivativeCoordinatesLinearMapZC_inj_of_stageProjsSeparate
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hsep
  · intro hcoord_inj
    exact
      zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_isProCGroup_of_inj
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hGproC hH hφHconv hφHgen hcoord_inj

/-- Once the closed-generated Fox vector satisfies the universal fundamental formula in
`A_psi(C)`, the displayed family differentials form a finite coordinate basis of `A_psi(C)`. -/
theorem isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family := by
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen
  have hLM : L.comp M = LinearMap.id := by
    exact
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
        (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen
  have hML : M.comp L = LinearMap.id := by
    apply zcCompletedDifferentialModuleHom_ext ProC.finiteQuotientClass psi.toMonoidHom
    intro g
    calc
      (M.comp L) (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) =
          M
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) := by
          change
            M (L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) =
              M
                (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                  (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g)
          rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
            (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen g]
      _ = zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g :=
          hfundamental g
      _ = LinearMap.id
          (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := rfl
  constructor
  · intro x y hxy
    have h := congrArg L hxy
    calc
      x = (L.comp M) x := by rw [hLM]; rfl
      _ = L (M x) := rfl
      _ = L (M y) := h
      _ = (L.comp M) y := rfl
      _ = y := by rw [hLM]; rfl
  · intro m
    refine ⟨L m, ?_⟩
    have h := congrArg (fun f => f m) hML
    simpa [M, L, LinearMap.comp_apply] using h

end ClosedGeneratedCoordinates

omit [IsTopologicalGroup G] in
/-- A left inverse to a bijective family map is the coordinate inverse associated to the basis. -/
theorem presentedCompletedDifferentialFamilyCoordinatesProCInteger_eq_of_leftInverse
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    (L :
      ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
        (X → ZCCompletedGroupAlgebra C H))
    (hL :
      L.comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      LinearMap.id) :
    L =
      (presentedCompletedDifferentialFamilyCoordinatesProCInteger
        (G := G) (H := H) C psi family hbasis_A).toLinearMap := by
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A
  let f :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  have hcoords : coords.toLinearMap.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change coords (coords.symm x) = x
    exact coords.apply_symm_apply x
  apply LinearMap.ext
  intro m
  rcases hbasis_A.2 m with ⟨x, hx⟩
  rw [← hx]
  calc
    L (f x) = (L.comp f) x := rfl
    _ = x := by
      rw [hL]
      rfl
    _ = (coords.toLinearMap.comp f) x := by
      rw [hcoords]
      rfl
    _ = coords.toLinearMap (f x) := rfl

section ClosedGeneratedCoordinateEquiv

variable (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
variable (psi : ContinuousMonoidHom G H)
variable {X : Type u} [Fintype X] [DecidableEq X]
variable (family : X → G)
variable
  (hfree :
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X G family)
variable
  (htarget :
    ProC
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
variable
  (hφconv :
    ProCGroups.FreeProC.FamilyConvergesToOne
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
      (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
        (ProC := ProC) (fun i : X => psi (family i))))

/-- Coordinate equivalence for `A_psi(C)` obtained from the closed-generated fundamental formula.

This is the algebraic packaging step: once the module-valued fundamental formula is proved in the
genuine Crowell module, the displayed family map is bijective and its inverse is the
closed-generated Fox coordinate map. -/
def closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom
      ≃ₗ[ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
  presentedCompletedDifferentialFamilyCoordinatesProCInteger
    (G := G) (H := H) ProC.finiteQuotientClass psi family
    (isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental)

/-- The coordinate equivalence from the fundamental formula has the closed-generated coordinate
map as its forward linear map. -/
theorem closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_toLinearMap
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental).toLinearMap =
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen := by
  let hbasis_A :=
    isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hleft :
      L.comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family) =
      LinearMap.id :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hL :
      L =
        (presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A).toLinearMap :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger_eq_of_leftInverse
      (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A L hleft
  simpa [closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula,
    hbasis_A, L] using hL.symm

/-- Closedness from a completed coordinate equivalence plus pre-quotient coordinate continuity.

This is the non-circular direction useful for the remaining completion problem: once the
module-valued fundamental formula has been proved by an independent route, it is enough to show
that the coordinate map, composed with the algebraic quotient map from the completed pre-module,
is continuous for the finite-stage pre-module topology. -/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoordPrequotient_continuous_of_fundFormula
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)
    (hprecoord_continuous :
      @Continuous
        (CrossedDifferentialPreModule
          (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) G)
        (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
        (zcCompletedDifferentialPreModuleNaturalTopology
          ProC.finiteQuotientClass psi.toMonoidHom)
        inferInstance
        (fun x =>
          (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
            (G := G) (H := H) ProC psi family hfree htarget hφconv
            hH hφHconv hφHgen hfundamental).toLinearMap
            ((crossedDifferentialRelationSubmodule
              (zcCompletedGroupAlgebraScalar
                ProC.finiteQuotientClass psi.toMonoidHom)).mkQ x))) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      ProC.finiteQuotientClass psi.toMonoidHom := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  exact
    zcDiffModuleRelSubmoduleClosed_of_inj_continuous_comp_mkQ
      ProC.finiteQuotientClass psi.toMonoidHom e.toLinearMap e.injective hprecoord_continuous

/-- Closedness from the closed-generated coordinate equivalence, stated on the quotient
finite-stage natural topology.

Compared with the pre-quotient criterion above, this uses the already formalized continuity of
the algebraic quotient map `pre-module -> A_psi(C)`: it is enough to prove that the coordinate map
`A_psi(C) -> Z_C[[H]]^X` is continuous for the natural finite-stage topology on `A_psi(C)`. -/
theorem zcDiffRelSubmoduleClosed_of_closedGenCoord_fundFormula
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)
    (hcoord_continuous :
      @Continuous
        (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
        (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
        (zcCompletedDifferentialModuleNaturalTopology
          ProC.finiteQuotientClass psi.toMonoidHom)
        inferInstance
        (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen hfundamental).toLinearMap) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      ProC.finiteQuotientClass psi.toMonoidHom := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  exact
    zcDiffModuleRelSubmoduleClosed_of_inj_continuous_naturalTopology
      ProC.finiteQuotientClass psi.toMonoidHom e.toLinearMap e.injective hcoord_continuous

/-- Closedness from the closed-generated fundamental formula and finite-stage coordinate
factorization.

The factorization hypothesis is the concrete finite-stage compatibility needed to make the
closed-generated coordinate map continuous for the natural topology on the algebraic
`A_psi(C)`. -/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_stage_factorization_of_fundFormula
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    (∀ (x : X) (j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H),
        ∃ i : ZCCompletedDifferentialModuleIndex
            ProC.finiteQuotientClass psi.toMonoidHom,
          ∃ stageCoord :
            ZCCompletedDifferentialModuleStage
                ProC.finiteQuotientClass psi.toMonoidHom i →
              ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j,
            ∀ a :
              ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom,
              zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j
                  (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
                    (G := G) (H := H) ProC psi family hfree htarget hφconv
                    hH hφHconv hφHgen a x) =
                stageCoord
                  (zcCompletedDifferentialModuleStageProjection
                    ProC.finiteQuotientClass psi.toMonoidHom i a)) →
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      ProC.finiteQuotientClass psi.toMonoidHom := by
  intro hfactor
  refine
    zcDiffRelSubmoduleClosed_of_closedGenCoord_fundFormula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental ?_
  have hcoord :=
    continuous_closedGenDerivCoordsZC_of_stageFactorization
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfactor
  have hmap :=
    closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_toLinearMap
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  simpa [hmap] using hcoord

/-- Closedness from the completed fundamental formula once the source is a concrete pro-`C`
group.

The finite-stage factorization is supplied internally by the open-normal pro-`C` basis of the
source, so the only remaining mathematical input is the non-circular module-valued fundamental
formula. -/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_isProCGroup_of_fundFormula
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    (hGproC : ProCGroups.ProC.IsProCGroup ProC.finiteQuotientClass G)
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      ProC.finiteQuotientClass psi.toMonoidHom :=
  zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_stage_factorization_of_fundFormula
    (G := G) (H := H) ProC psi family hfree htarget hφconv
    hH hφHconv hφHgen hfundamental
    (fun x j =>
      closedGenDerivativeCoordinatesLinearMapZC_stage_factorization_of_isProCGroup
        (G := G) (H := H) ProC psi family hfree htarget hφconv hGproC
        hH hφHconv hφHgen x j)

@[simp 900]
theorem closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_universal
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)
    (g : G) :
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  have hmap :=
    congrArg
      (fun L :
          ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom
            →ₗ[ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
              ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) =>
        L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g))
      (closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_toLinearMap
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  calc
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)
        =
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := hmap
    _ =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g := by
        exact closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen g

/-- The coordinate topology on `A_psi(C)` transported from the closed-generated coordinate
equivalence. -/
def closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
  TopologicalSpace.induced
    (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental)
    inferInstance

/-- The closed-generated coordinate equivalence is continuous for the transported coordinate
topology on `A_psi(C)`. -/
theorem continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    @Continuous
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
      inferInstance
      (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental) := by
  exact continuous_induced_dom

/-- The coordinate topology transported to `A_psi(C)` is Hausdorff. -/
theorem t2Space_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    @T2Space
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental) := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have hcont : Continuous (e :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  exact T2Space.of_injective_continuous e.injective hcont

/-- The inverse of the closed-generated coordinate equivalence is continuous for the transported
coordinate topology on `A_psi(C)`.  Equivalently, the displayed family map
`Z_C[[H]]^X -> A_psi(C)` is continuous for this topology. -/
theorem continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_symm
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    @Continuous
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
        (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
          (G := G) (H := H) ProC psi family hfree htarget hφconv
          hH hφHconv hφHgen hfundamental).symm := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  rw [continuous_induced_rng]
  change Continuous
    (fun x : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) =>
      e (e.symm x))
  have hfun :
      (fun x : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) =>
        e (e.symm x)) =
        (fun x : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) => x) := by
    funext x
    exact e.apply_symm_apply x
  rw [hfun]
  exact continuous_id

/-- The displayed family map is continuous for the coordinate topology transported to
`A_psi(C)`. -/
theorem continuous_presentedCompletedDifferentialFamilyMapZC_coordTopology_of_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    @Continuous
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family) := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  change @Continuous
      (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family)
  have hsymm :
      e.symm.toLinearMap =
        presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family := by
    simpa [e, closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula]
      using
        (presentedCompletedDifferentialFamilyCoordinatesProCInteger_symm_toLinearMap
          (G := G) (H := H) ProC.finiteQuotientClass psi family
          (isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
            (G := G) (H := H) ProC psi family hfree htarget hφconv
            hH hφHconv hφHgen hfundamental))
  simpa [← hsymm] using
    (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_symm
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental)

/-- The universal differential `g |-> d g` is continuous for the coordinate topology transported
to `A_psi(C)`. -/
theorem continuous_zcUniversalDifferential_coordinateTopology_of_fundamental_formula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    @Continuous G
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
        (fun g : G => zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  rw [continuous_induced_rng]
  change Continuous
    (fun g : G =>
      e (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g))
  have hfun :
      (fun g : G =>
        e (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) =
        (fun g : G =>
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) := by
    funext g
    exact
      closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_universal
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental g
  rw [hfun]
  exact
    continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (ProC := ProC) X H hfree (fun i : X => psi (family i)) htarget hφconv

/-- Addition is continuous for the transported coordinate topology on `A_psi(C)`. -/
theorem continuous_add_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    letI : TopologicalSpace
        (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
      closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
    Continuous (fun p :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom ×
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
      p.1 + p.2) := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have he : Continuous (e :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  rw [continuous_induced_rng]
  change Continuous
    (fun p :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom ×
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
      e (p.1 + p.2))
  simpa [map_add] using (he.comp continuous_fst).add (he.comp continuous_snd)

/-- Negation is continuous for the transported coordinate topology on `A_psi(C)`. -/
theorem continuous_neg_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    letI : TopologicalSpace
        (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
      closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
    Continuous
      (fun a : ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom => -a) := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have he : Continuous (e :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  rw [continuous_induced_rng]
  change Continuous
    (fun a : ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom => e (-a))
  simpa [map_neg] using he.neg

/-- Scalar multiplication is continuous for the transported coordinate topology on `A_psi(C)`. -/
theorem continuous_smul_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
    (hH : ProC (G := H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) :
    letI : TopologicalSpace
        (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
      closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
    Continuous
      (fun p :
        ZCCompletedGroupAlgebra ProC.finiteQuotientClass H ×
          ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
        p.1 • p.2) := by
  letI : TopologicalSpace
      (ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) ProC psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have he : Continuous (e :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) ProC psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  rw [continuous_induced_rng]
  change Continuous
    (fun p :
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H ×
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom =>
      e (p.1 • p.2))
  simpa [map_smul] using (continuous_fst.smul (he.comp continuous_snd))

end ClosedGeneratedCoordinateEquiv

omit [IsTopologicalGroup G] in
/-- The displayed Crowell map after the family map is the finite BL map with boundary
generators `psi(family i) - 1`. -/
theorem presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) :
    (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C psi).comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, presentedCompletedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap_apply, blanchfieldLyndonFiniteFamilyMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d]

omit [IsTopologicalGroup G] in
/-- The separated displayed Crowell map after the separated family map is the finite BL map with
boundary generators `psi(family i) - 1`. -/
theorem presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) :
    (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi).comp
        (presentedSeparatedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, presentedSeparatedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap_apply, blanchfieldLyndonFiniteFamilyMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d]


omit [IsTopologicalGroup G] in
/-- The finite Blanchfield--Lyndon boundary attached to the displayed family is exactly the
source-shaped completed Fox boundary for the abstract free group on that family.

This removes one layer from the remaining density statement: a BL-coordinate cycle is the same
as a vector killed by the completed Fox boundary
`zcFreeGroupFoxBoundary C (FreeGroup.lift (fun i => psi (family i)))`. -/
theorem finiteBLMap_boundaryZC_eq_zcFreeGroupFoxBoundary
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) :
    blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)) =
      FoxDifferential.zcFreeGroupFoxBoundary
        C (FreeGroup.lift (fun i : X => psi (family i))) := by
  apply LinearMap.ext
  intro v
  simp only [presentedCompletedDifferentialBoundaryProCInteger, zcCompletedGroupAlgebraBoundary,
  ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe, blanchfieldLyndonFiniteFamilyMap_apply, smul_eq_mul,
  zcFreeGroupFoxBoundary_apply, FreeGroup.lift_apply_of]

omit [IsTopologicalGroup G] in
/-- If the pushed-forward finite family topologically generates `H`, the finite BL map is
exact at the completed group algebra. -/
theorem exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
    [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)))
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  have hfoxExact :
      Function.Exact
        (FoxDifferential.foxBoundaryMap
          (fun i : X => zcGroupLike C H (psi (family i)) - 1) :
          (X → ZCCompletedGroupAlgebra C H) →
            ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H → ZCCoeff C) :=
    FoxDifferential.exact_foxBoundaryMap_zcGroupLike_sub_one_of_topologicallyGenerates
      (C := C) (hForm := hForm)
      (φ := fun i : X => psi (family i)) hgen
  have hmap :
      blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)) =
        FoxDifferential.foxBoundaryMap
          (fun i : X => zcGroupLike C H (psi (family i)) - 1) := by
    ext x
    simp only [presentedCompletedDifferentialBoundaryProCInteger, zcCompletedGroupAlgebraBoundary,
  ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe, LinearMap.coe_comp, LinearMap.coe_single,
  Function.comp_apply, blanchfieldLyndonFiniteFamilyMap_apply, smul_eq_mul, foxBoundaryMap_apply]
  rw [hmap]
  exact hfoxExact

omit [IsTopologicalGroup G] in
/-- Exactness of the finite BL map implies exactness of the displayed Crowell map; no
coordinate basis hypothesis is needed in this direction. -/
theorem exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbl :
      Function.Exact
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)))
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C)) :
    Function.Exact
      (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
        ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  let familyMap :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let delta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hcomp : delta.comp familyMap = blDelta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
      (G := G) (H := H) C psi family
  have hdelta_family : ∀ x, delta (familyMap x) = blDelta x := by
    intro x
    simpa [delta, blDelta, familyMap, LinearMap.comp_apply] using
      congrArg (fun f => f x) hcomp
  intro z
  constructor
  · intro hz
    rcases (hbl z).1 hz with ⟨x, hx⟩
    exact ⟨familyMap x, (hdelta_family x).trans hx⟩
  · rintro ⟨m, rfl⟩
    have hmem :
        delta m ∈ zcCompletedGroupAlgebraAugmentationIdeal C H := by
      have hstd :
          delta m ∈ zcCompletedGroupAlgebraStandardAugmentationIdeal C H := by
        simpa [delta, presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger] using
          zcToCompletedGroupAlgebra_mem_standardAugmentationIdeal
            C H psi.toMonoidHom m
      exact zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C H hstd
    exact (mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
      (C := C) (H := H) (x := delta m)).1 hmem

omit [IsTopologicalGroup G] in
/-- If the pushed-forward finite family topologically generates `H`, then the displayed Crowell
map is exact at the completed group algebra. -/
theorem exact_presentedCompletedToZC_of_boundary_family_topologicallyGenerates
    [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    Function.Exact
      (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
        ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) :=
  exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
    (G := G) (H := H) C psi family
    (exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
      (G := G) (H := H) C hForm psi family hgen)

omit [IsTopologicalGroup G] in
/-- Exactness of the finite BL map implies exactness of the separated displayed Crowell map at
`Z_C[[H]]`. -/
theorem exact_presentedSepToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbl :
      Function.Exact
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)))
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C)) :
    Function.Exact
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi :
        ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom ->
          ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  let familyMap :=
    presentedSeparatedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C hC psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hcomp : delta.comp familyMap = blDelta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
      (G := G) (H := H) C hC psi family
  have hdelta_family : ∀ x, delta (familyMap x) = blDelta x := by
    intro x
    simpa [delta, blDelta, familyMap, LinearMap.comp_apply] using
      congrArg (fun f => f x) hcomp
  have hcompleted :
      Function.Exact
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C psi :
          ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C) :=
    exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
      (G := G) (H := H) C psi family hbl
  have htoSep_surj :
      Function.Surjective (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) := by
    intro a
    refine Submodule.Quotient.induction_on
      (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom)
      (C := fun a =>
        ∃ b : ZCCompletedDifferentialModule C psi.toMonoidHom,
          zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom b = a)
      a ?_
    intro x
    refine ⟨(crossedDifferentialRelationSubmodule
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ x, ?_⟩
    rfl
  intro z
  constructor
  · intro hz
    rcases (hbl z).1 hz with ⟨x, hx⟩
    exact ⟨familyMap x, (hdelta_family x).trans hx⟩
  · rintro ⟨m, rfl⟩
    rcases htoSep_surj m with ⟨b, hb⟩
    have hdelta_lift :
        delta m =
          presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
            (G := G) (H := H) C psi b := by
      rw [← hb]
      have hcomp_toSep :=
        congrArg (fun f => f b)
          (presentedSepToZC_comp_toSep
            (G := G) (H := H) C hC psi)
      simpa [delta, LinearMap.comp_apply] using hcomp_toSep
    rw [hdelta_lift]
    exact
      (hcompleted
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C psi b)).2 ⟨b, rfl⟩

omit [IsTopologicalGroup G] in
/-- If the pushed-forward finite family topologically generates `H`, then the separated
displayed Crowell map is exact at the completed group algebra. -/
theorem exact_presentedSepToZC_of_boundary_family_topologicallyGenerates
    [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    Function.Exact
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi :
        ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom ->
          ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) :=
  exact_presentedSepToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
    (G := G) (H := H) C hC psi family
    (exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
      (G := G) (H := H) C hForm psi family hgen)

omit [IsTopologicalGroup G] in
/-- Exactness of the displayed Crowell map implies exactness of the finite BL map as soon as
the chosen family map is surjective.  Full basis/injectivity is not needed for this implication. -/
theorem exact_finiteBLMap_boundary_of_presentedToZC_of_familyMap_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A_surj :
      Function.Surjective
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family))
    (hexact_CompletedGroupAlgebra :
      Function.Exact
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
          ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C)) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)))
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  let familyMap :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let delta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hcomp : delta.comp familyMap = blDelta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
      (G := G) (H := H) C psi family
  have hdelta_family : ∀ x, delta (familyMap x) = blDelta x := by
    intro x
    simpa [delta, blDelta, familyMap, LinearMap.comp_apply] using
      congrArg (fun f => f x) hcomp
  intro z
  constructor
  · intro hz
    rcases (hexact_CompletedGroupAlgebra z).1 hz with ⟨m, hm⟩
    rcases hbasis_A_surj m with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      blDelta x = delta (familyMap x) := (hdelta_family x).symm
      _ = delta m := by rw [hx]
      _ = z := hm
  · rintro ⟨x, rfl⟩
    exact (hexact_CompletedGroupAlgebra (blDelta x)).2 ⟨familyMap x, hdelta_family x⟩

omit [IsTopologicalGroup G] in
/-- A basis family identifies exactness of the displayed Crowell map with exactness of the
finite Blanchfield--Lyndon map obtained by evaluating the displayed boundary on that family. -/
theorem exact_finiteBLMap_boundary_iff_presentedToZC_of_family_basis
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    Function.Exact
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)))
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C) <->
      Function.Exact
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
          ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  constructor
  · exact
      exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
        (G := G) (H := H) C psi family
  · exact
      exact_finiteBLMap_boundary_of_presentedToZC_of_familyMap_surj
        (G := G) (H := H) C psi family hbasis_A.2

omit [IsTopologicalGroup G] in
@[simp]
theorem presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d_of_mem_ker
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) (n : psi.toMonoidHom.ker) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
        (zcUniversalDifferential C psi.toMonoidHom n.1) =
      0 := by
  rw [presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d]
  exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (C := C) (H := H) psi.toMonoidHom n.2

omit [IsTopologicalGroup G] in
@[simp]
theorem presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d_of_mem_ker
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (n : psi.toMonoidHom.ker) :
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) =
      0 := by
  rw [presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d]
  exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (C := C) (H := H) psi.toMonoidHom n.2

end

end CrowellExactSequence
