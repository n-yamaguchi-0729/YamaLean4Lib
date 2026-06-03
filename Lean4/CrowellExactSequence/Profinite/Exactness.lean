import CrowellExactSequence.Profinite.KernelInjectivity
import FoxDifferential.Completed.FreeProC.FiniteQuotientStages
import FoxDifferential.Completed.Continuous.SemidirectKernelBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/Exactness.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Crowell exactness over pro-C integer coefficients

This file contains only the displayed paper sequence

```text
N^ab(C) -> A_psi(C) -> Z_C[[H]] -> Z_C.
```

The theorem below is stated in the paper's four maps, without route-level packages.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC
open ProCGroups.Completion
open ProCGroups.InverseSystems

universe u v

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The separated displayed boundary kills the separated kernel boundary. -/
theorem presentedSepToZC_profiniteKernelAbelianizationBoundaryAddSep
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (x : ProfiniteKernelAbelianizationAdd psi) :
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi x) =
      0 := by
  change
    (fun y : ProfiniteKernelAbelianization psi =>
      presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C hC psi
          (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
            (G := G) (H := H) C psi (Additive.ofMul y)) =
        0) (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi
          (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))) =
      0
  rw [profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of,
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d]
  exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (C := C) (H := H) psi.toMonoidHom n.2

/-- Separated middle exactness is equivalent to integrating every separated `delta`-cycle by a
kernel element. -/
theorem exact_boundaryAddZC_sep_iff_delta_cycles_integrate
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C hC psi) ↔
      ∀ a : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom,
        presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
            (G := G) (H := H) C hC psi a = 0 →
          ∃ n : ProfiniteKernelSubgroup psi,
            zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = a := by
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := G) (H := H) C psi
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C hC psi
  constructor
  · intro hexact a ha
    rcases (hexact a).1 ha with ⟨x, hx⟩
    revert hx
    change
      (fun q : ProfiniteKernelAbelianization psi =>
        dN (Additive.ofMul q) = a →
          ∃ n : ProfiniteKernelSubgroup psi,
            zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = a) (Additive.toMul x)
    refine QuotientGroup.induction_on (Additive.toMul x) ?_
    intro n hn
    refine ⟨n, ?_⟩
    simpa [dN] using hn
  · intro hintegrates a
    constructor
    · intro ha
      rcases hintegrates a ha with ⟨n, hn⟩
      refine ⟨Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n), ?_⟩
      simpa [dN] using hn
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact
        presentedSepToZC_profiniteKernelAbelianizationBoundaryAddSep
          (G := G) (H := H) C hC psi x

/-- Separated middle exactness from a direct coordinate-lifting criterion for finite Fox cycles.

The coordinate system is supplied explicitly as an equivalence from the separated completed
module to finite Fox coordinates.  This is the separated replacement for the algebraic finite
basis route: no closedness or algebraic coordinate-basis hypothesis is used. -/
theorem exact_boundaryAddZC_sep_of_coord_cycle_lift
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
    (coords :
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom ≃ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H))
    (hcoords_symm :
      coords.symm.toLinearMap =
        presentedSeparatedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family)
    (Dcoords : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hDcoords_kernel :
      ∀ n : ProfiniteKernelSubgroup psi,
        Dcoords n.1 =
          coords (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1))
    (hcycle_lift :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : X =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := G) (H := H) C psi (family i)) v = 0 →
          ∃ n : ProfiniteKernelSubgroup psi, Dcoords n.1 = v) :
    Function.Exact
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := G) (H := H) C psi)
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi) := by
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := G) (H := H) C psi
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C hC psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hblDelta_comp : delta.comp coords.symm.toLinearMap = blDelta := by
    rw [hcoords_symm]
    exact
      presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
        (G := G) (H := H) C hC psi family
  have hblDelta_apply (y) : blDelta y = delta (coords.symm y) := by
    have h := congrArg (fun f => f y) hblDelta_comp
    simpa [LinearMap.comp_apply, delta, blDelta] using h.symm
  change Function.Exact dN delta
  intro a
  constructor
  · intro ha
    have hcoord_cycle : blDelta (coords a) = 0 := by
      calc
        blDelta (coords a) = delta (coords.symm (coords a)) := hblDelta_apply (coords a)
        _ = delta a := by rw [coords.symm_apply_apply]
        _ = 0 := ha
    rcases hcycle_lift (coords a) hcoord_cycle with ⟨n, hncoords⟩
    refine ⟨Additive.ofMul
      (QuotientGroup.mk'
        (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n), ?_⟩
    apply coords.injective
    calc
      coords
          (dN (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))) =
          coords (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) := by
            rw [profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of]
      _ = Dcoords n.1 := (hDcoords_kernel n).symm
      _ = coords a := hncoords
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact
      presentedSepToZC_profiniteKernelAbelianizationBoundaryAddSep
        (G := G) (H := H) C hC psi x

/-- Continuity of the paper coordinate universal differential follows once its coordinates are
identified with the closed-generated completed Fox derivative vector. -/
theorem continuous_familyCoordinatesZC_zcUnivDiff_of_closedGen_leftGraph
    (ProC : ProCGroupPredicate.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family)
    (hfree :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProC) X G family)
    (htarget :
      ProC
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) (fun i : X => psi (family i))))
    (hleft_graph_eq :
      ∀ g : G,
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A
            (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) :
    Continuous
      (fun g : G =>
        presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A
          (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) := by
  let Dclosed : G → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g
  have hclosed_continuous : Continuous Dclosed := by
    simpa [Dclosed] using
      continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) X H hfree (fun i : X => psi (family i)) htarget hφconv
  have hcoords_eq :
      (fun g : G =>
        presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A
          (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) = Dclosed := by
    funext g
    exact (hleft_graph_eq g).symm
  rw [hcoords_eq]
  exact hclosed_continuous

/-- The left coordinate of the closed-generated completed Fox graph is the paper coordinate
universal differential, once the chosen completed differentials form the finite coordinate basis.

The proof avoids a separate continuity assumption for the paper coordinate map.  The
closed-generated Fox vector is a crossed differential, hence it is represented by a linear map out
of the universal completed differential module.  This linear map sends each basis differential
`d(family i)` to the standard coordinate vector, so the finite-basis hypothesis identifies it with
the inverse coordinate map. -/
theorem freeProCZCCompletedFoxDerivativeVectorViaClosedGen_eq_presentedCoordinates_zcUnivDiff
    (ProC : ProCGroupPredicate.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family)
    (hfree :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProC) X G family)
    (hH : ProC (G := H))
    (htarget :
      ProC
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) (fun i : X => psi (family i))))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ∀ g : G,
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g =
        presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A
          (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A
  let f :
      (X → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) →ₗ[
        ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
        ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi family
  let L :
      ZCCompletedDifferentialModule ProC.finiteQuotientClass psi.toMonoidHom →ₗ[
        ZCCompletedGroupAlgebra ProC.finiteQuotientClass H]
        ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen
  have hL_comp : L.comp f = LinearMap.id := by
    exact
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
        (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen
  have hL_eq_coords : L = coords.toLinearMap := by
    exact
      presentedCompletedDifferentialFamilyCoordinatesProCInteger_eq_of_leftInverse
        (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A L hL_comp
  intro g
  calc
    freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g =
        L (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
        rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
          (G := G) (H := H) ProC psi family hfree htarget hφconv hH hφHconv hφHgen g]
    _ = coords
        (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g) := by
        rw [hL_eq_coords]
        rfl

/-- The closed-generated coordinate identity makes the displayed boundary map on `N` factor through
the topological abelianization. -/
theorem completedBoundaryKillsTopCommZC_of_closedGen_leftGraph
    (ProC : ProCGroupPredicate.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
    [T1Space (ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))]
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) ProC.finiteQuotientClass psi family)
    (hfree :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProC) X G family)
    (htarget :
      ProC
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) (fun i : X => psi (family i))))
    (hleft_graph_eq :
      ∀ g : G,
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A
            (zcUniversalDifferential ProC.finiteQuotientClass psi.toMonoidHom g)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger
      (G := G) (H := H) ProC.finiteQuotientClass psi := by
  let Dclosed : G → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) hfree (fun i : X => psi (family i)) htarget hφconv g
  refine
    completedBoundaryKillsTopCommZC_of_continuous_ambient_familyCoords_fintype
      (G := G) (H := H) ProC.finiteQuotientClass psi family hbasis_A Dclosed ?_ ?_
  · simpa [Dclosed] using
      continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (ProC := ProC) X H hfree (fun i : X => psi (family i)) htarget hφconv
  · intro n
    exact hleft_graph_eq n.1

/-- The full standard finite quotient coefficient maps have zero-neighbourhood kernels.

For an open zero-neighbourhood in `Z_C[[H]]`, the inverse-limit topology gives a completed
group-algebra stage projection whose kernel lies inside the neighbourhood.  At the same index,
the finite Fox target is canonically identified with that `H/U` stage, so vanishing after the
finite Fox coefficient map forces vanishing of the original completed-stage projection. -/
theorem freeProCZCBifilteredAllFiniteQuotientStageCoeffMap_additive_basis
    {ProC : ProCGroupPredicate.{u}} [ProC.HasFiniteQuotientFormation]
    {X H : Type u} [DecidableEq X]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
    (φ : X → H)
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
      (A := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H =>
        (freeProCZCBifilteredAllFiniteQuotientStageCoeffMap
          (ProC := ProC) (X := X) (H := H) φ hφgen j).toAddMonoidHom) := by
  letI : ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass :=
    ProC.finiteQuotientContainsTrivialQuotients
  letI : Nonempty (ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) :=
    ⟨(ProCIntegerIndex.terminal (C := ProC.finiteQuotientClass) inferInstance,
      zcCompletedGroupAlgebraTopIndex ProC.finiteQuotientClass H)⟩
  let S := zcCompletedGroupAlgebraSystem ProC.finiteQuotientClass H
  have hdir :
      Directed (· ≤ ·) (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
        ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) :=
    directed_zcCompletedGroupAlgebraIndex
      (C := ProC.finiteQuotientClass) (H := H) ProC.finiteQuotientFormation
  intro U hU hUzero
  rcases S.exists_projection_preimage_subset hdir hU hUzero with
    ⟨j, V, _hVopen, hzeroV, hpre⟩
  refine ⟨j, ?_⟩
  intro z hz
  apply hpre
  change zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j z ∈ V
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H,
        DiscreteTopology
          (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2) :=
    fun j =>
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := H)
          ((OrderDual.ofDual j.2).1 : OpenNormalSubgroup H))
  have hqmap_inj :
      Function.Injective
        (freeProCFiniteQuotientStageQMapFamily
          (C := ProC.finiteQuotientClass) φ
          (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
            ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) hφgen j) := by
    exact
      freeProCFiniteQuotientStageQMapFamily_injective
        (C := ProC.finiteQuotientClass) φ
        (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
          ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) hφgen j
  have hstage_inj :
      Function.Injective
        (zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H)
          (freeProCFiniteQuotientStageKernelFamily
            (C := ProC.finiteQuotientClass) φ
            (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
              ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) j)
          j.1.modulus j dvd_rfl
          (freeProCFiniteQuotientStageQMapFamily
            (C := ProC.finiteQuotientClass) φ
            (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
              ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) hφgen j)) := by
    exact
      zcCompletedGroupAlgebraStageToFiniteFoxStage_self_injective
        (ProC := ProC) (X := X) (H := H)
        (freeProCFiniteQuotientStageKernelFamily
          (C := ProC.finiteQuotientClass) φ
          (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
            ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) j)
        j
        (freeProCFiniteQuotientStageQMapFamily
          (C := ProC.finiteQuotientClass) φ
          (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
            ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) hφgen j)
        hqmap_inj
  have hzstage :
      zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H j z = 0 := by
    apply hstage_inj
    simpa [freeProCZCBifilteredAllFiniteQuotientStageCoeffMap,
      freeProCZCBifilteredFiniteQuotientStageCoeffMap,
      zcCompletedGroupAlgebraBifilteredStageCoeffMap,
      zcCompletedGroupAlgebraFiniteFoxStageCoeffMap] using hz
  simpa [hzstage] using hzeroV

/-- Closed-generated target membership for all completed Fox boundary cycles from the standard
all-finite quotient stage family of `Z_C[[H]]`.

This is the finite-stage input needed by the separated route.  It is deliberately stated before
any Crowell middle term appears, so it does not mention the algebraic completed differential
module or its finite coordinate basis. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiAllStages_coeffGraphRelDeriv
    {ProC : ProCGroupPredicate.{u}} [ProC.HasFiniteQuotientFormation]
    {X H : Type u} [Fintype X] [DecidableEq X]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
    (φ : X → H)
    (hH_isProC : IsProCGroup ProC.finiteQuotientClass H)
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  letI : ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass :=
    ProC.finiteQuotientContainsTrivialQuotients
  letI : Nonempty (ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) :=
    ⟨(ProCIntegerIndex.terminal (C := ProC.finiteQuotientClass) inferInstance,
      zcCompletedGroupAlgebraTopIndex ProC.finiteQuotientClass H)⟩
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H,
        Fact (0 < j.1.modulus) :=
    fun j => ProCIntegerIndex.positiveFact j.1
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H,
        DiscreteTopology
          (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2) :=
    fun j =>
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := H)
          ((OrderDual.ofDual j.2).1 : OpenNormalSubgroup H))
  let J := ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H
  let Nstage : J → Subgroup (FreeGroup X) :=
    freeProCFiniteQuotientStageKernelFamily
      (C := ProC.finiteQuotientClass) φ
      (id : J → J)
  let nstage : J → ℕ := fun j => j.1.modulus
  let zcIndex : J → ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H := id
  let qmap : ∀ j : J,
      CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2 →*
        finiteFoxStageTargetQuotient (X := X) (Nstage j) :=
    freeProCFiniteQuotientStageQMapFamily
      (C := ProC.finiteQuotientClass) φ
      (id : J → J) hφgen
  have hdir : Directed (· ≤ ·) (id : J → J) :=
    directed_zcCompletedGroupAlgebraIndex
      (C := ProC.finiteQuotientClass) (H := H) ProC.finiteQuotientFormation
  have hN :
      ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i :=
    freeProCFiniteQuotientStageKernelFamily_antitone
      (C := ProC.finiteQuotientClass) φ
      (id : J → J) (fun hij => hij)
  have hcoeff_mod :
      ∀ {i j : J} (hij : i ≤ j),
        ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
          modNCompletedCoeffMap
              (n := nstage i) (m := (zcIndex i).1.modulus) (dvd_rfl)
              (modNCompletedCoeffMap
                (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
                (hij.1) a) =
            modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hij.1)
              (modNCompletedCoeffMap
                (n := nstage j) (m := (zcIndex j).1.modulus) (dvd_rfl) a) := by
    intro i j hij a
    simp only [id_eq, modNCompletedCoeffMap_rfl, RingHomCompTriple.comp_apply, RingHom.id_apply, nstage, zcIndex]
  have hqmap_transition :
      ∀ {i j : J} (hij : i ≤ j),
        ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
          qmap i
              ((OpenNormalSubgroupInClass.map
                (C := ProC.finiteQuotientClass) (G := H)
                (U := OrderDual.ofDual (zcIndex i).2)
                (V := OrderDual.ofDual (zcIndex j).2)
                (hij.2) q)) =
            finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q) := by
    intro i j hij q
    exact
      freeProCFiniteQuotientStageQMapFamily_transition
        (C := ProC.finiteQuotientClass) φ zcIndex (fun hij => hij) hφgen hij q
  have hgenerators :
      ∀ j : J, ∀ x : X,
        qmap j (QuotientGroup.mk (φ x)) =
          QuotientGroup.mk' (Nstage j) (FreeGroup.of x) := by
    simpa [J, Nstage, zcIndex, qmap] using
      freeProCFiniteQuotientStageQMapFamily_generator
        (C := ProC.finiteQuotientClass) φ
        (id : J → J) hφgen
  have hcoeff_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun j : J =>
          (zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex
            (fun _ => dvd_rfl) qmap j).toAddMonoidHom) := by
    simpa [J, nstage, zcIndex, qmap, freeProCZCBifilteredFiniteQuotientStageCoeffMap] using
      freeProCZCBifilteredAllFiniteQuotientStageCoeffMap_additive_basis
        (ProC := ProC) (X := X) (H := H) φ hφgen
  exact
    boundaryCycles_subset_closedGenTarget_of_zcBiGraph
      (ProC := ProC) (X := X) (H := H)
      (J := J) (Nstage := Nstage) (nstage := nstage)
      (hN := hN) (hn := fun hij => hij.1)
      (zcIndex := zcIndex) (hzcIndex := fun hij => hij)
      (hmod := fun _ => dvd_rfl) (qmap := qmap)
      φ hcoeff_mod hqmap_transition hgenerators
      (freeProCZCFoxSemiZCBifilteredStageMap_identity_basis_of_component_bases_standardTopology
        (ProC := ProC) (X := X) (H := H)
        (Nstage := Nstage) (nstage := nstage) (hN := hN) (hn := fun hij => hij.1)
        (zcIndex := zcIndex) (hzcIndex := fun hij => hij)
        (hmod := fun _ => dvd_rfl) (qmap := qmap)
        hdir hcoeff_mod hqmap_transition
        (zcFreeFoxCoordinatesBifilteredStageMap_additive_basis_of_coeff_basis_standardTopology
          (ProC := ProC) (X := X) (H := H)
          (Nstage := Nstage) (nstage := nstage) (hN := hN) (hn := fun hij => hij.1)
          (zcIndex := zcIndex) (hzcIndex := fun hij => hij)
          (hmod := fun _ => dvd_rfl) (qmap := qmap)
          hdir hcoeff_mod hqmap_transition hcoeff_basis)
        (zcCompletedGABifilteredStageRightMap_identity_basis_of_stageQuotient_basis
          (ProC := ProC) (X := X) (H := H)
          (Nstage := Nstage) (zcIndex := zcIndex) (qmap := qmap)
          (by
            simpa [J, zcIndex] using
              zcCompletedGroupAlgebraAllStageQuotientMap_identity_basis_of_isProCGroup
                (C := ProC.finiteQuotientClass) (H := H) hH_isProC)
          (by
            intro j
            simpa [J, Nstage, zcIndex, qmap] using
              freeProCFiniteQuotientStageQMapFamily_injective
                (C := ProC.finiteQuotientClass) φ
                (id : J → J) hφgen j)))

end

end CrowellExactSequence
