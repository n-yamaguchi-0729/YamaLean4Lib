import ReidemeisterSchreier.Profinite.OpenSubgroups.BasisTheorems
import ProCGroups.LocalWeight.LocalWeightTheorems

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/BasisInfiniteRank.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite open-subgroup Schreier theory

Profinite open subgroup quotients, finite permutation targets, dense free models, exact right Schreier generation, and topological rank bounds.
-/

open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC
open ProCGroups.ProC

universe u

/-- Hypotheses used by the infinite-rank Schreier basis theorem.  This mirrors
`SchreierBasisFiniteRankHypotheses`, with the additional bridge needed in the infinite-rank
argument. -/
structure SchreierBasisInfiniteRankHypotheses
    (C : ProCGroups.FiniteGroupClass.{u}) : Prop where
  bridge : PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C)
  variety : ProCGroups.FiniteGroupClass.Variety C
  isomClosed : ProCGroups.FiniteGroupClass.IsomClosed C
  extensionClosed : ProCGroups.FiniteGroupClass.ExtensionClosed C
  hasNontrivialCyclic :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A),
      C A ∧ IsCyclic A ∧ Nontrivial A


/-- Infinite-rank extension-closed variety case.  The basis of every open subgroup has the same
cardinality as the ambient converging-set basis. -/
theorem exists_basis_openSubgroup_of_extensionClosed_infiniteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hBridge :
      PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C))
    (hVar : ProCGroups.FiniteGroupClass.Variety C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Infinite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
        Cardinal.mk Fdata.basis = Cardinal.mk X := by
  classical
  let hFprof : ProCGroups.IsProfiniteGroup F := hF.isProC.1
  letI : CompactSpace F := ProCGroups.IsProfiniteGroup.compactSpace hFprof
  letI : T2Space F := ProCGroups.IsProfiniteGroup.t2Space hFprof
  letI : TotallyDisconnectedSpace F := ProCGroups.IsProfiniteGroup.totallyDisconnectedSpace hFprof
  let hHprof : ProCGroups.IsProfiniteGroup ↥(H : Subgroup F) :=
    ProCGroups.IsProfiniteGroup.of_isClosed_subgroup
      (G := F) hFprof (H : Subgroup F)
      (Subgroup.isClosed_of_isOpen (H : Subgroup F) H.isOpen')
  rcases exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass
      C hVar.quotientClosed hcyc with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, a, ha1, hgena⟩
  have hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
        (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := A) ∧
          ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) :=
    ⟨A, inferInstance, inferInstance, inferInstance, hA, a, ha1, hgena⟩
  have hιinj : Function.Injective ι :=
    freeProCGroupOnConvergingSet_injective (hι := hF) hnontrivial
  have hRangeInf : Set.Infinite (Set.range ι) :=
    ProCGroups.LocalWeight.setInfinite_of_cardinal_ge_aleph0 (X := Set.range ι) <| by
      calc
        Cardinal.aleph0 ≤ Cardinal.mk X := Cardinal.aleph0_le_mk X
        _ = Cardinal.mk (Set.range ι) := by
          simpa using (Cardinal.mk_range_eq ι hιinj).symm
  have hXlw : Cardinal.mk X = ProCGroups.LocalWeight.localWeight F := by
    calc
      Cardinal.mk X = Cardinal.mk (Set.range ι) := by
        simpa using (Cardinal.mk_range_eq ι hιinj).symm
      _ = ProCGroups.LocalWeight.localWeight F := by
        exact ProCGroups.LocalWeight.cardinalEqLocalWeight_of_generatesAndConvergesToOne_infinite
          (G := F) (Set.range ι) hFprof
          ⟨hF.generates_range, hF.convergesToOne.range⟩ hRangeInf
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := ⟨rfl⟩
  rcases exists_basis_openSubgroup_of_extensionClosed
      (C := C) hBridge hVar hIso hExt hF H with
    ⟨Fdata, ⟨e⟩⟩
  have hBasisInf : Infinite Fdata.basis := by
    by_contra hFin
    have hBasisFin : Finite Fdata.basis := not_infinite_iff_finite.mp hFin
    letI : Finite Fdata.basis := hBasisFin
    letI : Fintype Fdata.basis := Fintype.ofFinite Fdata.basis
    have hCarrierFg :
        ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated Fdata.carrier := by
      refine ⟨Finset.univ.image Fdata.inclusion, ?_⟩
      simpa [Finset.coe_image] using Fdata.isFree.generates_range
    let φ : ContinuousMonoidHom Fdata.carrier ↥(H : Subgroup F) := {
      toMonoidHom := e.toMonoidHom
      continuous_toFun := e.continuous_toFun
    }
    have hHfg :
        ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated ↥(H : Subgroup F) :=
      ProCGroups.FiniteGeneration.topologicallyFinitelyGenerated_of_continuousSurjective
        φ e.surjective hCarrierFg
    have hFfg :
        ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated F :=
      topologicallyFinitelyGenerated_of_openSubgroup_local H hHfg
    have hXfin : Finite X :=
      finite_of_topologicallyFinitelyGenerated_freeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
        (F := F) (ι := ι) hFprof hFfg hF hnontrivial
    exact (not_infinite_iff_finite.mpr hXfin) inferInstance
  have hFdataInj : Function.Injective Fdata.inclusion :=
    freeProCGroupOnConvergingSet_injective (hι := Fdata.isFree) hnontrivial
  let μ : Fdata.basis → ↥(H : Subgroup F) := fun x => e (Fdata.inclusion x)
  have hμinj : Function.Injective μ := e.injective.comp hFdataInj
  have hμrangeInf : Set.Infinite (Set.range μ) :=
    ProCGroups.LocalWeight.setInfinite_of_cardinal_ge_aleph0 (X := Set.range μ) <| by
      calc
        Cardinal.aleph0 ≤ Cardinal.mk Fdata.basis := Cardinal.aleph0_le_mk Fdata.basis
        _ = Cardinal.mk (Set.range μ) := by
          simpa using (Cardinal.mk_range_eq μ hμinj).symm
  have hFdataProf : ProCGroups.IsProfiniteGroup Fdata.carrier := Fdata.isFree.isProC.1
  have hμgc :
      Generation.GeneratesAndConvergesToOne (G := ↥(H : Subgroup F)) (Set.range μ) := by
    let X0 : Set Fdata.carrier := Set.range Fdata.inclusion
    have hX0 :
        Generation.GeneratesAndConvergesToOne (G := Fdata.carrier) X0 := by
      exact ⟨Fdata.isFree.generates_range, Fdata.isFree.convergesToOne.range⟩
    have hImg :
        Generation.GeneratesAndConvergesToOne (G := ↥(H : Subgroup F)) (e '' X0) :=
      Generation.GeneratesAndConvergesToOne.image_of_continuousMulEquiv
        (G := Fdata.carrier) hFdataProf e hX0
    have hRange : e '' X0 = Set.range μ := by
      ext y
      constructor
      · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨Fdata.inclusion b, ⟨b, rfl⟩, rfl⟩
    simpa [X0, μ, hRange] using hImg
  have hμlw :
      Cardinal.mk Fdata.basis = ProCGroups.LocalWeight.localWeight ↥(H : Subgroup F) := by
    calc
      Cardinal.mk Fdata.basis = Cardinal.mk (Set.range μ) := by
        simpa using (Cardinal.mk_range_eq μ hμinj).symm
      _ = ProCGroups.LocalWeight.localWeight ↥(H : Subgroup F) := by
        exact ProCGroups.LocalWeight.cardinalEqLocalWeight_of_generatesAndConvergesToOne_infinite
          (G := ↥(H : Subgroup F)) (Set.range μ) hHprof hμgc hμrangeInf
  exact
    ⟨Fdata, ⟨e⟩,
      hμlw.trans ((ProCGroups.LocalWeight.localWeight_openSubgroup_eq F H).trans
        hXlw.symm)⟩

/-- Infinite-rank Schreier basis theorem using a bundled hypothesis record. -/
theorem exists_basis_openSubgroup_of_infiniteRank_of_schreierBasisHypotheses
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : SchreierBasisInfiniteRankHypotheses C)
    {X : Type u} [Infinite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
        Cardinal.mk Fdata.basis = Cardinal.mk X :=
  exists_basis_openSubgroup_of_extensionClosed_infiniteRank
    (C := C) hC.bridge hC.variety hC.isomClosed hC.extensionClosed hC.hasNontrivialCyclic hF H

/-- Infinite-rank Melnikov-formation variant with explicit subgroup closure. -/
theorem exists_basis_openSubgroup_of_melnikovFormation_infiniteRank_of_subgroupClosed
    (C : ProCGroups.FiniteGroupClass.{u})
    (hBridge :
      PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C))
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Infinite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
        Cardinal.mk Fdata.basis = Cardinal.mk X := by
  let hVar : ProCGroups.FiniteGroupClass.Variety C :=
    { subgroupClosed := hSub
      quotientClosed := hC.quotientClosed
      finiteProductClosed := hC.formation.finiteProductClosed }
  exact
    exists_basis_openSubgroup_of_extensionClosed_infiniteRank
      (C := C) hBridge hVar hC.isomClosed hC.extensionClosed hcyc hF H

/-- Infinite-rank Melnikov-formation open-subgroup variant. -/
theorem exists_basis_openNormalSubgroup_of_melnikovFormation_infiniteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hBridge :
      PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C))
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Infinite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
        Cardinal.mk Fdata.basis = Cardinal.mk X :=
  exists_basis_openSubgroup_of_melnikovFormation_infiniteRank_of_subgroupClosed
    (C := C) hBridge hC hSub hcyc hF H



end Profinite
end ReidemeisterSchreier
