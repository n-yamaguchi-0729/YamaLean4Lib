import ReidemeisterSchreier.Profinite.OpenSubgroups.BasisFiniteRank
import ReidemeisterSchreier.Profinite.OpenSubgroups.BasisInfiniteRank

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/BasisCardinalRank.lean
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

/-- Hypotheses used by the cardinal-rank Schreier basis theorem.

The bridge is only needed in the infinite-rank branch, but bundling it here gives a single
public theorem whose conclusion uses `schreierRankTransformCardinal`. -/
structure SchreierBasisCardinalRankHypotheses
    (C : ProCGroups.FiniteGroupClass.{u}) : Prop where
  bridge : PointedToConvergingSetBasisBridge
    (ProCGroups.ProC.finiteGroupClassProCPredicate C)
  variety : ProCGroups.FiniteGroupClass.Variety C
  isomClosed : ProCGroups.FiniteGroupClass.IsomClosed C
  extensionClosed : ProCGroups.FiniteGroupClass.ExtensionClosed C
  hasNontrivialCyclic :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A),
      C A ∧ IsCyclic A ∧ Nontrivial A

/-- Cardinal-rank Schreier basis theorem for extension-closed varieties.

This is the public cardinal layer: finite bases give the classical finite Schreier transform,
and infinite bases stabilize at the ambient basis cardinal. -/
theorem exists_basis_openSubgroup_of_extensionClosed_cardinalRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hBridge :
      PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C))
    (hVar : ProCGroups.FiniteGroupClass.Variety C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
  classical
  by_cases hXfin : Finite X
  · letI : Finite X := hXfin
    rcases exists_basis_openSubgroup_of_extensionClosed_finiteRank
        (C := C) hVar hIso hExt hcyc hF H with
      ⟨Fdata, hFdataEquiv, hFdataCard⟩
    refine ⟨Fdata, hFdataEquiv, ?_⟩
    calc
      Cardinal.mk Fdata.basis =
          (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X)
            (Nat.card (F ⧸ (H : Subgroup F))) : Cardinal) := hFdataCard
      _ = schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
            exact (schreierRankTransformCardinal_mk_finite X
              (Nat.card (F ⧸ (H : Subgroup F)))).symm
  · haveI : Infinite X := not_finite_iff_infinite.1 hXfin
    rcases exists_basis_openSubgroup_of_extensionClosed_infiniteRank
        (C := C) hBridge hVar hIso hExt hcyc hF H with
      ⟨Fdata, hFdataEquiv, hFdataCard⟩
    refine ⟨Fdata, hFdataEquiv, ?_⟩
    calc
      Cardinal.mk Fdata.basis = Cardinal.mk X := hFdataCard
      _ = schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
            exact (schreierRankTransformCardinal_mk_infinite X
              (Nat.card (F ⧸ (H : Subgroup F)))).symm

/-- Cardinal-rank Schreier basis theorem using the bundled cardinal-rank hypotheses. -/
theorem exists_basis_openSubgroup_of_cardinalRank_of_schreierBasisHypotheses
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : SchreierBasisCardinalRankHypotheses C)
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) :=
  exists_basis_openSubgroup_of_extensionClosed_cardinalRank
    (C := C) hC.bridge hC.variety hC.isomClosed hC.extensionClosed
    hC.hasNontrivialCyclic hF H

/-- Cardinal-rank Melnikov-formation variant with explicit subgroup closure. -/
theorem exists_basis_openSubgroup_of_melnikovFormation_cardinalRank_of_subgroupClosed
    (C : ProCGroups.FiniteGroupClass.{u})
    (hBridge :
      PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C))
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
  classical
  by_cases hXfin : Finite X
  · letI : Finite X := hXfin
    rcases exists_basis_openSubgroup_of_melnikovFormation_finiteRank_of_subgroupClosed
        (C := C) hC hSub hcyc hF H with
      ⟨Fdata, hFdataEquiv, hFdataCard⟩
    refine ⟨Fdata, hFdataEquiv, ?_⟩
    calc
      Cardinal.mk Fdata.basis =
          (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X)
            (Nat.card (F ⧸ (H : Subgroup F))) : Cardinal) := hFdataCard
      _ = schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
            exact (schreierRankTransformCardinal_mk_finite X
              (Nat.card (F ⧸ (H : Subgroup F)))).symm
  · haveI : Infinite X := not_finite_iff_infinite.1 hXfin
    rcases exists_basis_openSubgroup_of_melnikovFormation_infiniteRank_of_subgroupClosed
        (C := C) hBridge hC hSub hcyc hF H with
      ⟨Fdata, hFdataEquiv, hFdataCard⟩
    refine ⟨Fdata, hFdataEquiv, ?_⟩
    calc
      Cardinal.mk Fdata.basis = Cardinal.mk X := hFdataCard
      _ = schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
            exact (schreierRankTransformCardinal_mk_infinite X
              (Nat.card (F ⧸ (H : Subgroup F)))).symm

/-- Cardinal-rank Melnikov-formation open-subgroup variant. -/
theorem exists_basis_openNormalSubgroup_of_melnikovFormation_cardinalRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hBridge :
      PointedToConvergingSetBasisBridge (ProCGroups.ProC.finiteGroupClassProCPredicate C))
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
  classical
  by_cases hXfin : Finite X
  · letI : Finite X := hXfin
    rcases exists_basis_openNormalSubgroup_of_melnikovFormation_finiteRank
        (C := C) hC hSub hcyc hF H with
      ⟨Fdata, hFdataEquiv, hFdataCard⟩
    refine ⟨Fdata, hFdataEquiv, ?_⟩
    calc
      Cardinal.mk Fdata.basis =
          (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X)
            (Nat.card (F ⧸ (H : Subgroup F))) : Cardinal) := hFdataCard
      _ = schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
            exact (schreierRankTransformCardinal_mk_finite X
              (Nat.card (F ⧸ (H : Subgroup F)))).symm
  · haveI : Infinite X := not_finite_iff_infinite.1 hXfin
    rcases exists_basis_openNormalSubgroup_of_melnikovFormation_infiniteRank
        (C := C) hBridge hC hSub hcyc hF H with
      ⟨Fdata, hFdataEquiv, hFdataCard⟩
    refine ⟨Fdata, hFdataEquiv, ?_⟩
    calc
      Cardinal.mk Fdata.basis = Cardinal.mk X := hFdataCard
      _ = schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
            exact (schreierRankTransformCardinal_mk_infinite X
              (Nat.card (F ⧸ (H : Subgroup F)))).symm

end Profinite
end ReidemeisterSchreier
