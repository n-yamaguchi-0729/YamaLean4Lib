import ProCGroups.Generation.GeneratingFamilies
import ReidemeisterSchreier.Profinite.OpenSubgroups.BasisCardinalRank

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/GeneratingFamilies.lean
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
open ProCGroups.Generation
open ProCGroups.ProC

universe u

/-- A free pro-`C` basis on a fixed carrier. -/
structure FreeProCBasis
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  index : Type u
  inclusion : index → G
  isFree : IsFreeProCGroupOnConvergingSet (ProC := ProC) index G inclusion

namespace FreeProCBasis

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instCoeFunFreeProCBasis : CoeFun (FreeProCBasis ProC G) (fun basis => basis.index → G) where
  coe basis := basis.inclusion

@[simp] theorem inclusion_eq_coe (basis : FreeProCBasis ProC G) :
    basis.inclusion = (basis : basis.index → G) := rfl

/-- The cardinality of the basis index. -/
def cardinal (basis : FreeProCBasis ProC G) : Cardinal :=
  Cardinal.mk basis.index

/-- A free pro-`C` basis forgets to a topological generating family. -/
def toGeneratingFamily (basis : FreeProCBasis ProC G) :
    TopologicalGeneratingFamily G where
  index := basis.index
  toFun := basis
  convergesToOne := basis.isFree.convergesToOne
  generates := basis.isFree.generates_range

/-- Forget the fixed-carrier basis to the existing carrier-and-basis data structure. -/
def toData (basis : FreeProCBasis ProC G) :
    FreeProCGroupOnConvergingSetData (ProC := ProC) where
  basis := basis.index
  carrier := G
  instGroup := inferInstance
  instTopologicalSpace := inferInstance
  instIsTopologicalGroup := inferInstance
  inclusion := basis.inclusion
  isFree := basis.isFree

/-- Repackage existing carrier-and-basis data as a fixed-carrier basis. -/
def ofData (data : FreeProCGroupOnConvergingSetData (ProC := ProC)) :
    FreeProCBasis ProC data.carrier where
  index := data.basis
  inclusion := data.inclusion
  isFree := data.isFree

end FreeProCBasis

/-- A free pro-`C` basis model for a target group, up to continuous multiplicative equivalence. -/
structure FreeProCBasisModel
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  carrier : Type u
  instGroup : Group carrier
  instTopologicalSpace : TopologicalSpace carrier
  instIsTopologicalGroup : IsTopologicalGroup carrier
  basis : FreeProCBasis ProC carrier
  equiv : carrier ≃ₜ* G

attribute [instance] FreeProCBasisModel.instGroup
attribute [instance] FreeProCBasisModel.instTopologicalSpace
attribute [instance] FreeProCBasisModel.instIsTopologicalGroup

namespace FreeProCBasisModel

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The cardinality of the modeled free pro-`C` basis. -/
def basisCardinal (model : FreeProCBasisModel ProC G) : Cardinal :=
  model.basis.cardinal

/-- Turn existing carrier-and-basis data plus an equivalence to the target into a basis model. -/
def ofData (data : FreeProCGroupOnConvergingSetData (ProC := ProC)) (e : data.carrier ≃ₜ* G) :
    FreeProCBasisModel ProC G where
  carrier := data.carrier
  instGroup := data.instGroup
  instTopologicalSpace := data.instTopologicalSpace
  instIsTopologicalGroup := data.instIsTopologicalGroup
  basis := FreeProCBasis.ofData data
  equiv := e

end FreeProCBasisModel

/-- Correctly named generating-family statement for the finite-rank open-subnormal result. -/
theorem exists_generatingFamily_openSubnormalSubgroup_of_melnikovFormation_finiteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ family : TopologicalGeneratingFamily ↥(H : Subgroup F),
      family.cardinal ≤
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) := by
  classical
  rcases exists_basis_openSubnormalSubgroup_of_melnikovFormation_finiteRank
      (C := C) hF H with
    ⟨Y, κ, hκ, hκcard⟩
  have hYfinite : Finite Y :=
    (Cardinal.lt_aleph0_iff_finite (α := Y)).mp <|
      lt_of_le_of_lt hκcard
        (Cardinal.natCast_lt_aleph0
          (n := _root_.ReidemeisterSchreier.Schreier.rankTransform
            (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F)))))
  letI : Finite Y := hYfinite
  let family : TopologicalGeneratingFamily ↥(H : Subgroup F) :=
    { index := Y
      toFun := κ
      convergesToOne := FamilyConvergesToOne.of_finite_domain (G := ↥(H : Subgroup F)) κ
      generates := hκ.1 }
  exact ⟨family, by simpa [TopologicalGeneratingFamily.cardinal, family] using hκcard⟩

/-- Cardinal-rank extension-closed basis theorem, with the conclusion explicitly packaged as a
free pro-`C` basis model rather than only a generating family. -/
theorem exists_freeProCBasisModel_openSubgroup_of_extensionClosed_cardinalRank
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
    ∃ model : FreeProCBasisModel
        (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F),
      model.basisCardinal =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
  rcases exists_basis_openSubgroup_of_extensionClosed_cardinalRank
      (C := C) hBridge hVar hIso hExt hcyc hF H with
    ⟨data, ⟨e⟩, hcard⟩
  let model : FreeProCBasisModel
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F) :=
    FreeProCBasisModel.ofData data e
  refine ⟨model, ?_⟩
  simpa [model, FreeProCBasisModel.basisCardinal, FreeProCBasisModel.ofData,
    FreeProCBasis.cardinal, FreeProCBasis.ofData] using hcard

/-- Bundled-hypothesis cardinal-rank basis theorem, with a basis-model conclusion. -/
theorem exists_freeProCBasisModel_openSubgroup_of_cardinalRank_of_schreierBasisHypotheses
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : SchreierBasisCardinalRankHypotheses C)
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ model : FreeProCBasisModel
        (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F),
      model.basisCardinal =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) :=
  exists_freeProCBasisModel_openSubgroup_of_extensionClosed_cardinalRank
    (C := C) hC.bridge hC.variety hC.isomClosed hC.extensionClosed
    hC.hasNontrivialCyclic hF H

/-- Cardinal-rank Melnikov-formation variant, with a basis-model conclusion. -/
theorem exists_freeProCBasisModel_openSubgroup_of_melnikovRank
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
    ∃ model : FreeProCBasisModel
        (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F),
      model.basisCardinal =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
  rcases exists_basis_openSubgroup_of_melnikovFormation_cardinalRank_of_subgroupClosed
      (C := C) hBridge hC hSub hcyc hF H with
    ⟨data, ⟨e⟩, hcard⟩
  let model : FreeProCBasisModel
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F) :=
    FreeProCBasisModel.ofData data e
  refine ⟨model, ?_⟩
  simpa [model, FreeProCBasisModel.basisCardinal, FreeProCBasisModel.ofData,
    FreeProCBasis.cardinal, FreeProCBasis.ofData] using hcard

/-- Cardinal-rank Melnikov-formation open-subgroup variant, with a basis-model conclusion. -/
theorem exists_freeProCBasisModel_openNormalSubgroup_of_melnikovFormation_cardinalRank
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
    ∃ model : FreeProCBasisModel
        (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F),
      model.basisCardinal =
        schreierRankTransformCardinal (Cardinal.mk X)
          (Nat.card (F ⧸ (H : Subgroup F))) := by
  rcases exists_basis_openNormalSubgroup_of_melnikovFormation_cardinalRank
      (C := C) hBridge hC hSub hcyc hF H with
    ⟨data, ⟨e⟩, hcard⟩
  let model : FreeProCBasisModel
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) ↥(H : Subgroup F) :=
    FreeProCBasisModel.ofData data e
  refine ⟨model, ?_⟩
  simpa [model, FreeProCBasisModel.basisCardinal, FreeProCBasisModel.ofData,
    FreeProCBasis.cardinal, FreeProCBasis.ofData] using hcard

end Profinite
end ReidemeisterSchreier
