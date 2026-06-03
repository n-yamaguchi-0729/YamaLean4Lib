import FoxDifferential.Completed.FiniteStage.Bifiltered.InverseSystem

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/Identity.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed differential modules

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Definition of identityCompletedGroupAlgebraOpenSubgroup. -/
def identityCompletedGroupAlgebraOpenSubgroup
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    OpenSubgroup G :=
  OpenSubgroup.mk (⊥ : Subgroup G) (isOpen_discrete _)

/-- The identity open normal subgroup of a discrete group. -/
def identityCompletedGroupAlgebraOpenNormalSubgroup
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    OpenNormalSubgroup G :=
  OpenNormalSubgroup.mk (identityCompletedGroupAlgebraOpenSubgroup G)
    (Subgroup.Normal.mk (by
      intro n hn g
      change n ∈ (⊥ : Subgroup G) at hn
      rw [Subgroup.mem_bot] at hn
      subst n
      simp only [mul_one, mul_inv_cancel, one_mem]))

/-- 標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem identityCompletedGroupAlgebraOpenNormalSubgroup_coe
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    ((identityCompletedGroupAlgebraOpenNormalSubgroup G : OpenNormalSubgroup G) :
        Subgroup G) = ⊥ := rfl

/-- The identity quotient `G/1`, as a completed-group-algebra index for a finite discrete group. -/
def identityCompletedGroupAlgebraSubgroupInClass
    (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Finite G] :
    OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G := by
  refine ⟨identityCompletedGroupAlgebraOpenNormalSubgroup G, ?_⟩
  change Finite
    (G ⧸ ((identityCompletedGroupAlgebraOpenNormalSubgroup G : OpenNormalSubgroup G) :
      Subgroup G))
  rw [identityCompletedGroupAlgebraOpenNormalSubgroup_coe]
  infer_instance

/-- The identity quotient `G/1`, as a class-restricted completed-group-algebra stage whenever
`G` itself lies in the finite-group class. -/
def identityCompletedGroupAlgebraSubgroupInClassOfMem
    (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C) (hG : C G) :
    OpenNormalSubgroupInClass C G := by
  refine ⟨identityCompletedGroupAlgebraOpenNormalSubgroup G, ?_⟩
  change C (G ⧸ (⊥ : Subgroup G))
  exact hIso ⟨(QuotientGroup.quotientBot (G := G)).symm⟩ hG

/-- The completed-group-algebra stage whose group quotient is `G/1`. -/
def identityCompletedGroupAlgebraIndex
    (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Finite G] :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G :=
  OrderDual.toDual (identityCompletedGroupAlgebraSubgroupInClass G)

/-- The class-restricted completed-group-algebra stage whose group quotient is `G/1`. -/
def identityCompletedGroupAlgebraIndexInClassOfMem
    (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C) (hG : C G) :
    CompletedGroupAlgebraIndexInClass G C :=
  OrderDual.toDual (identityCompletedGroupAlgebraSubgroupInClassOfMem C G hIso hG)

/-- The projection to the identity completed stage is injective on group elements. -/
theorem openNormalSubgroupInClassProj_identityCompletedGroupAlgebraIndex_injective
    (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Finite G] :
    Function.Injective
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (identityCompletedGroupAlgebraIndex G)) := by
  intro g h hgh
  change QuotientGroup.mk' (⊥ : Subgroup G) g =
      QuotientGroup.mk' (⊥ : Subgroup G) h at hgh
  have hbase := congrArg (QuotientGroup.quotientBot (G := G)) hgh
  simpa using hbase

/-- The projection to the class-restricted identity completed stage is injective on group
elements. -/
theorem openNormalSubgroupInClassProj_identityCompletedGAIndexInClassOfMem_inj
    (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C) (hG : C G) :
    Function.Injective
      (openNormalSubgroupInClassProj
        (C := C) (G := G)
        (identityCompletedGroupAlgebraIndexInClassOfMem C G hIso hG)) := by
  intro g h hgh
  change QuotientGroup.mk' (⊥ : Subgroup G) g =
      QuotientGroup.mk' (⊥ : Subgroup G) h at hgh
  have hbase := congrArg (QuotientGroup.quotientBot (G := G)) hgh
  simpa using hbase

/-- The residue group-algebra stage map to the identity completed stage is injective. -/
theorem modNCompletedGroupAlgebraStageMap_identityCompletedGroupAlgebraIndex_injective
    (n : ℕ)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [Finite G] :
    Function.Injective
      (modNCompletedGroupAlgebraStageMap n G
        (identityCompletedGroupAlgebraIndex G)) := by
  classical
  change Function.Injective
    (MonoidAlgebra.mapDomain
      (R := ModNCompletedCoeff n)
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (identityCompletedGroupAlgebraIndex G)))
  exact MonoidAlgebra.mapDomain_injective
    (openNormalSubgroupInClassProj_identityCompletedGroupAlgebraIndex_injective G)

/-- The residue group-algebra stage map to the class-restricted identity completed stage is
injective. -/
theorem modNCompletedGAStageMapInClass_identityCompletedGAIndexInClassOfMem_inj
    (n : ℕ) (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C) (hG : C G) :
    Function.Injective
      (modNCompletedGroupAlgebraStageMapInClass n G C
        (identityCompletedGroupAlgebraIndexInClassOfMem C G hIso hG)) := by
  classical
  change Function.Injective
    (MonoidAlgebra.mapDomain
      (R := ModNCompletedCoeff n)
      (openNormalSubgroupInClassProj
        (C := C) (G := G)
        (identityCompletedGroupAlgebraIndexInClassOfMem C G hIso hG)))
  exact MonoidAlgebra.mapDomain_injective
    (openNormalSubgroupInClassProj_identityCompletedGAIndexInClassOfMem_inj
      C G hIso hG)

end

end FoxDifferential
