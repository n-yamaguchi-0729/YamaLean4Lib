import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.ProC.Quotients.LeftQuotientMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Quotients/ClosedSubgroupNeighborhoods.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Given an open subgroup of a closed subgroup of a profinite group, one can shrink it to the
intersection with an ambient open normal subgroup. -/
theorem exists_openNormalSubgroup_inter_closedSubgroup_le
    (hG : IsProfiniteGroup G) (H : ClosedSubgroup G) (U : OpenSubgroup H) :
    ∃ V : OpenNormalSubgroup G,
      (OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V : Subgroup H) ≤
        (U : Subgroup H) := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  have hU_nhds : (((U : Subgroup H) : Set H)) ∈ 𝓝 (1 : H) := by
    exact U.isOpen'.mem_nhds U.one_mem'
  rcases (mem_nhds_subtype (H : Set G) (1 : H) (((U : Subgroup H) : Set H))).1 hU_nhds with
    ⟨W, hW_nhds, hWU⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W', hW'W, hW'open, h1W'⟩
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW'open h1W' with ⟨V, hVW'⟩
  refine ⟨V, ?_⟩
  intro x hx
  exact hWU <| by
    change x.1 ∈ W
    exact hW'W (hVW' hx)

omit [IsTopologicalGroup G] in
/-- Class-restricted version of `exists_openNormalSubgroup_inter_closedSubgroup_le` for a
closed subgroup of a pro-`C` group. -/
theorem exists_openNormalSubgroupInClass_inter_closedSubgroup_le
    {C : FiniteGroupClass.{u}} (hG : IsProCGroup C G)
    (H : ClosedSubgroup G) (U : OpenSubgroup H) :
    ∃ V : OpenNormalSubgroupInClass C G,
      (OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V.1 :
          Subgroup H) ≤
        (U : Subgroup H) := by
  letI : CompactSpace G := IsProCGroup.compactSpace hG
  letI : T2Space G := IsProCGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProCGroup.totallyDisconnectedSpace hG
  have hU_nhds : (((U : Subgroup H) : Set H)) ∈ 𝓝 (1 : H) := by
    exact U.isOpen'.mem_nhds U.one_mem'
  rcases (mem_nhds_subtype (H : Set G) (1 : H) (((U : Subgroup H) : Set H))).1
      hU_nhds with
    ⟨W, hW_nhds, hWU⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W', hW'W, hW'open, h1W'⟩
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW'open h1W' with
    ⟨V, hVW'⟩
  refine ⟨V, ?_⟩
  intro x hx
  exact hWU <| by
    change x.1 ∈ W
    exact hW'W (hVW' hx)

end ProCGroups.ProC
