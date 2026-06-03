import Mathlib.Topology.Algebra.ClopenNhdofOne

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/OpenNormalSubgroups/BasisAtOne.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

namespace ProCGroups.ProC

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In a compact totally disconnected topological group,
any open neighborhood of `1` contains an open normal subgroup. -/
theorem exists_openNormalSubgroup_sub_open_nhds_of_one [CompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U : OpenNormalSubgroup G, ((U : Subgroup G) : Set G) ⊆ W := by
  simpa using ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1W

end

end ProCGroups.ProC
