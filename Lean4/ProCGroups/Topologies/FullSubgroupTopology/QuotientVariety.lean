import ProCGroups.Topologies.FullSubgroupTopology.QuotientFormation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Topologies/FullSubgroupTopology/QuotientVariety.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topological group constructions

Topological subgroup, quotient, continuous homomorphism, continuous equivalence, conjugation, and full-subgroup-topology lemmas.
-/

open Set
open scoped Topology

namespace ProCGroups.Topologies

universe u

/-- A quotient variety is a quotient formation with the closure properties needed for varieties. -/
structure QuotientVariety extends QuotientFormation where
  comap_closed :
    ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) {N : Subgroup H},
      toQuotientFormation.contains N → toQuotientFormation.contains (N.comap f)

namespace QuotientVariety

variable (C : QuotientVariety)
variable {G H : Type u} [Group G] [Group H]

/-- Abstract form of the fact that full pro-`C` openness pulls back along a homomorphism. -/
theorem isOpenSubgroup_comap (f : G →* H) {K : Subgroup H}
    (hK : C.toQuotientFormation.IsOpenSubgroup K) :
    C.toQuotientFormation.IsOpenSubgroup (K.comap f) := by
  rcases hK with ⟨N, hN, hNK⟩
  refine ⟨N.comap f, C.comap_closed f hN, ?_⟩
  intro x hx
  exact hNK hx

end QuotientVariety

end ProCGroups.Topologies
