import ProCGroups.Profinite.OpenSubgroups
import ProCGroups.InverseSystems.ProfiniteSpace

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Profinite/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite group basics

Basic profinite group predicates, finite quotient facts, and standard closure properties used throughout the pro-C library.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups

universe u v

section Predicate

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An unbundled profinite group is a compact Hausdorff totally disconnected topological group. -/
def IsProfiniteGroup (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G

namespace IsProfiniteGroup

/-- The topological group component of a profinite group. -/
theorem isTopologicalGroup (hG : IsProfiniteGroup G) : IsTopologicalGroup G :=
  hG.1

/-- The compactness component of a profinite group. -/
theorem compactSpace (hG : IsProfiniteGroup G) : CompactSpace G :=
  hG.2.1

/-- The Hausdorff component of a profinite group. -/
theorem t2Space (hG : IsProfiniteGroup G) : T2Space G :=
  hG.2.2.1

/-- The `T1` component of a profinite group. -/
theorem t1Space (hG : IsProfiniteGroup G) : T1Space G := by
  letI : T2Space G := hG.t2Space
  infer_instance

/-- The totally disconnected component of a profinite group. -/
theorem totallyDisconnectedSpace (hG : IsProfiniteGroup G) : TotallyDisconnectedSpace G :=
  hG.2.2.2

/-- A topological group whose underlying topological space is profinite is a profinite group. -/
theorem of_isProfiniteSpace [IsTopologicalGroup G]
    (hG : InverseSystems.IsProfiniteSpace G) : IsProfiniteGroup G :=
  ⟨inferInstance, hG.1, hG.2.1, hG.2.2⟩

end IsProfiniteGroup

end Predicate

section Permanence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- Repackage a permanence theorem stated for `ClosedSubgroup`s into the ordinary subgroup form. -/
theorem of_isClosed_subgroup_of_closedSubgroup
    {P : Subgroup G → Prop}
    (h : ∀ H : ClosedSubgroup G, P (H : Subgroup G))
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    P H := by
  let HC : ClosedSubgroup G := ⟨H, hH⟩
  simpa using h HC

namespace IsProfiniteGroup

omit [IsTopologicalGroup G] in
/-- Any finite discrete topological group is profinite. -/
theorem of_finite_discrete (G : Type u) [Group G] [TopologicalSpace G]
    [Finite G] [DiscreteTopology G] : IsProfiniteGroup G := by
  letI : Fintype G := Fintype.ofFinite G
  letI : CompactSpace G := by infer_instance
  letI : T2Space G := by infer_instance
  letI : TotallyDisconnectedSpace G := by infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- A quotient of a profinite group by an open normal subgroup is profinite. -/
theorem quotient_openNormalSubgroup (hG : IsProfiniteGroup G) (U : OpenNormalSubgroup G) :
    IsProfiniteGroup (G ⧸ (U : Subgroup G)) := by
  letI : CompactSpace G := hG.compactSpace
  letI : T2Space G := hG.t2Space
  letI : Finite (G ⧸ (U : Subgroup G)) := openNormalSubgroup_finiteQuotient (G := G) U
  letI : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U)
  exact of_finite_discrete (G := G ⧸ (U : Subgroup G))

/-- Closed-subgroup permanence for profinite groups. -/
theorem of_closedSubgroup (hG : IsProfiniteGroup G) (H : ClosedSubgroup G) :
    IsProfiniteGroup ↥(H : Subgroup G) := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  letI : CompactSpace H := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Closed-subgroup permanence using an ordinary subgroup together with a closedness proof. -/
theorem of_isClosed_subgroup (hG : IsProfiniteGroup G) (H : Subgroup G)
    (hH : IsClosed (H : Set G)) : IsProfiniteGroup ↥H := by
  exact of_isClosed_subgroup_of_closedSubgroup
    (G := G) (P := fun H => IsProfiniteGroup ↥H) (of_closedSubgroup (G := G) hG) H hH

/-- Arbitrary product permanence for profinite groups. -/
theorem pi {α : Type v} {β : α → Type u}
    [∀ a, Group (β a)] [∀ a, TopologicalSpace (β a)] [∀ a, IsTopologicalGroup (β a)]
    (hβ : ∀ a, IsProfiniteGroup (β a)) :
    IsProfiniteGroup ((a : α) → β a) := by
  letI : ∀ a, CompactSpace (β a) := fun a => IsProfiniteGroup.compactSpace (hβ a)
  letI : ∀ a, T2Space (β a) := fun a => IsProfiniteGroup.t2Space (hβ a)
  letI : ∀ a, TotallyDisconnectedSpace (β a) := fun a =>
    IsProfiniteGroup.totallyDisconnectedSpace (hβ a)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Binary-product case of `IsProfiniteGroup.pi`. -/
theorem prod {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hG : IsProfiniteGroup G) (hH : IsProfiniteGroup H) :
    IsProfiniteGroup (G × H) := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : CompactSpace H := IsProfiniteGroup.compactSpace hH
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : T2Space H := IsProfiniteGroup.t2Space hH
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  letI : TotallyDisconnectedSpace H := IsProfiniteGroup.totallyDisconnectedSpace hH
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- In a profinite group, an element lying in every open normal subgroup must be `1`. -/
theorem eq_one_of_mem_all_openNormalSubgroups [CompactSpace G]
    [TotallyDisconnectedSpace G] {x : G}
    (hx : ∀ U : OpenNormalSubgroup G, x ∈ (U : Subgroup G)) : x = 1 := by
  by_contra hxne
  let W : Set G := ({x} : Set G)ᶜ
  have hW : IsOpen W := by
    simp only [isOpen_compl_iff, finite_singleton, Finite.isClosed, W]
  have h1W : (1 : G) ∈ W := by
    have hx1 : (1 : G) ≠ x := by
      intro h1x
      exact hxne h1x.symm
    simp only [mem_compl_iff, mem_singleton_iff, hx1, not_false_eq_true, W]
  rcases ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) hW h1W with ⟨U, hUW⟩
  have hxU : x ∈ (U : Subgroup G) := hx U
  have hxW : x ∈ W := hUW hxU
  simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, W] at hxW

end IsProfiniteGroup

end Permanence

end ProCGroups
