import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import ProCGroups.Profinite.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Profinite/MathlibBridge.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite group basics

Basic profinite group predicates, finite quotient facts, and standard closure properties used throughout the pro-C library.
-/

namespace ProCGroups

universe u v

namespace IsProfiniteGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every bundled profinite group is profinite in the working unbundled sense. -/
theorem of_profiniteGrp (G : ProfiniteGrp) : IsProfiniteGroup G := by
  letI : CompactSpace G := by infer_instance
  letI : T2Space G := by infer_instance
  letI : TotallyDisconnectedSpace G := by infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Bundle an unbundled profinite group as Mathlib's `ProfiniteGrp`. -/
noncomputable def toProfiniteGrp (hG : IsProfiniteGroup G) : ProfiniteGrp.{u} := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  exact ProfiniteGrp.of G

/-- The bundled profinite group has the same underlying type as the original profinite group. -/
@[simp] theorem coe_toProfiniteGrp (hG : IsProfiniteGroup G) :
    (IsProfiniteGroup.toProfiniteGrp (G := G) hG : Type u) = G := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  rfl

/-- Profiniteness transports across continuous multiplicative equivalences. -/
theorem ofContinuousMulEquiv {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (hG : IsProfiniteGroup G) (e : G ≃ₜ* H) :
    IsProfiniteGroup H := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  let PG : ProfiniteGrp := ProfiniteGrp.of G
  simpa using of_profiniteGrp (G := ProfiniteGrp.ofContinuousMulEquiv (G := PG) e)

end IsProfiniteGroup

end ProCGroups
