import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Solvable
import ProCGroups.FreeConstructions.Framework

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeConstructions/AmalgamsAndModules.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abstract free construction framework

Provides reusable universal-property infrastructure for free constructions, comparison maps, and uniqueness principles in topological group settings.
-/

noncomputable section

namespace ProCGroups.FreeConstructions

universe u

variable {G A B H : Type u} [Group G] [Group A] [Group B] [Group H]
variable [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup H]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A finite nontrivial `p`-group has a nontrivial central element.  This is the group-theoretic
core used for finite normal subgroups in pro-`p` amalgam arguments. -/
theorem finite_normal_subgroup_pro_p_has_central_element
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) :
    IsFiniteSubgroup N → Nontrivial N → IsPGroup p N →
        ∃ z : N, z ≠ 1 ∧ z ∈ Subgroup.center N := by
  intro hfinite hnontrivial hpN
  letI : Finite N := hfinite
  letI : Nontrivial N := hnontrivial
  have hcenter : Nontrivial (Subgroup.center N) := IsPGroup.center_nontrivial hpN
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center N)
  exact ⟨z.1, fun hz1 => hz (Subtype.ext hz1), z.2⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup H] in
/-- If an amalgamated free pro-`C` product embeds both factors into a solvable group `G`, then
the factors are solvable. -/
theorem solvable_amalgam_criterion
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AmalgamatedFreeProCProductData C G A B H →
      IsSolvable G → IsSolvable A ∧ IsSolvable B := by
  intro hprod hG
  rcases hprod with
    ⟨_, _, _, _, left, right, inl, inr, _hleft, _hright, hinl, hinr, _hcompat, _huniv⟩
  letI : IsSolvable G := hG
  exact
    ⟨solvable_of_solvable_injective (f := inl.toMonoidHom) hinl,
      solvable_of_solvable_injective (f := inr.toMonoidHom) hinr⟩

end ProCGroups.FreeConstructions
