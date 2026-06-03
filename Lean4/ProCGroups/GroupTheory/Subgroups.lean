import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/GroupTheory/Subgroups.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Subgroup relation helpers

Group-theoretic normal-in-subgroup and subnormal-subgroup predicates used by
profinite applications.
-/

namespace ProCGroups.GroupTheory

universe u

variable {G : Type u} [Group G]

/-- `H` is normal in `K` as an ambient subgroup relation. -/
def IsNormalIn (H K : Subgroup G) : Prop :=
  H ≤ K ∧ ∀ ⦃k h : G⦄, k ∈ K → h ∈ H → k * h * k⁻¹ ∈ H

/-- The transitive closure of the ambient normal-subgroup relation. -/
inductive IsSubnormalSubgroupOf : Subgroup G → Subgroup G → Prop
  | refl (H : Subgroup G) : IsSubnormalSubgroupOf H H
  | step {H K L : Subgroup G} :
      IsNormalIn H K → IsSubnormalSubgroupOf K L → IsSubnormalSubgroupOf H L

/-- An open subgroup is open subnormal if it is subnormal in the ambient group. -/
def IsOpenSubnormalSubgroup [TopologicalSpace G] (H : OpenSubgroup G) : Prop :=
  IsSubnormalSubgroupOf (G := G) (H : Subgroup G) ⊤

/-- The canonical embedding of a kernel quotient into the target range, viewed in the target. -/
noncomputable def quotientKerEmbedding
    {G T : Type u} [Group G] [Group T] (φ : G →* T) :
    G ⧸ φ.ker →* T :=
  φ.range.subtype.comp (QuotientGroup.quotientKerEquivRange φ).toMonoidHom

theorem quotientKerEmbedding_injective
    {G T : Type u} [Group G] [Group T] (φ : G →* T) :
    Function.Injective (quotientKerEmbedding φ) := by
  exact
    φ.range.subtype_injective.comp
      (QuotientGroup.quotientKerEquivRange φ).injective

theorem quotientKerEmbedding_mk
    {G T : Type u} [Group G] [Group T] (φ : G →* T) (x : G) :
    quotientKerEmbedding φ (QuotientGroup.mk' φ.ker x) = φ x := by
  rfl

end ProCGroups.GroupTheory
