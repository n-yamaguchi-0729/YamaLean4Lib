import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Topologies/OpenSubgroup.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topological group constructions

Topological subgroup, quotient, continuous homomorphism, continuous equivalence, conjugation, and full-subgroup-topology lemmas.
-/

open scoped Topology

namespace OpenSubgroup

universe u

/-- The top open subgroup is canonically equivalent to the ambient topological group. -/
noncomputable def topContinuousMulEquiv
    (G : Type u) [TopologicalSpace G] [Group G] :
    ↥((⊤ : OpenSubgroup G) : Subgroup G) ≃ₜ* G :=
  { toMulEquiv :=
      { toFun := fun x => x.1
        invFun := fun x => ⟨x, by simp only [toSubgroup_top, Subgroup.mem_top]⟩
        left_inv := by
          intro x
          ext
          rfl
        right_inv := by
          intro x
          rfl
        map_mul' := by
          intro x y
          rfl }
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      exact Continuous.subtype_mk continuous_id (by intro x; simp only [toSubgroup_top, id_eq, Subgroup.mem_top]) }

@[simp] theorem topContinuousMulEquiv_apply
    (G : Type u) [TopologicalSpace G] [Group G]
    (x : ↥((⊤ : OpenSubgroup G) : Subgroup G)) :
    topContinuousMulEquiv G x = x.1 :=
  rfl

@[simp] theorem topContinuousMulEquiv_symm_apply
    (G : Type u) [TopologicalSpace G] [Group G] (x : G) :
    (topContinuousMulEquiv G).symm x = ⟨x, by simp only [toSubgroup_top, Subgroup.mem_top]⟩ :=
  rfl

end OpenSubgroup
