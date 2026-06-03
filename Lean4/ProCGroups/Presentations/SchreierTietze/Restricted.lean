import ProCGroups.Presentations.SchreierTietze.Relators

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Presentations/SchreierTietze/Restricted.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite presentations

Presentation-level API for profinite groups, finite quotients, relators, and Schreier-Tietze restrictions.
-/

noncomputable section

open scoped Topology

namespace ProCGroups.Presentations

universe u v w

section RestrictedPresentations

variable {F G : Type u} [Group F] [Group G]
variable [TopologicalSpace F] [TopologicalSpace G]
variable [IsTopologicalGroup F] [IsTopologicalGroup G]

/-- The inverse image in a presentation source of a subgroup of the target. -/
def presentationSubgroupPreimage (π : F →ₜ* G) (U : Subgroup G) : Subgroup F :=
  Subgroup.comap π.toMonoidHom U

/-- The restricted epimorphism `π⁻¹(U) → U` attached to a presentation map `π : F → G`. -/
def restrictPresentationHom (π : F →ₜ* G) (U : Subgroup G) :
    presentationSubgroupPreimage π U →ₜ* U where
  toMonoidHom :=
    { toFun := fun x => ⟨π x.1, x.2⟩
      map_one' := by
        apply Subtype.ext
        simp only [OneMemClass.coe_one, map_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul]}
  continuous_toFun := by
    exact Continuous.subtype_mk
      (π.continuous_toFun.comp continuous_subtype_val)
      (fun x => x.2)

omit [IsTopologicalGroup F] [IsTopologicalGroup G] in
@[simp] theorem restrictPresentationHom_apply
    (π : F →ₜ* G) (U : Subgroup G)
    (x : presentationSubgroupPreimage π U) :
    restrictPresentationHom π U x = ⟨π x.1, x.2⟩ :=
  rfl

omit [IsTopologicalGroup F] [IsTopologicalGroup G] in
theorem restrictPresentationHom_surjective
    (π : F →ₜ* G) (U : Subgroup G)
    (hπsurj : Function.Surjective π) :
    Function.Surjective (restrictPresentationHom π U) := by
  intro y
  rcases hπsurj y.1 with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change π x ∈ U
    simp only [hx, y.2]
  · apply Subtype.ext
    exact hx

omit [IsTopologicalGroup F] [IsTopologicalGroup G] in
theorem restrictPresentationHom_ker
    (π : F →ₜ* G) (U : Subgroup G) :
    (restrictPresentationHom π U).toMonoidHom.ker =
      π.toMonoidHom.ker.subgroupOf (presentationSubgroupPreimage π U) := by
  ext x
  constructor
  · intro hx
    change x.1 ∈ π.toMonoidHom.ker
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    change π x.1 = 1
    change x.1 ∈ π.toMonoidHom.ker at hx
    simpa [MonoidHom.mem_ker] using hx

theorem isPresentationOf_subgroup_restrict
    (C : ProCGroups.FiniteGroupClass.{u})
    (π : F →ₜ* G) (U : Subgroup G)
    (hπsurj : Function.Surjective π)
    (hU : ProCGroups.ProC.IsProCGroup C U) :
    IsQuotientByKernel C
      (F := presentationSubgroupPreimage π U) (G := U)
      (π.toMonoidHom.ker.subgroupOf (presentationSubgroupPreimage π U)) := by
  exact ⟨hU, restrictPresentationHom π U,
    restrictPresentationHom_surjective π U hπsurj,
    restrictPresentationHom_ker π U⟩

theorem exists_isPresentationOf_subgroup_restrict_of_isPresentationOf
    (C : ProCGroups.FiniteGroupClass.{u})
    {K : Subgroup F}
    (U : Subgroup G)
    (hU : ProCGroups.ProC.IsProCGroup C U) :
    IsQuotientByKernel C (F := F) (G := G) K →
      ∃ π : F →ₜ* G, Function.Surjective π ∧ π.toMonoidHom.ker = K ∧
        IsQuotientByKernel C
          (F := presentationSubgroupPreimage π U) (G := U)
          (π.toMonoidHom.ker.subgroupOf (presentationSubgroupPreimage π U)) := by
  intro hpres
  rcases hpres with ⟨_hG, π, hπsurj, hπker⟩
  exact ⟨π, hπsurj, hπker,
    isPresentationOf_subgroup_restrict C π U hπsurj hU⟩

theorem isPresentationOf_openSubgroup_restrict
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G)
    (π : F →ₜ* G) (U : OpenSubgroup G)
    (hπsurj : Function.Surjective π) :
    IsQuotientByKernel C
      (F := presentationSubgroupPreimage π (U : Subgroup G)) (G := ↥(U : Subgroup G))
      (π.toMonoidHom.ker.subgroupOf (presentationSubgroupPreimage π (U : Subgroup G))) := by
  have hUclosed : IsClosed (((U : Subgroup G) : Set G)) :=
    ProCGroups.openSubgroup_isClosed (G := G) U
  have hUproC : ProCGroups.ProC.IsProCGroup C ↥(U : Subgroup G) :=
    ProCGroups.ProC.IsProCGroup.of_isClosed_subgroup_of_fullFormation
      hC hG (U : Subgroup G) hUclosed
  exact isPresentationOf_subgroup_restrict C π (U : Subgroup G) hπsurj hUproC

theorem exists_isPresentationOf_openSubgroup_restrict_of_isPresentationOf
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    {K : Subgroup F} (U : OpenSubgroup G) :
    IsQuotientByKernel C (F := F) (G := G) K →
      ∃ π : F →ₜ* G, Function.Surjective π ∧ π.toMonoidHom.ker = K ∧
        IsQuotientByKernel C
          (F := presentationSubgroupPreimage π (U : Subgroup G)) (G := ↥(U : Subgroup G))
          (π.toMonoidHom.ker.subgroupOf
            (presentationSubgroupPreimage π (U : Subgroup G))) := by
  intro hpres
  rcases hpres with ⟨hG, π, hπsurj, hπker⟩
  exact ⟨π, hπsurj, hπker,
    isPresentationOf_openSubgroup_restrict C hC hG π U hπsurj⟩

end RestrictedPresentations

end ProCGroups.Presentations
