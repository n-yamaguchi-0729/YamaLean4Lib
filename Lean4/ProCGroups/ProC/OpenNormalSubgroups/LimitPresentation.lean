import ProCGroups.InverseSystems.ProfiniteSpace
import ProCGroups.InverseSystems.CompatibilityAndSurjectivity
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.Topologies.ContinuousMulEquiv

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/OpenNormalSubgroups/LimitPresentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Inverse-limit presentations of pro-`C` groups

Canonical inverse-limit and exact-basis characterizations for pro-`C` groups.
-/

namespace ProCGroups.ProC

universe u v

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace IsProCGroup

/-- A pro-`C` group is canonically the inverse limit of its quotients by open normal subgroups
whose quotients lie in `C`. -/
noncomputable def openNormalSubgroupInClassMulEquivInverseLimit
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    G ≃ₜ* (openNormalSubgroupInClassSystem C G).inverseLimit := by
  let S := openNormalSubgroupInClassSystem C G
  letI : Nonempty (OpenNormalSubgroupInClass C G) := openNormalSubgroupInClass_nonempty hG
  letI : Nonempty (OrderDual (OpenNormalSubgroupInClass C G)) := inferInstance
  letI : CompactSpace G := IsProCGroup.compactSpace hG
  letI : T2Space G := IsProCGroup.t2Space hG
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), Group (S.X U) := fun U => by
    dsimp [S, openNormalSubgroupInClassSystem]
    infer_instance
  letI : InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), T2Space (S.X U) := fun U => by
    letI : DiscreteTopology (S.X U) := by
      dsimp [S, openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
    infer_instance
  letI : Group S.inverseLimit := by infer_instance
  letI : T2Space S.inverseLimit := S.t2Space_inverseLimit
  let φ : G →* S.inverseLimit :=
    { toFun := S.inverseLimitLift
        (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
          openNormalSubgroupInClassProj (C := C) (G := G) U)
        (openNormalSubgroupInClassProj_compatible (C := C) (G := G))
      map_one' := by
        apply S.ext
        intro i
        rfl
      map_mul' := by
        intro x y
        apply S.ext
        intro i
        rfl }
  have hφcont : Continuous φ :=
    S.continuous_inverseLimitLift
      (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
        openNormalSubgroupInClassProj (C := C) (G := G) U)
      (fun _ => continuous_quotient_mk')
      (openNormalSubgroupInClassProj_compatible (C := C) (G := G))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hmem :
        x⁻¹ * y ∈ iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) := by
      rw [Subgroup.mem_iInf]
      intro U
      let i : OrderDual (OpenNormalSubgroupInClass C G) := OrderDual.toDual U
      have hi :
          openNormalSubgroupInClassProj (C := C) (G := G) i x =
            openNormalSubgroupInClassProj (C := C) (G := G) i y := by
        simpa [φ] using congrArg (fun z : S.inverseLimit => S.projection i z) hxy
      exact QuotientGroup.eq.1 (by
        simpa [openNormalSubgroupInClassProj] using hi)
    have hone : x⁻¹ * y = 1 := by
      have : x⁻¹ * y ∈ (⊥ : Subgroup G) := by
        simpa [hG.iInf_openNormalSubgroupInClass_eq_bot] using hmem
      simpa using this
    calc
      x = x * 1 := by simp only [mul_one]
      _ = x * (x⁻¹ * y) := by rw [hone]
      _ = y := by simp only [mul_inv_cancel_left]
  have hφsurj : Function.Surjective φ :=
    InverseSystems.InverseSystem.surjective_inverseLimitLift (S := S)
      (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
        openNormalSubgroupInClassProj (C := C) (G := G) U)
      (fun _ => continuous_quotient_mk')
      (openNormalSubgroupInClassProj_compatible (C := C) (G := G))
      (fun U => openNormalSubgroupInClassProj_surjective (C := C) (G := G) U)
      (directed_openNormalSubgroupInClass (C := C) (G := G) hForm)
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 φ hφcont ⟨hφinj, hφsurj⟩

@[simp] theorem openNormalSubgroupInClassMulEquivInverseLimit_projection
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G)
    (U : OrderDual (OpenNormalSubgroupInClass C G)) (g : G) :
    (openNormalSubgroupInClassSystem C G).projection U
        (openNormalSubgroupInClassMulEquivInverseLimit
          (C := C) (G := G) hForm hG g) =
      openNormalSubgroupInClassProj (C := C) (G := G) U g := by
  simp only [openNormalSubgroupInClassMulEquivInverseLimit, ContinuousMulEquiv.ofBijectiveCompactToT2, id_eq,
  MonoidHom.coe_mk, OneHom.coe_mk, ContinuousMulEquiv.coe_mk', Equiv.toHomeomorphOfContinuousClosed_apply,
  Equiv.ofBijective_apply, InverseSystems.InverseSystem.inverseLimitLift,
  InverseSystems.InverseSystem.projection_apply]

/-- A pro-`C` group is topologically isomorphic to an inverse limit of finite groups in `C`,
realized using the quotient system indexed by the open normal subgroups whose quotients lie in
`C`. -/
theorem isomorphic_to_inverseLimit_finiteGroupsInClass
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    let S := openNormalSubgroupInClassSystem C G
    (∀ U : OrderDual (OpenNormalSubgroupInClass C G), C (S.X U) ∧ Finite (S.X U)) ∧
      Nonempty (G ≃ₜ* S.inverseLimit) := by
  let S := openNormalSubgroupInClassSystem C G
  refine ⟨?_, ⟨openNormalSubgroupInClassMulEquivInverseLimit (C := C) (G := G) hForm hG⟩⟩
  intro U
  dsimp [S, openNormalSubgroupInClassSystem]
  refine ⟨(OrderDual.ofDual U).2, ?_⟩
  exact hForm.finiteOnly (OrderDual.ofDual U).2

end IsProCGroup

/-- Existence of an exact open-normal subgroup basis with quotients in `C`. -/
def HasExactOpenNormalQuotientBasisInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  CompactSpace G ∧
    ∃ ι : Type u, ∃ U : ι → OpenNormalSubgroup G,
      (∀ i, C (G ⧸ (U i : Subgroup G))) ∧
      (∀ W : Set G, IsOpen W → (1 : G) ∈ W →
        ∃ i, (((U i : Subgroup G) : Set G)) ⊆ W) ∧
      iInf (fun i => (U i : Subgroup G)) = (⊥ : Subgroup G)

/-- An exact open-normal family with trivial intersection makes the group Hausdorff. -/
theorem t2Space_of_exactOpenNormalQuotientBasisInClass
    (hC : HasExactOpenNormalQuotientBasisInClass C G) : T2Space G := by
  rcases hC with ⟨_, ι, U, _, _, hInf⟩
  refine ⟨?_⟩
  intro x y hxy
  have hxy' : x⁻¹ * y ≠ 1 := by
    intro h1
    apply hxy
    simpa using inv_mul_eq_one.mp h1
  have hsep : ∃ i : ι, x⁻¹ * y ∉ (U i : Subgroup G) := by
    by_contra hsep
    have hxall : ∀ i : ι, x⁻¹ * y ∈ (U i : Subgroup G) := by
      intro i
      by_contra hxyi
      exact hsep ⟨i, hxyi⟩
    have hxinf : x⁻¹ * y ∈ iInf (fun i => (U i : Subgroup G)) := by
      simpa [Subgroup.mem_iInf] using hxall
    have hxbot : x⁻¹ * y ∈ (⊥ : Subgroup G) := by
      simpa [hInf] using hxinf
    exact hxy' (by simpa using hxbot)
  rcases hsep with ⟨i, hxyi⟩
  have hclopenCoset :
      ∀ z : G, IsClopen {g : G | z⁻¹ * g ∈ (U i : Subgroup G)} := by
    intro z
    let f : G → G := fun g => z⁻¹ * g
    have hf : Continuous f := continuous_const.mul continuous_id
    refine ⟨?_, ?_⟩
    · simpa [f] using (openSubgroup_isClosed (G := G) (U i).toOpenSubgroup).preimage hf
    · simpa [f] using (openSubgroup_isOpen (G := G) (U i).toOpenSubgroup).preimage hf
  refine ⟨{g : G | x⁻¹ * g ∈ (U i : Subgroup G)},
    {g : G | y⁻¹ * g ∈ (U i : Subgroup G)}, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hclopenCoset x).2
  · exact (hclopenCoset y).2
  · simp only [OpenSubgroup.mem_toSubgroup, Set.mem_setOf_eq, inv_mul_cancel, one_mem]
  · simp only [OpenSubgroup.mem_toSubgroup, Set.mem_setOf_eq, inv_mul_cancel, one_mem]
  · refine Set.disjoint_left.2 ?_
    intro g hx hg
    apply hxyi
    have hmul :
        (x⁻¹ * g) * (y⁻¹ * g)⁻¹ ∈ (U i : Subgroup G) :=
      (U i).mul_mem hx ((U i).inv_mem hg)
    simpa [mul_assoc] using hmul

/-- An exact open-normal family yields a clopen basis and hence total disconnectedness. -/
theorem totallyDisconnectedSpace_of_exactOpenNormalQuotientBasisInClass
    (hC : HasExactOpenNormalQuotientBasisInClass C G) : TotallyDisconnectedSpace G := by
  have hC' := hC
  rcases hC' with ⟨_, ι, U, _, hbasis, _⟩
  letI : T2Space G := t2Space_of_exactOpenNormalQuotientBasisInClass (C := C) hC
  have hclopenBasis : TopologicalSpace.IsTopologicalBasis {s : Set G | IsClopen s} := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · intro s hs
      exact hs.2
    · intro x W hxW hW
      let W₁ : Set G := (fun g : G => x * g) ⁻¹' W
      have hW₁ : IsOpen W₁ := hW.preimage (continuous_const.mul continuous_id)
      have h1W₁ : (1 : G) ∈ W₁ := by
        simpa [W₁] using hxW
      rcases hbasis W₁ hW₁ h1W₁ with ⟨i, hi⟩
      have hclopenCoset : IsClopen {g : G | x⁻¹ * g ∈ (U i : Subgroup G)} := by
        let f : G → G := fun g => x⁻¹ * g
        have hf : Continuous f := continuous_const.mul continuous_id
        refine ⟨?_, ?_⟩
        · simpa [f] using (openSubgroup_isClosed (G := G) (U i).toOpenSubgroup).preimage hf
        · simpa [f] using (openSubgroup_isOpen (G := G) (U i).toOpenSubgroup).preimage hf
      refine ⟨{g : G | x⁻¹ * g ∈ (U i : Subgroup G)}, ?_, by simp only [OpenSubgroup.mem_toSubgroup, Set.mem_setOf_eq, inv_mul_cancel, one_mem], ?_⟩
      · exact hclopenCoset
      · intro g hg
        have hxgW₁ : x⁻¹ * g ∈ W₁ := hi hg
        simpa [W₁, mul_assoc] using hxgW₁
  exact InverseSystems.totallyDisconnectedSpace_of_t2_basis_clopen G hclopenBasis

/-- An exact open-normal family with quotients in `C` implies the working Lean notion of a
pro-`C` group. This direction needs no formation closure: the exact basis already supplies the
required open-normal quotients in `C`. -/
theorem isProCGroup_of_hasExactOpenNormalQuotientBasisInClass
    (hC : HasExactOpenNormalQuotientBasisInClass C G) : IsProCGroup C G := by
  have hC' := hC
  rcases hC' with ⟨hcompact, ι, U, hCU, hbasis, hInf⟩
  letI : CompactSpace G := hcompact
  letI : T2Space G := t2Space_of_exactOpenNormalQuotientBasisInClass (C := C) hC
  letI : TotallyDisconnectedSpace G :=
    totallyDisconnectedSpace_of_exactOpenNormalQuotientBasisInClass (C := C) hC
  refine ⟨⟨inferInstance, hcompact, inferInstance, inferInstance⟩, ?_⟩
  intro W hW h1W
  rcases hbasis W hW h1W with ⟨i, hiW⟩
  exact ⟨U i, hiW, hCU i⟩

end ProCGroups.ProC
