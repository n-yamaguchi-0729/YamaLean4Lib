import ProCGroups.Abelian.TopologicalAbelianizationLimits
import ProCGroups.ProC.GroupPredicates.Basic
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/OpenNormalSubgroups/ClosedCommutator.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Closed commutators and the canonical open-normal quotient system

This file records the finite-quotient detection form of the closed commutator subgroup for
pro-`C` groups, using the canonical inverse-limit presentation by open normal quotients in `C`.
-/

namespace ProCGroups.ProC

open scoped Topology

universe u

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A quotient-level commutator descent along a surjective homomorphism.

If `f : N -> K` is onto, `f n` is in the ordinary commutator subgroup of `K`, and the
kernel of `f` dies in the quotient `N/U`, then the image of `n` in `N/U` is in the ordinary
commutator subgroup. -/
theorem quotient_mk_mem_commutator_of_surjective_image_mem_commutator
    {N K : Type u} [Group N] [Group K]
    (f : N →* K) (hf : Function.Surjective f)
    (U : Subgroup N) [U.Normal] (hkerU : f.ker ≤ U)
    {n : N} (hn : f n ∈ commutator K) :
    QuotientGroup.mk' U n ∈ commutator (N ⧸ U) := by
  have hcomm_le :
      commutator K ≤ (commutator N).map f := by
    rw [_root_.map_commutator_eq]
    have hrange : f.range = (⊤ : Subgroup K) := by
      ext k
      constructor
      · intro hk
        trivial
      · intro _hk
        rcases hf k with ⟨n, rfl⟩
        exact ⟨n, rfl⟩
    rw [hrange]
    exact Subgroup.commutator_mono (by intro x hx; trivial) (by intro x hx; trivial)
  rcases hcomm_le hn with ⟨c, hc, hcn⟩
  have hdiff : n * c⁻¹ ∈ U := by
    apply hkerU
    change f (n * c⁻¹) = 1
    rw [map_mul, map_inv, ← hcn, mul_inv_cancel]
  have hquot :
      QuotientGroup.mk' U n = QuotientGroup.mk' U c :=
    (QuotientGroup.eq_iff_div_mem (N := U)).2 (by
      simpa [div_eq_mul_inv] using hdiff)
  have hcquot :
      QuotientGroup.mk' U c ∈ commutator (N ⧸ U) := by
    have hmap :
        (commutator N).map (QuotientGroup.mk' U) ≤
          commutator (N ⧸ U) := by
      rw [_root_.map_commutator_eq]
      exact Subgroup.commutator_mono (by intro x hx; trivial) (by intro x hx; trivial)
    exact hmap ⟨c, hc, rfl⟩
  simpa [hquot] using hcquot

namespace IsProCGroup

/-- Membership in the closed commutator subgroup of a pro-`C` group is detected on every
open-normal quotient whose quotient lies in `C`. -/
theorem mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass C G,
      QuotientGroup.mk' (U.1 : Subgroup G) x ∈
        Subgroup.closedCommutator (G ⧸ (U.1 : Subgroup G))) :
    x ∈ Subgroup.closedCommutator G := by
  let S := openNormalSubgroupInClassSystem C G
  let e := openNormalSubgroupInClassMulEquivInverseLimit (C := C) (G := G) hForm hG
  letI : Nonempty (OpenNormalSubgroupInClass C G) := openNormalSubgroupInClass_nonempty hG
  letI : Nonempty (OrderDual (OpenNormalSubgroupInClass C G)) := inferInstance
  letI : CompactSpace G := hG.compactSpace
  letI : T2Space G := hG.t2Space
  letI : TotallyDisconnectedSpace G := hG.totallyDisconnectedSpace
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), Group (S.X U) := fun U => by
    dsimp [S, openNormalSubgroupInClassSystem]
    infer_instance
  letI : InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), Finite (S.X U) := fun U => by
    dsimp [S, openNormalSubgroupInClassSystem]
    exact hForm.finiteOnly (OrderDual.ofDual U).2
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), DiscreteTopology (S.X U) := fun U => by
    dsimp [S, openNormalSubgroupInClassSystem]
    exact QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), CompactSpace (S.X U) := fun _ => by
    infer_instance
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), T2Space (S.X U) := fun _ => by
    infer_instance
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G),
      TotallyDisconnectedSpace (S.X U) := fun _ => by
    infer_instance
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), IsTopologicalGroup (S.X U) :=
    fun _ => by
      infer_instance
  letI : Group S.inverseLimit := by infer_instance
  letI : IsTopologicalGroup S.inverseLimit := by infer_instance
  have hlim : e x ∈ Subgroup.closedCommutator S.inverseLimit := by
    rw [ProCGroups.Abelian.mem_closedCommutator_inverseLimit_iff
      (S := S) (directed_openNormalSubgroupInClass (C := C) (G := G) hForm)]
    intro U
    have hproj :
        S.projection U (e x) =
          openNormalSubgroupInClassProj (C := C) (G := G) U x := by
      simpa [S, e] using
        openNormalSubgroupInClassMulEquivInverseLimit_projection
          (C := C) (G := G) hForm hG U x
    rw [hproj]
    simpa [openNormalSubgroupInClassProj] using hx (OrderDual.ofDual U)
  have hmap :
      e x ∈
        ((Subgroup.closedCommutator G).map e.toMulEquiv.toMonoidHom :
          Subgroup S.inverseLimit) := by
    rw [Subgroup.closedCommutator_map_eq_of_equiv e]
    exact hlim
  rcases hmap with ⟨y, hy, hyx⟩
  have hy_eq : y = x := by
    exact e.toMulEquiv.injective hyx
  simpa [hy_eq] using hy

/-- Closed-commutator membership in a pro-`C` group is equivalent to closed-commutator
membership after every open-normal quotient whose quotient lies in `C`. -/
theorem mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) {x : G} :
    x ∈ Subgroup.closedCommutator G ↔
      ∀ U : OpenNormalSubgroupInClass C G,
        QuotientGroup.mk' (U.1 : Subgroup G) x ∈
          Subgroup.closedCommutator (G ⧸ (U.1 : Subgroup G)) := by
  constructor
  · intro hx U
    exact Subgroup.closedCommutator_map_le (OpenNormalSubgroupInClass.quotientProj (C := C) U)
      ⟨x, hx, rfl⟩
  · exact mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient hForm hG

/-- To prove membership in the closed commutator subgroup of a pro-`C` group, it is enough to
prove ordinary commutator membership in every finite open-normal quotient in `C`.

This is the finite-stage form used by Magnus-kernel arguments: each quotient stage is discrete, so
its closed commutator is the ordinary algebraic commutator subgroup. -/
theorem mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient_commutator
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass C G,
      QuotientGroup.mk' (U.1 : Subgroup G) x ∈
        commutator (G ⧸ (U.1 : Subgroup G))) :
    x ∈ Subgroup.closedCommutator G :=
  mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient hForm hG
    (by
      intro U
      simpa [Subgroup.closedCommutator_eq_commutator_of_discrete] using hx U)

/-- Cofinal finite-stage form of closed-commutator detection.

It is enough to prove ordinary commutator membership after passing, below every open-normal
quotient in `C`, to some smaller open-normal quotient in `C`. -/
theorem mem_closedCommutator_of_forall_exists_openNormalSubgroupInClass_le_quotient_commutator
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass C G,
      ∃ V : OpenNormalSubgroupInClass C G,
        (V.1 : Subgroup G) ≤ (U.1 : Subgroup G) ∧
          QuotientGroup.mk' (V.1 : Subgroup G) x ∈
            commutator (G ⧸ (V.1 : Subgroup G))) :
    x ∈ Subgroup.closedCommutator G := by
  refine
    mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient_commutator
      hForm hG ?_
  intro U
  rcases hx U with ⟨V, hVU, hxV⟩
  let qVU : G ⧸ (V.1 : Subgroup G) →* G ⧸ (U.1 : Subgroup G) :=
    QuotientGroup.map (V.1 : Subgroup G) (U.1 : Subgroup G)
      (MonoidHom.id G) (by
        intro g hg
        exact hVU hg)
  have hq :
      qVU (QuotientGroup.mk' (V.1 : Subgroup G) x) =
        QuotientGroup.mk' (U.1 : Subgroup G) x := by
    simp only [QuotientGroup.mk'_apply, QuotientGroup.map_mk, MonoidHom.id_apply, qVU]
  have hcomm_map :
      (commutator (G ⧸ (V.1 : Subgroup G))).map qVU ≤
        commutator (G ⧸ (U.1 : Subgroup G)) := by
    rw [_root_.map_commutator_eq]
    exact Subgroup.commutator_mono (by intro y hy; trivial) (by intro y hy; trivial)
  have hxU :
      qVU (QuotientGroup.mk' (V.1 : Subgroup G) x) ∈
        commutator (G ⧸ (U.1 : Subgroup G)) :=
    hcomm_map ⟨QuotientGroup.mk' (V.1 : Subgroup G) x, hxV, rfl⟩
  simpa [hq] using hxU

/-- Closed-commutator membership in a pro-`C` group is equivalent to ordinary commutator
membership after every finite open-normal quotient in `C`. -/
theorem mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient_commutator
    (hForm : FiniteGroupClass.Formation C) (hG : IsProCGroup C G) {x : G} :
    x ∈ Subgroup.closedCommutator G ↔
      ∀ U : OpenNormalSubgroupInClass C G,
        QuotientGroup.mk' (U.1 : Subgroup G) x ∈
          commutator (G ⧸ (U.1 : Subgroup G)) := by
  rw [mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient hForm hG]
  constructor
  · intro hx U
    simpa [Subgroup.closedCommutator_eq_commutator_of_discrete] using hx U
  · intro hx U
    simpa [Subgroup.closedCommutator_eq_commutator_of_discrete] using hx U

end IsProCGroup

namespace ProCGroup

/-- `ProCGroup`-namespace form of closed-commutator detection by finite open-normal quotients. -/
theorem mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [hG : ProCGroup ProC G] {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      QuotientGroup.mk' (U.1 : Subgroup G) x ∈
        Subgroup.closedCommutator (G ⧸ (U.1 : Subgroup G))) :
    x ∈ Subgroup.closedCommutator G :=
  IsProCGroup.mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient
    (C := ProC.finiteQuotientClass) ProC.finiteQuotientFormation hG.isProCGroup hx

/-- `ProCGroup`-namespace iff form of closed-commutator detection by finite open-normal
quotients. -/
theorem mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [hG : ProCGroup ProC G] {x : G} :
    x ∈ Subgroup.closedCommutator G ↔
      ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
        QuotientGroup.mk' (U.1 : Subgroup G) x ∈
          Subgroup.closedCommutator (G ⧸ (U.1 : Subgroup G)) :=
  IsProCGroup.mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient
    (C := ProC.finiteQuotientClass) ProC.finiteQuotientFormation hG.isProCGroup

/-- `ProCGroup`-namespace finite-stage form with ordinary commutators in the discrete quotient
stages. -/
theorem mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient_commutator
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [hG : ProCGroup ProC G] {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      QuotientGroup.mk' (U.1 : Subgroup G) x ∈
        commutator (G ⧸ (U.1 : Subgroup G))) :
    x ∈ Subgroup.closedCommutator G :=
  IsProCGroup.mem_closedCommutator_of_forall_openNormalSubgroupInClass_quotient_commutator
    (C := ProC.finiteQuotientClass) ProC.finiteQuotientFormation hG.isProCGroup hx

/-- `ProCGroup`-namespace cofinal finite-stage form with ordinary commutators. -/
theorem mem_closedCommutator_of_forall_exists_openNormalSubgroupInClass_le_quotient_commutator
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [hG : ProCGroup ProC G] {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      ∃ V : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
        (V.1 : Subgroup G) ≤ (U.1 : Subgroup G) ∧
          QuotientGroup.mk' (V.1 : Subgroup G) x ∈
            commutator (G ⧸ (V.1 : Subgroup G))) :
    x ∈ Subgroup.closedCommutator G :=
  IsProCGroup.mem_closedCommutator_of_forall_exists_openNormalSubgroupInClass_le_quotient_commutator
    (C := ProC.finiteQuotientClass) ProC.finiteQuotientFormation hG.isProCGroup hx

/-- `ProCGroup`-namespace iff form with ordinary commutators in the discrete quotient stages. -/
theorem mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient_commutator
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [hG : ProCGroup ProC G] {x : G} :
    x ∈ Subgroup.closedCommutator G ↔
      ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
        QuotientGroup.mk' (U.1 : Subgroup G) x ∈
          commutator (G ⧸ (U.1 : Subgroup G)) :=
  IsProCGroup.mem_closedCommutator_iff_forall_openNormalSubgroupInClass_quotient_commutator
    (C := ProC.finiteQuotientClass) ProC.finiteQuotientFormation hG.isProCGroup

end ProCGroup

end ProCGroups.ProC
