import ProCGroups.ProC.InverseLimits.Limits

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Subgroups/Closed.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace IsProCGroup

/-- Closed-subgroup permanence for pro-`C` groups.

The proof follows the standard finite-quotient argument: for an open normal subgroup `U` of the
closed subgroup `H`, choose an ambient open normal subgroup `V` of `G` with `V ∩ H ≤ U`, identify
`H / (V ∩ H)` with a subgroup of `G / V`, then pass to the quotient `H / U`.

The proof uses ambient open-normal approximation and finite quotient comparison. -/
theorem of_closedSubgroup
    (hIso : FiniteGroupClass.IsomClosed C)
    (hSub : FiniteGroupClass.SubgroupClosed C)
    (_hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : IsProCGroup C G) (H : ClosedSubgroup G) :
    IsProCGroup C ↥(H : Subgroup G) := by
  refine ⟨IsProfiniteGroup.of_closedSubgroup (G := G) hG.isProfinite H, ?_⟩
  intro W hW h1W
  letI : CompactSpace G := IsProCGroup.compactSpace hG
  letI : T2Space G := IsProCGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProCGroup.totallyDisconnectedSpace hG
  have hW_nhds : W ∈ 𝓝 (1 : H) := hW.mem_nhds h1W
  rcases (mem_nhds_subtype (H : Set G) (1 : H) W).1 hW_nhds with
    ⟨W₀, hW₀_nhds, hW₀W⟩
  rcases mem_nhds_iff.mp hW₀_nhds with ⟨W', hW'W₀, hW'open, h1W'⟩
  rcases hG.hasOpenNormalBasisInClass W' hW'open h1W' with
    ⟨V, hVW', hCV⟩
  let VH : OpenNormalSubgroup H :=
    OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V
  have hVHW : (((VH : Subgroup H) : Set H)) ⊆ W := by
    intro x hx
    exact hW₀W <| by
      change x.1 ∈ W₀
      exact hW'W₀ (hVW' hx)
  let ψ : H →* G ⧸ (V : Subgroup G) :=
    (QuotientGroup.mk' (V : Subgroup G)).comp ((H : Subgroup G).subtype)
  have hRange : C ψ.range := hSub ψ.range hCV
  have hKerEq : (VH : Subgroup H) = ψ.ker := by
    ext x
    constructor
    · intro hx
      simpa [MonoidHom.mem_ker, ψ] using
        (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) x.1).2 hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) x.1).1
        (by simpa [MonoidHom.mem_ker, ψ] using hx)
  have hQuotVH : C (H ⧸ (VH : Subgroup H)) := by
    let e1 : H ⧸ (VH : Subgroup H) ≃* H ⧸ ψ.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hIso
      ⟨(e1.trans (QuotientGroup.quotientKerEquivRange ψ)).symm⟩
      hRange
  exact ⟨VH, hVHW, hQuotVH⟩

/-- Closed-subgroup permanence using an ordinary subgroup together with a closedness proof. -/
theorem of_isClosed_subgroup
    (hIso : FiniteGroupClass.IsomClosed C)
    (hSub : FiniteGroupClass.SubgroupClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : IsProCGroup C G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsProCGroup C H := by
  exact ProCGroups.of_isClosed_subgroup_of_closedSubgroup
    (G := G) (P := fun H => IsProCGroup C ↥H)
    (of_closedSubgroup (C := C) hIso hSub hQuot hG) H hH

/-- Closed-subgroup permanence for pro-`C` groups from a full formation package. -/
theorem of_closedSubgroup_of_fullFormation
    (hC : FiniteGroupClass.FullFormation C)
    (hG : IsProCGroup C G) (H : ClosedSubgroup G) :
    IsProCGroup C ↥(H : Subgroup G) :=
  of_closedSubgroup hC.isomClosed hC.subgroupClosed hC.quotientClosed hG H

/-- Closed-subgroup permanence in ordinary subgroup form from a full formation package. -/
theorem of_isClosed_subgroup_of_fullFormation
    (hC : FiniteGroupClass.FullFormation C)
    (hG : IsProCGroup C G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsProCGroup C H :=
  of_isClosed_subgroup hC.isomClosed hC.subgroupClosed hC.quotientClosed hG H hH

/-- The range of a continuous homomorphism from a pro-`C` group to a Hausdorff topological group is
again pro-`C`, with the induced subtype topology. -/
theorem range
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : IsProCGroup C G)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) :
    IsProCGroup C f.toMonoidHom.range := by
  letI : CompactSpace G := hG.compactSpace
  let K : Subgroup G := f.toMonoidHom.ker
  have hKclosed : IsClosed (K : Set G) := by
    dsimp [K]
    exact f.isClosed_ker
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  have hQuotG : IsProCGroup C (G ⧸ K) :=
    quotient_closedNormalSubgroup (C := C) hIso hQuot hG K hKclosed
  have e : (G ⧸ K) ≃ₜ* f.toMonoidHom.range := by
    simpa [K] using ContinuousMonoidHom.quotientKerContinuousMulEquivRange f
  exact IsProCGroup.ofContinuousMulEquiv (C := C) (G := G ⧸ K) hIso hQuot hQuotG e

end IsProCGroup

namespace ProCGroup

/-- A closed subgroup of a `ProCGroup`, bundled as a `ClosedSubgroup`, is again a `ProCGroup`. -/
theorem of_closedSubgroup
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G] (H : ClosedSubgroup G) :
    ProCGroup ProC ↥(H : Subgroup G) :=
  ProCGroup.of_isProCGroup ProC ↥(H : Subgroup G)
    (IsProCGroup.of_closedSubgroup
      ProC.finiteQuotientIsomClosed
      ProC.finiteQuotientHereditary.subgroupClosed
      ProC.finiteQuotientQuotientClosed
      hG.isProCGroup H)

/-- A closed subgroup of a `ProCGroup` is again a `ProCGroup`.

The finite quotient input is the standard Melnikov-formation package together with hereditary
subgroup closure. -/
theorem of_isClosed_subgroup
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G] (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ProCGroup ProC H :=
  ProCGroup.of_isProCGroup ProC H
    (IsProCGroup.of_isClosed_subgroup
      ProC.finiteQuotientIsomClosed
      ProC.finiteQuotientHereditary.subgroupClosed
      ProC.finiteQuotientQuotientClosed
      hG.isProCGroup H hH)

/-- A quotient by a closed normal subgroup of a `ProCGroup` is again a
`ProCGroup`. -/
theorem quotient_closedNormalSubgroup
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G] (K : Subgroup G) [K.Normal] (hK : IsClosed (K : Set G)) :
    ProCGroup ProC (G ⧸ K) :=
  ProCGroup.of_isProCGroup ProC (G ⧸ K)
    (ProCGroups.ProC.quotient_closedNormalSubgroup
      ProC.finiteQuotientIsomClosed
      ProC.finiteQuotientQuotientClosed
      hG.isProCGroup K hK)

/-- The range of a continuous homomorphism from a `ProCGroup` to a Hausdorff topological group is
again a `ProCGroup`, with the induced subtype topology. -/
theorem range
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) :
    ProCGroup ProC f.toMonoidHom.range :=
  ProCGroup.of_isProCGroup ProC f.toMonoidHom.range
    (IsProCGroup.range
      ProC.finiteQuotientIsomClosed
      ProC.finiteQuotientQuotientClosed
      hG.isProCGroup f)

/-- A Hausdorff continuous quotient of a `ProCGroup` is again a `ProCGroup`. -/
theorem of_surjective
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation]
    [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    ProCGroup ProC H := by
  let R : Subgroup H := f.toMonoidHom.range
  have hR : ProCGroup ProC R := range (ProC := ProC) (G := G) f
  letI : ProCGroup ProC R := hR
  have hcompactR : CompactSpace R := hR.isProCGroup.compactSpace
  letI : CompactSpace R := hcompactR
  let e : R ≃ₜ* H :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 (Subgroup.subtype R)
      continuous_subtype_val
      ⟨by
        intro x y hxy
        exact Subtype.ext hxy,
       by
        intro h
        rcases hf h with ⟨g, rfl⟩
        exact ⟨⟨f g, ⟨g, rfl⟩⟩, rfl⟩⟩
  exact ProCGroup.ofContinuousMulEquiv (G := R) ProC e

end ProCGroup

namespace IsProCGroup

variable {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]

/-- Extension permanence for pro-`C` groups.

We assume `E` is already profinite; the `pro-`C` conclusion is then obtained by checking each
open-normal finite quotient of `E`.

Extensions of pro-`C` groups remain pro-`C` once the ambient group is known to be profinite. -/
theorem extension
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hExt : FiniteGroupClass.ExtensionClosed C)
    (hE : IsProfiniteGroup E)
    (K : Subgroup E) [K.Normal]
    (hK : IsProCGroup C K) (hQ : IsProCGroup C (E ⧸ K)) :
    IsProCGroup C E := by
  refine IsProCGroup.of_allOpenNormalQuotients (C := C) hE ?_
  intro U
  letI : CompactSpace E := IsProfiniteGroup.compactSpace hE
  letI : T2Space E := IsProfiniteGroup.t2Space hE
  letI : CompactSpace (E ⧸ K) := IsProfiniteGroup.compactSpace hQ.isProfinite
  letI : T2Space (E ⧸ K) := IsProfiniteGroup.t2Space hQ.isProfinite
  letI : CompactSpace K := IsProfiniteGroup.compactSpace hK.isProfinite
  letI : T2Space K := IsProfiniteGroup.t2Space hK.isProfinite
  let M : Subgroup E := K ⊔ (U : Subgroup E)
  let Wsub : Subgroup (E ⧸ K) := Subgroup.map (QuotientGroup.mk' K) M
  have hWclosed : IsClosed (Wsub : Set (E ⧸ K)) := by
    have hMclosed : IsClosed (M : Set E) := by
      have hMopen : IsOpen (M : Set E) := by
        exact Subgroup.isOpen_of_openSubgroup M (show (U : Subgroup E) ≤ M from le_sup_right)
      exact Subgroup.isClosed_of_isOpen M hMopen
    have hMcompact : IsCompact (M : Set E) := hMclosed.isCompact
    have hcont : Continuous (QuotientGroup.mk' K : E → E ⧸ K) := continuous_quotient_mk'
    have himage : IsCompact ((QuotientGroup.mk' K) '' (M : Set E)) := hMcompact.image hcont
    have hEq : (QuotientGroup.mk' K) '' (M : Set E) = (Wsub : Set (E ⧸ K)) := by
      ext x
      simp only [QuotientGroup.mk'_apply, mem_image, SetLike.mem_coe, Subgroup.coe_map, M, Wsub]
    rw [← hEq]
    exact himage.isClosed
  have hWfinite : Finite ((E ⧸ K) ⧸ Wsub) := by
    have hMopen : IsOpen (M : Set E) := by
      exact Subgroup.isOpen_of_openSubgroup M (show (U : Subgroup E) ≤ M from le_sup_right)
    have hMfinite : Finite (E ⧸ M) :=
      (subgroup_isOpen_iff_isClosed_finite_quotient (G := E) (U := M)).1 hMopen |>.2
    let e : (E ⧸ K) ⧸ Wsub ≃* E ⧸ M := by
      simpa [Wsub, M, Subgroup.map_sup] using
        (QuotientGroup.quotientQuotientEquivQuotient K M (show K ≤ M from le_sup_left))
    exact Finite.of_injective e e.injective
  have hWopen : IsOpen (Wsub : Set (E ⧸ K)) :=
    (subgroup_isOpen_iff_isClosed_finite_quotient (G := E ⧸ K) (U := Wsub)).2
      ⟨hWclosed, hWfinite⟩
  letI : Wsub.Normal := by
    dsimp [Wsub, M]
    have hMnormal : M.Normal := by infer_instance
    exact Subgroup.Normal.map hMnormal (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  let W : OpenNormalSubgroup (E ⧸ K) :=
    { toOpenSubgroup := ⟨Wsub, hWopen⟩
      isNormal' := inferInstance }
  have hQuotM : C (E ⧸ M) := by
    let e : (E ⧸ K) ⧸ (W : Subgroup (E ⧸ K)) ≃* E ⧸ M := by
      simpa [W, Wsub, M, Subgroup.map_sup] using
        (QuotientGroup.quotientQuotientEquivQuotient K M (show K ≤ M from le_sup_left))
    exact hIso ⟨e⟩
      (IsProCGroup.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
        hIso hQuot hQ W)
  let KU : OpenNormalSubgroup K :=
    OpenNormalSubgroup.comap (K.subtype) continuous_subtype_val U
  let ψ : K →* E ⧸ (U : Subgroup E) :=
    (QuotientGroup.mk' (U : Subgroup E)).comp K.subtype
  have hKerEq : (KU : Subgroup K) = ψ.ker := by
    ext x
    constructor
    · intro hx
      simpa [MonoidHom.mem_ker, KU, ψ] using
        (QuotientGroup.eq_one_iff (N := (U : Subgroup E)) x.1).2 hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := (U : Subgroup E)) x.1).1
        (by simpa [MonoidHom.mem_ker, KU, ψ] using hx)
  have hKernelC : C ψ.range := by
    have hQuotKU : C (K ⧸ (KU : Subgroup K)) :=
      IsProCGroup.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
        hIso hQuot hK KU
    let e1 : K ⧸ (KU : Subgroup K) ≃* K ⧸ ψ.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hIso ⟨e1.trans (QuotientGroup.quotientKerEquivRange ψ)⟩ hQuotKU
  let L : Subgroup (E ⧸ (U : Subgroup E)) := Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) K
  have hRangeEq : ψ.range = L := by
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.coe_comp, QuotientGroup.coe_mk', Subgroup.coe_subtype,
  Function.comp_apply, Subtype.exists, exists_prop, Subgroup.mem_map, QuotientGroup.mk'_apply, ψ, L]
  have hLC : C L := by
    exact hIso ⟨MulEquiv.subgroupCongr hRangeEq⟩ hKernelC
  have hMapUbot : Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) (U : Subgroup E) = ⊥ := by
    ext x
    constructor
    · intro hx
      rcases (Subgroup.mem_map).1 hx with ⟨u, hu, hux⟩
      rw [Subgroup.mem_bot]
      have hu1 : QuotientGroup.mk' (U : Subgroup E) u = 1 :=
        (QuotientGroup.eq_one_iff (N := (U : Subgroup E)) u).2 hu
      exact hux.symm.trans hu1
    · intro hx
      rcases Subgroup.mem_bot.1 hx with rfl
      exact ⟨1, U.one_mem, by simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one]⟩
  have hMapM : Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M = L := by
    calc
      Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M
          = Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) K ⊔
              Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) (U : Subgroup E) := by
                simp only [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_le, sup_of_le_left, M]
      _ = L ⊔ ⊥ := by simp only [hMapUbot, bot_le, sup_of_le_left, L]
      _ = L := by simp only [bot_le, sup_of_le_left]
  have hQuotL : C ((E ⧸ (U : Subgroup E)) ⧸ L) := by
    let e0 : (E ⧸ (U : Subgroup E)) ⧸ L ≃* (E ⧸ (U : Subgroup E)) ⧸
        Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M :=
      QuotientGroup.quotientMulEquivOfEq hMapM.symm
    let e1 : (E ⧸ (U : Subgroup E)) ⧸
        Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M ≃* E ⧸ M :=
      QuotientGroup.quotientQuotientEquivQuotient (U : Subgroup E) M
        (show (U : Subgroup E) ≤ M from le_sup_right)
    exact hIso ⟨(e0.trans e1).symm⟩ hQuotM
  letI : L.Normal := by
    dsimp [L]
    exact Subgroup.Normal.map inferInstance (QuotientGroup.mk' (U : Subgroup E))
      (QuotientGroup.mk'_surjective (U : Subgroup E))
  exact hExt L hLC hQuotL

end IsProCGroup

end

end ProCGroups.ProC
