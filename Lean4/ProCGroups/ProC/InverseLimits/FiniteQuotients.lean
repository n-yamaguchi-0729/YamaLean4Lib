import ProCGroups.ProC.GroupPredicates.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/InverseLimits/FiniteQuotients.lean
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

/-- Any finite discrete group already lying in the class `C` is pro-`C`. -/
theorem of_finite_discrete (hquot : FiniteGroupClass.QuotientClosed C)
    [Finite G] [DiscreteTopology G] (hCG : C G) : IsProCGroup C G := by
  refine IsProCGroup.of_allOpenNormalQuotients (C := C)
    (G := G) (ProCGroups.IsProfiniteGroup.of_finite_discrete G) ?_
  intro U
  exact hquot (N := (U : Subgroup G)) hCG

/-- If `G` is pro-`C` and `C` is closed
under quotients, then every quotient of `G` by an open normal subgroup is again pro-`C`. -/
theorem quotient_openNormalSubgroup
    (hForm : FiniteGroupClass.Formation C)
    (hG : IsProCGroup C G) (U : OpenNormalSubgroup G) :
    IsProCGroup C (G ⧸ (U : Subgroup G)) := by
  letI : Finite (G ⧸ (U : Subgroup G)) := hG.finite_quotient U
  letI : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U)
  exact IsProCGroup.of_finite_discrete (C := C) (G := G ⧸ (U : Subgroup G))
    hForm.quotientClosed (hG.quotient_mem hForm U)

/-- Quotients by open normal subgroups in the class-indexing family are pro-`C`. -/
theorem quotient_openNormalSubgroupInClass
    (hquot : FiniteGroupClass.QuotientClosed C)
    (hG : IsProCGroup C G) (U : OpenNormalSubgroupInClass C G) :
    IsProCGroup C (G ⧸ (U.1 : Subgroup G)) :=
  by
    letI : Finite (G ⧸ (U.1 : Subgroup G)) := hG.finite_quotient U.1
    letI : DiscreteTopology (G ⧸ (U.1 : Subgroup G)) :=
      QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U.1)
    exact IsProCGroup.of_finite_discrete (C := C)
      (G := G ⧸ (U.1 : Subgroup G)) hquot U.2

-- Product permanence for pro-`C` groups reduces an open normal subgroup of a product to a finite
-- product of open normal subgroups, then uses formation closure for the resulting finite quotient.
/-- Arbitrary products of pro-`C` groups remain pro-`C` when `C` is a formation. -/
theorem pi {α : Type u} {β : α → Type u}
    [∀ a, Group (β a)] [∀ a, TopologicalSpace (β a)] [∀ a, IsTopologicalGroup (β a)]
    (hForm : FiniteGroupClass.Formation C)
    (hβ : ∀ a, IsProCGroup C (β a)) :
    IsProCGroup C ((a : α) → β a) := by
  classical
  let G : Type u := (a : α) → β a
  letI : Group G := by
    dsimp [G]
    infer_instance
  letI : TopologicalSpace G := by
    dsimp [G]
    infer_instance
  letI : IsTopologicalGroup G := by
    dsimp [G]
    infer_instance
  have hProf : IsProfiniteGroup G := by
    letI : ∀ a, CompactSpace (β a) := fun a => IsProCGroup.compactSpace (hβ a)
    letI : ∀ a, T2Space (β a) := fun a => IsProCGroup.t2Space (hβ a)
    letI : ∀ a, TotallyDisconnectedSpace (β a) := fun a =>
      IsProCGroup.totallyDisconnectedSpace (hβ a)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  refine IsProCGroup.of_allOpenNormalQuotients (C := C) (G := G) hProf ?_
  intro U
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hProf
  letI : T2Space G := IsProfiniteGroup.t2Space hProf
  let hUnhds : ((U : Subgroup G) : Set G) ∈ 𝓝 (1 : G) := by
    exact U.toOpenSubgroup.isOpen'.mem_nhds U.one_mem'
  rcases mem_nhds_iff.mp hUnhds with ⟨W, hWU, hWopen, h1W⟩
  rcases (isOpen_pi_iff.mp hWopen) (1 : G) h1W with ⟨J, WJ, hJ1, hJ2⟩
  let V : ∀ j : J, OpenNormalSubgroup (β j) := fun j =>
    Classical.choose <|
      IsProCGroup.hasOpenNormalBasisInClass (C := C) (G := β j) (hβ j) (WJ j)
        (hJ1 j j.property).1 (hJ1 j j.property).2
  have hVsub : ∀ j : J, ((V j : Subgroup (β j)) : Set (β j)) ⊆ WJ j := fun j =>
    (Classical.choose_spec <|
      IsProCGroup.hasOpenNormalBasisInClass (C := C) (G := β j) (hβ j) (WJ j)
        (hJ1 j j.property).1 (hJ1 j j.property).2).1
  have hVquot : ∀ j : J, C (β j ⧸ (V j : Subgroup (β j))) := fun j =>
    (Classical.choose_spec <|
      IsProCGroup.hasOpenNormalBasisInClass (C := C) (G := β j) (hβ j) (WJ j)
        (hJ1 j j.property).1 (hJ1 j j.property).2).2
  let M : Subgroup G :=
    iInf fun j : J =>
      ((OpenNormalSubgroup.comap
        ({ toFun := fun g : G => g j.1
           map_one' := rfl
           map_mul' := by intro x y; rfl } : G →* β j.1)
        (continuous_apply j.1) (V j) : OpenNormalSubgroup G) : Subgroup G)
  letI : M.Normal := by
    exact Subgroup.normal_iInf_normal fun j : J =>
      (OpenNormalSubgroup.comap
        ({ toFun := fun g : G => g j.1
           map_one' := rfl
           map_mul' := by intro x y; rfl } : G →* β j.1)
        (continuous_apply j.1) (V j)).isNormal'
  have hMU : M ≤ (U : Subgroup G) := by
    intro x hx
    apply hWU
    apply hJ2
    intro j hj
    have hxall :
        ∀ k : J,
          x ∈ OpenNormalSubgroup.comap
            ({ toFun := fun g : G => g k.1
               map_one' := rfl
               map_mul' := by intro a b; rfl } : G →* β k.1)
            (continuous_apply k.1) (V k) := by
      simpa [M, Subgroup.mem_iInf] using hx
    have hxj :
        x ∈ OpenNormalSubgroup.comap
          ({ toFun := fun g : G => g j
             map_one' := rfl
             map_mul' := by intro a b; rfl } : G →* β j)
          (continuous_apply j) (V ⟨j, hj⟩) :=
      hxall ⟨j, hj⟩
    have hxj' : x j ∈ (V ⟨j, hj⟩ : Subgroup (β j)) := by
      simpa using hxj
    exact hVsub ⟨j, hj⟩ hxj'
  let φ : G →* ∀ j : J, β j ⧸ (V j : Subgroup (β j)) :=
    { toFun := fun g j => QuotientGroup.mk' (V j : Subgroup (β j)) (g j)
      map_one' := by funext j; rfl
      map_mul' := by intro x y; funext j; rfl }
  have hProd : C (∀ j : J, β j ⧸ (V j : Subgroup (β j))) := by
    exact FiniteGroupClass.Formation.finiteProductClosed (C := C) hForm hVquot
  have hRange : C φ.range := by
    let ψ : φ.range →* ∀ j : J, β j ⧸ (V j : Subgroup (β j)) :=
      φ.range.subtype
    have hψinj : Function.Injective ψ := Subtype.coe_injective
    have hψsurj : ∀ j : J, Function.Surjective fun x : φ.range => ψ x j := by
      intro j y
      rcases QuotientGroup.mk'_surjective (V j : Subgroup (β j)) y with ⟨xj, rfl⟩
      let g : G := Function.update 1 j.1 xj
      refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
      simp only [QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.subtype_apply,
  Function.update_self, φ, ψ, g]
    exact hForm.finiteSubdirectProductClosed ψ hψinj hψsurj hVquot
  have hKerEq : M = φ.ker := by
    ext x
    constructor
    · intro hx
      have hxM : ∀ j : J, x j.1 ∈ (V j : Subgroup (β j)) := by
        simpa [M, Subgroup.mem_iInf] using hx
      change (fun j : J => QuotientGroup.mk' (V j : Subgroup (β j)) (x j.1)) = 1
      funext j
      exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (β j))) (x j.1)).2 (hxM j)
    · intro hx
      have hxker :
          (fun j : J => QuotientGroup.mk' (V j : Subgroup (β j)) (x j.1)) = 1 := by
        simpa [MonoidHom.mem_ker, φ] using hx
      have hxM : ∀ j : J, x j.1 ∈ (V j : Subgroup (β j)) := by
        intro j
        exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (β j))) (x j.1)).1
          (congrArg (fun f : (j : J) → β j ⧸ (V j : Subgroup (β j)) => f j) hxker)
      simpa [M, Subgroup.mem_iInf] using hxM
  have hQuotM : C (G ⧸ M) := by
    let e1 : G ⧸ M ≃* G ⧸ φ.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hForm.isomClosed
      ⟨(e1.trans (QuotientGroup.quotientKerEquivRange φ)).symm⟩
      hRange
  have hQuotU' :
      C ((G ⧸ M) ⧸ Subgroup.map (QuotientGroup.mk' M) (U : Subgroup G)) := by
    exact hForm.quotientClosed
      (N := Subgroup.map (QuotientGroup.mk' M) (U : Subgroup G)) hQuotM
  exact hForm.isomClosed
    ⟨QuotientGroup.quotientQuotientEquivQuotient M (U : Subgroup G) hMU⟩
    hQuotU'

/-- Pro-`C` is preserved by continuous multiplicative equivalences. -/
theorem ofContinuousMulEquiv {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H]
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : IsProCGroup C G) (e : G ≃ₜ* H) :
    IsProCGroup C H := by
  letI : CompactSpace G := IsProCGroup.compactSpace hG
  letI : T2Space G := IsProCGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProCGroup.totallyDisconnectedSpace hG
  letI : CompactSpace H := e.toHomeomorph.compactSpace
  letI : T2Space H := e.toHomeomorph.t2Space
  letI : TotallyDisconnectedSpace H := e.toHomeomorph.totallyDisconnectedSpace
  refine IsProCGroup.of_allOpenNormalQuotients (C := C) (G := H)
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ ?_
  intro U
  let V : OpenNormalSubgroup G :=
    OpenNormalSubgroup.comap
      (e.toMulEquiv.toMonoidHom : G →* H)
      e.continuous
      U
  have hquotV : C (G ⧸ (V : Subgroup G)) :=
    IsProCGroup.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
      hIso hQuot hG V
  let φ : G ⧸ (V : Subgroup G) →* H ⧸ (U : Subgroup H) :=
    QuotientGroup.map _ _ (e.toMulEquiv.toMonoidHom) <| by
      intro g hg
      change e g ∈ (U : Subgroup H)
      simpa [V, OpenNormalSubgroup.toSubgroup_comap] using hg
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective (V : Subgroup G) x with ⟨gx, rfl⟩
    rcases QuotientGroup.mk'_surjective (V : Subgroup G) y with ⟨gy, rfl⟩
    apply QuotientGroup.eq.2
    change e (gx⁻¹ * gy) ∈ (U : Subgroup H)
    simpa [φ, map_mul] using QuotientGroup.eq.1 (by
      simpa [φ] using hxy)
  have hφsurj : Function.Surjective φ := by
    intro x
    rcases QuotientGroup.mk'_surjective (U : Subgroup H) x with ⟨h, rfl⟩
    refine ⟨QuotientGroup.mk' (V : Subgroup G) (e.symm h), ?_⟩
    change QuotientGroup.mk' (U : Subgroup H) (e (e.symm h)) = QuotientGroup.mk' (U : Subgroup H) h
    simp only [ContinuousMulEquiv.apply_symm_apply, QuotientGroup.mk'_apply]
  exact hIso ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩ hquotV

end IsProCGroup

namespace ProCGroup

/-- A finite discrete group in the induced finite quotient class is a bundled `ProCGroup`. -/
theorem of_finite_discrete
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    {Q : Type u} [Group Q] [TopologicalSpace Q]
    [Finite Q] [DiscreteTopology Q]
    (hQ : ProC.finiteQuotientClass Q) :
    ProCGroup ProC Q :=
  ProCGroup.of_isProCGroup ProC Q
    (IsProCGroup.of_finite_discrete
      (C := ProC.finiteQuotientClass) ProC.finiteQuotientQuotientClosed hQ)

/-- Transport a bundled `ProCGroup` structure across a continuous multiplicative equivalence. -/
theorem ofContinuousMulEquiv
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [hG : ProCGroup ProC G] (e : G ≃ₜ* H) :
    ProCGroup ProC H :=
  ProCGroup.of_isProCGroup ProC H
    (IsProCGroup.ofContinuousMulEquiv
      (C := ProC.finiteQuotientClass)
      ProC.finiteQuotientIsomClosed ProC.finiteQuotientQuotientClosed hG.isProCGroup e)

/-- Products of bundled `ProCGroup`s are bundled `ProCGroup`s. -/
theorem pi
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    {α : Type u} {β : α → Type u}
    [∀ a, Group (β a)] [∀ a, TopologicalSpace (β a)]
    [∀ a, IsTopologicalGroup (β a)]
    [hβ : ∀ a, ProCGroup ProC (β a)] :
    ProCGroup ProC ((a : α) → β a) :=
  ProCGroup.of_isProCGroup ProC ((a : α) → β a)
    (IsProCGroup.pi
      (C := ProC.finiteQuotientClass)
      ProC.finiteQuotientFormation
      (fun a => (hβ a).isProCGroup))

/-- Open normal quotients of a bundled `ProCGroup` are bundled `ProCGroup`s. -/
theorem quotient_openNormalSubgroup
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G] (U : OpenNormalSubgroup G) :
    ProCGroup ProC (G ⧸ (U : Subgroup G)) :=
  ProCGroup.of_isProCGroup ProC (G ⧸ (U : Subgroup G))
    (IsProCGroup.quotient_openNormalSubgroup
      ProC.finiteQuotientFormation hG.isProCGroup U)

/-- Open-normal-in-class quotients of a bundled `ProCGroup` are bundled `ProCGroup`s. -/
theorem quotient_openNormalSubgroupInClass
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    [hG : ProCGroup ProC G] (U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G) :
    ProCGroup ProC (G ⧸ (U.1 : Subgroup G)) :=
  quotient_openNormalSubgroup (G := G) ProC U.1

end ProCGroup

/-- Specialization of `IsProCGroup` to the class of all finite groups: this is exactly
profiniteness. -/
theorem isProC_allFinite_iff_isProfiniteGroup
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    IsProCGroup FiniteGroupClass.allFinite G ↔ IsProfiniteGroup G := by
  constructor
  · intro hG
    exact hG.isProfinite
  · intro hG
    refine ⟨hG, ?_⟩
    intro W hW h1W
    letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
    letI : T2Space G := IsProfiniteGroup.t2Space hG
    letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
    rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W with ⟨U, hUW⟩
    exact ⟨U, hUW, openNormalSubgroup_finiteQuotient (G := G) U⟩

end

end ProCGroups.ProC
