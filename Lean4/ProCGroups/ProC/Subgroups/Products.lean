import ProCGroups.ProC.Subgroups.Closed

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Subgroups/Products.lean
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

universe u v w

open InverseSystems

section

variable {ι : Type (max u v)}
variable {G₁ : Type u} {G₂ : Type v}
variable {Gs : ι → Type (max u v)}
variable {C : FiniteGroupClass.{max u v}}

variable [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
variable [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable [∀ i, Group (Gs i)]
variable [∀ i, TopologicalSpace (Gs i)]
variable [∀ i, IsTopologicalGroup (Gs i)]

/--
A closed subgroup of a product of profinite groups is profinite.
This is a direct theorem around the already-completed `pi` and closed-subgroup permanence lemmas.
-/
theorem IsProfiniteGroup.of_closedSubgroup_pi
    {H : Subgroup ((i : ι) → Gs i)}
    (hH : IsClosed (((H : Subgroup ((i : ι) → Gs i)) : Set ((i : ι) → Gs i))))
    (hGs : ∀ i, IsProfiniteGroup (Gs i)) :
    IsProfiniteGroup H := by
  have hpi : IsProfiniteGroup ((i : ι) → Gs i) :=
    IsProfiniteGroup.pi (β := Gs) hGs
  simpa using
    (IsProfiniteGroup.of_isClosed_subgroup
      (G := ((i : ι) → Gs i))
      (H := H)
      (hG := hpi)
      hH)

/--
A closed subgroup of a binary product of profinite groups is profinite.
This is the finite-product specialization of `IsProfiniteGroup.of_closedSubgroup_pi`.
-/
theorem IsProfiniteGroup.of_closedSubgroup_prod
    {H : Subgroup (G₁ × G₂)}
    (hH : IsClosed (((H : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))))
    (hG₁ : IsProfiniteGroup G₁) (hG₂ : IsProfiniteGroup G₂) :
    IsProfiniteGroup H := by
  have hprod : IsProfiniteGroup (G₁ × G₂) :=
    IsProfiniteGroup.prod (G := G₁) (H := G₂) hG₁ hG₂
  simpa using
    (IsProfiniteGroup.of_isClosed_subgroup
      (G := G₁ × G₂)
      (H := H)
      (hG := hprod)
      hH)

/--
A closed subgroup of a product of pro-`C` groups is pro-`C`.
This is the pro-class analogue of `IsProfiniteGroup.of_closedSubgroup_pi`.
-/
theorem IsProCGroup.of_closedSubgroup_pi
    {H : Subgroup ((i : ι) → Gs i)}
    (hH : IsClosed (((H : Subgroup ((i : ι) → Gs i)) : Set ((i : ι) → Gs i))))
    (hForm : FiniteGroupClass.Formation C)
    (hSub : FiniteGroupClass.SubgroupClosed C)
    (hGs : ∀ i, IsProCGroup C (Gs i)) :
    IsProCGroup C ↥H := by
  have hpi : IsProCGroup C ((i : ι) → Gs i) :=
    IsProCGroup.pi (C := C) (α := ι) (β := Gs) hForm hGs
  simpa using
    (IsProCGroup.of_isClosed_subgroup
      (C := C)
      (G := ((i : ι) → Gs i))
      (H := H)
      hForm.isomClosed
      hSub
      hForm.quotientClosed
      (hG := hpi)
      hH)

omit [∀ i, IsTopologicalGroup (Gs i)] in
/-- A profinite group embedded as a subdirect product of pro-`C` groups is itself pro-`C`.

The proof checks the finite-quotient criterion directly: an open normal subgroup of `H` pulls back
from finitely many coordinate open normal subgroups, and the resulting finite quotient is a finite
subdirect product of finite quotients lying in `C`.

The proof is organized coordinatewise so that downstream arguments can reuse the finite-subdirect
product step without reopening the entire compactness argument. -/
theorem IsProCGroup.of_subdirectProduct
    {H : Type (max u v)} [Group H] [TopologicalSpace H]
    (hH : IsProfiniteGroup H)
    (φ : H →* ((i : ι) → Gs i)) (hφcont : Continuous φ)
    (hφinj : Function.Injective φ)
    (hφsurj : ∀ i, Function.Surjective (fun x : H => φ x i))
      (hForm : FiniteGroupClass.Formation C)
      (hGs : ∀ i, IsProCGroup C (Gs i)) :
      IsProCGroup C H := by
  classical
  letI : IsTopologicalGroup H := hH.isTopologicalGroup
  letI : CompactSpace H := IsProfiniteGroup.compactSpace hH
  letI : T2Space H := IsProfiniteGroup.t2Space hH
  letI : TotallyDisconnectedSpace H := IsProfiniteGroup.totallyDisconnectedSpace hH
  letI : ∀ i, CompactSpace (Gs i) := fun i => IsProCGroup.compactSpace (hGs i)
  letI : ∀ i, T2Space (Gs i) := fun i => IsProCGroup.t2Space (hGs i)
  letI : ∀ i, TotallyDisconnectedSpace (Gs i) := fun i =>
    IsProCGroup.totallyDisconnectedSpace (hGs i)
  let φrange : H →* ↥(φ.range : Subgroup ((i : ι) → Gs i)) := φ.rangeRestrict
  have hφrange_continuous : Continuous φrange := by
    change Continuous (fun x : H => (⟨φ x, ⟨x, rfl⟩⟩ : ↥(φ.range : Subgroup ((i : ι) → Gs i))))
    exact Continuous.subtype_mk hφcont (fun x => ⟨x, rfl⟩)
  have hφrange_bij : Function.Bijective φrange := by
    constructor
    · intro x y hxy
      apply hφinj
      exact congrArg Subtype.val hxy
    · exact φ.rangeRestrict_surjective
  let e : H ≃ₜ* ↥(φ.range : Subgroup ((i : ι) → Gs i)) :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 φrange hφrange_continuous hφrange_bij
  refine IsProCGroup.of_allOpenNormalQuotients (C := C) hH ?_
  intro U
  let imgU : Set ↥(φ.range : Subgroup ((i : ι) → Gs i)) :=
    e.toHomeomorph '' (((U : Subgroup H) : Set H))
  have himgU_open : IsOpen imgU := e.toHomeomorph.isOpenMap _ U.isOpen'
  have h1imgU : (1 : ↥(φ.range : Subgroup ((i : ι) → Gs i))) ∈ imgU := by
    refine ⟨1, U.one_mem', ?_⟩
    change e 1 = 1
    simp only [map_one]
  have himgU_nhds : imgU ∈ 𝓝 (1 : ↥(φ.range : Subgroup ((i : ι) → Gs i))) := by
    exact himgU_open.mem_nhds h1imgU
  rcases (mem_nhds_subtype
      ((φ.range : Subgroup ((i : ι) → Gs i)) : Set ((i : ι) → Gs i))
      (1 : ↥(φ.range : Subgroup ((i : ι) → Gs i))) imgU).1 himgU_nhds with
    ⟨W, hW_nhds, hWU⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W', hW'W, hW'open, h1W'⟩
  rcases (isOpen_pi_iff.mp hW'open) (1 : (i : ι) → Gs i) h1W' with ⟨J, WJ, hJ1, hJ2⟩
  let V : ∀ j : J, OpenNormalSubgroup (Gs j) := fun j =>
    Classical.choose <|
      IsProCGroup.hasOpenNormalBasisInClass (C := C) (G := Gs j) (hGs j) (WJ j)
        (hJ1 j j.property).1 (hJ1 j j.property).2
  have hVsub : ∀ j : J, ((V j : Subgroup (Gs j)) : Set (Gs j)) ⊆ WJ j := fun j =>
    (Classical.choose_spec <|
      IsProCGroup.hasOpenNormalBasisInClass (C := C) (G := Gs j) (hGs j) (WJ j)
        (hJ1 j j.property).1 (hJ1 j j.property).2).1
  have hVquot : ∀ j : J, C (Gs j ⧸ (V j : Subgroup (Gs j))) := fun j =>
    (Classical.choose_spec <|
      IsProCGroup.hasOpenNormalBasisInClass (C := C) (G := Gs j) (hGs j) (WJ j)
        (hJ1 j j.property).1 (hJ1 j j.property).2).2
  let ψ : ∀ j : J, H →* Gs j := fun j =>
    { toFun := fun h => φ h j
      map_one' := by simp only [map_one, Pi.one_apply]
      map_mul' := by intro x y; simp only [map_mul, Pi.mul_apply]}
  let M : Subgroup H :=
    iInf fun j : J =>
      ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
        OpenNormalSubgroup H) : Subgroup H)
  letI : M.Normal := by
    exact Subgroup.normal_iInf_normal fun j : J =>
      (OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j)).isNormal'
  have hMU : M ≤ (U : Subgroup H) := by
    intro x hx
    have hxM :
        ∀ j : J,
          x ∈ OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) := by
      simpa [M, Subgroup.mem_iInf] using hx
    have hxW' : φ x ∈ W' := by
      apply hJ2
      intro j hj
      have hxj : ψ ⟨j, hj⟩ x ∈ (V ⟨j, hj⟩ : Subgroup (Gs j)) := by
        simpa [ψ] using hxM ⟨j, hj⟩
      exact hVsub ⟨j, hj⟩ hxj
    have hxW :
        ((e x : ↥(φ.range : Subgroup ((i : ι) → Gs i))) : ((i : ι) → Gs i)) ∈ W := by
      apply hW'W
      simpa [e, φrange] using hxW'
    rcases hWU hxW with ⟨u, huU, hux⟩
    have hxu : x = u := by
      apply hφinj
      exact congrArg Subtype.val hux.symm
    simpa [hxu] using huU
  let φM : H →* ∀ j : J, Gs j ⧸ (V j : Subgroup (Gs j)) :=
    { toFun := fun h j => QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ h j)
      map_one' := by
        funext j
        simp only [map_one, Pi.one_apply]
      map_mul' := by
        intro x y
        funext j
        simp only [map_mul, Pi.mul_apply]}
  have hRange : C φM.range := by
    let χ : φM.range →* ∀ j : J, Gs j ⧸ (V j : Subgroup (Gs j)) := φM.range.subtype
    have hχinj : Function.Injective χ := Subtype.coe_injective
    have hχsurj : ∀ j : J, Function.Surjective fun x : φM.range => χ x j := by
      intro j y
      rcases QuotientGroup.mk'_surjective (V j : Subgroup (Gs j)) y with ⟨g, rfl⟩
      rcases hφsurj j g with ⟨x, hx⟩
      refine ⟨⟨φM x, ⟨x, rfl⟩⟩, ?_⟩
      simp only [QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.subtype_apply, hx, φM, χ]
    exact hForm.finiteSubdirectProductClosed χ hχinj hχsurj hVquot
  have hKerEq : M = φM.ker := by
    ext x
    constructor
    · intro hx
      have hxM :
          ∀ j : J,
            x ∈ OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) := by
        simpa [M, Subgroup.mem_iInf] using hx
      change (fun j : J => QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ x j)) = 1
      funext j
      exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (Gs j))) (φ x j)).2 (by
        simpa [ψ] using hxM j)
    · intro hx
      have hxker :
          (fun j : J => QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ x j)) = 1 := by
        simpa [MonoidHom.mem_ker, φM] using hx
      have hxM :
          ∀ j : J,
            x ∈ OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) := by
        intro j
        change φ x j ∈ (V j : Subgroup (Gs j))
        exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (Gs j))) (φ x j)).1
          (congrArg
            (fun f : (j : J) → Gs j ⧸ (V j : Subgroup (Gs j)) => f j)
            hxker)
      simpa [M, Subgroup.mem_iInf] using hxM
  have hQuotM : C (H ⧸ M) := by
    let e1 : H ⧸ M ≃* H ⧸ φM.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hForm.isomClosed
      ⟨(e1.trans (QuotientGroup.quotientKerEquivRange φM)).symm⟩
      hRange
  have hQuotU :
      C ((H ⧸ M) ⧸ Subgroup.map (QuotientGroup.mk' M) (U : Subgroup H)) := by
    exact hForm.quotientClosed
      (N := Subgroup.map (QuotientGroup.mk' M) (U : Subgroup H)) hQuotM
  exact hForm.isomClosed
    ⟨QuotientGroup.quotientQuotientEquivQuotient M (U : Subgroup H) hMU⟩
    hQuotU

end

section BundledSameUniverse

variable {ι₀ : Type w}
variable {Gs₀ : ι₀ → Type w}
variable [∀ i, Group (Gs₀ i)]
variable [∀ i, TopologicalSpace (Gs₀ i)]
variable [∀ i, IsTopologicalGroup (Gs₀ i)]

/-- A closed subgroup of a product of bundled pro-`C` groups is bundled pro-`C`. -/
theorem ProCGroup.of_closedSubgroup_pi
    (ProC : ProCGroupPredicate.{w})
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    {H : Subgroup ((i : ι₀) → Gs₀ i)}
    (hH : IsClosed (((H : Subgroup ((i : ι₀) → Gs₀ i)) : Set ((i : ι₀) → Gs₀ i))))
    [hGs : ∀ i, ProCGroup ProC (Gs₀ i)] :
    ProCGroup ProC H :=
  ProCGroup.of_isProCGroup ProC H
    (IsProCGroup.of_closedSubgroup_pi.{w, w}
      (C := ProC.finiteQuotientClass)
      (Gs := Gs₀)
      hH
      ProC.finiteQuotientFormation
      ProC.finiteQuotientHereditary.subgroupClosed
      (fun i => (hGs i).isProCGroup))

/-- Bundled form of `IsProCGroup.of_subdirectProduct`. -/
theorem ProCGroup.of_subdirectProduct
    (ProC : ProCGroupPredicate.{w})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hH : IsProfiniteGroup H)
    (φ : H →* ((i : ι₀) → Gs₀ i)) (hφcont : Continuous φ)
    (hφinj : Function.Injective φ)
    (hφsurj : ∀ i, Function.Surjective (fun x : H => φ x i))
    [hGs : ∀ i, ProCGroup ProC (Gs₀ i)] :
    ProCGroup ProC H :=
  ProCGroup.of_isProCGroup ProC H
    (IsProCGroup.of_subdirectProduct.{w, w}
      (C := ProC.finiteQuotientClass)
      (Gs := Gs₀)
      hH φ hφcont hφinj hφsurj
      ProC.finiteQuotientFormation
      (fun i => (hGs i).isProCGroup))

end BundledSameUniverse

end ProCGroups.ProC
