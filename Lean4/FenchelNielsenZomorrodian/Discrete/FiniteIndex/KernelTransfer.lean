import FenchelNielsenZomorrodian.Discrete.FiniteIndex.NormalCore

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/FiniteIndex/KernelTransfer.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-index torsion-free subgroup data

Abstract finite-index and smooth quotient data, kernel transfer, normal core, and derived-length predicates for discrete Fuchsian groups.
-/

namespace FenchelNielsen

theorem subgroup_finiteIndex_comap_of_finiteIndex
    {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (H : Subgroup G') [H.FiniteIndex] :
    (H.comap f).FiniteIndex := by
  apply Subgroup.finiteIndex_iff.2
  rw [Subgroup.index_comap]
  exact Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf f.range)

theorem sourceSubgroup_exists_succ_of_commutativeQuotientKernelEquiv_targetSubgroup
    {G A H : Type*} [Group G] [CommGroup A] [Finite A] [Group H]
    (φ : G →* A)
    (e : φ.ker ≃* H) {n : ℕ}
    (hTarget : ∃ L : Subgroup H,
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L n) :
    ∃ S : Subgroup G,
      S.FiniteIndex ∧ IsTorsionFreeGroup S ∧
        SubgroupQuotientHasDerivedLengthAtMost S (n + 1) := by
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  rcases hTarget with ⟨L, hLFiniteIndex, hLTF, hLQuot⟩
  haveI : L.FiniteIndex := hLFiniteIndex
  let L₀ : Subgroup φ.ker := L.comap e.toMonoidHom
  let S : Subgroup G := L₀.map φ.ker.subtype
  haveI : L₀.FiniteIndex :=
    subgroup_finiteIndex_comap_of_finiteIndex e.toMonoidHom L
  haveI : S.FiniteIndex := by
    apply Subgroup.finiteIndex_iff.2
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := L₀))
      (Subgroup.FiniteIndex.index_ne_zero (H := φ.ker))
  have hL₀TF : IsTorsionFreeGroup L₀ := by
    intro x hxfin
    have hxfinKer : IsOfFinOrder (x : φ.ker) := by
      simpa using
        (Submonoid.isOfFinOrder_coe
          (H := L₀.toSubmonoid) (x := x)).2 hxfin
    let y : L := ⟨e (x : φ.ker), x.2⟩
    have hyfin : IsOfFinOrder y := by
      have heyfin : IsOfFinOrder (e (x : φ.ker)) :=
        MonoidHom.isOfFinOrder e.toMonoidHom hxfinKer
      simpa [y] using
        (Submonoid.isOfFinOrder_coe
          (H := L.toSubmonoid) (x := y)).1 heyfin
    have hyone : y = 1 := hLTF y hyfin
    have heyone : e (x : φ.ker) = 1 :=
      congrArg (fun z : L => (z : H)) hyone
    have hxoneKer : (x : φ.ker) = 1 := by
      apply e.injective
      simpa using heyone
    exact Subtype.ext hxoneKer
  let eS : L₀ ≃* S :=
    L₀.equivMapOfInjective φ.ker.subtype φ.ker.subtype_injective
  have hSTF : IsTorsionFreeGroup S :=
    isTorsionFreeGroup_of_mulEquiv eS hL₀TF
  have hDerivedL₀ : derivedSeries φ.ker n ≤ L₀ := by
    intro x hx
    change e x ∈ L
    have hxmap :
        e x ∈ (derivedSeries φ.ker n).map e.toMonoidHom := by
      exact ⟨x, hx, rfl⟩
    have hxDer : e x ∈ derivedSeries H n := by
      have hmapeq :
          (derivedSeries φ.ker n).map e.toMonoidHom = derivedSeries H n :=
        map_derivedSeries_eq (f := e.toMonoidHom) e.surjective n
      rw [hmapeq] at hxmap
      exact hxmap
    exact hLQuot hxDer
  have hFirstDerivedKer : derivedSeries G 1 ≤ φ.ker := by
    simpa [derivedSeries_one] using Abelianization.commutator_subset_ker φ
  have hDerivedS : derivedSeries G (n + 1) ≤ S := by
    intro g hg
    have hmap :
        g ∈ (derivedSeries φ.ker n).map φ.ker.subtype :=
      derivedSeries_succ_le_map_derivedSeries_of_firstDerived_le
        φ.ker hFirstDerivedKer n hg
    rcases Subgroup.mem_map.mp hmap with ⟨x, hx, hxeq⟩
    exact Subgroup.mem_map.mpr ⟨x, hDerivedL₀ hx, hxeq⟩
  exact ⟨S, inferInstance, hSTF, hDerivedS⟩

theorem sourceSubgroup_exists_of_mulEquiv
    {G H : Type*} [Group G] [Group H] {m : ℕ}
    (e : G ≃* H)
    (h : ∃ L : Subgroup H,
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L m) :
    ∃ K : Subgroup G,
      K.FiniteIndex ∧ IsTorsionFreeGroup K ∧
        SubgroupQuotientHasDerivedLengthAtMost K m := by
  rcases h with ⟨L, hLFiniteIndex, hLTF, hLQuot⟩
  haveI : L.FiniteIndex := hLFiniteIndex
  let K : Subgroup G := L.comap e.toMonoidHom
  haveI : K.FiniteIndex := subgroup_finiteIndex_comap_of_finiteIndex e.toMonoidHom L
  have hKTF : IsTorsionFreeGroup K := by
    intro x hxfin
    have hxfinG : IsOfFinOrder (x : G) := by
      simpa using
        (Submonoid.isOfFinOrder_coe
          (H := K.toSubmonoid) (x := x)).2 hxfin
    let y : L := ⟨e (x : G), x.2⟩
    have hyfin : IsOfFinOrder y := by
      have heyfin : IsOfFinOrder (e (x : G)) :=
        MonoidHom.isOfFinOrder e.toMonoidHom hxfinG
      simpa [y] using
        (Submonoid.isOfFinOrder_coe
          (H := L.toSubmonoid) (x := y)).1 heyfin
    have hyone : y = 1 := hLTF y hyfin
    have heyone : e (x : G) = 1 :=
      congrArg (fun z : L => (z : H)) hyone
    have hxoneG : (x : G) = 1 := by
      apply e.injective
      simpa using heyone
    exact Subtype.ext hxoneG
  have hKQuot : SubgroupQuotientHasDerivedLengthAtMost K m := by
    intro g hg
    change e g ∈ L
    have hmap : e g ∈ (derivedSeries G m).map e.toMonoidHom := ⟨g, hg, rfl⟩
    have hderH : e g ∈ derivedSeries H m :=
      (map_derivedSeries_le_derivedSeries e.toMonoidHom m) hmap
    exact hLQuot hderH
  exact ⟨K, inferInstance, hKTF, hKQuot⟩

end FenchelNielsen
