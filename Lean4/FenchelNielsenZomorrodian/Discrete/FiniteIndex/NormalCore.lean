import FenchelNielsenZomorrodian.Discrete.FiniteIndex.Definitions

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/FiniteIndex/NormalCore.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-index torsion-free subgroup data

Abstract finite-index and smooth quotient data, kernel transfer, normal core, and derived-length predicates for discrete Fuchsian groups.
-/

namespace FenchelNielsen

theorem isTorsionFreeGroup_of_subgroup_le
    {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hK : IsTorsionFreeGroup K) :
    IsTorsionFreeGroup H := by
  intro h hhfin
  have hhfinG : IsOfFinOrder (h : G) := by
    simpa using
      (Submonoid.isOfFinOrder_coe
        (H := H.toSubmonoid) (x := h)).2 hhfin
  let k : K := ⟨h, hHK h.2⟩
  have hkfin : IsOfFinOrder k := by
    simpa [k] using
      (Submonoid.isOfFinOrder_coe
        (H := K.toSubmonoid) (x := k)).1 hhfinG
  have hkone : k = 1 := hK k hkfin
  have hkoneG : ((k : K) : G) = 1 :=
    congrArg (fun x : K => (x : G)) hkone
  exact Subtype.ext (by simpa [k] using hkoneG)

theorem hasFiniteIndexTorsionFreeNormalSubgroupWithDerivedLengthAtMost_of_subgroup
    {G : Type*} [Group G] {m : ℕ}
    (H : Subgroup G) [H.FiniteIndex]
    (hTF : IsTorsionFreeGroup H)
    (hDerived : derivedSeries G m ≤ H) :
    HasFiniteIndexTorsionFreeNormalSubgroupWithDerivedLengthAtMost G m := by
  let K : Subgroup G := H.normalCore
  haveI : K.FiniteIndex := Subgroup.finiteIndex_normalCore (H := H)
  have hKTF : IsTorsionFreeGroup K :=
    isTorsionFreeGroup_of_subgroup_le (Subgroup.normalCore_le H) hTF
  have hDerivedK : derivedSeries G m ≤ K := by
    haveI : (derivedSeries G m).Normal := derivedSeries_normal G m
    exact
      (Subgroup.normal_le_normalCore
        (H := H) (N := derivedSeries G m)).2 hDerived
  exact ⟨K, inferInstance, inferInstance, hKTF, hDerivedK⟩

end FenchelNielsen
