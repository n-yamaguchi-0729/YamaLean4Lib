import FenchelNielsenZomorrodian.Discrete.FiniteIndex.NormalCore

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/FiniteIndex/Smooth.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-index torsion-free subgroup data

Abstract finite-index and smooth quotient data, kernel transfer, normal core, and derived-length predicates for discrete Fuchsian groups.
-/

namespace FenchelNielsen

structure SmoothQuotientData
    (G : Type*) [Group G]
    (ι : Type*) (periods : ι → ℕ) (elliptic : ι → G)
    (m : ℕ) where
  Q : Type
  [group : Group Q]
  [finite : Finite Q]
  φ : G →* Q
  derived_length : derivedSeries Q m = ⊥
  elliptic_exact : ∀ i : ι, orderOf (φ (elliptic i)) = periods i

namespace SmoothQuotientData

def kernel {G : Type*} [Group G] {ι : Type*} {periods : ι → ℕ}
    {elliptic : ι → G} {m : ℕ}
    (D : SmoothQuotientData G ι periods elliptic m) : Subgroup G := by
  letI : Group D.Q := D.group
  exact D.φ.ker

theorem kernel_quotient_has_derivedLengthAtMost
    {G : Type*} [Group G] {ι : Type*} {periods : ι → ℕ}
    {elliptic : ι → G} {m : ℕ}
    (D : SmoothQuotientData G ι periods elliptic m) :
    SubgroupQuotientHasDerivedLengthAtMost D.kernel m := by
  intro g hg
  letI : Group D.Q := D.group
  change g ∈ D.φ.ker
  rw [MonoidHom.mem_ker]
  have hmap : D.φ g ∈ (derivedSeries G m).map D.φ := by
    exact ⟨g, hg, rfl⟩
  have hle : (derivedSeries G m).map D.φ ≤ derivedSeries D.Q m :=
    map_derivedSeries_le_derivedSeries D.φ m
  have hderived : D.φ g ∈ derivedSeries D.Q m := hle hmap
  rw [D.derived_length] at hderived
  simpa using hderived

theorem source_element_eq_one_of_kernel_conjugate_elliptic_zpow
    {G : Type*} [Group G] {ι : Type*} {periods : ι → ℕ}
    {elliptic : ι → G} {m : ℕ}
    (D : SmoothQuotientData G ι periods elliptic m)
    (hEllipticZPow :
      ∀ i : ι, ∀ n : ℤ, (periods i : ℤ) ∣ n → elliptic i ^ n = 1)
    (g : G)
    (hgKernel : g ∈ D.kernel)
    (hConj : ∃ i : ι, ∃ n : ℤ, IsConj g (elliptic i ^ n)) :
    g = 1 := by
  letI : Group D.Q := D.group
  have hgKernel_eq : D.φ g = 1 := by
    change g ∈ D.φ.ker at hgKernel
    exact MonoidHom.mem_ker.mp hgKernel
  rcases hConj with ⟨i, n, hconj⟩
  have hφconj : IsConj (D.φ g) (D.φ (elliptic i ^ n)) :=
    D.φ.map_isConj hconj
  have hφtarget : D.φ (elliptic i ^ n) = 1 := by
    exact isConj_one_right.mp <| by simpa [hgKernel_eq] using hφconj
  have hdiv : (periods i : ℤ) ∣ n := by
    rw [← D.elliptic_exact i]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (by
      simpa [MonoidHom.map_zpow] using hφtarget)
  have htargetOne : elliptic i ^ n = 1 :=
    hEllipticZPow i n hdiv
  exact isConj_one_left.mp <| by simpa [htargetOne] using hconj

theorem kernel_torsionFree_of_finiteOrderClassification
    {G : Type*} [Group G] {ι : Type*} {periods : ι → ℕ}
    {elliptic : ι → G} {m : ℕ}
    (D : SmoothQuotientData G ι periods elliptic m)
    (hEllipticZPow :
      ∀ i : ι, ∀ n : ℤ, (periods i : ℤ) ∣ n → elliptic i ^ n = 1)
    (hFiniteOrder :
      ∀ g : G, IsOfFinOrder g →
        g = 1 ∨ ∃ i : ι, ∃ n : ℤ, IsConj g (elliptic i ^ n)) :
    IsTorsionFreeGroup D.kernel := by
  intro g hgfin
  have hgfinSource : IsOfFinOrder (g : G) := by
    simpa using
      (Submonoid.isOfFinOrder_coe
        (H := D.kernel.toSubmonoid) (x := g)).2 hgfin
  rcases hFiniteOrder (g : G) hgfinSource with hgOne | hConj
  · exact Subtype.ext hgOne
  · exact Subtype.ext
      (D.source_element_eq_one_of_kernel_conjugate_elliptic_zpow
        hEllipticZPow (g : G) g.2 hConj)

theorem sourceSubgroup_exists_of_finiteOrderClassification
    {G : Type*} [Group G] {ι : Type*} {periods : ι → ℕ}
    {elliptic : ι → G} {m : ℕ}
    (D : SmoothQuotientData G ι periods elliptic m)
    (hEllipticZPow :
      ∀ i : ι, ∀ n : ℤ, (periods i : ℤ) ∣ n → elliptic i ^ n = 1)
    (hFiniteOrder :
      ∀ g : G, IsOfFinOrder g →
        g = 1 ∨ ∃ i : ι, ∃ n : ℤ, IsConj g (elliptic i ^ n)) :
  ∃ L : Subgroup G,
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L m := by
  have hfinite : D.kernel.FiniteIndex := by
    letI : Group D.Q := D.group
    letI : Finite D.Q := D.finite
    change D.φ.ker.FiniteIndex
    exact Subgroup.finiteIndex_of_finite_quotient
  exact ⟨D.kernel, hfinite,
    D.kernel_torsionFree_of_finiteOrderClassification
      hEllipticZPow hFiniteOrder,
    D.kernel_quotient_has_derivedLengthAtMost⟩

end SmoothQuotientData

end FenchelNielsen
