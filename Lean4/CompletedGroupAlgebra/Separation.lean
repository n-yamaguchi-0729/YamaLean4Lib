import CompletedGroupAlgebra.AllFiniteFunctoriality.GroupLike

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Separation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebras

The completed group algebra is presented as an inverse limit of finite group algebras, together with canonical augmentation, augmentation ideal, finite-stage maps, functoriality, and profinite module universal properties.
-/
open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A finite set of nontrivial elements in a profinite group can be avoided by one open normal
finite quotient. This is the finite-support separation input in Lemma 5.3.5(a). -/
theorem exists_completedGroupAlgebraIndex_avoids_finset
    (hG : ProCGroups.IsProfiniteGroup G) (s : Finset G)
    (hs : ∀ x ∈ s, x ≠ 1) :
    ∃ U : CompletedGroupAlgebraIndex G,
      ∀ x ∈ s, x ∉ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
  classical
  let hProC : IsProCGroup ProCGroups.FiniteGroupClass.allFinite G :=
    (isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    letI : Nonempty (OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G) :=
      IsProCGroup.openNormalSubgroupInClass_nonempty hProC
    letI : Nonempty (CompletedGroupAlgebraIndex G) := inferInstance
    exact ⟨Classical.choice inferInstance, by simp only [Finset.notMem_empty, OpenSubgroup.mem_toSubgroup, IsEmpty.forall_iff, implies_true]⟩
  · intro a s has ih hs
    have ha : a ≠ 1 := hs a (by simp only [Finset.mem_insert, true_or])
    rcases hProC.exists_openNormalSubgroupInClass_not_mem ha with ⟨A, hA⟩
    have hs' : ∀ x ∈ s, x ≠ 1 := by
      intro x hx
      exact hs x (by simp only [Finset.mem_insert, hx, or_true])
    rcases ih hs' with ⟨U, hU⟩
    let Aidx : CompletedGroupAlgebraIndex G := OrderDual.toDual A
    rcases directed_openNormalSubgroupInClass
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) ProCGroups.FiniteGroupClass.allFinite_formation
        Aidx U with
      ⟨W, hAW, hUW⟩
    refine ⟨W, ?_⟩
    intro x hx hxW
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hA (hAW hxW)
    · exact hU x hx (hUW hxW)

omit [TopologicalSpace R] [IsTopologicalRing R]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/-- For a finite-support group-algebra element and a chosen basis element `g`, one finite
quotient separates the image of `g` from all other support points. -/
theorem exists_completedGroupAlgebraIndex_separating_support
    (hG : ProCGroups.IsProfiniteGroup G) (x : MonoidAlgebra R G) (g : G) :
    ∃ U : CompletedGroupAlgebraIndex G,
      ∀ h ∈ x.support, h ≠ g →
        openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U h ≠
          openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g := by
  classical
  let bad : Finset G := (x.support.erase g).image fun h => h⁻¹ * g
  have hbad : ∀ y ∈ bad, y ≠ 1 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨h, hh, rfl⟩
    intro h1
    have hg : h = g := by
      have hmul := congrArg (fun t : G => h * t) h1
      have hg' : g = h := by
        simpa [mul_assoc] using hmul
      exact hg'.symm
    exact (Finset.mem_erase.mp hh).1 hg
  rcases exists_completedGroupAlgebraIndex_avoids_finset (G := G) hG bad hbad with
    ⟨U, hU⟩
  refine ⟨U, ?_⟩
  intro h hh hne heq
  have hbadmem : h⁻¹ * g ∈ bad := by
    exact Finset.mem_image.mpr ⟨h, Finset.mem_erase.mpr ⟨hne, hh⟩, rfl⟩
  have hmem :
      h⁻¹ * g ∈ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
    exact QuotientGroup.eq.1 heq
  exact hU (h⁻¹ * g) hbadmem hmem

omit [TopologicalSpace R] [IsTopologicalRing R]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/-- If a finite quotient separates `g` from the other support points of `x`, then the coefficient
of the image of `g` in the quotient group algebra is exactly the original coefficient of `g`. -/
theorem completedGroupAlgebraStageMap_coeff_of_support_separated
    (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) (g : G)
    (hsep : ∀ h ∈ x.support, h ≠ g →
      openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U h ≠
        openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) :
    completedGroupAlgebraStageMap R G U x
        (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) =
      x g := by
  classical
  rw [completedGroupAlgebraStageMap]
  change (Finsupp.mapDomain
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U) x)
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) =
    x g
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single g]
  · simp only [Finsupp.single_eq_same]
  · intro h hh hne
    exact Finsupp.single_eq_of_ne fun heq =>
      hsep h (Finsupp.mem_support_iff.mpr hh) hne heq.symm
  · intro _hg
    simp only [Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

omit R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalGroup G] H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/-- A finite set of nontrivial elements in a pro-`C` group can be avoided by one open normal
`C`-quotient. This is the `C`-indexed finite-support separation input in Lemma 5.3.5(a). -/
theorem exists_completedGroupAlgebraIndexInClass_avoids_finset
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : IsProCGroup C G) (s : Finset G) (hs : ∀ x ∈ s, x ≠ 1) :
    ∃ U : CompletedGroupAlgebraIndexInClass G C,
      ∀ x ∈ s, x ∉ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    letI : Nonempty (OpenNormalSubgroupInClass C G) :=
      IsProCGroup.openNormalSubgroupInClass_nonempty hG
    letI : Nonempty (CompletedGroupAlgebraIndexInClass G C) := inferInstance
    exact ⟨Classical.choice inferInstance, by simp only [Finset.notMem_empty, OpenSubgroup.mem_toSubgroup, IsEmpty.forall_iff, implies_true]⟩
  · intro a s has ih hs
    have ha : a ≠ 1 := hs a (by simp only [Finset.mem_insert, true_or])
    rcases hG.exists_openNormalSubgroupInClass_not_mem ha with ⟨A, hA⟩
    have hs' : ∀ x ∈ s, x ≠ 1 := by
      intro x hx
      exact hs x (by simp only [Finset.mem_insert, hx, or_true])
    rcases ih hs' with ⟨U, hU⟩
    let Aidx : CompletedGroupAlgebraIndexInClass G C := OrderDual.toDual A
    rcases directed_openNormalSubgroupInClass (C := C) (G := G) hForm Aidx U with
      ⟨W, hAW, hUW⟩
    refine ⟨W, ?_⟩
    intro x hx hxW
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hA (hAW hxW)
    · exact hU x hx (hUW hxW)

omit R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalGroup G] H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/-- For any finitely supported family on a pro-`C` group and a chosen basis point `g`, one
`C`-quotient separates the image of `g` from all other support points. -/
theorem exists_completedGroupAlgebraIndexInClass_separating_finsupp_support
    {M : Type w} [Zero M]
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : IsProCGroup C G) (x : G →₀ M) (g : G) :
    ∃ U : CompletedGroupAlgebraIndexInClass G C,
      ∀ h ∈ x.support, h ≠ g →
        openNormalSubgroupInClassProj (C := C) (G := G) U h ≠
          openNormalSubgroupInClassProj (C := C) (G := G) U g := by
  classical
  let bad : Finset G := (x.support.erase g).image fun h => h⁻¹ * g
  have hbad : ∀ y ∈ bad, y ≠ 1 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨h, hh, rfl⟩
    intro h1
    have hg : h = g := by
      have hmul := congrArg (fun t : G => h * t) h1
      have hg' : g = h := by
        simpa [mul_assoc] using hmul
      exact hg'.symm
    exact (Finset.mem_erase.mp hh).1 hg
  rcases exists_completedGroupAlgebraIndexInClass_avoids_finset
      (G := G) C hForm hG bad hbad with
    ⟨U, hU⟩
  refine ⟨U, ?_⟩
  intro h hh hne heq
  have hbadmem : h⁻¹ * g ∈ bad := by
    exact Finset.mem_image.mpr ⟨h, Finset.mem_erase.mpr ⟨hne, hh⟩, rfl⟩
  have hmem :
      h⁻¹ * g ∈ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
    exact QuotientGroup.eq.1 heq
  exact hU (h⁻¹ * g) hbadmem hmem

omit [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalGroup G] H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/-- For a finite-support group-algebra element and a chosen basis element `g`, one `C`-quotient
separates the image of `g` from all other support points. -/
theorem exists_completedGroupAlgebraIndexInClass_separating_support
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : IsProCGroup C G) (x : MonoidAlgebra R G) (g : G) :
    ∃ U : CompletedGroupAlgebraIndexInClass G C,
      ∀ h ∈ x.support, h ≠ g →
        openNormalSubgroupInClassProj (C := C) (G := G) U h ≠
          openNormalSubgroupInClassProj (C := C) (G := G) U g :=
  exists_completedGroupAlgebraIndexInClass_separating_finsupp_support
    (G := G) C hForm hG x g

omit [TopologicalSpace R] [IsTopologicalRing R]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/-- If a `C`-quotient separates `g` from the other support points of `x`, then the coefficient of
the image of `g` in the quotient group algebra is exactly the original coefficient of `g`. -/
theorem completedGroupAlgebraStageMapInClass_coeff_of_support_separated
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x : MonoidAlgebra R G) (g : G)
    (hsep : ∀ h ∈ x.support, h ≠ g →
      openNormalSubgroupInClassProj (C := C) (G := G) U h ≠
        openNormalSubgroupInClassProj (C := C) (G := G) U g) :
    completedGroupAlgebraStageMapInClass C R G U x
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) =
      x g := by
  classical
  rw [completedGroupAlgebraStageMapInClass]
  change (Finsupp.mapDomain
      (openNormalSubgroupInClassProj (C := C) (G := G) U) x)
      (openNormalSubgroupInClassProj (C := C) (G := G) U g) =
    x g
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single g]
  · simp only [Finsupp.single_eq_same]
  · intro h hh hne
    exact Finsupp.single_eq_of_ne fun heq =>
      hsep h (Finsupp.mem_support_iff.mpr hh) hne heq.symm
  · intro _hg
    simp only [Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- Lemma 5.3.5(a), fixed-coefficient form: the canonical map from the abstract group algebra
to the completed group algebra is injective for profinite `G`. Equivalently, the kernels of the
finite group-quotient maps have trivial intersection. -/
theorem injective_toCompletedGroupAlgebraRingHom
    (hG : ProCGroups.IsProfiniteGroup G) :
    Function.Injective (toCompletedGroupAlgebraRingHom R G) := by
  intro x y hxy
  apply Finsupp.ext
  intro g
  have hcoeff : (x - y) g = 0 := by
    rcases exists_completedGroupAlgebraIndex_separating_support (R := R) (G := G)
        hG (x - y) g with
      ⟨U, hsep⟩
    have hstage_eq : completedGroupAlgebraStageMap R G U x =
        completedGroupAlgebraStageMap R G U y := by
      have hp := congrArg (fun z : Carrier R G =>
        completedGroupAlgebraProjection R G U z) hxy
      change completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G x) =
        completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G y) at hp
      simpa [completedGroupAlgebraProjection_toCompletedGroupAlgebra] using hp
    have hstage : completedGroupAlgebraStageMap R G U (x - y) = 0 := by
      rw [map_sub, hstage_eq, sub_self]
    have hstage_coeff :
        completedGroupAlgebraStageMap R G U (x - y)
            (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) = 0 := by
      simpa using congrArg
        (fun z : CompletedGroupAlgebraStage R G U =>
          z (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g))
        hstage
    rw [completedGroupAlgebraStageMap_coeff_of_support_separated
      (R := R) (G := G) U (x - y) g hsep] at hstage_coeff
    simpa using hstage_coeff
  exact sub_eq_zero.mp hcoeff

/-- Kernel form of Lemma 5.3.5(a). -/
theorem toCompletedGroupAlgebraRingHom_ker_eq_bot
    (hG : ProCGroups.IsProfiniteGroup G) :
    RingHom.ker (toCompletedGroupAlgebraRingHom R G) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot (toCompletedGroupAlgebraRingHom R G)).mp
    (injective_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG)

/-- The kernel of the map to `[[R G]]` is the intersection of the finite-stage kernels. -/
theorem toCompletedGroupAlgebraRingHom_ker_eq_iInf_stageMap_ker :
    RingHom.ker (toCompletedGroupAlgebraRingHom R G) =
      ⨅ U : CompletedGroupAlgebraIndex G, RingHom.ker (completedGroupAlgebraStageMap R G U) := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    rw [Submodule.mem_iInf]
    intro U
    rw [RingHom.mem_ker]
    have hU := congrArg (fun y : Carrier R G =>
      completedGroupAlgebraProjection R G U y) hx
    change completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G x) =
      completedGroupAlgebraProjection R G U (0 : Carrier R G) at hU
    simpa [completedGroupAlgebraProjection_toCompletedGroupAlgebra] using hU
  · intro hx
    rw [RingHom.mem_ker]
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraStageMap R G U x = 0
    exact (Submodule.mem_iInf
      (p := fun U : CompletedGroupAlgebraIndex G =>
        RingHom.ker (completedGroupAlgebraStageMap R G U))).1 hx U

/-- Fixed-coefficient finite-stage kernel-family form of Lemma 5.3.5(a). -/
theorem iInf_completedGroupAlgebraStageMap_ker_eq_bot
    (hG : ProCGroups.IsProfiniteGroup G) :
    (⨅ U : CompletedGroupAlgebraIndex G,
        RingHom.ker (completedGroupAlgebraStageMap R G U)) = ⊥ := by
  rw [← toCompletedGroupAlgebraRingHom_ker_eq_iInf_stageMap_ker (R := R) (G := G),
    toCompletedGroupAlgebraRingHom_ker_eq_bot (R := R) (G := G) hG]

/-- `C`-indexed form of Lemma 5.3.5(a): for a pro-`C` group, the canonical map from
the abstract group algebra to `[[R G]]_C` is injective. -/
theorem injective_toCompletedGroupAlgebraInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Function.Injective (toCompletedGroupAlgebraInClassRingHom C hC R G) := by
  intro x y hxy
  apply injective_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG.1
  have h := congrArg
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG) hxy
  simpa [RingHom.congr_fun
      (completedGroupAlgebraFromInClassRingHom_comp_toCompletedGroupAlgebraInClass
        (R := R) (G := G) C hC hForm hG)] using h

/-- Kernel form of the `C`-indexed injectivity statement. -/
theorem toCompletedGroupAlgebraInClassRingHom_ker_eq_bot
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    RingHom.ker (toCompletedGroupAlgebraInClassRingHom C hC R G) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot (toCompletedGroupAlgebraInClassRingHom C hC R G)).mp
    (injective_toCompletedGroupAlgebraInClassRingHom (R := R) (G := G) C hC hForm hG)

/-- The kernel of the map to `[[R G]]_C` is the intersection of the `C`-indexed finite-stage
kernels. -/
theorem toCompletedGroupAlgebraInClassRingHom_ker_eq_iInf_stageMapInClass_ker
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    RingHom.ker (toCompletedGroupAlgebraInClassRingHom C hC R G) =
      ⨅ U : CompletedGroupAlgebraIndexInClass G C,
        RingHom.ker (completedGroupAlgebraStageMapInClass C R G U) := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    rw [Submodule.mem_iInf]
    intro U
    rw [RingHom.mem_ker]
    have hU := congrArg (fun y : CompletedGroupAlgebraInClass C hC R G =>
      completedGroupAlgebraProjectionInClass C hC R G U y) hx
    change completedGroupAlgebraProjectionInClass C hC R G U
        (toCompletedGroupAlgebraInClass C hC R G x) =
      completedGroupAlgebraProjectionInClass C hC R G U
        (0 : CompletedGroupAlgebraInClass C hC R G) at hU
    simpa [completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass] using hU
  · intro hx
    rw [RingHom.mem_ker]
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    change completedGroupAlgebraStageMapInClass C R G U x = 0
    exact (Submodule.mem_iInf
      (p := fun U : CompletedGroupAlgebraIndexInClass G C =>
        RingHom.ker (completedGroupAlgebraStageMapInClass C R G U))).1 hx U

/-- `C`-indexed finite-stage kernel-family form of Lemma 5.3.5(a). -/
theorem iInf_completedGroupAlgebraStageMapInClass_ker_eq_bot
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    (⨅ U : CompletedGroupAlgebraIndexInClass G C,
        RingHom.ker (completedGroupAlgebraStageMapInClass C R G U)) = ⊥ := by
  rw [← toCompletedGroupAlgebraInClassRingHom_ker_eq_iInf_stageMapInClass_ker
      (R := R) (G := G) C hC,
    toCompletedGroupAlgebraInClassRingHom_ker_eq_bot (R := R) (G := G) C hC hForm hG]

/-- Lemma 5.3.5(a), book kernel-family form: the intersection of the kernels of
`R[G] -> (R/I)[G/U]`, over open coefficient ideals and finite group quotients, is zero. -/
theorem iInf_groupAlgebraOpenFiniteQuotientKernel_eq_bot
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    (⨅ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        groupAlgebraOpenFiniteQuotientKernel R G K) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_bot]
    have hxall :
        ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
          x ∈ groupAlgebraOpenFiniteQuotientKernel R G K := by
      simpa using (Submodule.mem_iInf
        (p := fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
          groupAlgebraOpenFiniteQuotientKernel R G K)).1 hx
    have hxlimit :
        toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G x = 0 := by
      apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
      intro K
      change groupAlgebraOpenFiniteQuotientMap R G K x = 0
      exact (mem_groupAlgebraOpenFiniteQuotientKernel_iff R G K x).1 (hxall K)
    have hcompleted :
        toCompletedGroupAlgebraRingHom R G x = 0 := by
      apply injective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G) hR
      change completedGroupAlgebraToOpenFiniteQuotientLimit R G
          (toCompletedGroupAlgebra R G x) =
        completedGroupAlgebraToOpenFiniteQuotientLimit R G
          (0 : Carrier R G)
      simpa [toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom] using hxlimit
    exact (injective_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG) (by
      simpa using hcompleted)
  · exact bot_le

/-- Lemma 5.3.5(b/c), concrete completion form: with the book kernel-neighborhood topology on
`R[G]`, the canonical map into `[[RG]]` is an injective dense continuous map into a profinite ring,
and that topology is precisely the one induced from `[[RG]]`. -/
theorem completedGroupAlgebra_kernelTopology_isHausdorffProfiniteCompletion
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    IsProfiniteRing (Carrier R G) ∧
      Function.Injective (toCompletedGroupAlgebraRingHom R G) ∧
        DenseRange (toCompletedGroupAlgebraRingHom R G) ∧
          Continuous (toCompletedGroupAlgebraRingHom R G) ∧
            groupAlgebraOpenFiniteQuotientKernelTopology R G =
              TopologicalSpace.induced (toCompletedGroupAlgebra R G) inferInstance := by
  have hProC : IsProCGroup ProCGroups.FiniteGroupClass.allFinite G :=
    (isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG
  letI : Nonempty (OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G) :=
    IsProCGroup.openNormalSubgroupInClass_nonempty hProC
  letI : Nonempty (CompletedGroupAlgebraIndex G) := inferInstance
  letI : Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G) := inferInstance
  refine ⟨completedGroupAlgebra_isProfiniteRing (R := R) (G := G) hR,
    injective_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG,
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG,
    continuous_toCompletedGroupAlgebraRingHom_kernelTopology (R := R) (G := G) hR, ?_⟩
  have hτ :=
    completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
      (R := R) (G := G) hR
  simpa [completedGroupAlgebraNaturalTopology] using hτ.symm

/-- Continuous ring homomorphisms out of `[[R G]]` into another completed group algebra are
determined by their values on the dense abstract group algebra. -/
theorem completedGroupAlgebraRingHom_ext_of_comp_toCompleted
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    {f g : Carrier R G →+* Carrier R H}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f.comp (toCompletedGroupAlgebraRingHom R G) =
      g.comp (toCompletedGroupAlgebraRingHom R G)) :
    f = g := by
  letI : T2Space (Carrier R H) :=
    completedGroupAlgebra_t2Space (R := R) (G := H) hR
  have hdense : DenseRange (toCompletedGroupAlgebraRingHom R G) :=
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG
  have hcomp : (f : Carrier R G → Carrier R H) ∘
        (toCompletedGroupAlgebraRingHom R G) =
      (g : Carrier R G → Carrier R H) ∘
        (toCompletedGroupAlgebraRingHom R G) := by
    funext x
    exact congrFun (congrArg DFunLike.coe hfg) x
  have hfun : (f : Carrier R G → Carrier R H) = g :=
    DenseRange.equalizer hdense hf hg hcomp
  exact RingHom.ext fun x => congrFun hfun x

/-- Lemma 5.3.5(e), identity law for the completed-group-algebra functor. -/
theorem completedGroupAlgebraMap_id
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    completedGroupAlgebraMap (G := G) (H := G) R hG (MonoidHom.id G) continuous_id =
      RingHom.id (Carrier R G) := by
  apply completedGroupAlgebraRingHom_ext_of_comp_toCompleted (R := R) (G := G) (H := G)
    hR hG
  · exact continuous_completedGroupAlgebraMap (R := R) (G := G) (H := G)
      hG (MonoidHom.id G) continuous_id
  · exact continuous_id
  · rw [completedGroupAlgebraMap_comp_toCompletedGroupAlgebra,
      finiteGroupAlgebra_mapDomainRingHom_id]
    rfl

/-- Lemma 5.3.5(e), identity law for the completed-group-algebra functor, as an `R`-algebra
homomorphism. -/
theorem completedGroupAlgebraMapAlgHom_id
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := G) R hG (MonoidHom.id G) continuous_id =
      AlgHom.id R (Carrier R G) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMap_id (R := R) (G := G) hR hG))
    x
  simpa using h

end

end CompletedGroupAlgebra
