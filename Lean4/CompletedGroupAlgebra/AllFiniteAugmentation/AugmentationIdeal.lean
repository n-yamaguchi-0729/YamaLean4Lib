import CompletedGroupAlgebra.AllFiniteAugmentation.InClassComparison
import CompletedGroupAlgebra.AllFiniteFunctoriality.Surjectivity

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteAugmentation/AugmentationIdeal.lean
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

/-- The canonical augmentation ideal of the concrete inverse-limit completed group algebra. -/
def completedGroupAlgebraCanonicalAugmentationIdeal (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Ideal (Carrier R G) :=
  RingHom.ker (completedGroupAlgebraCanonicalAugmentation R G)

/-- Membership in the all-finite canonical augmentation ideal is vanishing under the canonical augmentation. -/
@[simp]
theorem mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff
    (x : Carrier R G) :
    x ∈ completedGroupAlgebraCanonicalAugmentationIdeal R G ↔
      completedGroupAlgebraCanonicalAugmentation R G x = 0 :=
  Iff.rfl

/-- The inclusion of the canonical completed augmentation ideal is injective. -/
theorem completedGroupAlgebraCanonicalAugmentationIdeal_subtype_injective :
    Function.Injective
      (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
        (x : Carrier R G)) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The canonical completed augmentation ideal is exactly the kernel of the canonical
augmentation. -/
theorem exact_completedGroupAlgebraCanonicalAugmentationIdeal_subtype :
    Function.Exact
      (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
        (x : Carrier R G))
      (completedGroupAlgebraCanonicalAugmentation R G) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/-- The canonical completed augmentation sequence `0 → I_G → [[R G]] → R → 0` is short
exact. -/
theorem completedGroupAlgebraCanonicalAugmentation_shortExact :
    Function.Injective
        (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
          (x : Carrier R G)) ∧
      Function.Exact
        (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
          (x : Carrier R G))
        (completedGroupAlgebraCanonicalAugmentation R G) ∧
      Function.Surjective (completedGroupAlgebraCanonicalAugmentation R G) := by
  exact ⟨completedGroupAlgebraCanonicalAugmentationIdeal_subtype_injective (R := R) (G := G),
    exact_completedGroupAlgebraCanonicalAugmentationIdeal_subtype (R := R) (G := G),
    completedGroupAlgebraCanonicalAugmentation_surjective (R := R) (G := G)⟩

/-- The all-finite augmentation ideal pulls back along the from-in-class comparison map to the class-indexed augmentation ideal. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdeal_comap_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Ideal.comap (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG)
        (completedGroupAlgebraCanonicalAugmentationIdeal R G) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC := by
  ext x
  rw [Ideal.mem_comap, mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    completedGroupAlgebraFromInClassRingHom_apply,
    completedGroupAlgebraCanonicalAugmentation_fromInClass]

/-- The from-in-class comparison map sends the class-indexed augmentation ideal into the all-finite augmentation ideal. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_map_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Ideal.map (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC) =
      completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdeal_comap_fromInClass
    (R := R) (G := G) C hC hForm hG]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG)
    (completedGroupAlgebraFromInClass_surjective (R := R) (G := G) C hC hForm hG)
    (completedGroupAlgebraCanonicalAugmentationIdeal R G)

/-- The to-in-class comparison map preserves and reflects membership in the canonical augmentation ideal. -/
@[simp]
theorem completedGroupAlgebraToInClass_mem_canonicalAugmentationIdeal_iff
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (x : Carrier R G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC x ∈
        completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC ↔
      x ∈ completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff]
  have haug := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraCanonicalAugmentationInClass_comp_toInClass
        (R := R) (G := G) C hC))
    x
  change completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC
      (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC x) =
    completedGroupAlgebraCanonicalAugmentation R G x at haug
  rw [haug]

/-- The class-indexed augmentation ideal pulls back along the to-in-class comparison map to the all-finite augmentation ideal. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_toInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Ideal.comap (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC) =
      completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  ext x
  exact completedGroupAlgebraToInClass_mem_canonicalAugmentationIdeal_iff
    (R := R) (G := G) C hC x

/-- The to-in-class comparison map sends the all-finite augmentation ideal into the class-indexed augmentation ideal. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdeal_map_toInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Ideal.map (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)
        (completedGroupAlgebraCanonicalAugmentationIdeal R G) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_toInClass
    (R := R) (G := G) C hC]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)
    (completedGroupAlgebraToInClass_surjective (R := R) (G := G) C hC hForm hG)
    (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC)

/-- A functorial all-finite completed group-algebra map sends augmentation generators to their images. -/
@[simp]
theorem completedGroupAlgebraMap_sub_one_of
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
        (completedGroupAlgebraOf R G g - 1) =
      completedGroupAlgebraOf R H (φ g) - 1 := by
  rw [map_sub, completedGroupAlgebraMap_of, map_one]

/-- A functorial all-finite completed group-algebra map preserves and reflects the canonical augmentation ideal when appropriate. -/
@[simp]
theorem completedGroupAlgebraMap_mem_canonicalAugmentationIdeal_iff
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (x : Carrier R G) :
    completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x ∈
        completedGroupAlgebraCanonicalAugmentationIdeal R H ↔
      x ∈ completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff,
    completedGroupAlgebraCanonicalAugmentation_map]

/-- The canonical completed augmentation ideal is pulled back to the canonical completed
augmentation ideal by any completed group-algebra map. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdeal_comap_map
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) :
    Ideal.comap (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdeal R H) =
      completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  ext x
  exact completedGroupAlgebraMap_mem_canonicalAugmentationIdeal_iff
    (R := R) (G := G) (H := H) hG φ hφ x

/-- A surjective functorial map sends the canonical completed augmentation ideal onto the target
canonical augmentation ideal. -/
theorem completedGroupAlgebraCanonicalAugmentationIdeal_map_functorial_of_surjective
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    (hH : ProCGroups.IsProfiniteGroup H) (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) :
    Ideal.map (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdeal R G) =
      completedGroupAlgebraCanonicalAugmentationIdeal R H := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdeal_comap_map
    (R := R) (G := G) (H := H) hG φ hφ]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ)
    (completedGroupAlgebraMap_surjective_of_surjective
      (R := R) (G := G) (H := H) hR hG hH φ hφ hφsurj)
    (completedGroupAlgebraCanonicalAugmentationIdeal R H)
end

end CompletedGroupAlgebra
