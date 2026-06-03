import CompletedGroupAlgebra.InClassFunctoriality.UnitRepresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Augmentation/StageAugmentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Augmentation and augmentation ideals

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

variable (R : Type u) [CommRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The augmentation map on one `C`-indexed finite stage. -/
def completedGroupAlgebraStageAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraStageInClass C R G U →+* R :=
  groupAlgebraAugmentation R (CompletedGroupAlgebraQuotientInClass G C U)

/-- The in-class finite-stage augmentation sends every group-like basis element to one. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) :
    completedGroupAlgebraStageAugmentationInClass C R G U (MonoidAlgebra.of R _ q) = 1 := by
  simp only [completedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.of_apply,
  groupAlgebraAugmentation_single]

/-- The in-class finite-stage augmentation sends a singleton to its coefficient. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) (r : R) :
    completedGroupAlgebraStageAugmentationInClass C R G U (MonoidAlgebra.single q r) = r := by
  simp only [completedGroupAlgebraStageAugmentationInClass, groupAlgebraAugmentation_single]

/-- In-class finite-stage augmentations are compatible with transition maps. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraStageAugmentationInClass C R G U).comp
        (completedGroupAlgebraTransitionInClass C R G hUV) =
      completedGroupAlgebraStageAugmentationInClass C R G V := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R
    (CompletedGroupAlgebraQuotientInClass G C V)
    (CompletedGroupAlgebraQuotientInClass G C U)
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) x

/-- In-class finite-stage augmentation after the stage map is the abstract augmentation. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_stageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageAugmentationInClass C R G U).comp
        (completedGroupAlgebraStageMapInClass C R G U) =
      groupAlgebraAugmentation R G := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R G
    (CompletedGroupAlgebraQuotientInClass G C U)
    (openNormalSubgroupInClassProj (C := C) (G := G) U) x

/-- In-class finite-stage augmentation is natural in the coefficient ring. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageAugmentationInClass C S G U).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U) =
      f.comp (completedGroupAlgebraStageAugmentationInClass C R G U) := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapRangeRingHom R S
    (CompletedGroupAlgebraQuotientInClass G C U) f x

/-- In-class finite-stage augmentation is natural for functorial finite-stage maps. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_functorialStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    (completedGroupAlgebraStageAugmentationInClass C R H V).comp
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V) =
      completedGroupAlgebraStageAugmentationInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R
    (CompletedGroupAlgebraQuotientInClass G C
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V))
    (CompletedGroupAlgebraQuotientInClass H C V)
    (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V) x

end

end CompletedGroupAlgebra
