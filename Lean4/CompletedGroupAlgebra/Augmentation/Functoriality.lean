import CompletedGroupAlgebra.Augmentation.AugmentationIdeal

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Augmentation/Functoriality.lean
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

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The in-class canonical augmentation is natural under functorial completed maps. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentationInClass_map
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := H) C hC
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC x := by
  let V : CompletedGroupAlgebraIndexInClass H C :=
    terminalCompletedGroupAlgebraIndexInClass (G := H) C
  calc
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := H) C hC
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x)
        =
      completedGroupAlgebraAugmentationAtInClass C R H hC V
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x) := by
          exact completedGroupAlgebraCanonicalAugmentationInClass_eq_at
            (R := R) (G := H) C hC V
            (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x)
    _ =
      completedGroupAlgebraStageAugmentationInClass C R H V
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V
          (completedGroupAlgebraProjectionInClass C hC R G
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)) := by
          rw [completedGroupAlgebraAugmentationAtInClass, completedGroupAlgebraProjectionInClass_map]
    _ =
      completedGroupAlgebraStageAugmentationInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)
        (completedGroupAlgebraProjectionInClass C hC R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x) := by
          have hstage := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraStageAugmentationInClass_comp_functorialStageMapInClass
                (R := R) (G := G) (H := H) C hHer φ hφ V))
            (completedGroupAlgebraProjectionInClass C hC R G
              (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)
          exact hstage
    _ =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC x := by
          exact (completedGroupAlgebraCanonicalAugmentationInClass_eq_at
            (R := R) (G := G) C hC
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x).symm

/-- Composing an in-class completed map with augmentation gives the source augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationInClass_comp_map
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := H) C hC).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraCanonicalAugmentationInClass_map
    (R := R) (G := G) (H := H) C hC hHer φ hφ x

/-- Functorial in-class completed maps preserve membership in the canonical augmentation ideal. -/
@[simp]
theorem completedGroupAlgebraMapInClass_mem_canonicalAugmentationIdeal_iff
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ)
    (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x ∈
        completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C hC ↔
      x ∈ completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    completedGroupAlgebraCanonicalAugmentationInClass_map]

/-- The `C`-indexed canonical augmentation ideal is pulled back to itself by functorial maps. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_map
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    Ideal.comap (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C hC) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC := by
  ext x
  exact completedGroupAlgebraMapInClass_mem_canonicalAugmentationIdeal_iff
    (R := R) (G := G) (H := H) C hC hHer φ hφ x

/-- A surjective functorial map sends the `C`-indexed canonical augmentation ideal onto the
target canonical augmentation ideal. -/
theorem completedGACanonicalAugmentationIdealInClass_map_functorial_of_surj
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ) :
    Ideal.map (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C hC := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_map
    (R := R) (G := G) (H := H) C hC hHer φ hφ]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ)
    (completedGroupAlgebraMapInClass_surjective_of_surjective
      (R := R) (G := G) (H := H) C hC hForm hHer hR hH φ hφ hφsurj)
    (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C hC)

end

end CompletedGroupAlgebra
