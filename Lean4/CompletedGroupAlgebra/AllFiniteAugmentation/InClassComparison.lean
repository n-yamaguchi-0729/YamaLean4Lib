import CompletedGroupAlgebra.AllFiniteAugmentation.CanonicalAugmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteAugmentation/InClassComparison.lean
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

/-- The class-indexed canonical augmentation composed with the comparison map agrees with the
all-finite augmentation. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentationInClass_comp_toInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC).comp
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC) =
      completedGroupAlgebraCanonicalAugmentation R G := by
  apply RingHom.ext
  intro x
  let Uc : CompletedGroupAlgebraIndexInClass G C :=
    terminalCompletedGroupAlgebraIndexInClass (G := G) C
  let U : CompletedGroupAlgebraIndex G :=
    completedGroupAlgebraIndexInClassToAllFinite G C hC Uc
  calc
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC x)
        =
      completedGroupAlgebraAugmentationAtInClass C R G hC Uc
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC x) := by
          exact completedGroupAlgebraCanonicalAugmentationInClass_eq_at
            (R := R) (G := G) C hC Uc
            (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC x)
    _ =
      completedGroupAlgebraStageAugmentationInClass C R G Uc
        (completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC Uc x) := rfl
    _ =
      completedGroupAlgebraStageAugmentation R G U
        (completedGroupAlgebraProjection R G U x) := rfl
    _ = completedGroupAlgebraCanonicalAugmentation R G x := by
      exact (completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := G) U x).symm

/-- The all-finite canonical augmentation after the comparison map from a class-indexed
completion agrees with the class-indexed augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G)
    (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraCanonicalAugmentation R G
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC x := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraCanonicalAugmentationInClass_comp_toInClass
        (R := R) (G := G) C hC))
    (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x)
  change completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC
      (completedGroupAlgebraToInClass (R := R) (G := G) C hC
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x)) =
    completedGroupAlgebraCanonicalAugmentation R G
      (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x) at h
  rw [completedGroupAlgebraToInClass_fromInClass] at h
  exact h.symm
end

end CompletedGroupAlgebra
