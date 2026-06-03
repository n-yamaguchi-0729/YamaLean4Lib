import CompletedGroupAlgebra.InClassFunctoriality.GroupLike
import CompletedGroupAlgebra.UniversalProperty.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/InClassFunctoriality/Comparison.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Functoriality of completed group algebras

The completed group algebra is presented as an inverse limit of finite group algebras, together with canonical augmentation, augmentation ideal, finite-stage maps, functoriality, and profinite module universal properties.
-/
open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The all-finite completed group algebra comparison sends group-like elements to the
`C`-indexed group-like elements. -/
@[simp]
theorem completedGroupAlgebraToInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (g : G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC
        (completedGroupAlgebraOf R G g) =
      completedGroupAlgebraOfInClass C hC R G g := by
  change ((completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC).comp
      (toCompletedGroupAlgebraRingHom R G)) (MonoidAlgebra.of R G g) =
    toCompletedGroupAlgebraInClassRingHom C hC R G (MonoidAlgebra.of R G g)
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
        (R := R) (G := G) C hC))
    (MonoidAlgebra.of R G g)

/-- The comparison map to a class-indexed completion sends all-finite augmentation generators to class-indexed generators. -/
@[simp]
theorem completedGroupAlgebraToInClass_of_sub_one
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (g : G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC
        (completedGroupAlgebraOf R G g - 1) =
      completedGroupAlgebraOfInClass C hC R G g - 1 := by
  rw [map_sub, completedGroupAlgebraToInClass_of, map_one]

/-- After restricting scalars along `[[R G]] -> [[R G]]_C`, the all-finite
augmentation generator acts as the matching `C`-indexed generator. -/
@[simp]
theorem completedGroupAlgebraToInClass_restrictScalars_sub_one_smul
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (A : Type w) [AddCommGroup A] [Module (CompletedGroupAlgebraInClass C hC R G) A]
    (g : G) (a : A) :
    letI : Module (Carrier R G) A :=
      Module.compHom A (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)
    (completedGroupAlgebraOf R G g - 1) • a =
      (completedGroupAlgebraOfInClass C hC R G g - 1) • a := by
  letI : Module (Carrier R G) A :=
    Module.compHom A (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)
  change (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC
      (completedGroupAlgebraOf R G g - 1)) • a =
    (completedGroupAlgebraOfInClass C hC R G g - 1) • a
  rw [completedGroupAlgebraToInClass_of_sub_one]

/-- The comparison map from a class-indexed completion sends class-indexed group-like elements to all-finite group-like elements. -/
@[simp]
theorem completedGroupAlgebraFromInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (g : G) :
    completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
        (completedGroupAlgebraOfInClass C hC R G g) =
      completedGroupAlgebraOf R G g := by
  change ((completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG).comp
      (toCompletedGroupAlgebraInClassRingHom C hC R G)) (MonoidAlgebra.of R G g) =
    toCompletedGroupAlgebraRingHom R G (MonoidAlgebra.of R G g)
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraFromInClassRingHom_comp_toCompletedGroupAlgebraInClass
        (R := R) (G := G) C hC hForm hG))
    (MonoidAlgebra.of R G g)

/-- The comparison map from a class-indexed completion sends class-indexed augmentation generators to all-finite generators. -/
@[simp]
theorem completedGroupAlgebraFromInClass_of_sub_one
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (g : G) :
    completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
        (completedGroupAlgebraOfInClass C hC R G g - 1) =
      completedGroupAlgebraOf R G g - 1 := by
  change completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG
      (completedGroupAlgebraOfInClass C hC R G g - 1) =
    completedGroupAlgebraOf R G g - 1
  rw [map_sub, map_one]
  change completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
      (completedGroupAlgebraOfInClass C hC R G g) - 1 =
    completedGroupAlgebraOf R G g - 1
  rw [completedGroupAlgebraFromInClass_of]

/-- After restricting scalars along `[[R G]]_C -> [[R G]]`, the `C`-indexed
augmentation generator acts as the matching all-finite generator. -/
@[simp]
theorem completedGroupAlgebraFromInClass_restrictScalars_sub_one_smul
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G)
    (A : Type w) [AddCommGroup A] [Module (Carrier R G) A]
    (g : G) (a : A) :
    letI : Module (CompletedGroupAlgebraInClass C hC R G) A :=
      Module.compHom A (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG)
    (completedGroupAlgebraOfInClass C hC R G g - 1) • a =
      (completedGroupAlgebraOf R G g - 1) • a := by
  letI : Module (CompletedGroupAlgebraInClass C hC R G) A :=
    Module.compHom A (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG)
  change (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG
      (completedGroupAlgebraOfInClass C hC R G g - 1)) • a =
    (completedGroupAlgebraOf R G g - 1) • a
  rw [completedGroupAlgebraFromInClassRingHom_apply,
    completedGroupAlgebraFromInClass_of_sub_one]

/-- The class-indexed functorial map sends completed group-like elements to completed group-like elements. -/
@[simp]
theorem completedGroupAlgebraMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
        (completedGroupAlgebraOfInClass C hC R G g) =
      completedGroupAlgebraOfInClass C hC R H (φ g) := by
  simpa [completedGroupAlgebraOfInClass] using
    completedGroupAlgebraMapInClass_toCompletedGroupAlgebraInClass_of
      (R := R) (G := G) (H := H) C hC hHer φ hφ g

/-- The class-indexed functorial map sends group-like augmentation generators to their images. -/
@[simp]
theorem completedGroupAlgebraMapInClass_of_sub_one
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
        (completedGroupAlgebraOfInClass C hC R G g - 1) =
      completedGroupAlgebraOfInClass C hC R H (φ g) - 1 := by
  rw [map_sub, completedGroupAlgebraMapInClass_of, map_one]

end

end CompletedGroupAlgebra
