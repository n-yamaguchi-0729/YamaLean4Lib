import CompletedGroupAlgebra.Augmentation.CanonicalAugmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Augmentation/AugmentationIdeal.lean
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

/-- The canonical augmentation ideal of the `C`-indexed completed group algebra. -/
def completedGroupAlgebraCanonicalAugmentationIdealInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Ideal (CompletedGroupAlgebraInClass C hC R G) :=
  RingHom.ker (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC)

/-- Membership in the in-class canonical augmentation ideal is kernel membership. -/
@[simp]
theorem mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (x : CompletedGroupAlgebraInClass C hC R G) :
    x ∈ completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C hC ↔
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC x = 0 :=
  Iff.rfl

/-- The inclusion of the `C`-indexed canonical augmentation ideal is injective. -/
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype_injective
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Injective
      (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C hC => (x : CompletedGroupAlgebraInClass C hC R G)) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The `C`-indexed canonical augmentation ideal is exactly the kernel of the canonical
augmentation. -/
theorem exact_completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Exact
      (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C hC => (x : CompletedGroupAlgebraInClass C hC R G))
      (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/-- The `C`-indexed canonical augmentation sequence `0 → I_G → [[R G]]_C → R → 0` is
short exact. -/
theorem completedGroupAlgebraCanonicalAugmentationInClass_shortExact
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Injective
        (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C hC => (x : CompletedGroupAlgebraInClass C hC R G)) ∧
      Function.Exact
        (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C hC => (x : CompletedGroupAlgebraInClass C hC R G))
        (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC) ∧
      Function.Surjective
        (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC) := by
  exact ⟨completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype_injective
      (R := R) (G := G) C hC,
    exact_completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype
      (R := R) (G := G) C hC,
    completedGroupAlgebraCanonicalAugmentationInClass_surjective (R := R) (G := G) C hC⟩

/-- The in-class canonical augmentation sends every completed group-like element to one. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] (g : G) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C hC
        (completedGroupAlgebraOfInClass C hC R G g) = 1 := by
  rw [completedGroupAlgebraOfInClass,
    canonicalAugmentationInClass_toCompleted]
  simp only [MonoidAlgebra.of_apply, groupAlgebraAugmentation_single]

end

end CompletedGroupAlgebra
