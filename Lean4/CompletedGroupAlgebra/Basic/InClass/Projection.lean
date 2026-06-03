import CompletedGroupAlgebra.Basic.InClass.LimitAlgebra

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/InClass/Projection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Class-Indexed Completed Group Algebras

Finite-class-indexed inverse systems and inverse limits for completed group algebras.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]


/-- Projection from a `C`-indexed completed group algebra to a finite stage. -/
abbrev completedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C hC R G → CompletedGroupAlgebraStageInClass C R G U :=
  (completedGroupAlgebraSystemInClass C hC R G).projection U

/-- Projection of a coefficient element to a finite stage is the stage algebra map. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (r : R) :
    completedGroupAlgebraProjectionInClass C hC R G U
        (completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C hC r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r :=
  rfl

/-- Projection of a coefficient-changed element is coefficient change of the projection. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_coeffMap
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C)
    (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjectionInClass C hC S G U
        (completedGroupAlgebraCoeffMapInClass (R := R) (G := G) C hC S f x) =
      completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U
        (completedGroupAlgebraProjectionInClass C hC R G U x) :=
  rfl

/-- Projection from a `C`-indexed completed group algebra to a finite stage, as a ring
homomorphism. -/
def completedGroupAlgebraProjectionRingHomInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C hC R G →+* CompletedGroupAlgebraStageInClass C R G U :=
  projectionRingHom (S := completedGroupAlgebraSystemInClass C hC R G) U

/-- The ring-hom projection agrees with the underlying stage projection. -/
@[simp]
theorem completedGroupAlgebraProjectionRingHomInClass_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjectionRingHomInClass C hC R G U x =
      completedGroupAlgebraProjectionInClass C hC R G U x :=
  rfl

/-- Projection from a `C`-indexed completed group algebra to a finite stage, as an algebra
homomorphism. -/
def completedGroupAlgebraProjectionAlgHomInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C hC R G →ₐ[R] CompletedGroupAlgebraStageInClass C R G U where
  toRingHom := completedGroupAlgebraProjectionRingHomInClass C hC R G U
  commutes' := by
    intro r
    rfl

/-- The algebra-hom projection agrees with the underlying stage projection. -/
@[simp]
theorem completedGroupAlgebraProjectionAlgHomInClass_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjectionAlgHomInClass C hC R G U x =
      completedGroupAlgebraProjectionInClass C hC R G U x :=
  rfl

/-- Projection from a `C`-indexed completed group algebra to a finite stage, as an `R`-linear
map. -/
def completedGroupAlgebraProjectionLinearMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C hC R G →ₗ[R] CompletedGroupAlgebraStageInClass C R G U where
  toFun := completedGroupAlgebraProjectionInClass C hC R G U
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

/-- The linear-map projection agrees with the underlying stage projection. -/
@[simp]
theorem completedGroupAlgebraProjectionLinearMapInClass_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjectionLinearMapInClass C hC R G U x =
      completedGroupAlgebraProjectionInClass C hC R G U x :=
  rfl

/-- The finite-stage projections are compatible with the `C`-indexed transition maps. -/
theorem completedGroupAlgebraProjectionInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraTransitionInClass C R G hUV
        (completedGroupAlgebraProjectionInClass C hC R G V x) =
      completedGroupAlgebraProjectionInClass C hC R G U x :=
  x.2 U V hUV

/-- Composing a stage projection with a transition map gives the coarser stage projection. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_comp_projectionRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraProjectionRingHomInClass C hC R G V) =
      completedGroupAlgebraProjectionRingHomInClass C hC R G U := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraProjectionInClass_compatible (R := R) (G := G) C hC hUV x

/-- Continuity of the projection from the `C`-indexed completed group algebra to a stage. -/
theorem continuous_completedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
    Continuous (completedGroupAlgebraProjectionInClass C hC R G U) := by
  letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
  exact (completedGroupAlgebraSystemInClass C hC R G).continuous_projection U

/-- Projection from a `C`-indexed completed group algebra to a finite stage, as a continuous
`R`-linear map. -/
def completedGroupAlgebraProjectionContinuousLinearMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
    CompletedGroupAlgebraInClass C hC R G →L[R] CompletedGroupAlgebraStageInClass C R G U := by
  letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
  exact
    { toLinearMap := completedGroupAlgebraProjectionLinearMapInClass C hC R G U
      cont := (completedGroupAlgebraSystemInClass C hC R G).continuous_projection U }

/-- The continuous linear projection agrees with the underlying stage projection. -/
@[simp]
theorem completedGroupAlgebraProjectionContinuousLinearMapInClass_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjectionContinuousLinearMapInClass C hC R G U x =
      completedGroupAlgebraProjectionInClass C hC R G U x :=
  rfl


end

end CompletedGroupAlgebra
