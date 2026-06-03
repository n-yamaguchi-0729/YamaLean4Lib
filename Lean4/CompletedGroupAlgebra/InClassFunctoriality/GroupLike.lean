import CompletedGroupAlgebra.InClassFunctoriality.Maps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/InClassFunctoriality/GroupLike.lean
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
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The `C`-indexed inverse-limit construction satisfies the completed-group-algebra property
package whenever `G` is pro-`C`. -/
theorem completedGroupAlgebraInClass_isCompletedGroupAlgebraModel
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) :
    IsCompletedGroupAlgebraModel R G (CompletedGroupAlgebraInClass C hC R G) := by
  refine ⟨hR, hG.1, completedGroupAlgebraInClass_isProfiniteRing
    (R := R) (G := G) C hC hR, ?_⟩
  refine ⟨TopologicalSpace.induced (toCompletedGroupAlgebraInClass C hC R G)
    (inferInstance : TopologicalSpace (CompletedGroupAlgebraInClass C hC R G)), ?_⟩
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    TopologicalSpace.induced (toCompletedGroupAlgebraInClass C hC R G)
      (inferInstance : TopologicalSpace (CompletedGroupAlgebraInClass C hC R G))
  exact ⟨toCompletedGroupAlgebraInClassRingHom C hC R G,
    denseRange_toCompletedGroupAlgebraInClass (R := R) (G := G) C hC hForm hG,
    by
      change Continuous (toCompletedGroupAlgebraInClass C hC R G)
      exact continuous_induced_dom⟩

/-- The image of a group element in the `C`-indexed completed group algebra. -/
def completedGroupAlgebraOfInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : G) : CompletedGroupAlgebraInClass C hC R G :=
  toCompletedGroupAlgebraInClass C hC R G (MonoidAlgebra.of R G g)

/-- Projection of a class-indexed completed group-like element to a finite quotient stage. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (g : G) :
    completedGroupAlgebraProjectionInClass C hC R G U
        (completedGroupAlgebraOfInClass C hC R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  rw [completedGroupAlgebraOfInClass,
    completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass,
    completedGroupAlgebraStageMapInClass_of]

/-- The class-indexed completed group-like element attached to one is the unit. -/
@[simp]
theorem completedGroupAlgebraOfInClass_one
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    completedGroupAlgebraOfInClass C hC R G 1 =
      (1 : CompletedGroupAlgebraInClass C hC R G) := by
  apply (completedGroupAlgebraSystemInClass C hC R G).ext
  intro U
  change completedGroupAlgebraProjectionInClass C hC R G U
      (completedGroupAlgebraOfInClass C hC R G 1) =
    completedGroupAlgebraProjectionInClass C hC R G U
      (1 : CompletedGroupAlgebraInClass C hC R G)
  rw [completedGroupAlgebraProjectionInClass_of]
  change MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U 1)
      (1 : R) =
    completedGroupAlgebraProjectionRingHomInClass C hC R G U
      (1 : CompletedGroupAlgebraInClass C hC R G)
  rw [map_one]
  change MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U 1)
      (1 : R) = 1
  rfl

/-- Class-indexed completed group-like elements multiply according to the group law. -/
@[simp 900]
theorem completedGroupAlgebraOfInClass_mul
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (g h : G) :
    completedGroupAlgebraOfInClass C hC R G (g * h) =
      completedGroupAlgebraOfInClass C hC R G g *
        completedGroupAlgebraOfInClass C hC R G h := by
  apply (completedGroupAlgebraSystemInClass C hC R G).ext
  intro U
  change completedGroupAlgebraProjectionInClass C hC R G U
      (completedGroupAlgebraOfInClass C hC R G (g * h)) =
    completedGroupAlgebraProjectionInClass C hC R G U
      (completedGroupAlgebraOfInClass C hC R G g *
        completedGroupAlgebraOfInClass C hC R G h)
  rw [completedGroupAlgebraProjectionInClass_of]
  have hmul :
      completedGroupAlgebraProjectionInClass C hC R G U
          (completedGroupAlgebraOfInClass C hC R G g *
            completedGroupAlgebraOfInClass C hC R G h) =
        completedGroupAlgebraProjectionInClass C hC R G U
            (completedGroupAlgebraOfInClass C hC R G g) *
          completedGroupAlgebraProjectionInClass C hC R G U
            (completedGroupAlgebraOfInClass C hC R G h) := by
    exact map_mul (completedGroupAlgebraProjectionRingHomInClass C hC R G U)
      (completedGroupAlgebraOfInClass C hC R G g)
      (completedGroupAlgebraOfInClass C hC R G h)
  rw [hmul, completedGroupAlgebraProjectionInClass_of, completedGroupAlgebraProjectionInClass_of]
  change MonoidAlgebra.single
      (openNormalSubgroupInClassProj (C := C) (G := G) U (g * h)) (1 : R) =
    MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 *
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U h) 1
  simp only [map_mul, MonoidAlgebra.single_mul_single, mul_one]

/-- The class-indexed finite-stage group-like map is continuous. -/
theorem continuous_completedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
    Continuous fun g : G => completedGroupAlgebraStageMapInClass C R G U
      (MonoidAlgebra.of R G g) := by
  letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C hC U
  letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
  letI : DiscreteTopology (CompletedGroupAlgebraQuotientInClass G C U) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
  have hbasis :
      Continuous fun q : CompletedGroupAlgebraQuotientInClass G C U =>
        (MonoidAlgebra.of R (CompletedGroupAlgebraQuotientInClass G C U) q :
          CompletedGroupAlgebraStageInClass C R G U) :=
    continuous_of_discreteTopology
  have hproj :
      Continuous fun g : G => openNormalSubgroupInClassProj (C := C) (G := G) U g := by
    change Continuous
      (QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G))
    exact continuous_quotient_mk'
  simpa [MonoidAlgebra.of, completedGroupAlgebraStageMapInClass_single] using hbasis.comp hproj

/-- The class-indexed completed group-like map is continuous. -/
theorem continuous_completedGroupAlgebraOfInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Continuous (completedGroupAlgebraOfInClass C hC R G) := by
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    fun U => (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
  have hval : Continuous fun g : G =>
      fun U : CompletedGroupAlgebraIndexInClass G C =>
        (show CompletedGroupAlgebraStageInClass C R G U from
          (completedGroupAlgebraOfInClass C hC R G g).1 U) := by
    change Continuous fun g : G =>
      fun U : CompletedGroupAlgebraIndexInClass G C =>
        completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.of R G g)
    apply continuous_pi
    intro U
    exact continuous_completedGroupAlgebraStageMapInClass_of (R := R) (G := G) C hC U
  exact Continuous.subtype_mk hval fun g => (completedGroupAlgebraOfInClass C hC R G g).2

end

end CompletedGroupAlgebra
