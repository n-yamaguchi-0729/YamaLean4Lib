import CompletedGroupAlgebra.Basic.AllFinite.Ring

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/AllFinite/Projections.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Linear and algebraic projections

This module records the finite-stage projections of the all-finite completed group algebra and their compatibility with the transition maps.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The coefficient-ring map `R -> [[RG]]` is continuous. -/
theorem continuous_completedGroupAlgebra_algebraMap :
    Continuous (algebraMap R (Carrier R G)) := by
  letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
  have hval : Continuous fun r : R =>
      fun U : CompletedGroupAlgebraIndex G =>
        (show CompletedGroupAlgebraStage R G U from
          (algebraMap R (Carrier R G) r).1 U) := by
    change Continuous fun r : R =>
      fun U : CompletedGroupAlgebraIndex G =>
        algebraMap R (CompletedGroupAlgebraStage R G U) r
    apply continuous_pi
    intro U
    exact finiteGroupAlgebra_algebraMap_continuous R (CompletedGroupAlgebraQuotient G U)
  exact Continuous.subtype_mk hval fun r => (algebraMap R (Carrier R G) r).2

/-- The canonical projection to a finite stage, as an `R`-linear map. -/
def completedGroupAlgebraProjectionLinearMap (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    Carrier R G →ₗ[R] CompletedGroupAlgebraStage R G U where
  toFun := completedGroupAlgebraProjection R G U
  map_add' := completedGroupAlgebraProjection_add (R := R) (G := G) U
  map_smul' := completedGroupAlgebraProjection_smul (R := R) (G := G) U

/-- The finite-stage projection, as a continuous `R`-linear map. -/
def completedGroupAlgebraProjectionContinuousLinearMap (R : Type u) (G : Type v)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      (completedGroupAlgebraSystem R G).topologicalSpace U
    Carrier R G →L[R] CompletedGroupAlgebraStage R G U := by
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  exact
    { toLinearMap := completedGroupAlgebraProjectionLinearMap R G U
      cont := (completedGroupAlgebraSystem R G).continuous_projection U }

/-- The canonical projection to a finite stage, as a ring homomorphism. -/
def completedGroupAlgebraProjectionRingHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    Carrier R G →+* CompletedGroupAlgebraStage R G U where
  toFun := completedGroupAlgebraProjection R G U
  map_zero' := completedGroupAlgebraProjection_zero (R := R) (G := G) U
  map_one' := completedGroupAlgebraProjection_one (R := R) (G := G) U
  map_add' := completedGroupAlgebraProjection_add (R := R) (G := G) U
  map_mul' := completedGroupAlgebraProjection_mul (R := R) (G := G) U

/-- The canonical projection to a finite stage, as an `R`-algebra homomorphism. -/
def completedGroupAlgebraProjectionAlgHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    Carrier R G →ₐ[R] CompletedGroupAlgebraStage R G U where
  toRingHom := completedGroupAlgebraProjectionRingHom R G U
  commutes' := by
    intro r
    rfl

end

end CompletedGroupAlgebra
