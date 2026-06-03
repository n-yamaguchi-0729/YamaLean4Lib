import CompletedGroupAlgebra.Basic.AllFinite.Projections

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/AllFinite/Topology.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topology and profiniteness

This module equips the all-finite completed group algebra with its inverse-limit topology and proves the resulting profiniteness properties.
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

/-- Each finite stage `R[G/U]` is a topological ring for its product topology. -/
theorem completedGroupAlgebraStage_isTopologicalRing (U : CompletedGroupAlgebraIndex G) :
    IsTopologicalRing ((completedGroupAlgebraSystem R G).X U) := by
  dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
  exact finiteGroupAlgebra_isTopologicalRing R (CompletedGroupAlgebraQuotient G U)

instance instContinuousSMulCompletedGroupAlgebra :
    ContinuousSMul R (Carrier R G) where
  continuous_smul := by
    let A := Carrier R G
    letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
    have hval : Continuous fun p : R × A =>
        fun U : CompletedGroupAlgebraIndex G =>
          (show CompletedGroupAlgebraStage R G U from (p.1 • p.2).1 U) := by
      change Continuous fun p : R × A =>
        fun U : CompletedGroupAlgebraIndex G =>
          p.1 • completedGroupAlgebraProjection R G U p.2
      apply continuous_pi
      intro U
      letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
        (completedGroupAlgebraSystem R G).topologicalSpace U
      letI : ContinuousSMul R (CompletedGroupAlgebraStage R G U) :=
        finiteGroupAlgebra_continuousSMul R (CompletedGroupAlgebraQuotient G U)
      exact continuous_fst.smul
        (((completedGroupAlgebraSystem R G).continuous_projection U).comp continuous_snd)
    exact Continuous.subtype_mk hval fun p => (p.1 • p.2).2

instance instContinuousAddCompletedGroupAlgebra :
    ContinuousAdd (Carrier R G) where
  continuous_add := by
    let A := Carrier R G
    letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
    have hval : Continuous fun p : A × A =>
        ((p.1 + p.2 : A) :
          (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) := by
      change Continuous fun p : A × A =>
        fun U : CompletedGroupAlgebraIndex G =>
          completedGroupAlgebraProjection R G U p.1 +
            completedGroupAlgebraProjection R G U p.2
      apply continuous_pi
      intro U
      letI : IsTopologicalRing ((completedGroupAlgebraSystem R G).X U) :=
        completedGroupAlgebraStage_isTopologicalRing (R := R) (G := G) U
      exact (((completedGroupAlgebraSystem R G).continuous_projection U).comp continuous_fst).add
        (((completedGroupAlgebraSystem R G).continuous_projection U).comp continuous_snd)
    exact Continuous.subtype_mk hval fun p => (p.1 + p.2).2

instance instContinuousNegCompletedGroupAlgebra :
    ContinuousNeg (Carrier R G) where
  continuous_neg := by
    let A := Carrier R G
    letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
    have hval : Continuous fun x : A =>
        ((-x : A) :
          (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) := by
      change Continuous fun x : A =>
        fun U : CompletedGroupAlgebraIndex G => -completedGroupAlgebraProjection R G U x
      apply continuous_pi
      intro U
      letI : IsTopologicalRing ((completedGroupAlgebraSystem R G).X U) :=
        completedGroupAlgebraStage_isTopologicalRing (R := R) (G := G) U
      exact ((completedGroupAlgebraSystem R G).continuous_projection U).neg
    exact Continuous.subtype_mk hval fun x => (-x).2

instance instContinuousMulCompletedGroupAlgebra :
    ContinuousMul (Carrier R G) where
  continuous_mul := by
    let A := Carrier R G
    letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
    have hval : Continuous fun p : A × A =>
        ((p.1 * p.2 : A) :
          (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) := by
      change Continuous fun p : A × A =>
        fun U : CompletedGroupAlgebraIndex G =>
          completedGroupAlgebraProjection R G U p.1 *
            completedGroupAlgebraProjection R G U p.2
      apply continuous_pi
      intro U
      letI : IsTopologicalRing ((completedGroupAlgebraSystem R G).X U) :=
        completedGroupAlgebraStage_isTopologicalRing (R := R) (G := G) U
      exact (((completedGroupAlgebraSystem R G).continuous_projection U).comp continuous_fst).mul
        (((completedGroupAlgebraSystem R G).continuous_projection U).comp continuous_snd)
    exact Continuous.subtype_mk hval fun p => (p.1 * p.2).2

instance instIsTopologicalRingCompletedGroupAlgebra :
    IsTopologicalRing (Carrier R G) := by
  letI : ContinuousAdd (Carrier R G) :=
    instContinuousAddCompletedGroupAlgebra (R := R) (G := G)
  letI : ContinuousMul (Carrier R G) :=
    instContinuousMulCompletedGroupAlgebra (R := R) (G := G)
  letI : ContinuousNeg (Carrier R G) :=
    instContinuousNegCompletedGroupAlgebra (R := R) (G := G)
  letI : IsTopologicalSemiring (Carrier R G) := IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

/-- Each finite stage is profinite when the coefficient ring is profinite. -/
theorem completedGroupAlgebraStage_isProfiniteRing
    (hR : IsProfiniteRing R) (U : CompletedGroupAlgebraIndex G) :
    IsProfiniteRing ((completedGroupAlgebraSystem R G).X U) := by
  dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
  exact finiteGroupAlgebra_isProfiniteRing R (CompletedGroupAlgebraQuotient G U) hR

/-- The completed group algebra is compact when the coefficient ring is profinite. -/
theorem completedGroupAlgebra_compactSpace (hR : IsProfiniteRing R) :
    CompactSpace (Carrier R G) := by
  letI : ∀ U : CompletedGroupAlgebraIndex G,
      CompactSpace ((completedGroupAlgebraSystem R G).X U) := fun U =>
    (completedGroupAlgebraStage_isProfiniteRing (R := R) (G := G) hR U).2.1
  letI : ∀ U : CompletedGroupAlgebraIndex G,
      T2Space ((completedGroupAlgebraSystem R G).X U) := fun U =>
    (completedGroupAlgebraStage_isProfiniteRing (R := R) (G := G) hR U).2.2.1
  infer_instance

/-- The completed group algebra is Hausdorff when the coefficient ring is profinite. -/
theorem completedGroupAlgebra_t2Space (hR : IsProfiniteRing R) :
    T2Space (Carrier R G) := by
  letI : ∀ U : CompletedGroupAlgebraIndex G,
      T2Space ((completedGroupAlgebraSystem R G).X U) := fun U =>
    (completedGroupAlgebraStage_isProfiniteRing (R := R) (G := G) hR U).2.2.1
  exact (completedGroupAlgebraSystem R G).t2Space_inverseLimit

/-- The completed group algebra is totally disconnected when the coefficient ring is profinite. -/
theorem completedGroupAlgebra_totallyDisconnectedSpace (hR : IsProfiniteRing R) :
    TotallyDisconnectedSpace (Carrier R G) := by
  letI : ∀ U : CompletedGroupAlgebraIndex G,
      TotallyDisconnectedSpace ((completedGroupAlgebraSystem R G).X U) := fun U =>
    (completedGroupAlgebraStage_isProfiniteRing (R := R) (G := G) hR U).2.2.2
  exact (completedGroupAlgebraSystem R G).totallyDisconnectedSpace_inverseLimit

/-- The book §5.3 completed group algebra is a profinite topological ring. -/
theorem completedGroupAlgebra_isProfiniteRing (hR : IsProfiniteRing R) :
    IsProfiniteRing (Carrier R G) := by
  letI : CompactSpace (Carrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G) hR
  letI : T2Space (Carrier R G) :=
    completedGroupAlgebra_t2Space (R := R) (G := G) hR
  letI : TotallyDisconnectedSpace (Carrier R G) :=
    completedGroupAlgebra_totallyDisconnectedSpace (R := R) (G := G) hR
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The completed group algebra is a profinite module over its profinite coefficient ring. -/
theorem completedGroupAlgebra_isProfiniteModule (hR : IsProfiniteRing R) :
    IsProfiniteModule R (Carrier R G) := by
  letI : IsTopologicalRing R := hR.1
  letI : IsTopologicalRing (Carrier R G) :=
    instIsTopologicalRingCompletedGroupAlgebra (R := R) (G := G)
  letI : IsTopologicalAddGroup (Carrier R G) := inferInstance
  letI : ContinuousSMul R (Carrier R G) :=
    instContinuousSMulCompletedGroupAlgebra (R := R) (G := G)
  letI : CompactSpace (Carrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G) hR
  letI : T2Space (Carrier R G) :=
    completedGroupAlgebra_t2Space (R := R) (G := G) hR
  letI : TotallyDisconnectedSpace (Carrier R G) :=
    completedGroupAlgebra_totallyDisconnectedSpace (R := R) (G := G) hR
  exact ⟨hR, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The finite-stage projection preserves compatible. -/
@[simp]
theorem completedGroupAlgebraProjection_compatible
    (x : Carrier R G) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    completedGroupAlgebraTransition R G hUV (completedGroupAlgebraProjection R G V x) =
      completedGroupAlgebraProjection R G U x :=
  (completedGroupAlgebraSystem R G).projection_compatible x U V hUV

end

end CompletedGroupAlgebra
