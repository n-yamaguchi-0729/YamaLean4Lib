import CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.Algebra

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/OpenFiniteLimit/Topology.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topology on the open finite quotient limit
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (R : Type u) [CommRing R] [TopologicalSpace R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Each two-parameter finite quotient stage is a topological ring for its discrete topology. -/
theorem completedGroupAlgebraOpenFiniteQuotientStage_isTopologicalRing
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    IsTopologicalRing (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) := by
  letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  haveI : DiscreteTopology (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
  infer_instance

/-- Under profiniteness of `R`, each two-parameter quotient stage is a finite discrete profinite
ring. -/
theorem completedGroupAlgebraOpenFiniteQuotientStage_isProfiniteRing
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hR : IsProfiniteRing R)
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    IsProfiniteRing (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) := by
  classical
  letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  haveI : DiscreteTopology (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
  let I : Ideal R := (OrderDual.ofDual K.1).1
  have hIopen : IsOpen (I : Set R) := (OrderDual.ofDual K.1).2
  rcases finite_quotient_of_openIdeal R hR I hIopen with ⟨hIfin⟩
  letI : Fintype (R ⧸ I) := hIfin
  letI : Fintype (CompletedGroupAlgebraQuotient G K.2) :=
    Fintype.ofFinite (CompletedGroupAlgebraQuotient G K.2)
  letI : Fintype (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    Fintype.ofEquiv (CompletedGroupAlgebraQuotient G K.2 → R ⧸ I)
      Finsupp.equivFunOnFinite.symm
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Each open finite quotient stage is finite when the coefficient ring is profinite. -/
theorem completedGroupAlgebraOpenFiniteQuotientStage_fintype
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hR : IsProfiniteRing R)
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Nonempty (Fintype (CompletedGroupAlgebraOpenFiniteQuotientStage R G K)) := by
  classical
  let I : Ideal R := (OrderDual.ofDual K.1).1
  have hIopen : IsOpen (I : Set R) := (OrderDual.ofDual K.1).2
  rcases finite_quotient_of_openIdeal R hR I hIopen with ⟨hIfin⟩
  letI : Fintype (R ⧸ I) := hIfin
  letI : Fintype (CompletedGroupAlgebraQuotient G K.2) :=
    Fintype.ofFinite (CompletedGroupAlgebraQuotient G K.2)
  exact ⟨Fintype.ofEquiv
    (CompletedGroupAlgebraQuotient G K.2 → R ⧸ I)
    Finsupp.equivFunOnFinite.symm⟩

instance instContinuousAddCompletedGroupAlgebraOpenFiniteQuotientLimit :
    ContinuousAdd (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  continuous_add := by
    let A := CompletedGroupAlgebraOpenFiniteQuotientLimit R G
    letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      fun K => (completedGroupAlgebraOpenFiniteQuotientSystem R G).topologicalSpace K
    have hval : Continuous fun p : A × A =>
        ((p.1 + p.2 : A) :
          (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
            (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
      change Continuous fun p : A × A =>
        fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
          completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K p.1 +
            completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K p.2
      apply continuous_pi
      intro K
      letI : IsTopologicalRing ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
        completedGroupAlgebraOpenFiniteQuotientStage_isTopologicalRing (R := R) (G := G) K
      exact (((completedGroupAlgebraOpenFiniteQuotientSystem R G).continuous_projection K).comp
          continuous_fst).add
        (((completedGroupAlgebraOpenFiniteQuotientSystem R G).continuous_projection K).comp
          continuous_snd)
    exact Continuous.subtype_mk hval fun p => (p.1 + p.2).2

instance instContinuousNegCompletedGroupAlgebraOpenFiniteQuotientLimit :
    ContinuousNeg (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  continuous_neg := by
    let A := CompletedGroupAlgebraOpenFiniteQuotientLimit R G
    letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      fun K => (completedGroupAlgebraOpenFiniteQuotientSystem R G).topologicalSpace K
    have hval : Continuous fun x : A =>
        ((-x : A) :
          (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
            (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
      change Continuous fun x : A =>
        fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
          -completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x
      apply continuous_pi
      intro K
      letI : IsTopologicalRing ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
        completedGroupAlgebraOpenFiniteQuotientStage_isTopologicalRing (R := R) (G := G) K
      exact ((completedGroupAlgebraOpenFiniteQuotientSystem R G).continuous_projection K).neg
    exact Continuous.subtype_mk hval fun x => (-x).2

instance instContinuousMulCompletedGroupAlgebraOpenFiniteQuotientLimit :
    ContinuousMul (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  continuous_mul := by
    let A := CompletedGroupAlgebraOpenFiniteQuotientLimit R G
    letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      fun K => (completedGroupAlgebraOpenFiniteQuotientSystem R G).topologicalSpace K
    have hval : Continuous fun p : A × A =>
        ((p.1 * p.2 : A) :
          (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
            (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
      change Continuous fun p : A × A =>
        fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
          completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K p.1 *
            completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K p.2
      apply continuous_pi
      intro K
      letI : IsTopologicalRing ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
        completedGroupAlgebraOpenFiniteQuotientStage_isTopologicalRing (R := R) (G := G) K
      exact (((completedGroupAlgebraOpenFiniteQuotientSystem R G).continuous_projection K).comp
          continuous_fst).mul
        (((completedGroupAlgebraOpenFiniteQuotientSystem R G).continuous_projection K).comp
          continuous_snd)
    exact Continuous.subtype_mk hval fun p => (p.1 * p.2).2

instance instIsTopologicalRingCompletedGroupAlgebraOpenFiniteQuotientLimit :
    IsTopologicalRing (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  letI : ContinuousAdd (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    instContinuousAddCompletedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G)
  letI : ContinuousMul (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    instContinuousMulCompletedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G)
  letI : ContinuousNeg (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    instContinuousNegCompletedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G)
  letI : IsTopologicalSemiring (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

/-- The open finite quotient limit is compact when the coefficient ring is profinite. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_compactSpace
    (hR : IsProfiniteRing R) :
    CompactSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      CompactSpace ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K =>
    (completedGroupAlgebraOpenFiniteQuotientStage_isProfiniteRing (R := R) (G := G) hR K).2.1
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      T2Space ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K =>
    (completedGroupAlgebraOpenFiniteQuotientStage_isProfiniteRing (R := R) (G := G) hR K).2.2.1
  infer_instance

/-- The open finite quotient limit is Hausdorff when the coefficient ring is profinite. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_t2Space
    (hR : IsProfiniteRing R) :
    T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      T2Space ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K =>
    (completedGroupAlgebraOpenFiniteQuotientStage_isProfiniteRing (R := R) (G := G) hR K).2.2.1
  exact (completedGroupAlgebraOpenFiniteQuotientSystem R G).t2Space_inverseLimit

/-- The open finite quotient limit is totally disconnected when the coefficient ring is profinite. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_totallyDisconnectedSpace
    (hR : IsProfiniteRing R) :
    TotallyDisconnectedSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TotallyDisconnectedSpace ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K =>
    (completedGroupAlgebraOpenFiniteQuotientStage_isProfiniteRing (R := R) (G := G) hR K).2.2.2
  exact (completedGroupAlgebraOpenFiniteQuotientSystem R G).totallyDisconnectedSpace_inverseLimit

/-- The two-parameter kernel-neighborhood limit is a profinite ring. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_isProfiniteRing
    (hR : IsProfiniteRing R) :
    IsProfiniteRing (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  letI : CompactSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_compactSpace (R := R) (G := G) hR
  letI : T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_t2Space (R := R) (G := G) hR
  letI : TotallyDisconnectedSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_totallyDisconnectedSpace (R := R) (G := G) hR
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end

end CompletedGroupAlgebra
