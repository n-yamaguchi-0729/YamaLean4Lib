import CompletedGroupAlgebra.Basic.InClass.Projection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/InClass/Topology.lean
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


/-- Each `C`-indexed finite stage is a topological ring. -/
theorem completedGroupAlgebraStageInClass_isTopologicalRing
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C hC U
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
    IsTopologicalRing (CompletedGroupAlgebraStageInClass C R G U) := by
  letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C hC U
  letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace U
  dsimp [completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
  exact finiteGroupAlgebra_isTopologicalRing R (CompletedGroupAlgebraQuotientInClass G C U)

instance instIsTopologicalRingCompletedGroupAlgebraSystemInClassX
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    IsTopologicalRing ((completedGroupAlgebraSystemInClass C hC R G).X U) :=
  completedGroupAlgebraStageInClass_isTopologicalRing (R := R) (G := G) C hC U

instance instIsTopologicalRingCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    IsTopologicalRing (CompletedGroupAlgebraInClass C hC R G) := by
  change IsTopologicalRing (completedGroupAlgebraSystemInClass C hC R G).inverseLimit
  infer_instance

instance instContinuousSMulCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    ContinuousSMul R (CompletedGroupAlgebraInClass C hC R G) where
  continuous_smul := by
    let A := CompletedGroupAlgebraInClass C hC R G
    let S := completedGroupAlgebraSystemInClass C hC R G
    letI : ∀ U : CompletedGroupAlgebraIndexInClass G C,
        TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      fun U => S.topologicalSpace U
    have hval : Continuous fun p : R × A =>
        fun U : CompletedGroupAlgebraIndexInClass G C =>
          (show CompletedGroupAlgebraStageInClass C R G U from (p.1 • p.2).1 U) := by
      change Continuous fun p : R × A =>
        fun U : CompletedGroupAlgebraIndexInClass G C =>
          p.1 • completedGroupAlgebraProjectionInClass C hC R G U p.2
      apply continuous_pi
      intro U
      letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
        finite_completedGroupAlgebraQuotientInClass G C hC U
      letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
        S.topologicalSpace U
      letI : ContinuousSMul R (CompletedGroupAlgebraStageInClass C R G U) :=
        finiteGroupAlgebra_continuousSMul R (CompletedGroupAlgebraQuotientInClass G C U)
      exact continuous_fst.smul ((S.continuous_projection U).comp continuous_snd)
    exact Continuous.subtype_mk hval fun p => (p.1 • p.2).2

/-- The coefficient-ring map into the `C`-indexed completed group algebra is continuous. -/
theorem continuous_completedGroupAlgebraAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Continuous (algebraMap R (CompletedGroupAlgebraInClass C hC R G)) := by
  let S := completedGroupAlgebraSystemInClass C hC R G
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    fun U => S.topologicalSpace U
  have hval : Continuous fun r : R =>
      fun U : CompletedGroupAlgebraIndexInClass G C =>
        (show CompletedGroupAlgebraStageInClass C R G U from
          (algebraMap R (CompletedGroupAlgebraInClass C hC R G) r).1 U) := by
    change Continuous fun r : R =>
      fun U : CompletedGroupAlgebraIndexInClass G C =>
        algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r
    apply continuous_pi
    intro U
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C hC U
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      S.topologicalSpace U
    exact finiteGroupAlgebra_algebraMap_continuous R (CompletedGroupAlgebraQuotientInClass G C U)
  exact Continuous.subtype_mk hval fun r =>
    (algebraMap R (CompletedGroupAlgebraInClass C hC R G) r).2

/-- Each `C`-indexed finite stage is a profinite ring when the coefficient ring is profinite. -/
theorem completedGroupAlgebraStageInClass_isProfiniteRing
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) (U : CompletedGroupAlgebraIndexInClass G C) :
    IsProfiniteRing ((completedGroupAlgebraSystemInClass C hC R G).X U) := by
  letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C hC U
  dsimp [completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
  exact finiteGroupAlgebra_isProfiniteRing R (CompletedGroupAlgebraQuotientInClass G C U) hR

/-- The `C`-indexed completed group algebra is compact when the coefficient ring is profinite. -/
theorem completedGroupAlgebraInClass_compactSpace
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) :
    CompactSpace (CompletedGroupAlgebraInClass C hC R G) := by
  let S := completedGroupAlgebraSystemInClass C hC R G
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C, CompactSpace (S.X U) := fun U =>
    (completedGroupAlgebraStageInClass_isProfiniteRing (R := R) (G := G) C hC hR U).2.1
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C, T2Space (S.X U) := fun U =>
    (completedGroupAlgebraStageInClass_isProfiniteRing (R := R) (G := G) C hC hR U).2.2.1
  change CompactSpace S.inverseLimit
  infer_instance

/-- The `C`-indexed completed group algebra is Hausdorff when the coefficient ring is profinite. -/
theorem completedGroupAlgebraInClass_t2Space
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) :
    T2Space (CompletedGroupAlgebraInClass C hC R G) := by
  let S := completedGroupAlgebraSystemInClass C hC R G
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C, T2Space (S.X U) := fun U =>
    (completedGroupAlgebraStageInClass_isProfiniteRing (R := R) (G := G) C hC hR U).2.2.1
  exact S.t2Space_inverseLimit

/-- The `C`-indexed completed group algebra is totally disconnected for profinite coefficients. -/
theorem completedGroupAlgebraInClass_totallyDisconnectedSpace
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) :
    TotallyDisconnectedSpace (CompletedGroupAlgebraInClass C hC R G) := by
  let S := completedGroupAlgebraSystemInClass C hC R G
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C, TotallyDisconnectedSpace (S.X U) :=
    fun U =>
      (completedGroupAlgebraStageInClass_isProfiniteRing (R := R) (G := G) C hC hR U).2.2.2
  exact S.totallyDisconnectedSpace_inverseLimit

/-- The `C`-indexed completed group algebra is profinite when the coefficient ring is profinite. -/
theorem completedGroupAlgebraInClass_isProfiniteRing
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) :
    IsProfiniteRing (CompletedGroupAlgebraInClass C hC R G) := by
  letI : IsTopologicalRing (CompletedGroupAlgebraInClass C hC R G) :=
    instIsTopologicalRingCompletedGroupAlgebraInClass (R := R) (G := G) C hC
  letI : CompactSpace (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_compactSpace (R := R) (G := G) C hC hR
  letI : T2Space (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_t2Space (R := R) (G := G) C hC hR
  letI : TotallyDisconnectedSpace (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_totallyDisconnectedSpace (R := R) (G := G) C hC hR
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The `C`-indexed completed group algebra is a profinite module over its coefficient ring. -/
theorem completedGroupAlgebraInClass_isProfiniteModule
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) :
    IsProfiniteModule R (CompletedGroupAlgebraInClass C hC R G) := by
  letI : IsTopologicalRing R := hR.1
  letI : IsTopologicalRing (CompletedGroupAlgebraInClass C hC R G) :=
    instIsTopologicalRingCompletedGroupAlgebraInClass (R := R) (G := G) C hC
  letI : IsTopologicalAddGroup (CompletedGroupAlgebraInClass C hC R G) := inferInstance
  letI : ContinuousSMul R (CompletedGroupAlgebraInClass C hC R G) :=
    instContinuousSMulCompletedGroupAlgebraInClass (R := R) (G := G) C hC
  letI : CompactSpace (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_compactSpace (R := R) (G := G) C hC hR
  letI : T2Space (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_t2Space (R := R) (G := G) C hC hR
  letI : TotallyDisconnectedSpace (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_totallyDisconnectedSpace (R := R) (G := G) C hC hR
  exact ⟨hR, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩


end

end CompletedGroupAlgebra
