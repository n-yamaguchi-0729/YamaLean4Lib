import CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteQuotients

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/OpenFiniteLimit/System.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Open finite quotient systems
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

/-- The two-parameter inverse system `K = (I,U) ↦ (R/I)[G/U]` for the
kernel-neighborhood topology. -/
def completedGroupAlgebraOpenFiniteQuotientSystem
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ProCGroups.InverseSystems.InverseSystem
      (I := CompletedGroupAlgebraOpenQuotientIndex R G) where
  X := CompletedGroupAlgebraOpenFiniteQuotientStage R G
  topologicalSpace := completedGroupAlgebraOpenFiniteQuotientStageTopology R G
  map := fun {K L} hKL => completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
  continuous_map := by
    intro K L hKL
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G L) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G L
    haveI : DiscreteTopology (CompletedGroupAlgebraOpenFiniteQuotientStage R G L) :=
      completedGroupAlgebraOpenFiniteQuotientStage_discrete R G L
    exact continuous_of_discreteTopology
  map_id := by
    intro K
    exact congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_id R G K)
  map_comp := by
    intro K L M hKL hLM
    exact congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_comp R G hKL hLM)

/-- The two-parameter inverse limit appearing in RZ §5.3,
`lim_{I,U} (R/I)[G/U]`. -/
abbrev CompletedGroupAlgebraOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Type (max u v) :=
  (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit

/-- Projection from the two-parameter limit to one quotient `(R/I)[G/U]`. -/
abbrev completedGroupAlgebraOpenFiniteQuotientLimitProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G →
      CompletedGroupAlgebraOpenFiniteQuotientStage R G K :=
  (completedGroupAlgebraOpenFiniteQuotientSystem R G).projection K

end

end CompletedGroupAlgebra
