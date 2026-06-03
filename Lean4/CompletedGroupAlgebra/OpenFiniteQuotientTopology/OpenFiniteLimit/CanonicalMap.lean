import CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.Topology

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/OpenFiniteLimit/CanonicalMap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Canonical maps to the open finite quotient limit
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

/-- The abstract group-algebra map onto an open finite quotient stage is surjective. -/
theorem groupAlgebraOpenFiniteQuotientMap_surjective
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Function.Surjective (groupAlgebraOpenFiniteQuotientMap R G K) :=
  groupAlgebraFiniteQuotientMap_surjective (R := R) (G := G)
    ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/-- The abstract group-algebra maps to open finite quotient stages are compatible. -/
theorem groupAlgebraOpenFiniteQuotientMap_compatibleMaps
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (completedGroupAlgebraOpenFiniteQuotientSystem R G).CompatibleMaps
      (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
        groupAlgebraOpenFiniteQuotientMap R G K) := by
  intro K L hKL
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_comp_map R G hKL))
    x

/-- The canonical map from `[R G]` to the two-parameter limit `lim_{I,U}(R/I)[G/U]`. -/
def toCompletedGroupAlgebraOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
  ⟨fun K => groupAlgebraOpenFiniteQuotientMap R G K x, by
    intro K L hKL
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraOpenFiniteQuotientTransition_comp_map R G hKL))
      x⟩

/-- Projecting the canonical map to the open finite quotient limit recovers the stage quotient map. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_toLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) (x : MonoidAlgebra R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
        (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x) =
      groupAlgebraOpenFiniteQuotientMap R G K x :=
  rfl

/-- The canonical map from `[R G]` to the two-parameter limit, as a ring homomorphism. -/
def toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →+* CompletedGroupAlgebraOpenFiniteQuotientLimit R G where
  toFun := toCompletedGroupAlgebraOpenFiniteQuotientLimit R G
  map_zero' := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_zero (groupAlgebraOpenFiniteQuotientMap R G K)
  map_one' := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_one (groupAlgebraOpenFiniteQuotientMap R G K)
  map_add' x y := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_add (groupAlgebraOpenFiniteQuotientMap R G K) x y
  map_mul' x y := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_mul (groupAlgebraOpenFiniteQuotientMap R G K) x y

/-- The canonical ring homomorphism to the open finite quotient limit has the expected function. -/
@[simp]
theorem toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom_apply
    [IsTopologicalRing R]
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G x =
      toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x :=
  rfl

/-- Projection after the canonical ring homomorphism is the corresponding open finite quotient map. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjectionRingHom_comp_toLimit
    [IsTopologicalRing R]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    (completedGroupAlgebraOpenFiniteQuotientLimitProjectionRingHom R G K).comp
        (toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G) =
      groupAlgebraOpenFiniteQuotientMap R G K := by
  apply RingHom.ext
  intro x
  rfl

/-- The canonical map to the open finite quotient limit is continuous for the kernel topology. -/
theorem continuous_toCompletedGroupAlgebraOpenFiniteQuotientLimit_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    Continuous (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  have hprod : Continuous (groupAlgebraOpenFiniteQuotientProductMap R G) :=
    continuous_groupAlgebraOpenFiniteQuotientProductMap_kernelTopology R G
  change Continuous fun x : MonoidAlgebra R G =>
    (⟨groupAlgebraOpenFiniteQuotientProductMap R G x, _⟩ :
      CompletedGroupAlgebraOpenFiniteQuotientLimit R G)
  exact Continuous.subtype_mk hprod fun x => (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x).2

/-- The abstract group algebra has dense image in the two-parameter kernel-neighborhood limit
`lim_{I,U}(R/I)[G/U]`. -/
theorem denseRange_toCompletedGroupAlgebraOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    DenseRange (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  letI : TopologicalSpace (MonoidAlgebra R G) := ⊥
  have hdir :
      Directed (α := CompletedGroupAlgebraOpenQuotientIndex R G) (· ≤ ·) fun K => K :=
    directed_completedGroupAlgebraOpenQuotientIndex R G
  have hdense :
      DenseRange
        (S.inverseLimitLift
          (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
            groupAlgebraOpenFiniteQuotientMap R G K)
          (groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G)) :=
    S.denseRange_lift
      (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
        groupAlgebraOpenFiniteQuotientMap R G K)
      (groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G)
      (fun K => groupAlgebraOpenFiniteQuotientMap_surjective R G K)
      hdir
  simpa [S, toCompletedGroupAlgebraOpenFiniteQuotientLimit] using hdense

end

end CompletedGroupAlgebra
