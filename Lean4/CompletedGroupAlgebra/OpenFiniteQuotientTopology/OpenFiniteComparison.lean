import CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.CanonicalMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/OpenFiniteComparison.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebras

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

/-- The canonical map from the fixed-coefficient completed group algebra `[[R G]]` to the
two-parameter limit `lim_{I,U}(R/I)[G/U]`. -/
def completedGroupAlgebraToOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : Carrier R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
  ⟨fun K => completedGroupAlgebraOpenFiniteQuotientProjection R G K x, by
    intro K L hKL
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraOpenFiniteQuotientTransition_comp_projection R G hKL))
      x⟩

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_fromCompleted
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) (x : Carrier R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
        (completedGroupAlgebraToOpenFiniteQuotientLimit R G x) =
      completedGroupAlgebraOpenFiniteQuotientProjection R G K x :=
  rfl

@[simp]
theorem completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) :
    completedGroupAlgebraToOpenFiniteQuotientLimit R G (toCompletedGroupAlgebra R G x) =
      toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x := by
  apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
  intro K
  rfl

/-- The canonical map `[[R G]] -> lim_{I,U}(R/I)[G/U]`, as a ring homomorphism. -/
def completedGroupAlgebraToOpenFiniteQuotientLimitRingHom
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Carrier R G →+* CompletedGroupAlgebraOpenFiniteQuotientLimit R G where
  toFun := completedGroupAlgebraToOpenFiniteQuotientLimit R G
  map_zero' := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_zero (completedGroupAlgebraOpenFiniteQuotientProjection R G K)
  map_one' := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_one (completedGroupAlgebraOpenFiniteQuotientProjection R G K)
  map_add' x y := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_add (completedGroupAlgebraOpenFiniteQuotientProjection R G K) x y
  map_mul' x y := by
    apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
    intro K
    exact map_mul (completedGroupAlgebraOpenFiniteQuotientProjection R G K) x y

@[simp]
theorem openFiniteLimitProjectionRingHom_comp_fromCompleted
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    (completedGroupAlgebraOpenFiniteQuotientLimitProjectionRingHom R G K).comp
        (completedGroupAlgebraToOpenFiniteQuotientLimitRingHom R G) =
      completedGroupAlgebraOpenFiniteQuotientProjection R G K := by
  apply RingHom.ext
  intro x
  rfl

@[simp]
theorem completedGAToOpenFiniteQuotientLimitRingHom_comp_toCompletedGA :
    (completedGroupAlgebraToOpenFiniteQuotientLimitRingHom R G).comp
        (toCompletedGroupAlgebraRingHom R G) =
      toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra (R := R) (G := G) x

/-- The comparison map `[[RG]] -> lim_{I,U}(R/I)[G/U]` is continuous. -/
theorem continuous_completedGroupAlgebraToOpenFiniteQuotientLimit :
    Continuous (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  let A := Carrier R G
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  have hval : Continuous fun x : A =>
      ((completedGroupAlgebraToOpenFiniteQuotientLimit R G x) :
        (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
          (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
    change Continuous fun x : A =>
      fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
        completedGroupAlgebraOpenFiniteQuotientProjection R G K x
    apply continuous_pi
    intro K
    exact continuous_completedGroupAlgebraOpenFiniteQuotientProjection (R := R) (G := G) K
  exact Continuous.subtype_mk hval fun x =>
    (completedGroupAlgebraToOpenFiniteQuotientLimit R G x).2

theorem denseRange_completedGroupAlgebraToOpenFiniteQuotientLimit
    [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    DenseRange (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  have hdense :
      DenseRange
        ((completedGroupAlgebraToOpenFiniteQuotientLimit R G) ∘
          (toCompletedGroupAlgebra R G)) := by
    simpa [Function.comp] using
      denseRange_toCompletedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G)
  exact DenseRange.of_comp hdense

/-- The comparison map to the two-parameter kernel-neighborhood limit is injective when the
coefficient ring is profinite. This is the completed-stage form of the kernel-intersection
assertion in Lemma 5.3.5(a). -/
theorem injective_completedGroupAlgebraToOpenFiniteQuotientLimit
    (hR : IsProfiniteRing R) :
    Function.Injective (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  intro x y hxy
  apply (completedGroupAlgebraSystem R G).ext
  intro U
  apply Finsupp.ext
  intro q
  have hzero : ((completedGroupAlgebraProjection R G U x -
        completedGroupAlgebraProjection R G U y) q) = 0 := by
    apply profiniteRing_eq_zero_of_forall_openIdeal_quotient_eq_zero (R := R) hR
    intro Iopen
    let K : CompletedGroupAlgebraOpenQuotientIndex R G := (OrderDual.toDual Iopen, U)
    have hcoord := congrArg
      (fun z : CompletedGroupAlgebraOpenFiniteQuotientLimit R G =>
        completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K z) hxy
    change completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 U
        (completedGroupAlgebraProjection R G U x) =
      completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 U
        (completedGroupAlgebraProjection R G U y) at hcoord
    have hdiff : completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 U
        (completedGroupAlgebraProjection R G U x -
          completedGroupAlgebraProjection R G U y) = 0 := by
      rw [map_sub, hcoord, sub_self]
    have hq := congrArg
      (fun z : CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 U => z q) hdiff
    simpa [completedGroupAlgebraStageCoeffQuotientMap,
      MonoidAlgebra.mapRangeRingHom_apply] using hq
  have hsub : (completedGroupAlgebraProjection R G U x) q -
      (completedGroupAlgebraProjection R G U y) q = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- The comparison map to the two-parameter kernel-neighborhood limit is onto for profinite
coefficients: its dense image is compact, hence closed, in the Hausdorff two-parameter limit. -/
theorem surjective_completedGroupAlgebraToOpenFiniteQuotientLimit
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Function.Surjective (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  letI : CompactSpace (Carrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G) hR
  letI : T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_t2Space (R := R) (G := G) hR
  have hclosed : IsClosed (Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G)) := by
    exact (isCompact_range
      (continuous_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G))).isClosed
  have hdense :
      closure (Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G)) = Set.univ :=
    (denseRange_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G)).closure_range
  have hrange : Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G) = Set.univ := by
    rwa [hclosed.closure_eq] at hdense
  intro y
  have hy : y ∈ Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
    rw [hrange]
    exact Set.mem_univ y
  simpa using hy

/-- The comparison map `[[RG]] -> lim_{I,U}(R/I)[G/U]` is a bijection under the profinite
coefficient hypothesis. -/
theorem bijective_completedGroupAlgebraToOpenFiniteQuotientLimit
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Function.Bijective (completedGroupAlgebraToOpenFiniteQuotientLimit R G) :=
  ⟨injective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G) hR,
    surjective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G) hR⟩

/-- RZ §5.3 comparison: the fixed-coefficient inverse-limit model `[[RG]]` is ring-isomorphic to
the two-parameter kernel-neighborhood limit `lim_{I,U}(R/I)[G/U]` for profinite coefficient rings. -/
def completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Carrier R G ≃+* CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
  RingEquiv.ofBijective (completedGroupAlgebraToOpenFiniteQuotientLimitRingHom R G)
    (bijective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G) hR)

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv_apply
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)]
    (x : Carrier R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv (R := R) (G := G) hR x =
      completedGroupAlgebraToOpenFiniteQuotientLimit R G x :=
  rfl

/-- The same comparison as a homeomorphism of the underlying profinite spaces. -/
def completedGroupAlgebraOpenFiniteQuotientLimitHomeomorph
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Carrier R G ≃ₜ CompletedGroupAlgebraOpenFiniteQuotientLimit R G := by
  letI : CompactSpace (Carrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G) hR
  letI : T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_t2Space (R := R) (G := G) hR
  let e : Carrier R G ≃ CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
    (completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv (R := R) (G := G) hR).toEquiv
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (by
    change Continuous (completedGroupAlgebraToOpenFiniteQuotientLimit R G)
    exact continuous_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G))

/-- Lemma 5.3.5(c), fixed-coefficient inverse-limit form: the abstract group algebra maps
dense into the completed group algebra. -/
theorem denseRange_toCompletedGroupAlgebra (hG : ProCGroups.IsProfiniteGroup G) :
    DenseRange (toCompletedGroupAlgebra R G) := by
  let S := completedGroupAlgebraSystem R G
  letI : TopologicalSpace (MonoidAlgebra R G) := ⊥
  have hProC : IsProCGroup ProCGroups.FiniteGroupClass.allFinite G :=
    (isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG
  letI : Nonempty (OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G) :=
    IsProCGroup.openNormalSubgroupInClass_nonempty hProC
  letI : Nonempty (CompletedGroupAlgebraIndex G) := inferInstance
  have hdir : Directed (α := CompletedGroupAlgebraIndex G) (· ≤ ·) fun U => U :=
    directed_openNormalSubgroupInClass
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) ProCGroups.FiniteGroupClass.allFinite_formation
  have hdense :
      DenseRange
        (S.inverseLimitLift (fun U : CompletedGroupAlgebraIndex G => completedGroupAlgebraStageMap R G U)
          (completedGroupAlgebraStageMap_compatibleMaps (R := R) (G := G))) :=
    S.denseRange_lift
      (fun U : CompletedGroupAlgebraIndex G => completedGroupAlgebraStageMap R G U)
      (completedGroupAlgebraStageMap_compatibleMaps (R := R) (G := G))
      (fun U => completedGroupAlgebraStageMap_surjective (R := R) (G := G) U)
      hdir
  simpa [S, toCompletedGroupAlgebra] using hdense

theorem denseRange_toCompletedGroupAlgebraRingHom (hG : ProCGroups.IsProfiniteGroup G) :
    DenseRange (toCompletedGroupAlgebraRingHom R G) := by
  simpa [toCompletedGroupAlgebraRingHom] using
    denseRange_toCompletedGroupAlgebra (R := R) (G := G) hG

/-- The completion topology on the abstract group algebra, induced by the canonical map into
`[[R G]]`; below it is identified with the kernel-neighborhood topology generated by the maps
`R[G] -> (R/I)[G/U]`. -/
def completedGroupAlgebraNaturalTopology (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    TopologicalSpace (MonoidAlgebra R G) :=
  TopologicalSpace.induced (toCompletedGroupAlgebra R G) inferInstance

theorem continuous_toCompletedGroupAlgebraRingHom_naturalTopology :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      completedGroupAlgebraNaturalTopology R G
    Continuous (toCompletedGroupAlgebraRingHom R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  change Continuous (toCompletedGroupAlgebra R G)
  exact (continuous_induced_dom : Continuous (toCompletedGroupAlgebra R G))

/-- The canonical map as a continuous `R`-linear map for the topology induced from `[[RG]]`. -/
def toCompletedGroupAlgebraContinuousLinearMap_naturalTopology :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      completedGroupAlgebraNaturalTopology R G
    MonoidAlgebra R G →L[R] Carrier R G := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  exact
    { toLinearMap := toCompletedGroupAlgebraLinearMap R G
      cont := continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G) }

omit [IsTopologicalRing R] in
/-- The kernel-neighborhood topology is exactly the topology induced by the canonical map from
`R[G]` to the two-parameter kernel-neighborhood limit. -/
theorem groupAlgebraOpenFiniteQuotientKernelTopology_eq_induced_toLimit :
    groupAlgebraOpenFiniteQuotientKernelTopology R G =
      TopologicalSpace.induced (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G) inferInstance := by
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  change TopologicalSpace.induced (groupAlgebraOpenFiniteQuotientProductMap R G) inferInstance =
    TopologicalSpace.induced (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G)
      (TopologicalSpace.induced (fun z : S.inverseLimit => z.1) inferInstance)
  rw [induced_compose]
  rfl

/-- Under the profinite coefficient hypothesis, the topology on `R[G]` induced from `[[RG]]`
agrees with the topology induced by the two-parameter kernel-neighborhood limit. -/
theorem completedGroupAlgebraNaturalTopology_eq_induced_toOpenFiniteQuotientLimit
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    completedGroupAlgebraNaturalTopology R G =
      TopologicalSpace.induced (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G) inferInstance := by
  let e := completedGroupAlgebraOpenFiniteQuotientLimitHomeomorph (R := R) (G := G) hR
  have hcomp : e ∘ toCompletedGroupAlgebra R G =
      toCompletedGroupAlgebraOpenFiniteQuotientLimit R G := by
    funext x
    exact completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra
      (R := R) (G := G) x
  dsimp [completedGroupAlgebraNaturalTopology]
  rw [e.isInducing.eq_induced]
  rw [induced_compose]
  rw [hcomp]

/-- RZ §5.3 natural topology comparison: the topology on the abstract group algebra induced from
`[[RG]]` is the kernel-neighborhood topology generated by the maps `R[G] -> (R/I)[G/U]`. -/
theorem completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    completedGroupAlgebraNaturalTopology R G =
      groupAlgebraOpenFiniteQuotientKernelTopology R G := by
  rw [completedGroupAlgebraNaturalTopology_eq_induced_toOpenFiniteQuotientLimit
      (R := R) (G := G) hR,
    groupAlgebraOpenFiniteQuotientKernelTopology_eq_induced_toLimit (R := R) (G := G)]

/-- The canonical map `R[G] -> [[RG]]` is continuous for the kernel-neighborhood topology on
`R[G]`. -/
theorem continuous_toCompletedGroupAlgebraRingHom_kernelTopology
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    Continuous (toCompletedGroupAlgebraRingHom R G) := by
  let τnat := completedGroupAlgebraNaturalTopology R G
  let τker := groupAlgebraOpenFiniteQuotientKernelTopology R G
  have hτ : τnat = τker :=
    completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
      (R := R) (G := G) hR
  change @Continuous (MonoidAlgebra R G) (Carrier R G)
    τker inferInstance (toCompletedGroupAlgebraRingHom R G)
  rw [← hτ]
  exact continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G)

/-- The canonical map as a continuous `R`-linear map for the kernel-neighborhood topology. -/
def toCompletedGroupAlgebraContinuousLinearMap_kernelTopology
    (hR : IsProfiniteRing R) [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    MonoidAlgebra R G →L[R] Carrier R G := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  exact
    { toLinearMap := toCompletedGroupAlgebraLinearMap R G
      cont := continuous_toCompletedGroupAlgebraRingHom_kernelTopology
        (R := R) (G := G) hR }

/-- Lemma 5.3.5(b/c), kernel-topology data form: for profinite `R` and profinite `G`, the
concrete inverse-limit `[[RG]]` is profinite and receives a dense continuous map from `R[G]`
when `R[G]` carries the kernel-neighborhood topology. -/
theorem completedGroupAlgebra_kernelTopologyCompletionData
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    IsProfiniteRing (Carrier R G) ∧
      DenseRange (toCompletedGroupAlgebraRingHom R G) ∧
        Continuous (toCompletedGroupAlgebraRingHom R G) := by
  have hProC : IsProCGroup ProCGroups.FiniteGroupClass.allFinite G :=
    (isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG
  letI : Nonempty (OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G) :=
    IsProCGroup.openNormalSubgroupInClass_nonempty hProC
  letI : Nonempty (CompletedGroupAlgebraIndex G) := inferInstance
  letI : Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G) := inferInstance
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  exact ⟨completedGroupAlgebra_isProfiniteRing (R := R) (G := G) hR,
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG,
    continuous_toCompletedGroupAlgebraRingHom_kernelTopology (R := R) (G := G) hR⟩

/-- Linear-module form of the kernel-topology completion data for Lemma 5.3.5. -/
theorem completedGroupAlgebra_kernelTopologyModuleCompletionData
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    IsProfiniteModule R (Carrier R G) ∧
      DenseRange (toCompletedGroupAlgebraLinearMap R G) ∧
        Continuous (toCompletedGroupAlgebraLinearMap R G) := by
  have hProC : IsProCGroup ProCGroups.FiniteGroupClass.allFinite G :=
    (isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG
  letI : Nonempty (OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G) :=
    IsProCGroup.openNormalSubgroupInClass_nonempty hProC
  letI : Nonempty (CompletedGroupAlgebraIndex G) := inferInstance
  letI : Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G) := inferInstance
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  refine ⟨completedGroupAlgebra_isProfiniteModule (R := R) (G := G) hR, ?_, ?_⟩
  · change DenseRange (toCompletedGroupAlgebra R G)
    simpa [toCompletedGroupAlgebraRingHom] using
      denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG
  · change Continuous (toCompletedGroupAlgebra R G)
    exact continuous_toCompletedGroupAlgebraRingHom_kernelTopology (R := R) (G := G) hR
end

end CompletedGroupAlgebra
