import CompletedGroupAlgebra.OpenFiniteQuotientTopology.FiniteQuotients

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/OpenFiniteQuotients.lean
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

/-- Open coefficient ideals used in the RZ §5.3 kernel-neighborhood topology. -/
abbrev CompletedGroupAlgebraOpenIdeal
    (R : Type u) [CommRing R] [TopologicalSpace R] : Type u :=
  {I : Ideal R // IsOpen (I : Set R)}

omit G [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [IsTopologicalRing R] in
/-- In a profinite coefficient ring, the open-ideal quotients separate points. This is the
coefficient part of Lemma 5.3.5(a)'s kernel-intersection statement. -/
theorem profiniteRing_eq_zero_of_forall_openIdeal_quotient_eq_zero
    (hR : IsProfiniteRing R) {r : R}
    (hr : ∀ I : CompletedGroupAlgebraOpenIdeal R, Ideal.Quotient.mk I.1 r = 0) :
    r = 0 := by
  by_contra hne
  letI : T2Space R := hR.2.2.1
  letI : T1Space R := inferInstance
  have h0 : (0 : R) ∈ ({r}ᶜ : Set R) := by
    exact fun h0r => hne h0r.symm
  have hU : ({r}ᶜ : Set R) ∈ 𝓝 (0 : R) :=
    isOpen_compl_singleton.mem_nhds h0
  rcases profiniteRing_hasOpenIdealBasisAtZero R hR ({r}ᶜ) hU with
    ⟨I, hIopen, hIU⟩
  have hrI : r ∈ I := by
    exact Ideal.Quotient.eq_zero_iff_mem.1 (hr ⟨I, hIopen⟩)
  exact (hIU hrI) rfl

/-- The two-parameter index set for the kernel-neighborhood quotients `(R/I)[G/U]`, with open
ideals in the coefficient direction and finite group quotients in the group direction. -/
abbrev CompletedGroupAlgebraOpenQuotientIndex
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] : Type (max u v) :=
  OrderDual (CompletedGroupAlgebraOpenIdeal R) × CompletedGroupAlgebraIndex G

instance instNonemptyCompletedGroupAlgebraOpenIdeal
    (R : Type u) [CommRing R] [TopologicalSpace R] :
    Nonempty (CompletedGroupAlgebraOpenIdeal R) :=
  ⟨⟨⊤, isOpen_univ⟩⟩

theorem directed_completedGroupAlgebraOpenQuotientIndex
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Directed (α := CompletedGroupAlgebraOpenQuotientIndex R G) (· ≤ ·) fun K => K := by
  intro K L
  rcases directed_openNormalSubgroupInClass
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) ProCGroups.FiniteGroupClass.allFinite_formation
      K.2 L.2 with
    ⟨W, hKW, hLW⟩
  let I : CompletedGroupAlgebraOpenIdeal R :=
    ⟨(OrderDual.ofDual K.1).1 ⊓ (OrderDual.ofDual L.1).1, by
      simpa using (OrderDual.ofDual K.1).2.inter (OrderDual.ofDual L.1).2⟩
  refine ⟨(OrderDual.toDual I, W), ?_, ?_⟩
  · constructor
    · change (I.1 : Ideal R) ≤ (OrderDual.ofDual K.1).1
      exact inf_le_left
    · exact hKW
  · constructor
    · change (I.1 : Ideal R) ≤ (OrderDual.ofDual L.1).1
      exact inf_le_right
    · exact hLW

/-- The stage `(R/I)[G/U]` attached to an open-ideal/finite-group quotient index. -/
abbrev CompletedGroupAlgebraOpenFiniteQuotientStage
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Type (max u v) :=
  CompletedGroupAlgebraCoeffQuotientStage R G ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/-- The quotient map `[R G] -> (R/I)[G/U]` for an open-ideal/finite-group quotient index. -/
def groupAlgebraOpenFiniteQuotientMap
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraOpenFiniteQuotientStage R G K :=
  groupAlgebraFiniteQuotientMap R G ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/-- The kernel neighborhood attached to an open-ideal/finite-group quotient index. -/
def groupAlgebraOpenFiniteQuotientKernel
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Ideal (MonoidAlgebra R G) :=
  groupAlgebraFiniteQuotientKernel R G ((OrderDual.ofDual K.1).1 : Ideal R) K.2

@[simp]
theorem mem_groupAlgebraOpenFiniteQuotientKernel_iff
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) (x : MonoidAlgebra R G) :
    x ∈ groupAlgebraOpenFiniteQuotientKernel R G K ↔
      groupAlgebraOpenFiniteQuotientMap R G K x = 0 :=
  Iff.rfl

/-- The transition `(R/I_L)[G/U_L] -> (R/I_K)[G/U_K]` for `K ≤ L`. -/
def completedGroupAlgebraOpenFiniteQuotientTransition
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    CompletedGroupAlgebraOpenFiniteQuotientStage R G L →+*
      CompletedGroupAlgebraOpenFiniteQuotientStage R G K :=
  completedGroupAlgebraFiniteQuotientTransition R G
    (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
        ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1)
    hKL.2

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_comp_map
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL).comp
        (groupAlgebraOpenFiniteQuotientMap R G L) =
      groupAlgebraOpenFiniteQuotientMap R G K := by
  exact completedGroupAlgebraFiniteQuotientTransition_comp_finiteQuotientMap
    (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2)

/-- The projection `[[R G]] -> (R/I)[G/U]` for an open-ideal/finite-group quotient index. -/
def completedGroupAlgebraOpenFiniteQuotientProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Carrier R G →+* CompletedGroupAlgebraOpenFiniteQuotientStage R G K :=
  completedGroupAlgebraFiniteQuotientProjection R G
    ((OrderDual.ofDual K.1).1 : Ideal R) K.2

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientProjection_toCompletedGroupAlgebra
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    (completedGroupAlgebraOpenFiniteQuotientProjection R G K).comp
        (toCompletedGroupAlgebraRingHom R G) =
      groupAlgebraOpenFiniteQuotientMap R G K := by
  rfl

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_comp_projection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL).comp
        (completedGroupAlgebraOpenFiniteQuotientProjection R G L) =
      completedGroupAlgebraOpenFiniteQuotientProjection R G K := by
  exact completedGroupAlgebraFiniteQuotientTransition_comp_projection
    (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2)

theorem groupAlgebraOpenFiniteQuotientKernel_antitone
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    groupAlgebraOpenFiniteQuotientKernel R G L ≤
      groupAlgebraOpenFiniteQuotientKernel R G K := by
  intro x hx
  rw [mem_groupAlgebraOpenFiniteQuotientKernel_iff] at hx ⊢
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_comp_map (R := R) (G := G) hKL))
    x
  rw [RingHom.comp_apply, hx, map_zero] at hcomp
  exact hcomp.symm

/-- The discrete topology on each kernel-neighborhood quotient `(R/I)[G/U]`. This is the topology
used in the construction of the abstract group-algebra topology. -/
def completedGroupAlgebraOpenFiniteQuotientStageTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
  ⊥

theorem completedGroupAlgebraOpenFiniteQuotientStage_discrete
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    DiscreteTopology (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) := by
  letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  exact ⟨rfl⟩

/-- The coefficient quotient from the finite stage `R[G/U]` to the kernel-neighborhood quotient
`(R/I)[G/U]` is continuous when the target carries the discrete quotient topology. -/
theorem continuous_completedGroupAlgebraStageCoeffQuotientMap_openIdeal
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G K.2) :=
      (completedGroupAlgebraSystem R G).topologicalSpace K.2
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (completedGroupAlgebraStageCoeffQuotientMap R G
      ((OrderDual.ofDual K.1).1 : Ideal R) K.2) := by
  let Iopen : CompletedGroupAlgebraOpenIdeal R := OrderDual.ofDual K.1
  let Q := CompletedGroupAlgebraQuotient G K.2
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G K.2) :=
    (completedGroupAlgebraSystem R G).topologicalSpace K.2
  letI : TopologicalSpace (R ⧸ (Iopen.1 : Ideal R)) := ⊥
  haveI : DiscreteTopology (R ⧸ (Iopen.1 : Ideal R)) := ⟨rfl⟩
  have hmk : Continuous (Ideal.Quotient.mk (Iopen.1 : Ideal R)) :=
    continuous_idealQuotient_mk_openIdeal_discrete
      (R := R) (I := Iopen.1) Iopen.2
  have hcont :
      letI : TopologicalSpace (CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 K.2) :=
        finiteGroupAlgebraTopology (R ⧸ (Iopen.1 : Ideal R)) Q
      Continuous (completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 K.2) := by
    dsimp [CompletedGroupAlgebraStage, CompletedGroupAlgebraCoeffQuotientStage, Q]
    exact finiteGroupAlgebra_mapRangeRingHom_continuous
      (R := R) (S := R ⧸ (Iopen.1 : Ideal R)) Q
      (Ideal.Quotient.mk (Iopen.1 : Ideal R)) hmk
  have hdisc :
      letI : TopologicalSpace (CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 K.2) :=
        finiteGroupAlgebraTopology (R ⧸ (Iopen.1 : Ideal R)) Q
      DiscreteTopology (CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 K.2) := by
    dsimp [CompletedGroupAlgebraCoeffQuotientStage, Q]
    exact finiteGroupAlgebraTopology_discrete_of_discrete_coeff
      (S := R ⧸ (Iopen.1 : Ideal R)) Q
  let tfin : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    finiteGroupAlgebraTopology (R ⧸ (Iopen.1 : Ideal R)) Q
  let tdisc : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  have ht : tfin = tdisc := by
    dsimp [tfin, tdisc, completedGroupAlgebraOpenFiniteQuotientStageTopology]
    exact hdisc.eq_bot
  change @Continuous (CompletedGroupAlgebraStage R G K.2)
    (CompletedGroupAlgebraOpenFiniteQuotientStage R G K)
    ((completedGroupAlgebraSystem R G).topologicalSpace K.2) tdisc
    (completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 K.2)
  rw [← ht]
  exact hcont

/-- The projection `[[RG]] -> (R/I)[G/U]` to any two-parameter finite quotient is
continuous. -/
theorem continuous_completedGroupAlgebraOpenFiniteQuotientProjection
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (completedGroupAlgebraOpenFiniteQuotientProjection R G K) := by
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G K.2) :=
    (completedGroupAlgebraSystem R G).topologicalSpace K.2
  letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  exact (continuous_completedGroupAlgebraStageCoeffQuotientMap_openIdeal
    (R := R) (G := G) K).comp ((completedGroupAlgebraSystem R G).continuous_projection K.2)

/-- The product of all open finite quotient maps `[R G] -> (R/I)[G/U]`. -/
def groupAlgebraOpenFiniteQuotientProductMap
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        CompletedGroupAlgebraOpenFiniteQuotientStage R G K :=
  fun x K => groupAlgebraOpenFiniteQuotientMap R G K x

/-- The kernel-neighborhood topology on `[R G]`, induced by all maps
`[R G] -> (R/I)[G/U]` with `I` open and `U` open normal with finite quotient. -/
def groupAlgebraOpenFiniteQuotientKernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    TopologicalSpace (MonoidAlgebra R G) :=
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  TopologicalSpace.induced (groupAlgebraOpenFiniteQuotientProductMap R G) inferInstance

theorem continuous_groupAlgebraOpenFiniteQuotientProductMap_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (groupAlgebraOpenFiniteQuotientProductMap R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  exact continuous_induced_dom

theorem continuous_groupAlgebraOpenFiniteQuotientMap_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (groupAlgebraOpenFiniteQuotientMap R G K) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  change Continuous fun x : MonoidAlgebra R G =>
    groupAlgebraOpenFiniteQuotientProductMap R G x K
  exact (continuous_apply K).comp
    (continuous_groupAlgebraOpenFiniteQuotientProductMap_kernelTopology R G)

theorem groupAlgebraOpenFiniteQuotientKernel_isOpen_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    IsOpen (groupAlgebraOpenFiniteQuotientKernel R G K : Set (MonoidAlgebra R G)) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  letI : TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  haveI : DiscreteTopology (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
  change IsOpen ((groupAlgebraOpenFiniteQuotientMap R G K) ⁻¹'
    ({0} : Set (CompletedGroupAlgebraOpenFiniteQuotientStage R G K)))
  exact (isOpen_discrete ({0} : Set (CompletedGroupAlgebraOpenFiniteQuotientStage R G K))).preimage
    (continuous_groupAlgebraOpenFiniteQuotientMap_kernelTopology R G K)

theorem groupAlgebraOpenFiniteQuotientKernel_mem_nhds_zero_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    (groupAlgebraOpenFiniteQuotientKernel R G K : Set (MonoidAlgebra R G)) ∈
      𝓝 (0 : MonoidAlgebra R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  apply IsOpen.mem_nhds
    (groupAlgebraOpenFiniteQuotientKernel_isOpen_kernelTopology R G K)
  change (0 : MonoidAlgebra R G) ∈ groupAlgebraOpenFiniteQuotientKernel R G K
  rw [mem_groupAlgebraOpenFiniteQuotientKernel_iff]
  exact map_zero (groupAlgebraOpenFiniteQuotientMap R G K)

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_single
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L)
    (q : CompletedGroupAlgebraQuotient G L.2)
    (r : R ⧸ ((OrderDual.ofDual L.1).1 : Ideal R)) :
    completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual L.2) hKL.2) q)
        (Ideal.Quotient.factor
          (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
            ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1) r) := by
  exact completedGroupAlgebraFiniteQuotientTransition_single (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2) q r

@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_id
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    completedGroupAlgebraOpenFiniteQuotientTransition R G (le_rfl : K ≤ K) =
      RingHom.id (CompletedGroupAlgebraOpenFiniteQuotientStage R G K) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    rw [completedGroupAlgebraOpenFiniteQuotientTransition_single]
    simp only [map_one, Ideal.Quotient.factor_eq, RingHom.id_apply]
  · intro q
    rw [completedGroupAlgebraOpenFiniteQuotientTransition_single]
    change MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual K.2)
          (le_rfl : K.2 ≤ K.2)) q) 1 =
      MonoidAlgebra.single q 1
    rw [OpenNormalSubgroupInClass.map_id]
    simp only [MonoidHom.id_apply]

@[simp 900]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_comp
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L M : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) (hLM : L ≤ M) :
    (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL).comp
        (completedGroupAlgebraOpenFiniteQuotientTransition R G hLM) =
      completedGroupAlgebraOpenFiniteQuotientTransition R G (hKL.trans hLM) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, completedGroupAlgebraOpenFiniteQuotientTransition_single,
      completedGroupAlgebraOpenFiniteQuotientTransition_single,
      completedGroupAlgebraOpenFiniteQuotientTransition_single]
    simp only [map_one, Ideal.Quotient.factor_comp_apply]
  · intro q
    rw [RingHom.comp_apply, completedGroupAlgebraOpenFiniteQuotientTransition_single,
      completedGroupAlgebraOpenFiniteQuotientTransition_single,
      completedGroupAlgebraOpenFiniteQuotientTransition_single]
    have hmap := congrFun
      (congrArg DFunLike.coe
        (OpenNormalSubgroupInClass.map_comp
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual L.2) (W := OrderDual.ofDual M.2)
          hKL.2 hLM.2))
      q
    exact congrArg
      (fun t => MonoidAlgebra.single t
        (1 : R ⧸ ((OrderDual.ofDual K.1).1 : Ideal R)))
      hmap

theorem completedGroupAlgebraOpenFiniteQuotientTransition_surjective
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    Function.Surjective (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL) :=
  completedGroupAlgebraFiniteQuotientTransition_surjective
    (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2)
end

end CompletedGroupAlgebra
