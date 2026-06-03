import CompletedGroupAlgebra.OpenFiniteQuotientTopology.CanonicalMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/FiniteQuotients.lean
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

/-- An open coefficient ideal gives a continuous quotient map when the quotient is equipped
with the discrete topology. This is the coefficient-side continuity used in RZ §5.3. -/
theorem continuous_idealQuotient_mk_openIdeal_discrete
    (I : Ideal R) (hI : IsOpen (I : Set R)) :
    letI : TopologicalSpace (R ⧸ I) := ⊥
    Continuous (Ideal.Quotient.mk I) := by
  letI : TopologicalSpace (R ⧸ I) := ⊥
  haveI : DiscreteTopology (R ⧸ I) := ⟨rfl⟩
  rw [continuous_discrete_rng]
  intro b
  rcases Ideal.Quotient.mk_surjective (I := I) b with ⟨a, rfl⟩
  have hpre :
      (Ideal.Quotient.mk I) ⁻¹' ({Ideal.Quotient.mk I a} : Set (R ⧸ I)) =
        (fun x : R => x - a) ⁻¹' (I : Set R) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Ideal.Quotient.eq, SetLike.mem_coe]
  rw [hpre]
  exact hI.preimage (continuous_id.sub continuous_const)

omit G [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [IsTopologicalRing R] in
/-- Finite-stage group algebras are functorial in the coefficient ring by continuous maps. -/
theorem finiteGroupAlgebra_mapRangeRingHom_continuous
    (S : Type u) [CommRing S] [TopologicalSpace S]
    (Q : Type v) [Group Q] [Finite Q]
    (f : R →+* S) (hf : Continuous f) :
    letI : TopologicalSpace (MonoidAlgebra R Q) := finiteGroupAlgebraTopology R Q
    letI : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
    Continuous (MonoidAlgebra.mapRangeRingHom Q f :
      MonoidAlgebra R Q → MonoidAlgebra S Q) := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : TopologicalSpace (MonoidAlgebra R Q) := finiteGroupAlgebraTopology R Q
  letI : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
  let eR : MonoidAlgebra R Q ≃ (Q → R) := Finsupp.equivFunOnFinite
  let eS : MonoidAlgebra S Q ≃ (Q → S) := Finsupp.equivFunOnFinite
  have heS : Topology.IsInducing (eS : MonoidAlgebra S Q → Q → S) :=
    Topology.IsInducing.induced eS
  have hcoordR : ∀ q : Q, Continuous fun x : MonoidAlgebra R Q => x q := by
    intro q
    simpa [eR] using
      (continuous_apply q).comp
        (continuous_induced_dom : Continuous (eR : MonoidAlgebra R Q → Q → R))
  rw [heS.continuous_iff]
  apply continuous_pi
  intro q
  change Continuous fun x : MonoidAlgebra R Q =>
    (MonoidAlgebra.mapRangeRingHom Q f x : MonoidAlgebra S Q) q
  simpa [MonoidAlgebra.mapRangeRingHom_apply] using hf.comp (hcoordR q)

omit R G [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If the coefficient ring is discrete, then the finite-stage group algebra has the discrete
finite-product topology. -/
theorem finiteGroupAlgebraTopology_discrete_of_discrete_coeff
    (S : Type u) [CommRing S] [TopologicalSpace S] [DiscreteTopology S]
    (Q : Type v) [Group Q] [Finite Q] :
    letI : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
    DiscreteTopology (MonoidAlgebra S Q) := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
  let e : MonoidAlgebra S Q ≃ (Q → S) := Finsupp.equivFunOnFinite
  haveI : DiscreteTopology (Q → S) := inferInstance
  exact DiscreteTopology.of_continuous_injective
    (continuous_induced_dom : Continuous (e : MonoidAlgebra S Q → Q → S)) e.injective

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The RZ §5.3 finite quotient `[(R/I)(G/U)]`, with both coefficient and group quotient
applied, used in the kernel-neighborhood topology. -/
abbrev CompletedGroupAlgebraCoeffQuotientStage
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Type (max u v) :=
  MonoidAlgebra (R ⧸ I) (CompletedGroupAlgebraQuotient G U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The coefficient quotient map `R[G/U] -> (R/I)[G/U]`. -/
def completedGroupAlgebraStageCoeffQuotientMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraStage R G U →+*
      CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  MonoidAlgebra.mapRangeRingHom (CompletedGroupAlgebraQuotient G U)
    (Ideal.Quotient.mk I)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraStageCoeffQuotientMap_single
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G)
    (q : CompletedGroupAlgebraQuotient G U) (r : R) :
    completedGroupAlgebraStageCoeffQuotientMap R G I U (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (Ideal.Quotient.mk I r) := by
  exact MonoidAlgebra.mapRangeRingHom_single (Ideal.Quotient.mk I) q r

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageCoeffQuotientMap_surjective
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (completedGroupAlgebraStageCoeffQuotientMap R G I U) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero (completedGroupAlgebraStageCoeffQuotientMap R G I U)⟩
  | single_add q r x _ _ ih =>
      rcases Ideal.Quotient.mk_surjective (I := I) r with ⟨a, ha⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single q a : CompletedGroupAlgebraStage R G U) + y, ?_⟩
      rw [map_add, completedGroupAlgebraStageCoeffQuotientMap_single, hy, ha]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The RZ §5.3 quotient map `[R G] -> [(R/I)(G/U)]`. -/
def groupAlgebraFiniteQuotientMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  (completedGroupAlgebraStageCoeffQuotientMap R G I U).comp
    (completedGroupAlgebraStageMap R G U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem groupAlgebraFiniteQuotientMap_single
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (g : G) (r : R) :
    groupAlgebraFiniteQuotientMap R G I U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g)
        (Ideal.Quotient.mk I r) := by
  rw [groupAlgebraFiniteQuotientMap, RingHom.comp_apply,
    completedGroupAlgebraStageMap_single, completedGroupAlgebraStageCoeffQuotientMap_single]

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem groupAlgebraFiniteQuotientMap_of
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (g : G) :
    groupAlgebraFiniteQuotientMap R G I U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.of (R ⧸ I) (CompletedGroupAlgebraQuotient G U)
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) := by
  simp only [MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk,
  groupAlgebraFiniteQuotientMap_single (R := R) (G := G) I U g (1 : R), map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The quotient map `[R G] -> [(R/I)(G/U)]` factors equally as coefficient quotient followed
by group quotient, or group quotient followed by coefficient quotient. -/
theorem groupAlgebraFiniteQuotientMap_eq_mapDomain_comp_mapRange
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    groupAlgebraFiniteQuotientMap R G I U =
      (MonoidAlgebra.mapDomainRingHom (R ⧸ I)
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)).comp
        (MonoidAlgebra.mapRangeRingHom G (Ideal.Quotient.mk I)) := by
  simpa [groupAlgebraFiniteQuotientMap, completedGroupAlgebraStageCoeffQuotientMap,
    completedGroupAlgebraStageMap] using
      (MonoidAlgebra.mapRangeRingHom_comp_mapDomainRingHom
        (f := Ideal.Quotient.mk I)
        (g := openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U))

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem groupAlgebraFiniteQuotientMap_surjective
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (groupAlgebraFiniteQuotientMap R G I U) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero (groupAlgebraFiniteQuotientMap R G I U)⟩
  | single_add q r x _ _ ih =>
      rcases openNormalSubgroupInClassProj_surjective
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U q with
        ⟨g, hg⟩
      rcases Ideal.Quotient.mk_surjective (I := I) r with ⟨a, ha⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single g a : MonoidAlgebra R G) + y, ?_⟩
      rw [map_add, groupAlgebraFiniteQuotientMap_single, hy, hg, ha]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The kernels used in Ribes--Zalesskii's natural topology on `[R G]`; for the
kernel-neighborhood topology this family is restricted to open ideals `I` and open normal
subgroups `U`. -/
def groupAlgebraFiniteQuotientKernel
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Ideal (MonoidAlgebra R G) :=
  RingHom.ker (groupAlgebraFiniteQuotientMap R G I U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem mem_groupAlgebraFiniteQuotientKernel_iff
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) :
    x ∈ groupAlgebraFiniteQuotientKernel R G I U ↔
      groupAlgebraFiniteQuotientMap R G I U x = 0 :=
  Iff.rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem groupAlgebraFiniteQuotientKernel_eq_comap
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    groupAlgebraFiniteQuotientKernel R G I U =
      Ideal.comap (completedGroupAlgebraStageMap R G U)
        (RingHom.ker (completedGroupAlgebraStageCoeffQuotientMap R G I U)) :=
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Coefficient transition `(R/I)[G/U] -> (R/J)[G/U]` induced by an inclusion `I ≤ J`. -/
def completedGroupAlgebraCoeffQuotientTransition
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {I J : Ideal R} (hIJ : I ≤ J)
    (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCoeffQuotientStage R G I U →+*
      CompletedGroupAlgebraCoeffQuotientStage R G J U :=
  MonoidAlgebra.mapRangeRingHom (CompletedGroupAlgebraQuotient G U)
    (Ideal.Quotient.factor hIJ)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraCoeffQuotientTransition_single
    {I J : Ideal R} (hIJ : I ≤ J) (U : CompletedGroupAlgebraIndex G)
    (q : CompletedGroupAlgebraQuotient G U) (r : R ⧸ I) :
    completedGroupAlgebraCoeffQuotientTransition R G hIJ U (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (Ideal.Quotient.factor hIJ r) := by
  exact MonoidAlgebra.mapRangeRingHom_single (Ideal.Quotient.factor hIJ) q r

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraCoeffQuotientTransition_comp_stageCoeffQuotientMap
    {I J : Ideal R} (hIJ : I ≤ J) (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraCoeffQuotientTransition R G hIJ U).comp
        (completedGroupAlgebraStageCoeffQuotientMap R G I U) =
      completedGroupAlgebraStageCoeffQuotientMap R G J U := by
  rw [completedGroupAlgebraCoeffQuotientTransition,
    completedGroupAlgebraStageCoeffQuotientMap, completedGroupAlgebraStageCoeffQuotientMap,
    ← MonoidAlgebra.mapRangeRingHom_comp]
  simp only [Ideal.Quotient.factor_comp_mk]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraCoeffQuotientTransition_surjective
    {I J : Ideal R} (hIJ : I ≤ J) (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (completedGroupAlgebraCoeffQuotientTransition R G hIJ U) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero (completedGroupAlgebraCoeffQuotientTransition R G hIJ U)⟩
  | single_add q r x _ _ ih =>
      rcases Ideal.Quotient.factor_surjective hIJ r with ⟨a, ha⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single q a :
        CompletedGroupAlgebraCoeffQuotientStage R G I U) + y, ?_⟩
      rw [map_add, completedGroupAlgebraCoeffQuotientTransition_single, hy, ha]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Group-quotient transition `(R/I)[G/V] -> (R/I)[G/U]` induced by `U ≤ V`. -/
def completedGroupAlgebraCoeffQuotientGroupTransition
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Ideal R) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    CompletedGroupAlgebraCoeffQuotientStage R G I V →+*
      CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  MonoidAlgebra.mapDomainRingHom (R ⧸ I)
    (OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraCoeffQuotientGroupTransition_single
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotient G V) (r : R ⧸ I) :
    completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r := by
  classical
  simp only [completedGroupAlgebraCoeffQuotientGroupTransition, MonoidAlgebra.single,
  MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraCoeffQuotientGroupTransition_comp_stageCoeffQuotientMap
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV).comp
        (completedGroupAlgebraStageCoeffQuotientMap R G I V) =
      (completedGroupAlgebraStageCoeffQuotientMap R G I U).comp
        (completedGroupAlgebraTransition R G hUV) := by
  rw [completedGroupAlgebraCoeffQuotientGroupTransition,
    completedGroupAlgebraStageCoeffQuotientMap, completedGroupAlgebraStageCoeffQuotientMap,
    completedGroupAlgebraTransition]
  exact (MonoidAlgebra.mapRangeRingHom_comp_mapDomainRingHom
    (f := Ideal.Quotient.mk I)
    (g := OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)).symm

omit [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalGroup G] in
theorem completedGroupAlgebraQuotientTransition_surjective
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    Function.Surjective
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)) q with
    ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
    ((((OrderDual.ofDual V).1 : OpenNormalSubgroup G) : Subgroup G)) g, rfl⟩

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraCoeffQuotientGroupTransition_surjective
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    Function.Surjective (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV)⟩
  | single_add q r x _ _ ih =>
      rcases completedGroupAlgebraQuotientTransition_surjective
          (G := G) hUV q with
        ⟨p, hp⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single p r :
        CompletedGroupAlgebraCoeffQuotientStage R G I V) + y, ?_⟩
      rw [map_add, completedGroupAlgebraCoeffQuotientGroupTransition_single, hy, hp]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The combined transition `(R/I)[G/V] -> (R/J)[G/U]`. -/
def completedGroupAlgebraFiniteQuotientTransition
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {I J : Ideal R} (hIJ : I ≤ J)
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    CompletedGroupAlgebraCoeffQuotientStage R G I V →+*
      CompletedGroupAlgebraCoeffQuotientStage R G J U :=
  (completedGroupAlgebraCoeffQuotientTransition R G hIJ U).comp
    (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraFiniteQuotientTransition_single
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) (q : CompletedGroupAlgebraQuotient G V) (r : R ⧸ I) :
    completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q)
        (Ideal.Quotient.factor hIJ r) := by
  rw [completedGroupAlgebraFiniteQuotientTransition, RingHom.comp_apply,
    completedGroupAlgebraCoeffQuotientGroupTransition_single,
    completedGroupAlgebraCoeffQuotientTransition_single]

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraCoeffQuotientGroupTransition_comp_finiteQuotientMap
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV).comp
        (groupAlgebraFiniteQuotientMap R G I V) =
      groupAlgebraFiniteQuotientMap R G I U := by
  rw [groupAlgebraFiniteQuotientMap_eq_mapDomain_comp_mapRange,
    groupAlgebraFiniteQuotientMap_eq_mapDomain_comp_mapRange]
  rw [completedGroupAlgebraCoeffQuotientGroupTransition, ← RingHom.comp_assoc,
    ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraFiniteQuotientTransition_comp_finiteQuotientMap
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    (completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV).comp
        (groupAlgebraFiniteQuotientMap R G I V) =
      groupAlgebraFiniteQuotientMap R G J U := by
  rw [completedGroupAlgebraFiniteQuotientTransition, RingHom.comp_assoc,
    completedGroupAlgebraCoeffQuotientGroupTransition_comp_finiteQuotientMap]
  rw [groupAlgebraFiniteQuotientMap, groupAlgebraFiniteQuotientMap]
  rw [← RingHom.comp_assoc,
    completedGroupAlgebraCoeffQuotientTransition_comp_stageCoeffQuotientMap]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraFiniteQuotientTransition_surjective
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    Function.Surjective (completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV) := by
  intro x
  rcases completedGroupAlgebraCoeffQuotientTransition_surjective
      (R := R) (G := G) hIJ U x with
    ⟨y, hy⟩
  rcases completedGroupAlgebraCoeffQuotientGroupTransition_surjective
      (R := R) (G := G) I hUV y with
    ⟨z, hz⟩
  exact ⟨z, by rw [completedGroupAlgebraFiniteQuotientTransition, RingHom.comp_apply, hz, hy]⟩

/-- The corresponding projection from the completed group algebra to `[(R/I)(G/U)]`. -/
def completedGroupAlgebraFiniteQuotientProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Carrier R G →+*
      CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  (completedGroupAlgebraStageCoeffQuotientMap R G I U).comp
    (completedGroupAlgebraProjectionRingHom R G U)

@[simp]
theorem completedGroupAlgebraFiniteQuotientProjection_toCompletedGroupAlgebra
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraFiniteQuotientProjection R G I U).comp
        (toCompletedGroupAlgebraRingHom R G) =
      groupAlgebraFiniteQuotientMap R G I U := by
  apply RingHom.ext
  intro x
  rfl

@[simp]
theorem completedGroupAlgebraFiniteQuotientProjection_apply_toCompletedGroupAlgebra
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) :
    completedGroupAlgebraFiniteQuotientProjection R G I U
        (toCompletedGroupAlgebra R G x) =
      groupAlgebraFiniteQuotientMap R G I U x :=
  rfl

@[simp 900]
theorem completedGroupAlgebraFiniteQuotientTransition_comp_projection
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    (completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV).comp
        (completedGroupAlgebraFiniteQuotientProjection R G I V) =
      completedGroupAlgebraFiniteQuotientProjection R G J U := by
  apply RingHom.ext
  intro x
  calc
    completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV
        (completedGroupAlgebraFiniteQuotientProjection R G I V x)
        =
      completedGroupAlgebraCoeffQuotientTransition R G hIJ U
        (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV
          (completedGroupAlgebraStageCoeffQuotientMap R G I V
            (completedGroupAlgebraProjection R G V x))) := rfl
    _ =
      completedGroupAlgebraCoeffQuotientTransition R G hIJ U
        (completedGroupAlgebraStageCoeffQuotientMap R G I U
          (completedGroupAlgebraTransition R G hUV
            (completedGroupAlgebraProjection R G V x))) := by
        have hstage := congrFun
          (congrArg DFunLike.coe
            (completedGroupAlgebraCoeffQuotientGroupTransition_comp_stageCoeffQuotientMap
              (R := R) (G := G) I (U := U) (V := V) hUV))
          (completedGroupAlgebraProjection R G V x)
        exact congrArg (completedGroupAlgebraCoeffQuotientTransition R G hIJ U) hstage
    _ =
      completedGroupAlgebraCoeffQuotientTransition R G hIJ U
        (completedGroupAlgebraStageCoeffQuotientMap R G I U
          (completedGroupAlgebraProjection R G U x)) := by
        rw [completedGroupAlgebraProjection_compatible (R := R) (G := G) x hUV]
    _ =
      completedGroupAlgebraStageCoeffQuotientMap R G J U
        (completedGroupAlgebraProjection R G U x) := by
        exact congrFun
          (congrArg DFunLike.coe
            (completedGroupAlgebraCoeffQuotientTransition_comp_stageCoeffQuotientMap
              (R := R) (G := G) (I := I) (J := J) hIJ U))
          (completedGroupAlgebraProjection R G U x)
    _ = completedGroupAlgebraFiniteQuotientProjection R G J U x := rfl
end

end CompletedGroupAlgebra
