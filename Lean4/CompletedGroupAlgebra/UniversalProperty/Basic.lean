import CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteComparison

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/UniversalProperty/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebra group-like elements

This module isolates the group-like elements and dense algebraic group-ring map that control maps out of a completed group algebra.
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

/-- The concrete inverse-limit construction satisfies the completed-group-algebra
property package. -/
theorem completedGroupAlgebra_isCompletedGroupAlgebraModel
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    IsCompletedGroupAlgebraModel R G (Carrier R G) := by
  refine ⟨hR, hG, completedGroupAlgebra_isProfiniteRing (R := R) (G := G) hR, ?_⟩
  refine ⟨completedGroupAlgebraNaturalTopology R G, ?_⟩
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  exact ⟨toCompletedGroupAlgebraRingHom R G,
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG,
    continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G)⟩

/-- The image of a group element in the completed group algebra. -/
def completedGroupAlgebraOf (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : G) : Carrier R G :=
  toCompletedGroupAlgebra R G (MonoidAlgebra.of R G g)

/-- Projection of a completed group-like element to a finite quotient stage. -/
@[simp]
theorem completedGroupAlgebraProjection_of
    (U : CompletedGroupAlgebraIndex G) (g : G) :
    completedGroupAlgebraProjection R G U (completedGroupAlgebraOf R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 := by
  rw [completedGroupAlgebraOf, completedGroupAlgebraProjection_toCompletedGroupAlgebra,
    completedGroupAlgebraStageMap_of]

/-- The completed group-like element attached to `1` is the unit. -/
@[simp]
theorem completedGroupAlgebraOf_one :
    completedGroupAlgebraOf R G 1 = (1 : Carrier R G) := by
  apply (completedGroupAlgebraSystem R G).ext
  intro U
  change completedGroupAlgebraProjection R G U (completedGroupAlgebraOf R G 1) =
    completedGroupAlgebraProjection R G U (1 : Carrier R G)
  rw [completedGroupAlgebraProjection_of, completedGroupAlgebraProjection_one]
  change MonoidAlgebra.single
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U 1) (1 : R) = 1
  rfl

/-- Completed group-like elements multiply according to the group law. -/
@[simp]
theorem completedGroupAlgebraOf_mul (g h : G) :
    completedGroupAlgebraOf R G (g * h) =
      completedGroupAlgebraOf R G g * completedGroupAlgebraOf R G h := by
  apply (completedGroupAlgebraSystem R G).ext
  intro U
  change completedGroupAlgebraProjection R G U (completedGroupAlgebraOf R G (g * h)) =
    completedGroupAlgebraProjection R G U (completedGroupAlgebraOf R G g * completedGroupAlgebraOf R G h)
  rw [completedGroupAlgebraProjection_of, completedGroupAlgebraProjection_mul,
    completedGroupAlgebraProjection_of, completedGroupAlgebraProjection_of]
  change MonoidAlgebra.single
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U (g * h)) (1 : R) =
    MonoidAlgebra.single
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 *
    MonoidAlgebra.single
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U h) 1
  simp only [map_mul, MonoidAlgebra.single_mul_single, mul_one]

/-- The finite-stage group-like map `G → R[G/U]` is continuous. -/
theorem continuous_completedGroupAlgebraStageMap_of
    (U : CompletedGroupAlgebraIndex G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      (completedGroupAlgebraSystem R G).topologicalSpace U
    Continuous fun g : G => completedGroupAlgebraStageMap R G U (MonoidAlgebra.of R G g) := by
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  letI : DiscreteTopology (CompletedGroupAlgebraQuotient G U) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
  have hbasis :
      Continuous fun q : CompletedGroupAlgebraQuotient G U =>
        (MonoidAlgebra.of R (CompletedGroupAlgebraQuotient G U) q :
          CompletedGroupAlgebraStage R G U) :=
    continuous_of_discreteTopology
  have hproj :
      Continuous fun g : G =>
        openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g := by
    change Continuous
      (QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G))
    exact continuous_quotient_mk'
  simpa [MonoidAlgebra.of, completedGroupAlgebraStageMap_single] using hbasis.comp hproj

/-- The completed group-like map `G → [[RG]]` is continuous. -/
theorem continuous_completedGroupAlgebraOf :
    Continuous (completedGroupAlgebraOf R G) := by
  letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
  have hval : Continuous fun g : G =>
      fun U : CompletedGroupAlgebraIndex G =>
        (show CompletedGroupAlgebraStage R G U from (completedGroupAlgebraOf R G g).1 U) := by
    change Continuous fun g : G =>
      fun U : CompletedGroupAlgebraIndex G =>
        completedGroupAlgebraStageMap R G U (MonoidAlgebra.of R G g)
    apply continuous_pi
    intro U
    exact continuous_completedGroupAlgebraStageMap_of (R := R) (G := G) U
  exact Continuous.subtype_mk hval fun g => (completedGroupAlgebraOf R G g).2

/-- The dense abstract group-algebra map lands in the span of the completed group-like
elements. -/
theorem toCompletedGroupAlgebraRingHom_mem_span_completedGroupAlgebraOf
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraRingHom R G x ∈
      Submodule.span R (Set.range (completedGroupAlgebraOf R G)) := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [show toCompletedGroupAlgebraRingHom R G (0 : MonoidAlgebra R G) =
          (0 : Carrier R G) by
        exact map_zero (toCompletedGroupAlgebraRingHom R G)]
      exact Submodule.zero_mem _
  | single_add g r x _ _ ih =>
      rw [map_add]
      refine Submodule.add_mem _ ?_ ih
      have hsingle :
          toCompletedGroupAlgebraRingHom R G (MonoidAlgebra.single g r) =
            r • completedGroupAlgebraOf R G g := by
        rw [show MonoidAlgebra.single g r =
            r • MonoidAlgebra.of R G g by
          simp only [MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
        change toCompletedGroupAlgebra R G (r • MonoidAlgebra.of R G g) =
          r • completedGroupAlgebraOf R G g
        rw [toCompletedGroupAlgebra_smul]
        rfl
      rw [hsingle]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨g, rfl⟩)

/-- The completed group-like elements topologically generate `[[RG]]` as an `R`-module. -/
theorem completedGroupAlgebraOf_dense_span (hG : ProCGroups.IsProfiniteGroup G) :
    closure (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
      Set (Carrier R G)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  have hy :
      y ∈ closure (Set.range (toCompletedGroupAlgebraRingHom R G)) := by
    rw [(denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG).closure_range]
    exact Set.mem_univ y
  exact closure_mono (by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact toCompletedGroupAlgebraRingHom_mem_span_completedGroupAlgebraOf
      (R := R) (G := G) x) hy

/-- The structural inputs for Lemma 5.3.5(d)'s free profinite-module statement; the full
continuous-linear universal property is proved below. -/
theorem completedGroupAlgebraOf_freeProfiniteModule_prerequisites
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    IsProfiniteRing R ∧ IsProfiniteModule R (Carrier R G) ∧
      Continuous (completedGroupAlgebraOf R G) ∧
        closure (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
          Set (Carrier R G)) = Set.univ := by
  exact ⟨hR, completedGroupAlgebra_isProfiniteModule (R := R) (G := G) hR,
    continuous_completedGroupAlgebraOf (R := R) (G := G),
    completedGroupAlgebraOf_dense_span (R := R) (G := G) hG⟩

/-- Uniqueness half of Lemma 5.3.5(d)'s universal property: a continuous linear map out of
`[[RG]]` is determined by its values on the completed group-like elements. -/
theorem completedGroupAlgebraContinuousLinearMap_ext_of_basis
    (hG : ProCGroups.IsProfiniteGroup G)
    {N : Type (max u v)} [AddCommGroup N] [TopologicalSpace N] [Module R N] [T2Space N]
    {F K : Carrier R G →L[R] N}
    (hbasis : ∀ g : G, F (completedGroupAlgebraOf R G g) =
      K (completedGroupAlgebraOf R G g)) :
    F = K := by
  apply ContinuousLinearMap.ext
  intro x
  have hclosed : IsClosed {x : Carrier R G | F x = K x} :=
    isClosed_eq F.continuous K.continuous
  have hspan :
      (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
        Set (Carrier R G)) ⊆
        {x : Carrier R G | F x = K x} := by
    intro y hy
    exact Submodule.span_induction
      (fun z hz => by
        rcases hz with ⟨g, rfl⟩
        exact hbasis g)
      (by simp only [Set.mem_setOf_eq, map_zero])
      (fun z w _ _ hz hw => by
        change F (z + w) = K (z + w)
        rw [map_add, map_add, hz, hw])
      (fun r z _ hz => by
        change F (r • z) = K (r • z)
        rw [map_smul, map_smul, hz])
      hy
  have hx :
      x ∈ closure (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
        Set (Carrier R G)) := by
    rw [completedGroupAlgebraOf_dense_span (R := R) (G := G) hG]
    exact Set.mem_univ x
  exact hclosed.closure_subset_iff.2 hspan hx
end

end CompletedGroupAlgebra
