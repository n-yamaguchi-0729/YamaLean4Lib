import CompletedGroupAlgebra.UniversalProperty.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/UniversalProperty/FiniteQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-quotient and discrete-target lifts

This module proves the finite-quotient form of the universal property: maps to finite discrete targets are determined by sufficiently deep finite stages.
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

/-- Finite-quotient construction used in Lemma 5.3.5(d): a map on one finite quotient
`G/U` extends linearly and continuously from `[[RG]]`. -/
def completedGroupAlgebraLiftOfFiniteQuotient
    (U : CompletedGroupAlgebraIndex G) (N : Type (max u v))
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N]
    [ContinuousSMul R N] (f : CompletedGroupAlgebraQuotient G U → N) :
    Carrier R G →L[R] N := by
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  exact (finiteGroupAlgebraLift R (CompletedGroupAlgebraQuotient G U) N f).comp
    (completedGroupAlgebraProjectionContinuousLinearMap R G U)

/-- The finite-quotient lift has the prescribed value on completed group-like elements. -/
@[simp]
theorem completedGroupAlgebraLiftOfFiniteQuotient_apply_of
    (U : CompletedGroupAlgebraIndex G) (N : Type (max u v))
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N]
    [ContinuousSMul R N] (f : CompletedGroupAlgebraQuotient G U → N) (g : G) :
    completedGroupAlgebraLiftOfFiniteQuotient (R := R) (G := G) U N f
        (completedGroupAlgebraOf R G g) =
      f (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) := by
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  change finiteGroupAlgebraLift R (CompletedGroupAlgebraQuotient G U) N f
      (completedGroupAlgebraProjection R G U (completedGroupAlgebraOf R G g)) =
    f (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g)
  rw [completedGroupAlgebraProjection_of]
  exact finiteGroupAlgebraLift_apply_of R (CompletedGroupAlgebraQuotient G U) N f
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g)

/-- If a continuous target map already factors through one finite quotient `G/U`, the
finite-quotient construction gives the required unique continuous linear extension. -/
theorem completedGroupAlgebra_existsUnique_lift_of_factors
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] [T2Space N]
    (U : CompletedGroupAlgebraIndex G) (f : G → N)
    (fbar : CompletedGroupAlgebraQuotient G U → N)
    (hfac : ∀ g : G,
      fbar (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) = f g) :
    ∃! F : Carrier R G →L[R] N,
      ∀ g : G, F (completedGroupAlgebraOf R G g) = f g := by
  let F := completedGroupAlgebraLiftOfFiniteQuotient (R := R) (G := G) U N fbar
  refine ⟨F, ?_, ?_⟩
  · intro g
    rw [completedGroupAlgebraLiftOfFiniteQuotient_apply_of, hfac]
  · intro K hK
    apply completedGroupAlgebraContinuousLinearMap_ext_of_basis (R := R) (G := G) hG
    intro g
    rw [completedGroupAlgebraLiftOfFiniteQuotient_apply_of, hfac, hK]

/-- A continuous map from a profinite group to a discrete space is unchanged on the cosets of
some finite open normal quotient. This is the topological factorization input in the book proof of
Lemma 5.3.5(d). -/
theorem exists_completedGroupAlgebraIndex_factor_continuous_discrete
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [TopologicalSpace N] [DiscreteTopology N]
    (f : G → N) (hf : Continuous f) :
    ∃ U : CompletedGroupAlgebraIndex G, ∃ fbar : CompletedGroupAlgebraQuotient G U → N,
      ∀ g : G,
        fbar (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) = f g := by
  letI : CompactSpace G := ProCGroups.IsProfiniteGroup.compactSpace hG
  let T : Set (G × G) := {p | f p.1 = f p.2}
  have hTopen : IsOpen T := by
    have hpair : Continuous fun p : G × G => (f p.1, f p.2) :=
      (hf.comp continuous_fst).prodMk (hf.comp continuous_snd)
    change IsOpen ((fun p : G × G => (f p.1, f p.2)) ⁻¹'
      {q : N × N | q.1 = q.2})
    exact hpair.isOpen_preimage _ (isOpen_discrete _)
  let A : Set (G × G) := {p | f p.1 = f (p.1 * p.2)}
  have hAopen : IsOpen A := by
    have hmul : Continuous fun p : G × G => (p.1, p.1 * p.2) :=
      continuous_fst.prodMk (continuous_fst.mul continuous_snd)
    change IsOpen ((fun p : G × G => (p.1, p.1 * p.2)) ⁻¹' T)
    exact hTopen.preimage hmul
  have hcontains : (Set.univ : Set G) ×ˢ ({1} : Set G) ⊆ A := by
    rintro ⟨g, u⟩ ⟨_hg, hu⟩
    change u = 1 at hu
    change f g = f (g * u)
    rw [hu, mul_one]
  rcases generalized_tube_lemma (s := (Set.univ : Set G)) isCompact_univ
      (t := ({1} : Set G)) isCompact_singleton hAopen hcontains with
    ⟨W, V, _hWopen, hVopen, hWuniv, h1V, hWV⟩
  have hVone : (1 : G) ∈ V := h1V (by simp only [Set.mem_singleton_iff])
  have hProC : IsProCGroup ProCGroups.FiniteGroupClass.allFinite G :=
    (isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG
  rcases hProC.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hVopen hVone with
    ⟨U0, hU0V⟩
  let U : CompletedGroupAlgebraIndex G := OrderDual.toDual U0
  let fbar : CompletedGroupAlgebraQuotient G U → N := Quotient.lift f (by
    intro a b hab
    have habU : a⁻¹ * b ∈ (U0.1 : Subgroup G) :=
      (QuotientGroup.leftRel_apply).1 hab
    have habV : a⁻¹ * b ∈ V := hU0V habU
    have hA : (a, a⁻¹ * b) ∈ A :=
      hWV ⟨hWuniv (Set.mem_univ a), habV⟩
    simpa [A, mul_assoc] using hA)
  refine ⟨U, fbar, ?_⟩
  intro g
  rfl

/-- Discrete-target form of Lemma 5.3.5(d): a continuous map from the profinite group `G` to a
discrete `R`-module extends uniquely to a continuous `R`-linear map out of `[[RG]]`. -/
theorem completedGroupAlgebra_existsUnique_lift_to_discreteModule
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] [DiscreteTopology N]
    (f : G → N) (hf : Continuous f) :
    ∃! F : Carrier R G →L[R] N,
      ∀ g : G, F (completedGroupAlgebraOf R G g) = f g := by
  letI : T2Space N := inferInstance
  rcases exists_completedGroupAlgebraIndex_factor_continuous_discrete
      (G := G) hG N f hf with
    ⟨U, fbar, hfac⟩
  exact completedGroupAlgebra_existsUnique_lift_of_factors (R := R) (G := G) hG N
    U f fbar hfac

/-- The chosen discrete-target extension in Lemma 5.3.5(d). -/
def completedGroupAlgebraLiftToDiscreteModule
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] [DiscreteTopology N]
    (f : G → N) (hf : Continuous f) :
    Carrier R G →L[R] N :=
  Classical.choose
    (completedGroupAlgebra_existsUnique_lift_to_discreteModule
      (R := R) (G := G) hG N f hf)

/-- The chosen discrete-target lift has the prescribed value on completed group-like elements. -/
@[simp]
theorem completedGroupAlgebraLiftToDiscreteModule_apply_of
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] [DiscreteTopology N]
    (f : G → N) (hf : Continuous f) (g : G) :
    completedGroupAlgebraLiftToDiscreteModule
        (R := R) (G := G) hG N f hf
        (completedGroupAlgebraOf R G g) = f g := by
  exact (Classical.choose_spec
    (completedGroupAlgebra_existsUnique_lift_to_discreteModule
      (R := R) (G := G) hG N f hf)).1 g
end

end CompletedGroupAlgebra
