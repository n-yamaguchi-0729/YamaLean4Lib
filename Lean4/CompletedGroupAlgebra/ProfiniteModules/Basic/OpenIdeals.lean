import CompletedGroupAlgebra.ProfiniteModules.Basic.Generators

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/ProfiniteModules/Basic/OpenIdeals.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Open ideals in profinite rings
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- Open ideals form a neighborhood basis at zero. -/
def HasOpenIdealBasisAtZero (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] : Prop :=
  ∀ U ∈ 𝓝 (0 : Λ), ∃ I : Ideal Λ, IsOpen (I : Set Λ) ∧ (I : Set Λ) ⊆ U

/-- Open ideals with finite quotient form a neighborhood basis at zero. -/
def HasFiniteOpenIdealQuotientBasis (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] : Prop :=
  ∀ U ∈ 𝓝 (0 : Λ), ∃ I : Ideal Λ,
    IsOpen (I : Set Λ) ∧ (I : Set Λ) ⊆ U ∧ Nonempty (Fintype (Λ ⧸ I))

/-- The finite-quotient characterization of a profinite ring. -/
def IsInverseLimitOfFiniteRingQuotients (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] : Prop :=
  HasFiniteOpenIdealQuotientBasis Λ

/-- An open ideal of a compact topological ring has finite additive quotient. -/
theorem finite_quotient_of_openIdeal
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ)
    (I : Ideal Λ) (hI : IsOpen (I : Set Λ)) :
    Nonempty (Fintype (Λ ⧸ I)) := by
  letI : IsTopologicalRing Λ := hΛ.1
  letI : ContinuousAdd Λ := inferInstance
  letI : CompactSpace Λ := hΛ.2.1
  haveI : Finite (Λ ⧸ I) :=
    AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup hI
  exact ⟨Fintype.ofFinite (Λ ⧸ I)⟩

/-- The quotient by an open ideal is a discrete module over the original ring. -/
theorem quotient_openIdeal_isDiscreteModule
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ)
    (I : Ideal Λ) (hI : IsOpen (I : Set Λ)) :
    IsDiscreteModule Λ (Λ ⧸ I) := by
  letI : IsTopologicalRing Λ := hΛ.1
  letI : IsTopologicalAddGroup Λ := inferInstance
  letI : ContinuousAdd Λ := inferInstance
  letI : ContinuousSMul Λ Λ := inferInstance
  haveI : DiscreteTopology (Λ ⧸ I) :=
    QuotientAddGroup.discreteTopology (N := I.toAddSubgroup) hI
  exact ⟨⟨hΛ.1, inferInstance, inferInstance⟩, inferInstance⟩

/-- Open ideal quotients are finite discrete modules over the original ring. -/
theorem quotient_openIdeal_finiteDiscreteModule
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ)
    (I : Ideal Λ) (hI : IsOpen (I : Set Λ)) :
    IsDiscreteModule Λ (Λ ⧸ I) ∧ Nonempty (Fintype (Λ ⧸ I)) :=
  ⟨quotient_openIdeal_isDiscreteModule Λ hΛ I hI,
    finite_quotient_of_openIdeal Λ hΛ I hI⟩

/-- Proposition 5.1.2(d/e), linear-topology interface: a profinite ring whose topology is linear
has a fundamental system of open ideals with finite quotient. -/
theorem profiniteRing_hasFiniteOpenIdealQuotientBasis_of_linearTopology
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsLinearTopology Λ Λ]
    (hΛ : IsProfiniteRing Λ) :
    HasFiniteOpenIdealQuotientBasis Λ := by
  letI : IsTopologicalRing Λ := hΛ.1
  letI : ContinuousAdd Λ := inferInstance
  intro U hU
  rcases ((IsLinearTopology.hasBasis_open_ideal).mem_iff.mp hU) with
    ⟨I, hIopen, hIU⟩
  exact ⟨I, hIopen, hIU, finite_quotient_of_openIdeal Λ hΛ I hIopen⟩

/-- Proposition 5.1.2(e), inverse-limit finite-ring-quotient formulation under the same
linear-topology hypothesis. -/
theorem profiniteRing_isInverseLimitOfFiniteRingQuotients_of_linearTopology
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsLinearTopology Λ Λ]
    (hΛ : IsProfiniteRing Λ) :
    IsInverseLimitOfFiniteRingQuotients Λ :=
  profiniteRing_hasFiniteOpenIdealQuotientBasis_of_linearTopology Λ hΛ

/-- A profinite ring is a profinite module over itself by left multiplication. -/
theorem profiniteRing_self_isProfiniteModule
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ) :
    IsProfiniteModule Λ Λ := by
  letI : IsTopologicalRing Λ := hΛ.1
  have hsmul : ContinuousSMul Λ Λ :=
    ContinuousSMul.mk (by simpa [smul_eq_mul] using continuous_mul)
  exact ⟨hΛ, inferInstance, hsmul, hΛ.2.1, hΛ.2.2.1, hΛ.2.2.2⟩

/-- Proposition 5.1.2(d/e), linear-topology part for profinite rings. -/
theorem profiniteRing_isLinearTopology
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ) :
    IsLinearTopology Λ Λ := by
  exact profiniteModule_isLinearTopology Λ Λ (profiniteRing_self_isProfiniteModule Λ hΛ)

/-- Proposition 5.1.2(d/e): a profinite ring has a fundamental system of open ideals with finite
quotient. -/
theorem profiniteRing_hasFiniteOpenIdealQuotientBasis
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ) :
    HasFiniteOpenIdealQuotientBasis Λ := by
  letI : IsLinearTopology Λ Λ := profiniteRing_isLinearTopology Λ hΛ
  exact profiniteRing_hasFiniteOpenIdealQuotientBasis_of_linearTopology Λ hΛ

/-- Proposition 5.1.2(d): a profinite ring has a basis of open ideals at zero. -/
theorem profiniteRing_hasOpenIdealBasisAtZero
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] (hΛ : IsProfiniteRing Λ) :
    HasOpenIdealBasisAtZero Λ := by
  intro U hU
  rcases profiniteRing_hasFiniteOpenIdealQuotientBasis Λ hΛ U hU with
    ⟨I, hIopen, hIU, _hfin⟩
  exact ⟨I, hIopen, hIU⟩

end CompletedGroupAlgebra
