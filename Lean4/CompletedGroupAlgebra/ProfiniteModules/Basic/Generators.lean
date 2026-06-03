import CompletedGroupAlgebra.ProfiniteModules.Basic.FiniteQuotients
import ProCGroups.Generation.QuotientGeneratorConvergingPairs

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/ProfiniteModules/Basic/Generators.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Generating sets converging to zero
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- A subset converges to zero in the book's "all but finitely many elements" sense. -/
def SetConvergesToZero {M : Type v} [TopologicalSpace M] [Zero M] (S : Set M) : Prop :=
  ∀ U ∈ 𝓝 (0 : M), (S \ U).Finite

/-- A map from an arbitrary index type converges to zero along the cofinite filter. This is the
map-level version used in Lemma 5.2.5(b). -/
def MapConvergesToZero {S : Type u} {M : Type v} [TopologicalSpace M] [Zero M]
    (f : S → M) : Prop :=
  Filter.Tendsto f Filter.cofinite (𝓝 (0 : M))

/-- A map converging to zero has image set converging to zero. -/
theorem MapConvergesToZero.setConvergesToZero_range
    {S : Type u} {M : Type v} [TopologicalSpace M] [Zero M] {f : S → M}
    (hf : MapConvergesToZero f) :
    SetConvergesToZero (Set.range f) := by
  intro U hU
  have hpre : {s : S | f s ∉ U}.Finite := by
    have hmem : {s : S | f s ∈ U} ∈ (Filter.cofinite : Filter S) := hf hU
    simpa [Filter.mem_cofinite, Set.compl_setOf] using hmem
  exact (hpre.image f).subset (by
    rintro y ⟨⟨s, rfl⟩, hsU⟩
    exact ⟨s, hsU, rfl⟩)

/-- An injective parametrization of a set converging to zero is a map converging to zero. -/
theorem SetConvergesToZero.mapConvergesToZero_of_injective
    {S : Type u} {M : Type v} [TopologicalSpace M] [Zero M] {f : S → M}
    (hfconv : SetConvergesToZero (Set.range f)) (hfinj : Function.Injective f) :
    MapConvergesToZero f := by
  intro U hU
  have hbad : ({s : S | f s ∉ U} : Set S).Finite := by
    have hpre :
        ({s : S | f s ∉ U} : Set S) = f ⁻¹' (Set.range f \ U) := by
      ext s
      simp only [Set.mem_setOf_eq, Set.preimage_diff, Set.preimage_range, Set.mem_diff, Set.mem_univ,
  Set.mem_preimage, true_and]
    rw [hpre]
    exact Set.Finite.preimage (f := f) (s := Set.range f \ U) hfinj.injOn
      (hfconv U hU)
  simpa [Filter.mem_cofinite, Set.compl_setOf] using hbad

/-- The inclusion of a set converging to zero, viewed as a parametrized map, converges to zero. -/
theorem SetConvergesToZero.subtype_val
    {M : Type v} [TopologicalSpace M] [Zero M] {S : Set M}
    (hS : SetConvergesToZero S) :
    MapConvergesToZero (fun s : S => (s : M)) := by
  have hrange : Set.range (fun s : S => (s : M)) = S := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hRangeConv : SetConvergesToZero (Set.range fun s : S => (s : M)) := by
    simpa [hrange] using hS
  exact hRangeConv.mapConvergesToZero_of_injective Subtype.val_injective

/-- A map from a discrete set converges to zero iff its zero-extension to the one-point
compactification is continuous. -/
theorem continuous_onePoint_zero_extension_iff_mapConvergesToZero
    {S : Type u} {M : Type v} [TopologicalSpace S] [DiscreteTopology S]
    [TopologicalSpace M] [Zero M] (f : S → M) :
    Continuous (fun x : OnePoint S => x.elim 0 f) ↔ MapConvergesToZero f := by
  rw [OnePoint.continuous_iff_from_discrete]
  rfl

/-- Finite subsets converge to zero in the book's "all but finitely many elements" sense. -/
theorem finite_setConvergesToZero
    {M : Type v} [TopologicalSpace M] [Zero M] {S : Set M} (hS : S.Finite) :
    SetConvergesToZero S := by
  intro U _hU
  exact hS.subset Set.diff_subset

/-- A set of topological module generators converging to zero. -/
def HasGeneratingSetConvergingToZero (Λ : Type u) (M : Type v) [Ring Λ]
    [TopologicalSpace M] [AddCommGroup M] [Module Λ M] : Prop :=
  ∃ S : Set M, closure (Submodule.span Λ S : Set M) = Set.univ ∧ SetConvergesToZero S

/-- A finite dense generating set is a generating set converging to zero. This gives the
finite-generated special case of Lemma 5.1.1(c). -/
theorem finiteGeneratingSet_convergesToZero
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M] [AddCommGroup M]
    [Module Λ M] {S : Set M}
    (hgen : closure (Submodule.span Λ S : Set M) = Set.univ) (hS : S.Finite) :
    HasGeneratingSetConvergingToZero Λ M := by
  exact ⟨S, hgen, finite_setConvergesToZero hS⟩

/-- A dense additive generating set is also a dense module generating set. -/
theorem hasGeneratingSetConvergingToZero_of_dense_addSubgroup
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M] [AddCommGroup M]
    [Module Λ M] {S : Set M}
    (hspan : closure (((AddSubgroup.closure S : AddSubgroup M) : Set M)) = Set.univ)
    (hconv : SetConvergesToZero S) :
    HasGeneratingSetConvergingToZero Λ M := by
  refine ⟨S, ?_, hconv⟩
  have hsubset : ((AddSubgroup.closure S : AddSubgroup M) : Set M) ⊆
      ((Submodule.span Λ S : Submodule Λ M) : Set M) := by
    intro x hx
    have hle : AddSubgroup.closure S ≤ (Submodule.span Λ S).toAddSubgroup :=
      (AddSubgroup.closure_le (K := (Submodule.span Λ S).toAddSubgroup)).2
        fun y hy => Submodule.subset_span hy
    exact hle hx
  have hclosure :
      closure (((AddSubgroup.closure S : AddSubgroup M) : Set M)) ⊆
        closure (((Submodule.span Λ S : Submodule Λ M) : Set M)) :=
    closure_mono hsubset
  exact Set.eq_univ_of_univ_subset (by simpa [hspan] using hclosure)

private def multiplicativeHomeomorph (M : Type*) [TopologicalSpace M] : M ≃ₜ Multiplicative M where
  toEquiv := Multiplicative.ofAdd
  continuous_toFun := continuous_ofAdd
  continuous_invFun := continuous_toAdd

/-- Lemma 5.1.1(c): every profinite module has a generating set converging to zero. -/
theorem profiniteModule_hasGeneratingSetConvergingToZero
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M]
    (hM : IsProfiniteModule Λ M) :
    HasGeneratingSetConvergingToZero Λ M := by
  letI : IsTopologicalAddGroup M := hM.2.1
  letI : ContinuousSMul Λ M := hM.2.2.1
  letI : CompactSpace M := hM.2.2.2.1
  letI : T2Space M := hM.2.2.2.2.1
  letI : TotallyDisconnectedSpace M := hM.2.2.2.2.2
  let e : M ≃ₜ Multiplicative M := multiplicativeHomeomorph M
  letI : CompactSpace (Multiplicative M) := e.compactSpace
  letI : T2Space (Multiplicative M) := e.t2Space
  letI : TotallyDisconnectedSpace (Multiplicative M) := e.totallyDisconnectedSpace
  have hG : ProCGroups.IsProfiniteGroup (Multiplicative M) :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  rcases ProCGroups.Generation.exists_generatorsConvergingToOne
      (G := Multiplicative M) hG with ⟨X, hXgen, hXconv⟩
  let S : Set M := Multiplicative.toAdd '' X
  have hpre : Multiplicative.toAdd ⁻¹' S = X := by
    ext x
    simp only [Equiv.preimage_image, S]
  have hsub : (AddSubgroup.closure S).toSubgroup = Subgroup.closure X := by
    rw [AddSubgroup.toSubgroup_closure]
    rw [hpre]
  have hspan : closure (((AddSubgroup.closure S : AddSubgroup M) : Set M)) = Set.univ := by
    have htopSub : (Subgroup.closure X).topologicalClosure = ⊤ := by
      simpa [ProCGroups.Generation.TopologicallyGenerates] using hXgen
    have htopMul : ((AddSubgroup.closure S).toSubgroup).topologicalClosure = ⊤ := by
      simpa [hsub] using htopSub
    change ((AddSubgroup.closure S).topologicalClosure : Set M) = Set.univ
    ext x
    constructor
    · intro _
      simp only [Set.mem_univ]
    · intro _
      have hxmul : Multiplicative.ofAdd x ∈
          (((AddSubgroup.closure S).toSubgroup).topologicalClosure :
            Set (Multiplicative M)) := by
        rw [htopMul]
        simp only [Subgroup.coe_top, Set.mem_univ]
      simpa [AddSubgroup.topologicalClosure_coe] using hxmul
  have hconv : SetConvergesToZero S := by
    intro U hU
    rcases profiniteModule_hasFiniteIndexSubmoduleBasis Λ M hM U hU with
      ⟨N, hNopen, hNU, _⟩
    let V : OpenSubgroup (Multiplicative M) :=
      { toSubgroup := N.toAddSubgroup.toSubgroup
        isOpen' := by
          simpa using hNopen }
    have hsubset : S \ U ⊆ Multiplicative.toAdd '' (X \ (V : Set (Multiplicative M))) := by
      intro y hy
      rcases hy with ⟨hyS, hyU⟩
      rcases hyS with ⟨x, hxX, rfl⟩
      refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
      intro hxV
      exact hyU (hNU (by simpa [V] using hxV))
    exact ((hXconv V).image Multiplicative.toAdd).subset hsubset
  exact hasGeneratingSetConvergingToZero_of_dense_addSubgroup Λ M hspan hconv

end CompletedGroupAlgebra
