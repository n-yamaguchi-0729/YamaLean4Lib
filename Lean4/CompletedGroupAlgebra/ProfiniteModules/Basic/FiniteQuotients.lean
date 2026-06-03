import CompletedGroupAlgebra.ProfiniteModules.Basic.OpenSubmodule

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/ProfiniteModules/Basic/FiniteQuotients.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite quotient bases for profinite modules
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- Lemma 5.1.1(b), linear-topology interface: a profinite module with a linear topology has a
basis of open finite-index submodules at zero. -/
theorem profiniteModule_hasFiniteIndexSubmoduleBasis_of_linearTopology
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] [IsLinearTopology Λ M]
    (hM : IsProfiniteModule Λ M) :
    HasFiniteIndexSubmoduleBasis Λ M := by
  letI : IsTopologicalAddGroup M := hM.2.1
  letI : ContinuousAdd M := inferInstance
  intro U hU
  rcases ((IsLinearTopology.hasBasis_open_submodule Λ).mem_iff.mp hU) with
    ⟨N, hNopen, hNU⟩
  exact ⟨N, hNopen, hNU,
    finite_quotient_of_openSubmodule Λ M hM N hNopen⟩

/-- Lemma 5.1.1(b), inverse-limit formulation under the same linear-topology hypothesis. -/
theorem profiniteModule_isInverseLimitOfFiniteQuotientModules_of_linearTopology
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] [IsLinearTopology Λ M]
    (hM : IsProfiniteModule Λ M) :
    IsInverseLimitOfFiniteQuotientModules Λ M := by
  rw [inverseLimitOfFiniteQuotientModules_iff_finiteIndexSubmoduleBasis]
  exact profiniteModule_hasFiniteIndexSubmoduleBasis_of_linearTopology Λ M hM

/-- Lemma 5.1.1(b): finite-index submodules form a neighborhood basis at zero in a profinite
module. -/
theorem profiniteModule_hasFiniteIndexSubmoduleBasis
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] (hM : IsProfiniteModule Λ M) :
    HasFiniteIndexSubmoduleBasis Λ M := by
  letI : IsLinearTopology Λ M := profiniteModule_isLinearTopology Λ M hM
  exact profiniteModule_hasFiniteIndexSubmoduleBasis_of_linearTopology Λ M hM

/-- Open submodule quotients separate points of a profinite module. -/
theorem profiniteModule_ext_of_openSubmoduleQuotients
    {R : Type u} (N : Type v) [Ring R] [TopologicalSpace R]
    [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) {x y : N}
    (h : ∀ W : Submodule R N, IsOpen (W : Set N) → Submodule.mkQ W x = Submodule.mkQ W y) :
    x = y := by
  by_contra hxy
  letI : T2Space N := hN.2.2.2.2.1
  let O : Set N := ({x - y} : Set N)ᶜ
  have hd0 : x - y ≠ 0 := by
    intro hd
    exact hxy (sub_eq_zero.mp hd)
  have hOopen : IsOpen O := isClosed_singleton.isOpen_compl
  have h0O : (0 : N) ∈ O := by
    change (0 : N) ≠ x - y
    exact hd0.symm
  rcases profiniteModule_hasFiniteIndexSubmoduleBasis R N hN O (hOopen.mem_nhds h0O) with
    ⟨W, hWopen, hWO, _hfinite⟩
  have hq := h W hWopen
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hq
  have hdiff : x - y ∈ W := (Submodule.Quotient.eq W).1 hq
  have hdO : x - y ∈ O := hWO hdiff
  exact hdO (by simp only [Set.mem_singleton_iff])

/-- Open submodules of a profinite module. -/
abbrev ProfiniteModuleOpenSubmodule
    (R : Type u) (N : Type v) [Ring R] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] : Type _ :=
  {W : Submodule R N // IsOpen (W : Set N)}

/-- Open submodule quotients detect continuity of maps into a profinite module. -/
theorem continuous_of_forall_openSubmodule_quotient_continuous
    {R : Type u} (N : Type v) [Ring R] [TopologicalSpace R]
    [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N)
    {Y : Type z} [TopologicalSpace Y] {F : Y → N}
    (hF : ∀ W : Submodule R N, IsOpen (W : Set N) →
      Continuous fun y : Y => Submodule.mkQ W (F y)) :
    Continuous F := by
  letI : IsTopologicalAddGroup N := hN.2.1
  letI : ContinuousAdd N := inferInstance
  rw [continuous_iff_continuousAt]
  intro y
  rw [continuousAt_def]
  intro A hA
  rcases mem_nhds_iff.mp hA with ⟨O, hOA, hOopen, hFO⟩
  let U0 : Set N := {z | F y + z ∈ O}
  have hU0 : U0 ∈ 𝓝 (0 : N) := by
    apply IsOpen.mem_nhds
    · exact hOopen.preimage (continuous_const.add continuous_id)
    · simp only [Set.mem_setOf_eq, add_zero, hFO, U0]
  rcases profiniteModule_hasFiniteIndexSubmoduleBasis R N hN U0 hU0 with
    ⟨W, hWopen, hWU, _hfinite⟩
  let hdisc : IsDiscreteModule R (N ⧸ W) :=
    quotient_openSubmodule_isDiscreteModule R N hN W hWopen
  letI : DiscreteTopology (N ⧸ W) := hdisc.2
  let q : Y → N ⧸ W := fun z => Submodule.mkQ W (F z)
  let B : Set (N ⧸ W) := {Submodule.mkQ W (F y)}
  have hqcont : Continuous q := hF W hWopen
  have hpreOpen : IsOpen (q ⁻¹' B) := (isOpen_discrete B).preimage hqcont
  have hypre : y ∈ q ⁻¹' B := by
    simp only [Submodule.mkQ_apply, Set.mem_preimage, Set.mem_singleton_iff, q, B]
  refine Filter.mem_of_superset (hpreOpen.mem_nhds hypre) ?_
  intro z hz
  apply hOA
  have hquot : Submodule.mkQ W (F z) = Submodule.mkQ W (F y) := by
    simpa [q, B] using hz
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hquot
  have hdiff : F z - F y ∈ W := (Submodule.Quotient.eq W).1 hquot
  have hU : F z - F y ∈ U0 := hWU hdiff
  change F y + (F z - F y) ∈ O at hU
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hU

/-- A finite family of open submodules has an open submodule contained in all of them. -/
theorem exists_openSubmodule_le_finset
    {R : Type u} (N : Type v) [Ring R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (s : Finset (ProfiniteModuleOpenSubmodule (R := R) N)) :
    ∃ K : ProfiniteModuleOpenSubmodule (R := R) N,
      ∀ W ∈ s, K.1 ≤ W.1 := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · refine ⟨⟨⊤, isOpen_univ⟩, ?_⟩
    simp only [Finset.notMem_empty, top_le_iff, IsEmpty.forall_iff, implies_true]
  · intro W s hWs ih
    rcases ih with ⟨K, hK⟩
    refine ⟨⟨K.1 ⊓ W.1, K.2.inter W.2⟩, ?_⟩
    intro V hV
    rw [Finset.mem_insert] at hV
    rcases hV with hVW | hVs
    · subst V
      exact inf_le_right
    · exact inf_le_left.trans (hK V hVs)

/-- The quotient of a profinite module by a closed submodule is profinite. -/
theorem quotient_closedSubmodule_isProfiniteModule
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] (hM : IsProfiniteModule Λ M)
    (K : Submodule Λ M) (hK : IsClosed (K : Set M)) :
    IsProfiniteModule Λ (M ⧸ K) := by
  classical
  letI : IsTopologicalRing Λ := hM.1.1
  letI : IsTopologicalAddGroup M := hM.2.1
  letI : ContinuousAdd M := inferInstance
  letI : ContinuousSMul Λ M := hM.2.2.1
  letI : CompactSpace M := hM.2.2.2.1
  letI : T2Space M := hM.2.2.2.2.1
  letI : TotallyDisconnectedSpace M := hM.2.2.2.2.2
  letI : IsClosed (K : Set M) := hK
  letI : IsTopologicalAddGroup (M ⧸ K) := Submodule.topologicalAddGroup_quotient K
  letI : ContinuousAdd (M ⧸ K) := inferInstance
  letI : ContinuousSMul Λ (M ⧸ K) := Submodule.continuousSMul_quotient K
  letI : CompactSpace (M ⧸ K) := Quotient.compactSpace
  letI : T3Space (M ⧸ K) := Submodule.t3_quotient_of_isClosed K
  letI : T2Space (M ⧸ K) := inferInstance
  have htotSep : TotallySeparatedSpace (M ⧸ K) := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    intro a
    refine Submodule.Quotient.induction_on K a ?_
    intro x b
    refine Submodule.Quotient.induction_on K b ?_
    intro y hab
    have hxyK : x - y ∉ K := by
      intro hxy
      exact hab ((Submodule.Quotient.eq K).2 hxy)
    let O : Set M := {z | x - y - z ∉ K}
    have hOopen : IsOpen O := by
      exact hK.isOpen_compl.preimage ((continuous_const.sub continuous_const).sub continuous_id)
    have h0O : (0 : M) ∈ O := by
      simpa [O] using hxyK
    rcases profiniteModule_hasFiniteIndexSubmoduleBasis Λ M hM O
        (hOopen.mem_nhds h0O) with
      ⟨W, hWopen, hWO, _hWfinite⟩
    let H : Submodule Λ M := K ⊔ W
    have hHopen : IsOpen (H : Set M) := by
      have hWsubH : (W : Set M) ⊆ (H : Set M) := fun z hz =>
        Submodule.mem_sup_right hz
      exact H.toAddSubgroup.isOpen_of_mem_nhds
        (Filter.mem_of_superset (hWopen.mem_nhds (zero_mem W)) hWsubH)
    have hxyH : x - y ∉ H := by
      intro hxyH
      rcases (Submodule.mem_sup.1 hxyH) with ⟨k, hk, w, hw, hkw⟩
      have hwO : w ∈ O := hWO hw
      have hxysub : x - y - w = k := by
        rw [← hkw]
        abel
      exact hwO (by simpa [hxysub] using hk)
    let Q : Submodule Λ (M ⧸ K) := Submodule.map K.mkQ H
    have hQopen : IsOpen (Q : Set (M ⧸ K)) := by
      rw [Submodule.map_coe]
      exact K.isOpenMap_mkQ (H : Set M) hHopen
    have hQclosed : IsClosed (Q : Set (M ⧸ K)) :=
      AddSubgroup.isClosed_of_isOpen Q.toAddSubgroup hQopen
    have hmk_mem_Q_iff : ∀ z : M, Submodule.Quotient.mk z ∈ Q ↔ z ∈ H := by
      intro z
      constructor
      · intro hz
        rcases (Submodule.mem_map.1 hz) with ⟨h, hh, hhz⟩
        have hdiff : h - z ∈ K := (Submodule.Quotient.eq K).1 hhz
        have hdiffH : h - z ∈ H := Submodule.mem_sup_left hdiff
        have hzH : h - (h - z) ∈ H := H.sub_mem hh hdiffH
        simpa using hzH
      · intro hz
        exact Submodule.mem_map.2 ⟨z, hz, rfl⟩
    let C : Set (M ⧸ K) := {q | q - Submodule.Quotient.mk x ∈ Q}
    have hCclosed : IsClosed C :=
      hQclosed.preimage (continuous_id.sub continuous_const)
    have hCopen : IsOpen C :=
      hQopen.preimage (continuous_id.sub continuous_const)
    refine ⟨C, ⟨hCclosed, hCopen⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, sub_self, zero_mem, C]
    · intro hyC
      have hyxQ : Submodule.Quotient.mk (y - x) ∈ Q := by
        simpa [C] using hyC
      have hyxH : y - x ∈ H := (hmk_mem_Q_iff (y - x)).1 hyxQ
      have hxyH' : x - y ∈ H := by
        simpa using H.neg_mem hyxH
      exact hxyH hxyH'
  letI : TotallySeparatedSpace (M ⧸ K) := htotSep
  letI : TotallyDisconnectedSpace (M ⧸ K) := inferInstance
  exact ⟨hM.1, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Strengthened finite quotient basis: the quotients can be used as finite discrete modules. -/
theorem profiniteModule_hasFiniteDiscreteQuotientBasis
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] (hM : IsProfiniteModule Λ M) :
    ∀ U ∈ 𝓝 (0 : M), ∃ N : Submodule Λ M,
      IsOpen (N : Set M) ∧ (N : Set M) ⊆ U ∧
        IsDiscreteModule Λ (M ⧸ N) ∧ Nonempty (Fintype (M ⧸ N)) := by
  intro U hU
  rcases profiniteModule_hasFiniteIndexSubmoduleBasis Λ M hM U hU with
    ⟨N, hNopen, hNU, _hfinite⟩
  exact ⟨N, hNopen, hNU, quotient_openSubmodule_isDiscreteModule Λ M hM N hNopen,
    finite_quotient_of_openSubmodule Λ M hM N hNopen⟩

/-- Lemma 5.1.1(b): a profinite module is the inverse limit of its finite quotient modules, in the
finite-index-basis formulation used by this file. -/
theorem profiniteModule_isInverseLimitOfFiniteQuotientModules
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] (hM : IsProfiniteModule Λ M) :
    IsInverseLimitOfFiniteQuotientModules Λ M := by
  rw [inverseLimitOfFiniteQuotientModules_iff_finiteIndexSubmoduleBasis]
  exact profiniteModule_hasFiniteIndexSubmoduleBasis Λ M hM

end CompletedGroupAlgebra
