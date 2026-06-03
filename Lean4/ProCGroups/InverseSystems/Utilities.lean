import Mathlib.Topology.Homeomorph.Lemmas

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/InverseSystems/Utilities.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Inverse systems and inverse limits

Defines inverse systems of topological groups and proves lift, projection, exactness, quotient, stagewise isomorphism, and finite-stage factorization results.
-/

namespace Continuous

/-- A continuous bijection from a compact space to a Hausdorff space is a homeomorphism. -/
noncomputable def homeoOfBijectiveCompactToT2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    (hbij : Function.Bijective f) :
    X ≃ₜ Y :=
  homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf

end Continuous

namespace ProCGroups.InverseSystems

universe u

section

variable {I : Type u} [Preorder I]

/-- A finite subset of a directed preorder admits an upper bound. -/
theorem exists_upperBound_finset (hdir : Directed (· ≤ ·) (id : I → I)) :
    ∀ s : Finset I, s.Nonempty → ∃ j, ∀ i ∈ s, i ≤ j := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro hs
    rcases hs with ⟨i, hi⟩
    simp only [Finset.notMem_empty] at hi
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨j, hj⟩
      rcases hdir a j with ⟨k, hak, hjk⟩
      refine ⟨k, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hak
      · exact (hj i hi).trans hjk
    · have hs'' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hs''
      refine ⟨a, ?_⟩
      intro i hi
      simp only [insert_empty_eq, Finset.mem_singleton] at hi
      simp only [hi, le_refl]

end

end ProCGroups.InverseSystems
