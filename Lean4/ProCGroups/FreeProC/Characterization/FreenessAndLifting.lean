import ProCGroups.FreeProC.Characterization.EmbeddingProblems

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Characterization/FreenessAndLifting.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

namespace ProCGroups.FreeProC.Characterization

universe u

section CoreTheorems

variable {E : EmbeddingProblemPredicate.{u}}

/-- Weak solvability reduces to the finite minimal normal kernel case when the reduction step is
supplied explicitly. -/
theorem weakSolvability_of_finiteMinimalNormalKernel
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hfinite :
      ∀ P : TopologicalEmbeddingProblem G, E P →
        P.HasFiniteMinimalNormalKernel → P.HasWeakSolution)
    (hreduce :
      ∀ P : TopologicalEmbeddingProblem G, E P →
        ∃ P₀ : TopologicalEmbeddingProblem G, E P₀ ∧
          P₀.HasFiniteMinimalNormalKernel ∧
          (P₀.HasWeakSolution → P.HasWeakSolution)) :
    ∀ P : TopologicalEmbeddingProblem G, E P → P.HasWeakSolution := by
  intro P hP
  rcases hreduce P hP with ⟨P₀, hP₀, hker, hback⟩
  exact hback (hfinite P₀ hP₀ hker)

end CoreTheorems


/-- Weak lifting can be tested on finite-target embedding problems, with explicit reduction data
from arbitrary problems to finite-target finite-minimal-normal-kernel problems. -/
theorem weakLiftingProperty_iff_finiteTargetProblems
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : EmbeddingProblemPredicate.{u}}
    (hreduce :
      ∀ P : TopologicalEmbeddingProblem G, E P →
        ∃ P₀ : TopologicalEmbeddingProblem G, E P₀ ∧
          P₀.HasFiniteMinimalNormalKernel ∧
          (P₀.HasWeakSolution → P.HasWeakSolution))
    (hfiniteTargetOfFiniteMinimalKernel :
      ∀ P : TopologicalEmbeddingProblem G, E P →
        P.HasFiniteMinimalNormalKernel → Finite P.A) :
    HasWeakLiftingPropertyOver E G ↔
      ∀ P : TopologicalEmbeddingProblem G, E P → Finite P.A → P.HasWeakSolution := by
  constructor
  · intro h P hP _hfinite
    exact h P hP
  · intro h P hP
    rcases hreduce P hP with ⟨P₀, hP₀, hmin, hback⟩
    exact hback (h P₀ hP₀ (hfiniteTargetOfFiniteMinimalKernel P₀ hP₀ hmin))


end ProCGroups.FreeProC.Characterization
