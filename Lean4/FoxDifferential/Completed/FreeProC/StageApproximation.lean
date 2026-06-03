import FoxDifferential.Completed.FreeProC.Density
import FoxDifferential.Completed.FiniteStage.SemidirectCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/StageApproximation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage approximation routes for completed Fox density

This file adds the library layer between finite-stage Fox exactness and the completed density
statement.  It separates three ingredients:

* quotient kernels form a neighbourhood basis in the completed semidirect product;
* completed boundary cycles project to finite-stage boundary cycles;
* finite-stage boundary cycles are covered by finite-stage relation-word cycles.

The last theorem in this file is the intended bridge from the finite theorem
`ker ∂ = im D` at every finite stage to the completed closure statement.
-/

namespace FoxDifferential

noncomputable section

universe u v

section GenericStageExactClosureAPI

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {S T : Set Y}

/-- Quotient-kernel density from exact finite-stage images.

For each quotient stage `j`, let `Tstage j` be the image condition satisfied by points of `T`,
and let `Sstage j` be the finite-stage image of algebraic approximants from `S`.  If every
`Tstage` point is in `Sstage`, and every `Sstage` point lifts to an actual point of `S`, then
`T` is contained in the closure of `S`. -/
theorem subset_closure_of_quotientKernel_stage_exact
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J, Y →* Q j)
    (hbasis : HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (Sstage Tstage : ∀ j : J, Set (Q j))
    (hTstage : ∀ y : Y, y ∈ T → ∀ j : J, π j y ∈ Tstage j)
    (hstage_exact : ∀ j : J, Tstage j ⊆ Sstage j)
    (hlift_stage : ∀ j : J, ∀ q : Q j, q ∈ Sstage j →
      ∃ s : Y, s ∈ S ∧ π j s = q) :
    T ⊆ closure S := by
  refine subset_closure_of_quotientKernel_approximation π hbasis ?_
  intro y hy j
  exact hlift_stage j (π j y) (hstage_exact j (hTstage y hy j))

end GenericStageExactClosureAPI

section CompletedFoxStageExact

open scoped Topology

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [DecidableEq X]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Completed Fox density from exactness of arbitrary quotient-stage images.

This is the general completed semidirect bridge: choose quotient maps out of the completed
semidirect product, prove that boundary cycles land in the chosen finite-stage `Tstage`, prove
finite-stage exactness `Tstage ⊆ Sstage`, and lift every `Sstage` point to an actual kernel word.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stage_exact
    [Fintype X] (φ : X → H)
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →* Q j)
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) π)
    (Sstage Tstage : ∀ j : J, Set (Q j))
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J, π j y ∈ Tstage j)
    (hstage_exact : ∀ j : J, Tstage j ⊆ Sstage j)
    (hlift_stage :
      ∀ j : J, ∀ q : Q j, q ∈ Sstage j →
        ∃ w : FreeGroup X,
          FreeGroup.lift φ w = 1 ∧
            π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) = q) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine subset_closure_of_quotientKernel_stage_exact
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ)
    π hbasis Sstage Tstage hboundary_stage hstage_exact ?_
  intro j q hq
  rcases hlift_stage j q hq with ⟨w, hw, hπw⟩
  refine ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w, ?_, hπw⟩
  exact freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
    (ProC := ProC) φ hw

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Completed Fox density from finite semidirect Fox exactness at every quotient stage.

Here the finite-stage `Tstage` is the set of finite semidirect boundary cycles and the finite-stage
`Sstage` is the set of honest kernel-word derivative points.  The hypotheses that remain are the
actual comparison data between completed stages and finite Fox stages. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J,
            π j y ∈ finiteFoxStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        finiteFoxStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
          finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stage_exact
      (ProC := ProC) φ π hbasis
      (fun j => finiteFoxStageSemidirectKernelWordDerivativeSet
        (X := X) (Nstage j) (nstage j))
      (fun j => finiteFoxStageSemidirectBoundaryCycleSet
        (X := X) (Nstage j) (nstage j))
      hboundary_stage ?_ ?_
  · intro j
    exact
      (finiteFoxStageSemidirectBoundaryCyclesCoveredByKernelWords_iff
        (X := X) (Nstage j) (nstage j)).2 (hstage_exact j)
  · intro j q hq
    rcases hq with ⟨w, hwN, hpoint⟩
    refine ⟨w, hNstage_kernel j hwN, ?_⟩
    calc
      π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w)
          = finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w :=
            hkernel_word_projection j w hwN
      _ = q := hpoint

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Completed Fox graph-word density from finite semidirect Fox exactness at every quotient stage.

This is the finite-quotient form that does not require words in the finite relation subgroup
`Nstage j` to be genuine kernel words for `φ`.  A word `w ∈ Nstage j` only has to project to the
trivial right coordinate at the `j`-th finite stage; the completed approximant remains the honest
graph point `(D w, φ(w))`. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J,
            π j y ∈ finiteFoxStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        finiteFoxStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hgraph_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectGraphWordPoint (ProC := ProC) φ w) =
          finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ) := by
  refine subset_closure_of_quotientKernel_stage_exact
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (S := freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ)
    π hbasis
    (fun j => finiteFoxStageSemidirectKernelWordDerivativeSet
      (X := X) (Nstage j) (nstage j))
    (fun j => finiteFoxStageSemidirectBoundaryCycleSet
      (X := X) (Nstage j) (nstage j))
    hboundary_stage ?_ ?_
  · intro j
    exact
      (finiteFoxStageSemidirectBoundaryCyclesCoveredByKernelWords_iff
        (X := X) (Nstage j) (nstage j)).2 (hstage_exact j)
  · intro j q hq
    rcases hq with ⟨w, hwN, hpoint⟩
    refine ⟨freeProCZCCompletedFoxSemidirectGraphWordPoint (ProC := ProC) φ w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · calc
        π j (freeProCZCCompletedFoxSemidirectGraphWordPoint (ProC := ProC) φ w)
            = finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w :=
              hgraph_word_projection j w hwN
        _ = q := hpoint

/-- Finite-stage semidirect exactness places every completed boundary cycle in the closed
generated Fox graph target without assuming finite relation words are genuine kernel words. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_graphWord_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J,
            π j y ∈ finiteFoxStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        finiteFoxStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hgraph_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectGraphWordPoint (ProC := ProC) φ w) =
          finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact
        (ProC := ProC) φ Nstage nstage π hbasis hboundary_stage hstage_exact
        hgraph_word_projection)

/-- The finite-stage semidirect exactness route also places every completed boundary cycle in the
closed generated Fox graph target. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J,
            π j y ∈ finiteFoxStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        finiteFoxStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
          finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_semi_exact
        (ProC := ProC) φ Nstage nstage π hbasis hboundary_stage hstage_exact
        hNstage_kernel hkernel_word_projection)

end CompletedFoxStageExact

end

end FoxDifferential
