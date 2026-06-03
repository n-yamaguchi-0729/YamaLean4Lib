import FoxDifferential.Completed.FreeProC.RelationSubmoduleApproximation
import FoxDifferential.Completed.FreeProC.QuotientKernelBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/StageProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed-to-finite semidirect stage projections

This file builds the reusable projection layer needed by the completed Crowell density argument.
A finite semidirect projection is constructed from its mathematical coordinates:

* a coordinate projection on completed Fox vectors;
* a quotient map on the target group;
* compatibility of the coordinate projection with the semidirect scalar action.

The resulting API expresses finite-stage comparison by the actual boundary and derivative
coordinate formulas.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section CompletedFiniteStageMap

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- A semidirect projection from the completed Fox semidirect product to a finite Fox stage,
constructed from a left coordinate map and a right target quotient map.

The only compatibility required is that the left coordinate map respects the scalar action used in
semidirect multiplication.  This is the abstract form of the finite quotient map
`Z_C[[H]]^X ⋊ H -> (Z/n)[F/N]^X ⋊ F/N`. -/
def freeProCZCCompletedFoxSemidirectStageMap
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageSemidirect (X := X) N n where
  toFun y :=
    { left := stageLeft y.left
      right := stageRight y.right }
  map_one' := by
    apply FiniteFoxStageSemidirect.ext
    · change stageLeft 0 = 0
      exact map_zero stageLeft
    · exact map_one stageRight
  map_mul' a b := by
    apply FiniteFoxStageSemidirect.ext
    · change
        stageLeft (a.left + zcGroupLike ProC.finiteQuotientClass H a.right • b.left) =
          stageLeft a.left +
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (finiteFoxStageTargetQuotient (X := X) N) (stageRight a.right)) •
              stageLeft b.left
      rw [map_add, hscalar]
    · change stageRight (a.right * b.right) = stageRight a.right * stageRight b.right
      exact map_mul stageRight a.right b.right

omit [DecidableEq X] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectStageMap_left
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    (freeProCZCCompletedFoxSemidirectStageMap
      (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar y).left =
      stageLeft y.left :=
  rfl

omit [DecidableEq X] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectStageMap_right
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    (freeProCZCCompletedFoxSemidirectStageMap
      (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar y).right =
      stageRight y.right :=
  rfl

omit [DecidableEq X] in
/-- Membership in the kernel of a completed-to-finite semidirect stage map, read in the two
coordinates. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_mem_ker_iff
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H} :
    y ∈ (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar).ker ↔
      stageLeft y.left = 0 ∧ stageRight y.right = 1 := by
  constructor
  · intro hy
    change
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar y = 1 at hy
    have hleft := congrArg (fun z : FiniteFoxStageSemidirect (X := X) N n => z.left) hy
    have hright := congrArg (fun z : FiniteFoxStageSemidirect (X := X) N n => z.right) hy
    exact ⟨by simpa using hleft, by simpa using hright⟩
  · rintro ⟨hleft, hright⟩
    change
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar y = 1
    apply FiniteFoxStageSemidirect.ext
    · simpa using hleft
    · simpa using hright

omit [DecidableEq X] in
/-- A completed boundary-cycle point projects to a finite boundary-cycle point once the left
coordinate projection commutes with the source-shaped Fox boundary. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
    [Fintype X]
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (stageBoundary :
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) N n)
    (hboundary :
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageFoxBoundary (X := X) N n (stageLeft v) =
          stageBoundary
            (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ) :
    freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar y ∈
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N n := by
  rcases hy with ⟨hyright, hyboundary⟩
  constructor
  · change stageRight y.right = 1
    rw [hyright]
    exact map_one stageRight
  · rw [mem_finiteFoxStageBoundaryCycleSubmodule]
    calc
      finiteFoxStageFoxBoundary (X := X) N n
          ((freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar y).left)
          = finiteFoxStageFoxBoundary (X := X) N n (stageLeft y.left) := rfl
      _ = stageBoundary
            (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) y.left) :=
          hboundary y.left
      _ = 0 := by
          rw [hyboundary]
          exact map_zero stageBoundary

/-- The stage map sends the completed kernel-word point `(D w, 1)` to the corresponding finite
kernel-word point, provided the left coordinate projection commutes with Fox derivatives. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N n w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) N n w := by
  apply FiniteFoxStageSemidirect.ext
  · change
      stageLeft
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
        finiteFoxStageDerivativeVector (X := X) N n w
    exact hderivative w
  · simp only [freeProCZCCompletedFoxSemidirectKernelWordPoint, freeProCZCCompletedFoxSemidirectStageMap_right,
  map_one, finiteFoxStageSemidirectKernelWordPoint]

/-- The stage map sends a completed graph-word point `(D w, φ(w))` to the corresponding finite
stage graph point. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N n w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectGraphWordPoint (ProC := ProC) φ w) =
      ({ left := finiteFoxStageDerivativeVector (X := X) N n w,
         right := stageRight (FreeGroup.lift φ w) } :
        FiniteFoxStageSemidirect (X := X) N n) := by
  apply FiniteFoxStageSemidirect.ext
  · exact hderivative w
  · rfl

/-- If a word is in the finite-stage relation subgroup, the stage image of its completed graph
point is the finite kernel-word point. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint_of_stage_kernel
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N n)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N n w)
    (hright_word :
      ∀ w : FreeGroup X, stageRight (FreeGroup.lift φ w) = QuotientGroup.mk' N w)
    (w : FreeGroup X) (hw : w ∈ N) :
    freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N n stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectGraphWordPoint (ProC := ProC) φ w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) N n w := by
  rw [freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint
    (ProC := ProC) (X := X) (H := H) N n φ stageLeft stageRight hscalar hderivative w]
  apply FiniteFoxStageSemidirect.ext
  · rfl
  · change stageRight (FreeGroup.lift φ w) = 1
    rw [hright_word w]
    exact (QuotientGroup.eq_one_iff (N := N) w).2 hw

end CompletedFiniteStageMap

section StageMapDensityRoute

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Completed Fox density from a family of concrete completed-to-finite semidirect stage maps.

The finite exactness input is the relation-ideal derivative theorem already proved at every
finite stage.  The remaining data are now exactly the two projection formulas expected from the
completed Fox construction: boundary compatibility and derivative compatibility. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stageMaps_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  let π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j) :=
    fun j =>
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j)
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_relDeriv
      (ProC := ProC) φ Nstage nstage π ?_ ?_ hNstage_kernel ?_
  · exact hquotient_basis
  · intro y hy j
    exact
      freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (stageBoundary j)
        (hboundary j) hy
  · intro j w hw
    exact
      freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (hderivative j) w

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Completed graph-word density from concrete completed-to-finite semidirect stage maps.

Unlike the kernel-word route, this theorem does not ask for
`w ∈ Nstage j -> FreeGroup.lift φ w = 1`.  Finite-stage exactness supplies `w ∈ Nstage j`, and
the completed approximating point is the graph point `(D w, φ(w))`. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_stageMaps_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ) := by
  let π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j) :=
    fun j =>
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j)
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact
      (ProC := ProC) φ Nstage nstage π ?_ ?_ ?_ ?_
  · exact hquotient_basis
  · intro y hy j
    exact
      freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (stageBoundary j)
        (hboundary j) hy
  · intro j
    exact finiteFoxStageBoundaryCyclesCoveredBySourceKernel_of_relationIdeal_derivatives
      (X := X) (Nstage j) (nstage j)
  · intro j w hw
    exact
      freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint_of_stage_kernel
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (hderivative j)
        (hright_word j) w hw

/-- Concrete stage-map graph-word density, phrased as closed-generated-target membership. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_stageMaps_graphRelDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_stageMaps_relDeriv
        (ProC := ProC) φ Nstage nstage stageLeft stageRight hscalar hquotient_basis
        stageBoundary hboundary hright_word hderivative)

/-- The same concrete stage-map route, with the conclusion phrased as membership in the
closed-generated Fox graph target. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_stageMaps_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stageMaps_relDeriv
        (ProC := ProC) φ Nstage nstage stageLeft stageRight hscalar hquotient_basis
        stageBoundary hboundary hNstage_kernel hderivative)


/-- Stage-map density using identity-neighbourhood kernels rather than left-coset kernels.

This is the topological form naturally produced by profinite finite quotient separation.  The
conversion to the left-coset closure basis is performed internally. -/
theorem boundaryCycles_subset_kernelClosure_of_stageMaps
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stageMaps_relDeriv
      (ProC := ProC) φ Nstage nstage stageLeft stageRight hscalar ?_
      stageBoundary hboundary hNstage_kernel hderivative
  exact HasIdentityQuotientKernelNeighbourhoodBasis.to_left
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (π := fun j : J =>
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j))
    hidentity_basis

/-- Graph-word density using identity-neighbourhood kernels rather than left-coset kernels. -/
theorem boundaryCycles_subset_graphWordClosure_of_stageMaps
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ) := by
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_stageMaps_relDeriv
      (ProC := ProC) φ Nstage nstage stageLeft stageRight hscalar ?_
      stageBoundary hboundary hright_word hderivative
  exact HasIdentityQuotientKernelNeighbourhoodBasis.to_left
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (π := fun j : J =>
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j))
    hidentity_basis

/-- Closed-generated-target version of the identity-kernel graph-word stage-map theorem. -/
theorem boundaryCycles_subset_closedGenTarget_of_stageGraph
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density
      (ProC := ProC) φ
      (boundaryCycles_subset_graphWordClosure_of_stageMaps
        (ProC := ProC) φ Nstage nstage stageLeft stageRight hscalar hidentity_basis
        stageBoundary hboundary hright_word hderivative)

/-- Closed-generated-target version of the identity-kernel stage-map density theorem. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_stageMaps_identityKernel_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (boundaryCycles_subset_kernelClosure_of_stageMaps
        (ProC := ProC) φ Nstage nstage stageLeft stageRight hscalar hidentity_basis
        stageBoundary hboundary hNstage_kernel hderivative)

end StageMapDensityRoute

end

end FoxDifferential
