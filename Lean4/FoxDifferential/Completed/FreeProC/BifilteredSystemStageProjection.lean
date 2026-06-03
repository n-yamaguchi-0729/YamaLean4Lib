import FoxDifferential.Completed.FreeProC.BifilteredStageProjection
import FoxDifferential.Completed.FiniteStage.Bifiltered.InverseSystem

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/BifilteredSystemStageProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed maps into bifiltered finite Fox semidirect inverse systems

This file is the completed-side companion to
`FiniteStage/Bifiltered/InverseSystem.lean`.  It packages compatible completed-to-finite stage maps
as one homomorphism into the bifiltered inverse limit, records the projection formulas, and connects
that inverse-system layer back to the relation-ideal derivative density route.

The point is to make the remaining profinite approximation problem structural: after constructing
actual completed coordinate projections and proving their bifiltered transition formulas, the whole
finite-stage density argument can be invoked without treating finite stages as unrelated quotients.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section BifilteredLimitMap

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
variable (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
variable (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)

/-- Assemble compatible completed-to-finite semidirect stage maps into a map to the bifiltered
inverse limit. -/
def freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn where
  toFun y :=
    ⟨fun j => π j y, by
      intro i j hij
      exact congrArg (fun f => f y) (hπ hij)⟩
  map_one' := by
    apply Subtype.ext
    funext j
    exact map_one (π j)
  map_mul' y z := by
    apply Subtype.ext
    funext j
    exact map_mul (π j) y z

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMap_projection
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i)
    (j : J) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    finiteFoxStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn π hπ y) =
      π j y :=
  rfl

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- A completed boundary-cycle point maps to a stagewise boundary-cycle point in the bifiltered
inverse limit. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMap_mem_boundaryCycleSet
    [Fintype X] (φ : X → H)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J, π j y ∈ finiteFoxStageSemidirectBoundaryCycleSet
            (X := X) (Nstage j) (nstage j))
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn π hπ y ∈
      finiteFoxStageBifilteredSemidirectLimitBoundaryCycleSet
        (X := X) Nstage nstage hN hn := by
  intro j
  simpa using hboundary_stage y hy j

omit [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Kernel-word points commute with the bifiltered inverse-limit map. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMap_kernelWordPoint
    (φ : X → H)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i)
    (hkernel_stage :
      ∀ j : J, ∀ w : FreeGroup X,
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
          finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn π hπ
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
      finiteFoxStageBifilteredSemidirectKernelWordPointLimit
        (X := X) Nstage nstage hN hn w := by
  apply Subtype.ext
  funext j
  exact hkernel_stage j w

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed stage maps built from left/right coordinates commute with the bifiltered finite
transition whenever the left and right coordinate maps commute with that transition. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_bifilteredFamilyTransition
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
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    {i j : J} (hij : i ≤ j) :
    (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j)) =
    freeProCZCCompletedFoxSemidirectStageMap
      (ProC := ProC) (X := X) (H := H) (Nstage i) (nstage i)
      (stageLeft i) (stageRight i) (hscalar i) := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (ProC := ProC) (X := X) (H := H) (hN hij) (hn hij)
      (stageLeft j) (stageRight j) (hscalar j)
      (stageLeft i) (stageRight i) (hscalar i)
      (hleft hij) (hright hij)

/-- The completed-to-finite stage maps built from a bifiltered-compatible family assemble into a
map to the bifiltered finite Fox semidirect inverse limit. -/
def freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps
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
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
    (fun j =>
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j))
    (fun hij =>
      freeProCZCCompletedFoxSemidirectStageMap_bifilteredFamilyTransition
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
        stageLeft stageRight hscalar hleft hright hij)

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp 900]
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps_projection
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
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (j : J) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    finiteFoxStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
          stageLeft stageRight hscalar hleft hright y) =
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j) y :=
  rfl

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Bifiltered-compatible completed stage maps feed the relation-ideal derivative theorem and
therefore give completed density of algebraic kernel-word points. -/
theorem boundaryCycles_subset_kernelClosure_of_biStageMaps
    [Fintype X] (φ : X → H)
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
    (_hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (_hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
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
  -- The transition hypotheses are intentionally kept in this theorem: they make the stage family
  -- an honest bifiltered inverse system, even though the final closure criterion only uses the
  -- resulting quotient kernels stage by stage.
  exact
    boundaryCycles_subset_kernelClosure_of_stageMaps
      (ProC := ProC) (X := X) (H := H) φ Nstage nstage stageLeft stageRight hscalar
      hidentity_basis stageBoundary hboundary hNstage_kernel hderivative

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated-target form of the bifiltered stage-map density theorem. -/
theorem boundaryCycles_subset_closedGenTarget_of_biStageMaps
    [Fintype X] (φ : X → H)
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
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
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
      (boundaryCycles_subset_kernelClosure_of_biStageMaps
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn φ
        stageLeft stageRight hscalar hleft hright hidentity_basis stageBoundary hboundary
        hNstage_kernel hderivative)

end BifilteredLimitMap

end

end FoxDifferential
