import FoxDifferential.Completed.FreeProC.StageProjection
import FoxDifferential.Completed.FiniteStage.Bifiltered.Transition
import FoxDifferential.Completed.FiniteStage.Bifiltered.System
import FoxDifferential.Completed.FiniteStage.Bifiltered.InverseSystem

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/BifilteredStageProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bifiltered compatibility for completed-to-finite Fox stage projections

This file connects the completed semidirect stage maps from `Free/StageProjection.lean` with the
simultaneous finite transition in target quotient and coefficient modulus.  It isolates the exact
compatibility formulas needed to build cofinal finite quotient systems from actual completed
coordinate projections.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Fact (0 < n)] [Fact (0 < m)] in
/-- Compatibility of two completed-to-finite stage maps with the bifiltered finite transition.

The statement says that if the left completed coordinate maps commute with the combined
coefficient/target transition and the right maps commute with `F/N → F/M`, then the two
semidirect stage maps commute. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
    (stageLeftN :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N m)
    (stageRightN : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftN (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) M n)
    (stageRightM : H →* finiteFoxStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftM (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h) :
    (finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm).comp
        (freeProCZCCompletedFoxSemidirectStageMap
          (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) =
      freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) M n stageLeftM stageRightM hscalarM := by
  apply MonoidHom.ext
  intro y
  apply FiniteFoxStageSemidirect.ext
  · change finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm
        (stageLeftN y.left) = stageLeftM y.left
    exact hleft y.left
  · change finiteFoxStageTargetQuotientMap (X := X) hNM (stageRightN y.right) =
      stageRightM y.right
    exact hright y.right

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Fact (0 < n)] [Fact (0 < m)] in
/-- Kernel membership descends along a compatible bifiltered transition between completed stage
maps. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_mem_ker_of_bifilteredTransition
    (stageLeftN :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N m)
    (stageRightN : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftN (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) M n)
    (stageRightM : H →* finiteFoxStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftM (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h)
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hy : y ∈ (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN).ker) :
    y ∈ (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) M n stageLeftM stageRightM hscalarM).ker := by
  have hcomm :=
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (ProC := ProC) (X := X) (H := H) hNM hnm
      stageLeftN stageRightN hscalarN stageLeftM stageRightM hscalarM hleft hright
  have hyone :
      (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y = 1 := by
    simpa using hy
  have hy' :
      ((finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm).comp
        (freeProCZCCompletedFoxSemidirectStageMap
          (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN)) y = 1 := by
    change finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm
        ((freeProCZCCompletedFoxSemidirectStageMap
          (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y) = 1
    rw [hyone]
    exact map_one (finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm)
  change (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) M n stageLeftM stageRightM hscalarM) y = 1
  rw [← congrArg (fun f => f y) hcomm]
  exact hy'

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- Bifiltered compatibility transports boundary-cycle preservation from a finer completed stage
to a coarser completed stage. -/
theorem freeProCZCFoxSemiStageMap_mem_boundaryCycleSet_of_bifilteredTransition
    [Fintype X]
    (_φ : X → H)
    (stageLeftN :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N m)
    (stageRightN : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftN (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) M n)
    (stageRightM : H →* finiteFoxStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftM (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h)
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hyN :
      (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y ∈
          finiteFoxStageSemidirectBoundaryCycleSet (X := X) N m) :
      (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) M n stageLeftM stageRightM hscalarM) y ∈
          finiteFoxStageSemidirectBoundaryCycleSet (X := X) M n := by
  have hcomm :=
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (ProC := ProC) (X := X) (H := H) hNM hnm
      stageLeftN stageRightN hscalarN stageLeftM stageRightM hscalarM hleft hright
  rw [← congrArg (fun f => f y) hcomm]
  change finiteFoxStageSemidirectMap (X := X) hNM n
      (finiteFoxStageSemidirectCoeffMap (X := X) N hnm
        ((freeProCZCCompletedFoxSemidirectStageMap
          (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y)) ∈
    finiteFoxStageSemidirectBoundaryCycleSet (X := X) M n
  exact finiteFoxStageSemidirectMap_mem_boundaryCycleSet (X := X) hNM n
    (finiteFoxStageSemidirectCoeffMap_mem_boundaryCycleSet (X := X) N hnm hyN)

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Bifiltered compatibility transports kernel-word point formulas from a finer completed stage to
a coarser completed stage. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint_of_bifilteredTransition
    (φ : X → H)
    (stageLeftN :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N m)
    (stageRightN : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftN (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (finiteFoxStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) M n)
    (stageRightM : H →* finiteFoxStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeftM (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h)
    (hderivativeN :
      ∀ w : FreeGroup X,
        stageLeftN
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N m w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) M n stageLeftM stageRightM hscalarM
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) M n w := by
  have hcomm :=
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (ProC := ProC) (X := X) (H := H) hNM hnm
      stageLeftN stageRightN hscalarN stageLeftM stageRightM hscalarM hleft hright
  rw [← congrArg
    (fun f => f (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w)) hcomm]
  change finiteFoxStageBifilteredSemidirectMap (X := X) hNM hnm
      (freeProCZCCompletedFoxSemidirectStageMap
        (ProC := ProC) (X := X) (H := H) N m stageLeftN stageRightN hscalarN
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w)) =
    finiteFoxStageSemidirectKernelWordPoint (X := X) M n w
  rw [freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
    (ProC := ProC) (X := X) (H := H) N m φ
    stageLeftN stageRightN hscalarN hderivativeN w]
  exact finiteFoxStageBifilteredSemidirectMap_kernelWordPoint (X := X) hNM hnm w

end

end FoxDifferential
