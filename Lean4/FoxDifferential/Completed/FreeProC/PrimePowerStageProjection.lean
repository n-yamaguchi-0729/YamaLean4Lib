import FoxDifferential.Completed.FreeProC.StageProjection
import FoxDifferential.Completed.FreeProC.CofinalQuotientKernelBasis
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Semidirect

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/PrimePowerStageProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Prime-power completed-to-finite Fox stage projections

This file specializes the completed-to-finite semidirect projection layer to a fixed relation
quotient and prime-power coefficient stages.  It also constructs the induced map from the completed
semidirect product to the inverse limit of the prime-power finite Fox semidirect stages.

This is the next structural layer toward the completed Crowell density theorem: after the finite
relation-ideal derivative theorem is available, the remaining proof needs actual compatible
finite-stage projections and a quotient-kernel neighbourhood basis.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section PrimePowerStageMaps

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable (N : Subgroup (FreeGroup X)) [N.Normal]

/-- A completed Fox semidirect projection to the `ℓ^a` finite stage. -/
def freeProCZCCompletedFoxSemidirectPrimePowerStageMap
    (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageSemidirect (X := X) N (ℓ ^ a) :=
  freeProCZCCompletedFoxSemidirectStageMap
    (ProC := ProC) (X := X) (H := H) N (ℓ ^ a) stageLeft stageRight hscalar

omit [Fact (0 < ℓ)] [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_left
    (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    (freeProCZCCompletedFoxSemidirectPrimePowerStageMap
      (ProC := ProC) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar y).left =
      stageLeft y.left :=
  rfl

omit [Fact (0 < ℓ)] [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_right
    (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    (freeProCZCCompletedFoxSemidirectPrimePowerStageMap
      (ProC := ProC) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar y).right =
      stageRight y.right :=
  rfl

omit [Fact (0 < ℓ)] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
omit [DecidableEq X] in
/-- Boundary-cycle preservation for a prime-power completed-to-finite stage map. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_mem_finiteBoundaryCycleSet
    [Fintype X]
    (φ : X → H) (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (stageBoundary :
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
    (hboundary :
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        finiteFoxStageFoxBoundary (X := X) N (ℓ ^ a) (stageLeft v) =
          stageBoundary
            (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ) :
    freeProCZCCompletedFoxSemidirectPrimePowerStageMap
        (ProC := ProC) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar y ∈
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
      (ProC := ProC) (X := X) (H := H) N (ℓ ^ a) φ
      stageLeft stageRight hscalar stageBoundary hboundary hy

omit [Fact (0 < ℓ)] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Kernel-word points project to kernel-word points at prime-power finite stages. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_kernelWordPoint
    (φ : X → H) (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N (ℓ ^ a) w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectPrimePowerStageMap
        (ProC := ProC) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
      (ProC := ProC) (X := X) (H := H) N (ℓ ^ a) φ
      stageLeft stageRight hscalar hderivative w

/-- Assemble compatible prime-power stage maps into a map to the inverse limit of finite
semidirect stages. -/
def freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N where
  toFun y :=
    ⟨fun a => π a y, by
      intro a b hab
      exact congrArg (fun f => f y) (hπ hab)⟩
  map_one' := by
    apply Subtype.ext
    funext a
    exact map_one (π a)
  map_mul' y z := by
    apply Subtype.ext
    funext a
    exact map_mul (π a) y z

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_projection
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a)
    (a : ℕ) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a
        (freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
          (ProC := ProC) (X := X) (H := H) ℓ N π hπ y) =
      π a y :=
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- A completed boundary-cycle point maps to a stagewise boundary-cycle point in the prime-power
inverse limit. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_mem_boundaryCycleSet
    [Fintype X] (φ : X → H)
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ a : ℕ, π a y ∈ finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a))
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ) :
    freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
        (ProC := ProC) (X := X) (H := H) ℓ N π hπ y ∈
      finiteFoxStagePrimePowerSemidirectLimitBoundaryCycleSet (ℓ := ℓ) (X := X) N := by
  intro a
  simpa using hboundary_stage y hy a

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Kernel-word points commute with the prime-power inverse-limit map. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_kernelWordPoint
    (φ : X → H)
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
        FiniteFoxStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a)
    (hkernel_word_projection :
      ∀ a : ℕ, ∀ w : FreeGroup X,
        π a (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
          finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
        (ProC := ProC) (X := X) (H := H) ℓ N π hπ
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
      finiteFoxStagePrimePowerSemidirectKernelWordPointLimit (ℓ := ℓ) (X := X) N w := by
  apply Subtype.ext
  funext a
  exact hkernel_word_projection a w

omit [Fact (0 < ℓ)] in
/-- Completed Fox density from prime-power stage maps and the finite relation-ideal derivative
theorem. -/
theorem boundaryCycles_subset_kernelClosure_of_ppStageMaps
    [Fintype X] (φ : X → H)
    (stageLeft : ∀ a : ℕ,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : ∀ _a : ℕ,
      H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ a : ℕ, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft a (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight a h)) •
            stageLeft a v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun a : ℕ =>
          freeProCZCCompletedFoxSemidirectPrimePowerStageMap
            (ProC := ProC) (X := X) (H := H) ℓ N a
            (stageLeft a) (stageRight a) (hscalar a)))
    (stageBoundary : ∀ a : ℕ,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
    (hboundary :
      ∀ a : ℕ,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) N (ℓ ^ a) (stageLeft a v) =
            stageBoundary a
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hN_kernel : ∀ {w : FreeGroup X}, w ∈ N → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ a : ℕ, ∀ w : FreeGroup X,
        stageLeft a
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N (ℓ ^ a) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine
    boundaryCycles_subset_kernelClosure_of_stageMaps
      (ProC := ProC) φ (fun _ : ℕ => N) (fun a : ℕ => ℓ ^ a)
      stageLeft stageRight hscalar ?_ stageBoundary hboundary ?_ hderivative
  · simpa [freeProCZCCompletedFoxSemidirectPrimePowerStageMap] using hidentity_basis
  · intro _ w hw
    exact hN_kernel hw

omit [Fact (0 < ℓ)] in
/-- Closed-generated-target version of the prime-power stage-map density theorem. -/
theorem boundaryCycles_subset_closedGenTarget_of_ppStageMaps
    [Fintype X] (φ : X → H)
    (stageLeft : ∀ a : ℕ,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : ∀ _a : ℕ,
      H →* finiteFoxStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ a : ℕ, ∀ (h : H)
        (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft a (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N) (stageRight a h)) •
            stageLeft a v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun a : ℕ =>
          freeProCZCCompletedFoxSemidirectPrimePowerStageMap
            (ProC := ProC) (X := X) (H := H) ℓ N a
            (stageLeft a) (stageRight a) (hscalar a)))
    (stageBoundary : ∀ a : ℕ,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+
        finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
    (hboundary :
      ∀ a : ℕ,
        ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
          finiteFoxStageFoxBoundary (X := X) N (ℓ ^ a) (stageLeft a v) =
            stageBoundary a
              (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v))
    (hN_kernel : ∀ {w : FreeGroup X}, w ∈ N → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ a : ℕ, ∀ w : FreeGroup X,
        stageLeft a
          (zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (FreeGroup.lift φ) w) =
          finiteFoxStageDerivativeVector (X := X) N (ℓ ^ a) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (boundaryCycles_subset_kernelClosure_of_ppStageMaps
        (ProC := ProC) (X := X) (H := H) ℓ N φ
        stageLeft stageRight hscalar hidentity_basis stageBoundary hboundary hN_kernel
        hderivative)

end PrimePowerStageMaps

end

end FoxDifferential
