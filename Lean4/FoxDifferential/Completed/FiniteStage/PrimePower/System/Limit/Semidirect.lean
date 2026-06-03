import FoxDifferential.Completed.FiniteStage.PrimePower.System.Semidirect

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Limit/Semidirect.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Inverse limits of prime-power finite Fox semidirect stages

This file exposes the limit object attached to the prime-power finite semidirect system and the
compatible kernel-word points living in that limit.  It is the finite-stage side of the eventual
completed semidirect projection map.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Inverse limit of the prime-power finite Fox semidirect stage system. -/
abbrev FiniteFoxStagePrimePowerSemidirectLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] : Type u :=
  (finiteFoxStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N).inverseLimit

/-- Forget a semidirect inverse-limit element to its compatible family of finite stages. -/
def finiteFoxStagePrimePowerSemidirectLimitToFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N →
      ((a : ℕ) → FiniteFoxStageSemidirect (X := X) N (ℓ ^ a)) :=
  fun z a => z.1 a

omit [DecidableEq X] in
/-- The family map out of the semidirect inverse limit is injective. -/
theorem finiteFoxStagePrimePowerSemidirectLimitToFamily_injective
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Function.Injective
      (finiteFoxStagePrimePowerSemidirectLimitToFamily (ℓ := ℓ) (X := X) N) := by
  intro x y h
  apply Subtype.ext
  funext a
  exact congrFun h a

/-- The `a`th finite-stage projection from the semidirect prime-power inverse limit. -/
def finiteFoxStagePrimePowerSemidirectLimitProjection
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N →
      FiniteFoxStageSemidirect (X := X) N (ℓ ^ a) :=
  (finiteFoxStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N).projection a

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStagePrimePowerSemidirectLimitProjection_apply
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (z : FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N) (a : ℕ) :
    finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z = z.1 a :=
  rfl

omit [DecidableEq X] in
/-- The finite-stage projections of a semidirect limit element are compatible with the
prime-power transition maps. -/
theorem finiteFoxStagePrimePowerSemidirectLimitProjection_transition
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b)
    (z : FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
        (finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N b z) =
      finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z := by
  exact (finiteFoxStagePrimePowerSemidirectSystem
    (ℓ := ℓ) (X := X) N).projection_compatible z a b hab

/-- Boundary-cycle condition for a prime-power semidirect limit element, read stagewise. -/
def finiteFoxStagePrimePowerSemidirectLimitBoundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Set (FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N) :=
  { z | ∀ a : ℕ,
      finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z ∈
        finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) }

omit [DecidableEq X] in
@[simp]
theorem mem_finiteFoxStagePrimePowerSemidirectLimitBoundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {z : FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N} :
    z ∈ finiteFoxStagePrimePowerSemidirectLimitBoundaryCycleSet (ℓ := ℓ) (X := X) N ↔
      ∀ a : ℕ,
        finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z ∈
          finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) :=
  Iff.rfl

/-- The compatible semidirect limit point represented by the finite kernel-word points for one
free-group word. -/
def finiteFoxStagePrimePowerSemidirectKernelWordPointLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) :
    FiniteFoxStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N :=
  ⟨fun a => finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w,
    by
      intro a b hab
      exact finiteFoxStagePrimePowerSemidirectTransition_kernelWordPoint
        (ℓ := ℓ) (X := X) N hab w⟩

@[simp]
theorem finiteFoxStagePrimePowerSemidirectKernelWordPointLimit_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    finiteFoxStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a
        (finiteFoxStagePrimePowerSemidirectKernelWordPointLimit
          (ℓ := ℓ) (X := X) N w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w :=
  rfl

/-- If `w` is a relation word, its compatible prime-power semidirect point is a stagewise
boundary cycle. -/
theorem finiteFoxStagePrimePowerSemidirectKernelWordPointLimit_mem_boundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {w : FreeGroup X} (hw : w ∈ N) :
    finiteFoxStagePrimePowerSemidirectKernelWordPointLimit (ℓ := ℓ) (X := X) N w ∈
      finiteFoxStagePrimePowerSemidirectLimitBoundaryCycleSet (ℓ := ℓ) (X := X) N := by
  intro a
  have hstage :
      finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w ∈
        finiteFoxStageSemidirectKernelWordDerivativeSet (X := X) N (ℓ ^ a) := by
    exact ⟨w, hw, rfl⟩
  rw [finiteFoxStagePrimePowerSemidirectKernelWordPointLimit_projection]
  exact finiteFoxStageSemidirectKernelWordDerivativeSet_subset_boundaryCycleSet
    (X := X) N (ℓ ^ a) hstage

end

end FoxDifferential
