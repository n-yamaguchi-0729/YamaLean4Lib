import FoxDifferential.Completed.FiniteStage.PrimePower.System.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Limit/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- Inverse limit of the prime-power finite Fox source group-algebra system. -/
abbrev FiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) : Type u :=
  (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).inverseLimit

/-- Inverse limit of the prime-power finite Fox target group-algebra system. -/
abbrev FiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] : Type u :=
  (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).inverseLimit

/-- Forget a source inverse-limit element to its compatible family of source stages. -/
def finiteFoxStagePrimePowerSourceLimitToFamily
    (N : Subgroup (FreeGroup X)) :
    FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →
      ((a : ℕ) → finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a) :=
  fun z a => z.1 a

/-- Forget a target inverse-limit element to its compatible family of target stages. -/
def finiteFoxStagePrimePowerTargetLimitToFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N →
      ((a : ℕ) → finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a) :=
  fun z a => z.1 a

omit [DecidableEq X] in
/-- The family map out of the source inverse limit is injective. -/
theorem finiteFoxStagePrimePowerSourceLimitToFamily_injective
    (N : Subgroup (FreeGroup X)) :
    Function.Injective
      (finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N) := by
  intro x y h
  apply Subtype.ext
  funext a
  exact congrFun h a

omit [DecidableEq X] in
/-- The family map out of the target inverse limit is injective. -/
theorem finiteFoxStagePrimePowerTargetLimitToFamily_injective
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Function.Injective
      (finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N) := by
  intro x y h
  apply Subtype.ext
  funext a
  exact congrFun h a




end

end FoxDifferential
