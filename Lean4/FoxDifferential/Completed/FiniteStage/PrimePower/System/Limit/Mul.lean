import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Limit/Mul.lean
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


/-- Multiplicative identity on the prime-power finite Fox source inverse limit. -/
instance instOneFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    One (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  one := ⟨fun a => (1 : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (1 : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) = 1
      exact map_one _⟩

/-- Multiplication on the prime-power finite Fox source inverse limit. -/
instance instMulFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Mul (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  mul x y := ⟨fun a =>
      (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
        (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          ((show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) *
            (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
          (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_mul]
      exact congrArg₂ HMul.hMul (x.2 a b hab) (y.2 a b hab)⟩

/-- Multiplicative identity on the prime-power finite Fox target inverse limit. -/
instance instOneFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    One (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  one := ⟨fun a => (1 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (1 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) = 1
      exact map_one _⟩

/-- Multiplication on the prime-power finite Fox target inverse limit. -/
instance instMulFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Mul (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  mul x y := ⟨fun a =>
      (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          ((show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) *
            (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
          (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_mul]
      exact congrArg₂ HMul.hMul (x.2 a b hab) (y.2 a b hab)⟩

omit [DecidableEq X] in
/-- The source-limit family of one is the one family. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceLimitToFamily_one
    (N : Subgroup (FreeGroup X)) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N 1 = 1 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves multiplication. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceLimitToFamily_mul
    (N : Subgroup (FreeGroup X))
    (x y : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (x * y) =
      finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x *
        finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family of one is the one family. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetLimitToFamily_one
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N 1 = 1 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves multiplication. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetLimitToFamily_mul
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x y : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (x * y) =
      finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x *
        finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl




end

end FoxDifferential
