import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Target

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Derivative/Limit.lean
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


/-- Naturality of the finite-stage group-algebra Fox derivative along a prime-power transition. -/
theorem finiteFoxStagePrimePowerGroupAlgebraDerivative_transition
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) (i : X)
    (x : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N
        (primePow_dvd_primePow (ℓ := ℓ) hab)
        (finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ b) i x) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        (finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab x) := by
  exact finiteFoxStageGroupAlgebraDerivative_powerCoeff_natural
    (X := X) N (primePow_dvd_primePow (ℓ := ℓ) hab) i x

/-- The inverse-limit Fox derivative obtained by applying the finite-stage derivative at every
prime-power stage. -/
def finiteFoxStagePrimePowerDerivativeLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) :
    FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →
      FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N :=
  (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).inverseLimitLift
    (fun a z =>
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z))
    (by
      intro a b hab
      funext z
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ b) i
            ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection b z)) =
        finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)
      rw [finiteFoxStagePrimePowerTargetTransition,
        finiteFoxStagePrimePowerGroupAlgebraDerivative_transition]
      congr 1
      exact
        (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection_compatible
          z a b hab)

/-- Projection formula for the prime-power derivative limit. -/
@[simp]
theorem finiteFoxStagePrimePowerDerivativeLimit_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (z : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) (a : ℕ) :
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z) := rfl

/-- The prime-power finite-stage derivative limit is uniquely determined by its projections to
all finite stages. -/
theorem finiteFoxStagePrimePowerDerivativeLimit_unique
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (f : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →
      FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (hf : ∀ z a,
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (f z) =
        finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)) :
    f = finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i := by
  funext z
  apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change
    (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a (f z) =
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z)
  rw [hf, finiteFoxStagePrimePowerDerivativeLimit_projection]

/-- The finite-stage fundamental formula, expressed after projecting a prime-power derivative
limit to one stage. -/
theorem finiteFoxStagePrimePowerDerivativeLimit_fundamental_formula_projection
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (z : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) (a : ℕ) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ a)
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z) -
        algebraMap (ModNCompletedCoeff (ℓ ^ a))
          (finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N (ℓ ^ a)
            ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)) =
      ∑ i : X,
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z)) *
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (finiteFoxStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rw [finiteFoxStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    (X := X) (N := N) (n := ℓ ^ a)
    ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteFoxStagePrimePowerDerivativeLimit_projection]

/-- Additive-homomorphism version of the prime-power derivative limit. -/
def finiteFoxStagePrimePowerDerivativeLimitAddHom
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) :
    FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →+
      FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N where
  toFun := finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
  map_zero' := by
    apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i 0) =
        (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (0 : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    rw [finiteFoxStagePrimePowerDerivativeLimit_projection]
    change finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
          (0 : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N)) = 0
    change finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        (0 : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a) = 0
    exact map_zero _
  map_add' x y := by
    apply finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i (x + y)) =
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i x)) +
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i y))
    rw [finiteFoxStagePrimePowerDerivativeLimit_projection,
      finiteFoxStagePrimePowerDerivativeLimit_projection,
      finiteFoxStagePrimePowerDerivativeLimit_projection]
    change finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a (x + y)) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a x) +
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a y)
    change finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a x) +
          (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from
            (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a y)) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a x) +
      finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a y)
    exact map_add _ _ _

/-- Evaluation formula for the additive-homomorphism version of the derivative limit. -/
@[simp]
theorem finiteFoxStagePrimePowerDerivativeLimitAddHom_apply
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (z : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i z =
      finiteFoxStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z := rfl

/-- Additive maps into the prime-power finite-stage target limit are uniquely determined by the
finite-stage Fox derivative projection formula. -/
theorem finiteFoxStagePrimePowerDerivativeLimitAddHom_unique
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (f : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →+
      FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (hf : ∀ z a,
      (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (f z) =
        finiteFoxStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          ((finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)) :
    f = finiteFoxStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i := by
  apply AddMonoidHom.ext
  intro z
  exact congrFun
    (finiteFoxStagePrimePowerDerivativeLimit_unique (ℓ := ℓ) (X := X) N i f hf) z



end

end FoxDifferential
