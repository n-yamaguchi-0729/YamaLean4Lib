import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.AddCommGroup
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.CoeffMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Completion/Target.lean
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


/-- The canonical additive map from the prime-power target inverse limit to the completed group
algebra of the finite-stage target quotient. -/
def finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)] :
    AddMonoidHom
      (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
      (PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N)) where
  toFun z :=
    ⟨fun i =>
        modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
          (finiteFoxStageTargetQuotient (X := X) N) i.2
          ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 z),
      by
        intro i j hij
        change primePowerCompletedGroupAlgebraTransition
            (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) hij
            (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
              (finiteFoxStageTargetQuotient (X := X) N) j.2
              ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
            (finiteFoxStageTargetQuotient (X := X) N) i.2
            ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 z)
        rw [primePowerCompletedGroupAlgebraTransition_eq, RingHom.comp_apply]
        have hstage := congrFun
          (congrArg DFunLike.coe
            (modNCompletedGroupAlgebraStageMap_compatible
          (n := ℓ ^ j.1) (G := finiteFoxStageTargetQuotient (X := X) N)
          (U := i.2) (V := j.2) hij.2))
          ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z)
        change modNCompletedGroupAlgebraTransition (ℓ ^ j.1)
            (finiteFoxStageTargetQuotient (X := X) N) hij.2
            (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
              (finiteFoxStageTargetQuotient (X := X) N) j.2
              ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
            (finiteFoxStageTargetQuotient (X := X) N) i.2
            ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z) at hstage
        rw [hstage]
        rw [finiteFoxStagePrimePowerTargetStageMap_coeffMap
          (ℓ := ℓ) (X := X) N hij.1 i.2]
        exact congrArg
          (modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
            (finiteFoxStageTargetQuotient (X := X) N) i.2)
          ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection_compatible
            z i.1 j.1 hij.1)⟩
  map_zero' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ
      (finiteFoxStageTargetQuotient (X := X) N)).ext
    intro i
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1
          (0 : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)) = 0
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        (0 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1) = 0
    exact map_zero _
  map_add' x y := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ
      (finiteFoxStageTargetQuotient (X := X) N)).ext
    intro i
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 (x + y)) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) +
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) +
          (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
            (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) +
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
    exact map_add _ _ _

omit [DecidableEq X] in
/-- Projection formula for the map from the prime-power target limit to the completed target group
algebra. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (z : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (i : PrimePowerCompletedGroupAlgebraIndex (finiteFoxStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := finiteFoxStageTargetQuotient (X := X) N) i
        (finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
          ℓ (X := X) N z) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (finiteFoxStageTargetQuotient (X := X) N) i.2
        ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 z) := rfl

omit [DecidableEq X] in
/-- The target-limit-to-completed-group-algebra map preserves one. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_one
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)] :
    finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (1 : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) =
      (1 : PrimePowerCompletedGroupAlgebra ℓ
        (finiteFoxStageTargetQuotient (X := X) N)) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro i
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1
        (1 : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)) = 1
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      (1 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1) = 1
  exact map_one _

omit [DecidableEq X] in
/-- The target-limit-to-completed-group-algebra map preserves multiplication. -/
@[simp 900]
theorem finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra_mul
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (x y : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N (x * y) =
      finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
          ℓ (X := X) N x *
        finiteFoxStagePrimePowerTargetLimitToCompletedGroupAlgebra
          ℓ (X := X) N y := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (finiteFoxStageTargetQuotient (X := X) N)).ext
  intro i
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 (x * y)) =
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) *
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
        (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) *
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
          (finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)) =
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) *
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (finiteFoxStageTargetQuotient (X := X) N) i.2
      ((finiteFoxStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
  exact map_mul _ _ _



end

end FoxDifferential
