import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Module

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Augmentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed coefficient algebras

Coefficient algebras, residue stages, and completed group-algebra maps are kept as the scalar layer for completed Fox calculus.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The prime-power completed group algebra carries a canonical augmentation to the corresponding
coefficient inverse limit. -/
def primePowerCompletedGroupAlgebraAugmentation :
    PrimePowerCompletedGroupAlgebra ℓ G → PrimePowerCompletedCoeff ℓ G := by
  intro x
  refine ⟨fun i => ?_, ?_⟩
  · letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    exact modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2 (x.1 i)
  · intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    calc
      modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ j.1) G j.2 (x.1 j))
        =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij (x.1 j)) := by
          symm
          exact congrFun
            (congrArg DFunLike.coe
              (primePowerCompletedGroupAlgebraStageAugmentation_comp_transition
                (ℓ := ℓ) (G := G) hij)) (x.1 j)
      _ =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2 (x.1 i) := by
          have hx :
              primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij (x.1 j) = x.1 i :=
            x.2 i j hij
          exact congrArg (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2) hx

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限段階射影が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_augmentation
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x) := rfl

omit [Fact (0 < ℓ)] in
/-- Stagewise augmentations of a completed group-algebra element are independent of the
finite-quotient component once the prime-power exponent is fixed. -/
theorem primePowerCompletedGroupAlgebraStageAugmentation_eq_of_same_exponent
    (a : ℕ) (U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ a) G U
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) (a, U) x) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ a) G V
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) (a, V) x) := by
  simpa [primePowerCompletedCoeffProjection_augmentation] using
    primePowerCompletedCoeffProjection_eq_of_same_exponent
      (ℓ := ℓ) (G := G) a U V
      (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x)

end

end FoxDifferential
