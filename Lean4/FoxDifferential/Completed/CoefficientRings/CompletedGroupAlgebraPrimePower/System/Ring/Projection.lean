import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.GroupLike

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/System/Ring/Projection.lean
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

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限段階射影が自然数の標準像を各有限段階で同じ自然数の標準像として計算することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_natCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℕ) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedGroupAlgebra ℓ G) = n := by
  change (n : PrimePowerCompletedGroupAlgebraStage ℓ G i) = n
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限段階射影が整数の標準像を各有限段階で同じ整数の標準像として計算することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_intCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℤ) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedGroupAlgebra ℓ G) = n := by
  change (n : PrimePowerCompletedGroupAlgebraStage ℓ G i) = n
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_zero
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedGroupAlgebra ℓ G) = 0 := by
  change (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) = 0
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_add
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x + y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x +
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (x + y).1 i) =
    (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_neg
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (-x) =
      -primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (-x).1 i) =
    -(show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_sub
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x - y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x -
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (x - y).1 i) =
    (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) -
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- Composition lemma primePowerCompletedGroupAlgebraStageAugmentation_comp_transition. -/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentation_comp_transition
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2).comp
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ j.1) G j.2) := by
  rw [primePowerCompletedGroupAlgebraTransition_eq]
  rw [← RingHom.comp_assoc]
  rw [modNCompletedGroupAlgebraStageAugmentation_comp_coeffMap]
  rw [RingHom.comp_assoc]
  rw [modNCompletedGroupAlgebraStageAugmentation_compatible]

end

end FoxDifferential
