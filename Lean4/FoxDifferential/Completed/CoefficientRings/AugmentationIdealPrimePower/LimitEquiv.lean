import FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Module

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/AugmentationIdealPrimePower/LimitEquiv.lean
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

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_zero
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) = 0 := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_add
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (x + y) =
      primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x +
        primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_neg
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (-x) =
      -primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_sub
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (x - y) =
      primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x -
        primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は自然数倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_nsmul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (m • x) =
      m • primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は整数倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_zsmul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (m • x) =
      m • primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影はスカラー倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_smul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (a • x) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

/-- A prime-power augmentation-kernel point determines a compatible family in the finite-stage
augmentation ideals. -/
def toPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) →
      PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G := by
  intro x
  refine ⟨fun i => ⟨primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x.1, ?_⟩, ?_⟩
  · exact (mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
      (ℓ := ℓ) (G := G) (i := i)
      (x := primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x.1)).2
      ((mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall
        (ℓ := ℓ) (G := G) (x := x.1)).1 x.2 i)
  · intro i j hij
    apply Subtype.ext
    exact (primePowerCompletedGroupAlgebraSystem ℓ G).projection_compatible x.1 i j hij

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限段階射影がaugmentation ideal の元を基礎にある完備群環へ戻す写像の値を記述することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_to
    (x : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G))
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    ((primePowerCompletedGroupAlgebraAugmentationIdealProjection
        (ℓ := ℓ) (G := G) i
        (toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x)) :
      PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x.1 := rfl

/-- A compatible family of prime-power finite-stage augmentation-ideal elements determines a
prime-power augmentation-kernel point. -/
def ofPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →
      PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) := by
  intro x
  let y : PrimePowerCompletedGroupAlgebra ℓ G := ⟨fun i => (x.1 i).1, by
    intro i j hij
    exact congrArg Subtype.val (x.2 i j hij)⟩
  refine ⟨y, ?_⟩
  exact (mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall
    (ℓ := ℓ) (G := G) (x := y)).2 (fun i =>
      (mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
        (ℓ := ℓ) (G := G) (i := i) (x := (x.1 i).1)).1 (x.1 i).2)

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限段階射影が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G)
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
          (ℓ := ℓ) (G := G) x).1 =
      ((primePowerCompletedGroupAlgebraAugmentationIdealProjection
          (ℓ := ℓ) (G := G) i x) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i) := rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像がaugmentation ideal の元を基礎にある完備群環へ戻す写像の値を記述することを述べる。 -/
@[simp]
theorem ofPrimePowerCompletedGroupAlgebraAugmentationIdeal_to
    (x : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G)) :
    ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
        (toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x) = x := by
  apply Subtype.ext
  apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
  intro i
  rfl

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of. -/
@[simp]
theorem toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
        (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x) = x := by
  apply (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).ext
  intro i
  apply Subtype.ext
  rfl

/-- The prime-power completed augmentation kernel is canonically equivalent to the inverse limit of
the prime-power finite-stage augmentation ideals. -/
def primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit :
    PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) ≃
      PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G where
  toFun := toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
  invFun := ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
  left_inv := ofPrimePowerCompletedGroupAlgebraAugmentationIdeal_to (ℓ := ℓ) (G := G)
  right_inv := toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_apply. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G)) :
    primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit
        (ℓ := ℓ) (G := G) x =
      toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x := rfl

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_symm_apply. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_symm_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    (primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit
        (ℓ := ℓ) (G := G)).symm x =
      ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x := rfl

end

end FoxDifferential
