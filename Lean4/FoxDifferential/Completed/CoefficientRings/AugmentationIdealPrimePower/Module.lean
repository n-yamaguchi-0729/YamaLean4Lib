import FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Additive

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/AugmentationIdealPrimePower/Module.lean
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
/-- 素冪係数段階で、有限段階間の遷移写像はスカラー倍と両立する。 -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_smul
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (a : ZMod (ℓ ^ j.1))
    (x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
    primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
        (ℓ := ℓ) (G := G) hij (a • x) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) •
        primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
          (ℓ := ℓ) (G := G) hij x := by
  apply Subtype.ext
  change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      ((a • x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
        PrimePowerCompletedGroupAlgebraStage ℓ G j) =
    (((modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) •
      primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
        (ℓ := ℓ) (G := G) hij x :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i)
  simpa using
    primePowerCompletedGroupAlgebraTransition_smul
      (ℓ := ℓ) (G := G) hij a
      ((x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
        PrimePowerCompletedGroupAlgebraStage ℓ G j)

instance instCommRingPrimePowerCompletedCoeffAugmentationIdealLocal :
    CommRing (PrimePowerCompletedCoeff ℓ G) := by
  infer_instance

instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGAAugmentationIdealFamily :
    SMul (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) where
  smul a x := fun i =>
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x i)

instance instModulePpCoeffPpGAAugIdealFamily :
    Module (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) where
  one_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedCoeff ℓ G)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) =
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
        (ℓ := ℓ) (G := G) i from x i)
    rw [primePowerCompletedCoeffProjection_one, one_smul]
  mul_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a * b)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i))
    rw [primePowerCompletedCoeffProjection_mul, mul_smul]
  smul_zero a := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (0 : primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i) = 0
    rw [smul_zero]
  smul_add a x y := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) +
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from y i)) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from y i)
    rw [smul_add]
  add_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a + b)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i)
    rw [primePowerCompletedCoeffProjection_add, add_smul]
  zero_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedCoeff ℓ G)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) = 0
    rw [primePowerCompletedCoeffProjection_zero, zero_smul]

instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    SMul (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  smul a x := ⟨fun i =>
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
          (ℓ := ℓ) (G := G) hij
          ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a) •
            (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
              from x.1 j)) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)) •
        primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
          (ℓ := ℓ) (G := G) hij
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) := by
            exact
              primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_smul
                (ℓ := ℓ) (G := G) hij
                (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)
                (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
                  (ℓ := ℓ) (G := G) j from x.1 j)
      _ =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x.1 i) := by
            exact congrArg₂ HSMul.hSMul (a.2 i j hij) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_smul_primePowerCompletedGroupAlgebraAugmentationIdeal
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    letI := instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraAugmentationIdeal
      (ℓ := ℓ) (G := G)
    ((a • x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) =
      a • (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) := by
  funext i
  change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) =
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i)
  rfl

instance instModulePpCoeffPpGAAugIdeal :
    Module (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :=
  Function.Injective.module (PrimePowerCompletedCoeff ℓ G)
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    Subtype.val_injective
    (coe_smul_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))


end

end FoxDifferential
