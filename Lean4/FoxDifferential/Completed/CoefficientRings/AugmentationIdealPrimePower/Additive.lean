import FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Stage

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/AugmentationIdealPrimePower/Additive.lean
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

instance instZeroPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Zero (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  zero := ⟨fun i =>
    (0 : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G j) = 0
    exact map_zero _⟩

instance instAddPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Add (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  add x y := ⟨fun i =>
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
        from x.1 i) +
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from y.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j) +
          ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from y.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j)) =
      (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i) +
        ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from y.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_add]
    exact congrArg₂ HAdd.hAdd
      (congrArg Subtype.val (x.2 i j hij))
      (congrArg Subtype.val (y.2 i j hij))⟩

instance instAddZeroClassPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    AddZeroClass (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) +
      ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal
        (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i) +
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i)
    simp only [add_zero]

instance instNegPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Neg (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  neg x := ⟨fun i =>
    -(show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
      from x.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (-(((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      -(((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_neg]
    exact congrArg Neg.neg (congrArg Subtype.val (x.2 i j hij))⟩

instance instSubPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Sub (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  sub x y := ⟨fun i =>
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
        from x.1 i) -
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from y.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        ((((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j)) -
          (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from y.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      ((((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
            from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i)) -
        (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
            from y.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i)))
    rw [map_sub]
    exact congrArg₂ HSub.hSub
      (congrArg Subtype.val (x.2 i j hij))
      (congrArg Subtype.val (y.2 i j hij))⟩

instance instSMulNatPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    SMul ℕ (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  smul m x := ⟨fun i =>
    m • (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
      from x.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_nsmul]
    exact congrArg (m • ·) (congrArg Subtype.val (x.2 i j hij))⟩

instance instSMulIntPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    SMul ℤ (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  smul m x := ⟨fun i =>
    m • (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
      from x.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_zsmul]
    exact congrArg (m • ·) (congrArg Subtype.val (x.2 i j hij))⟩

instance instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraAugmentationIdealSystem]
  infer_instance

instance instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) :=
  inferInstance

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zero_primePowerCompletedGroupAlgebraAugmentationIdeal :
    ((0 : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_add_primePowerCompletedGroupAlgebraAugmentationIdeal
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((x + y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_neg_primePowerCompletedGroupAlgebraAugmentationIdeal
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((-x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_sub_primePowerCompletedGroupAlgebraAugmentationIdeal
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((x - y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_nsmul_primePowerCompletedGroupAlgebraAugmentationIdeal
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zsmul_primePowerCompletedGroupAlgebraAugmentationIdeal
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = m • x := by
  funext i
  rfl

instance instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    AddCommGroup (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (fun x m => coe_nsmul_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) m x)
    (fun x m => coe_zsmul_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) m x)


end

end FoxDifferential
