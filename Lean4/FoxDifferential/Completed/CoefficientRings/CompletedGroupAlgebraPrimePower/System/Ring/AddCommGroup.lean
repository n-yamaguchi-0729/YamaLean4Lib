import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/System/Ring/AddCommGroup.lean
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

instance instZeroPrimePowerCompletedGroupAlgebra : Zero (PrimePowerCompletedGroupAlgebra ℓ G) where
  zero := ⟨fun i => (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G j) = 0
    exact map_zero _⟩

instance instAddPrimePowerCompletedGroupAlgebra : Add (PrimePowerCompletedGroupAlgebra ℓ G) where
  add x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) +
            (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) +
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j) := by
            rw [map_add]
      _ =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i) := by
            exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

instance instAddZeroClassPrimePowerCompletedGroupAlgebra :
    AddZeroClass (PrimePowerCompletedGroupAlgebra ℓ G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    change (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) +
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext i
    change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    simp only [add_zero]

instance instNegPrimePowerCompletedGroupAlgebra : Neg (PrimePowerCompletedGroupAlgebra ℓ G) where
  neg x := ⟨fun i => -(show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (-(show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      -(show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

instance instSubPrimePowerCompletedGroupAlgebra : Sub (PrimePowerCompletedGroupAlgebra ℓ G) where
  sub x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) -
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j)) =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

instance instSMulNatPrimePowerCompletedGroupAlgebra :
    SMul ℕ (PrimePowerCompletedGroupAlgebra ℓ G) where
  smul m x := ⟨fun i => m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

instance instSMulIntPrimePowerCompletedGroupAlgebra :
    SMul ℤ (PrimePowerCompletedGroupAlgebra ℓ G) where
  smul m x := ⟨fun i => m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

instance instAddCommGroupPrimePowerCompletedGroupAlgebraStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraSystem, PrimePowerCompletedGroupAlgebraStage]
  infer_instance

instance instAddCommGroupPrimePowerCompletedGroupAlgebraFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) :=
  inferInstance

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zero_primePowerCompletedGroupAlgebra :
    ((0 : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_add_primePowerCompletedGroupAlgebra
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((x + y : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_neg_primePowerCompletedGroupAlgebra
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((-x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_sub_primePowerCompletedGroupAlgebra
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((x - y : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_nsmul_primePowerCompletedGroupAlgebra
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zsmul_primePowerCompletedGroupAlgebra
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = m • x := by
  funext i
  rfl

instance instAddCommGroupPrimePowerCompletedGroupAlgebra :
    AddCommGroup (PrimePowerCompletedGroupAlgebra ℓ G) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedGroupAlgebra ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (fun x m => coe_nsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) m x)
    (fun x m => coe_zsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) m x)

end

end FoxDifferential
