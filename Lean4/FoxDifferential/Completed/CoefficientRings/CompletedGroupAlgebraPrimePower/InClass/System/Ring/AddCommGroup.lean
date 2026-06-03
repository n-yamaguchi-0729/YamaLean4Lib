import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/InClass/System/Ring/AddCommGroup.lean
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

instance instZeroPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Zero (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  zero := ⟨fun i => (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = 0
    exact map_zero _⟩

instance instAddPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Add (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  add x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) +
            (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) +
        primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j) := by
            rw [map_add]
      _ =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i) := by
            exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

instance instAddZeroClassPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddZeroClass (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    change (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) +
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) =
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext i
    change (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) +
      (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    simp only [add_zero]

instance instNegPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Neg (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  neg x := ⟨fun i => -(show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (-(show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j)) =
      -(show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

instance instSubPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Sub (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  sub x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) -
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j)) =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

instance instSMulNatPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℕ (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  smul m x := ⟨fun i =>
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

instance instSMulIntPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℤ (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  smul m x := ⟨fun i =>
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zero_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    ((0 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_add_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((x + y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_neg_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((-x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_sub_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((x - y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_nsmul_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((m • x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zsmul_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((m • x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = m • x := by
  funext i
  rfl

instance instAddCommGroupPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddCommGroup (PrimePowerCompletedGroupAlgebraInClass ℓ G C) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedGroupAlgebraInClass ℓ G C =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_add_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_neg_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_sub_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (fun x m => coe_nsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C m x)
    (fun x m => coe_zsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C m x)

end

end FoxDifferential
