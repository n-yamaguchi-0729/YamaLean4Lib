import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.AddCommGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/InClass/System/Ring/Multiplicative.lean
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

instance instOnePrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    One (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  one := ⟨fun i => (1 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (1 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = 1
    exact map_one _⟩

instance instMulPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Mul (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  mul x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) *
            (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) *
        primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j) := by
            rw [map_mul]
      _ =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i) := by
            exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

instance instNatCastPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    NatCast (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  natCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = n
    exact map_natCast _ _⟩

instance instIntCastPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    IntCast (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  intCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = n
    exact map_intCast _ _⟩

instance instPowPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Pow (PrimePowerCompletedGroupAlgebraInClass ℓ G C) ℕ where
  pow x n := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) ^ n, by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) ^ n) =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_one_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    ((1 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (1 :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_mul_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((x * y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (x * y :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_natCast_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (n : ℕ) :
    ((n : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_intCast_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (n : ℤ) :
    ((n : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_pow_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) (n : ℕ) :
    ((x ^ n : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (x ^ n :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

instance instRingPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Ring (PrimePowerCompletedGroupAlgebraInClass ℓ G C) :=
  Function.Injective.ring
    (fun x : PrimePowerCompletedGroupAlgebraInClass ℓ G C =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_one_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_add_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_mul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_neg_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_sub_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (fun n x => coe_nsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C n x)
    (fun n x => coe_zsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C n x)
    (fun x n => coe_pow_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C x n)
    (by
      intro n
      exact coe_natCast_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C n)
    (by
      intro z
      exact coe_intCast_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C z)

end

end FoxDifferential
