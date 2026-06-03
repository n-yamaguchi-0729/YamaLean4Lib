import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.AddCommGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/System/Ring/Multiplicative.lean
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

instance instOnePrimePowerCompletedGroupAlgebra : One (PrimePowerCompletedGroupAlgebra ℓ G) where
  one := ⟨fun i => (1 : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (1 : PrimePowerCompletedGroupAlgebraStage ℓ G j) = 1
    exact map_one _⟩

instance instMulPrimePowerCompletedGroupAlgebra : Mul (PrimePowerCompletedGroupAlgebra ℓ G) where
  mul x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) *
            (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) *
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j) := by
            rw [map_mul]
      _ =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i) := by
            exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

instance instNatCastPrimePowerCompletedGroupAlgebra :
    NatCast (PrimePowerCompletedGroupAlgebra ℓ G) where
  natCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (n : PrimePowerCompletedGroupAlgebraStage ℓ G j) = n
    exact map_natCast _ _⟩

instance instIntCastPrimePowerCompletedGroupAlgebra :
    IntCast (PrimePowerCompletedGroupAlgebra ℓ G) where
  intCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (n : PrimePowerCompletedGroupAlgebraStage ℓ G j) = n
    exact map_intCast _ _⟩

instance instRingPrimePowerCompletedGroupAlgebraStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Ring ((primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraSystem, PrimePowerCompletedGroupAlgebraStage]
  infer_instance

instance instRingPrimePowerCompletedGroupAlgebraFamily :
    Ring
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) :=
  inferInstance

instance instPowPrimePowerCompletedGroupAlgebra : Pow (PrimePowerCompletedGroupAlgebra ℓ G) ℕ where
  pow x n := ⟨fun i => (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) ^ n, by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) ^ n) =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_one_primePowerCompletedGroupAlgebra :
    ((1 : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (1 :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_mul_primePowerCompletedGroupAlgebra
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((x * y : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (x * y :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_natCast_primePowerCompletedGroupAlgebra
    (n : ℕ) :
    ((n : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_intCast_primePowerCompletedGroupAlgebra
    (n : ℤ) :
    ((n : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_pow_primePowerCompletedGroupAlgebra
    (x : PrimePowerCompletedGroupAlgebra ℓ G) (n : ℕ) :
    ((x ^ n : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (x ^ n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

instance instRingPrimePowerCompletedGroupAlgebra :
    Ring (PrimePowerCompletedGroupAlgebra ℓ G) :=
  Function.Injective.ring
    (fun x : PrimePowerCompletedGroupAlgebra ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_one_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_mul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (fun n x => coe_nsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) n x)
    (fun n x => coe_zsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) n x)
    (fun x n => coe_pow_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) x n)
    (by
      intro n
      exact coe_natCast_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) n)
    (by
      intro z
      exact coe_intCast_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) z)

end

end FoxDifferential
