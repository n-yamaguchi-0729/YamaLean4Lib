import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.AddCommGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Coeff/Ring.lean
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

instance instOnePrimePowerCompletedCoeff : One (PrimePowerCompletedCoeff ℓ G) where
  one := ⟨fun i => (1 : ZMod (ℓ ^ i.1)), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    exact map_one
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1))⟩

instance instMulPrimePowerCompletedCoeff : Mul (PrimePowerCompletedCoeff ℓ G) where
  mul x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) * (show ZMod (ℓ ^ i.1) from y.1 i), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) * (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) * (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_mul]
    exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

instance instNatCastPrimePowerCompletedCoeff : NatCast (PrimePowerCompletedCoeff ℓ G) where
  natCast n := ⟨fun i => (n : ZMod (ℓ ^ i.1)), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    exact map_natCast
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)) n⟩

instance instIntCastPrimePowerCompletedCoeff : IntCast (PrimePowerCompletedCoeff ℓ G) where
  intCast n := ⟨fun i => (n : ZMod (ℓ ^ i.1)), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    exact map_intCast
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)) n⟩

instance instCommRingPrimePowerCompletedCoeffStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    CommRing ((primePowerCompletedCoeffSystem ℓ G).X i) := by
  dsimp [primePowerCompletedCoeffSystem]
  infer_instance

instance instCommRingPrimePowerCompletedCoeffFamily :
    CommRing
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) :=
  inferInstance

instance instPowPrimePowerCompletedCoeff : Pow (PrimePowerCompletedCoeff ℓ G) ℕ where
  pow x n := ⟨fun i => (show ZMod (ℓ ^ i.1) from x.1 i) ^ n, by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) ^ n) =
      (show ZMod (ℓ ^ i.1) from x.1 i) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_one_primePowerCompletedCoeff :
    ((1 : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (1 :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_mul_primePowerCompletedCoeff
    (x y : PrimePowerCompletedCoeff ℓ G) :
    ((x * y : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (x * y :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_natCast_primePowerCompletedCoeff
    (n : ℕ) :
    ((n : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_intCast_primePowerCompletedCoeff
    (n : ℤ) :
    ((n : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_pow_primePowerCompletedCoeff
    (x : PrimePowerCompletedCoeff ℓ G) (n : ℕ) :
    ((x ^ n : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (x ^ n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

instance instCommRingPrimePowerCompletedCoeff :
    CommRing (PrimePowerCompletedCoeff ℓ G) :=
  Function.Injective.commRing
    (fun x : PrimePowerCompletedCoeff ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_one_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_mul_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (fun n x => coe_nsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) n x)
    (fun n x => coe_zsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) n x)
    (fun x n => coe_pow_primePowerCompletedCoeff (ℓ := ℓ) (G := G) x n)
    (by
      intro n
      exact coe_natCast_primePowerCompletedCoeff (ℓ := ℓ) (G := G) n)
    (by
      intro z
      exact coe_intCast_primePowerCompletedCoeff (ℓ := ℓ) (G := G) z)

end

end FoxDifferential
