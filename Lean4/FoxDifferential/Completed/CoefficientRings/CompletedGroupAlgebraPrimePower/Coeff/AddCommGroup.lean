import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.System

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Coeff/AddCommGroup.lean
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

instance instZeroPrimePowerCompletedCoeff : Zero (PrimePowerCompletedCoeff ℓ G) where
  zero := ⟨fun i => (0 : ZMod (ℓ ^ i.1)), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    exact map_zero
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1))⟩

instance instAddPrimePowerCompletedCoeff : Add (PrimePowerCompletedCoeff ℓ G) where
  add x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) + (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

instance instAddZeroClassPrimePowerCompletedCoeff :
    AddZeroClass (PrimePowerCompletedCoeff ℓ G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    change (0 : ZMod (ℓ ^ i.1)) + (show ZMod (ℓ ^ i.1) from x.1 i) =
      (show ZMod (ℓ ^ i.1) from x.1 i)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext i
    change (show ZMod (ℓ ^ i.1) from x.1 i) + (0 : ZMod (ℓ ^ i.1)) =
      (show ZMod (ℓ ^ i.1) from x.1 i)
    simp only [add_zero]

instance instNegPrimePowerCompletedCoeff : Neg (PrimePowerCompletedCoeff ℓ G) where
  neg x := ⟨fun i => -(show ZMod (ℓ ^ i.1) from x.1 i), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (-(show ZMod (ℓ ^ j.1) from x.1 j)) =
      -(show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

instance instSubPrimePowerCompletedCoeff : Sub (PrimePowerCompletedCoeff ℓ G) where
  sub x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) - (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

instance instSMulNatPrimePowerCompletedCoeff : SMul ℕ (PrimePowerCompletedCoeff ℓ G) where
  smul m x := ⟨fun i => m • (show ZMod (ℓ ^ i.1) from x.1 i), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (m • (show ZMod (ℓ ^ j.1) from x.1 j)) =
      m • (show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

instance instSMulIntPrimePowerCompletedCoeff : SMul ℤ (PrimePowerCompletedCoeff ℓ G) where
  smul m x := ⟨fun i => m • (show ZMod (ℓ ^ i.1) from x.1 i), by
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (m • (show ZMod (ℓ ^ j.1) from x.1 j)) =
      m • (show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

instance instAddCommGroupPrimePowerCompletedCoeffStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedCoeffSystem ℓ G).X i) := by
  dsimp [primePowerCompletedCoeffSystem]
  infer_instance

instance instAddCommGroupPrimePowerCompletedCoeffFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) :=
  inferInstance

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zero_primePowerCompletedCoeff :
    ((0 : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_add_primePowerCompletedCoeff
    (x y : PrimePowerCompletedCoeff ℓ G) :
    ((x + y : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_neg_primePowerCompletedCoeff
    (x : PrimePowerCompletedCoeff ℓ G) :
    ((-x : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_sub_primePowerCompletedCoeff
    (x y : PrimePowerCompletedCoeff ℓ G) :
    ((x - y : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_nsmul_primePowerCompletedCoeff
    (m : ℕ) (x : PrimePowerCompletedCoeff ℓ G) :
    ((m • x : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 係数側の射影または係数変更写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zsmul_primePowerCompletedCoeff
    (m : ℤ) (x : PrimePowerCompletedCoeff ℓ G) :
    ((m • x : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = m • x := by
  funext i
  rfl

instance instAddCommGroupPrimePowerCompletedCoeff :
    AddCommGroup (PrimePowerCompletedCoeff ℓ G) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedCoeff ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (fun x m => coe_nsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) m x)
    (fun x m => coe_zsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) m x)

end

end FoxDifferential
