import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.Projection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Module.lean
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
/-- 素冪係数で定めた 遷移写像が関手的写像が有限段階射影と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_algebraMap
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (a : ZMod (ℓ ^ j.1)) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (algebraMap (ZMod (ℓ ^ j.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G j) a) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) := by
  rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
  classical
  rw [primePowerCompletedGroupAlgebraTransition_eq']
  simp only [modNCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, map_intCast]

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が関手的写像が有限段階射影と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentation_algebraMap
    (i : PrimePowerCompletedGroupAlgebraIndex G) (a : ZMod (ℓ ^ i.1)) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i) a) = a := by
  rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
  classical
  simp only [modNCompletedGroupAlgebraStageAugmentation, map_intCast]

/-- The coefficient inverse limit maps canonically into the completed group algebra by taking
the stagewise scalar units. -/
def primePowerCompletedCoeffToGroupAlgebra :
    PrimePowerCompletedCoeff ℓ G →+* PrimePowerCompletedGroupAlgebra ℓ G where
  toFun a := ⟨fun i =>
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (algebraMap (ZMod (ℓ ^ j.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G j)
          (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)
    rw [primePowerCompletedGroupAlgebraTransition_algebraMap]
    exact congrArg
      (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
      (a.2 i j hij)⟩
  map_one' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (1 : PrimePowerCompletedCoeff ℓ G))
      = 1
    rw [primePowerCompletedCoeffProjection_one]
    exact map_one (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
  map_mul' := by
    intro a b
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a * b)) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) *
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)
    rw [primePowerCompletedCoeffProjection_mul]
    exact
      map_mul
        (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)
  map_zero' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (0 : PrimePowerCompletedCoeff ℓ G))
      = 0
    rw [primePowerCompletedCoeffProjection_zero]
    exact map_zero (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
  map_add' := by
    intro a b
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a + b)) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) +
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)
    rw [primePowerCompletedCoeffProjection_add]
    exact
      map_add
        (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限段階射影が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_coeffToGroupAlgebra
    (i : PrimePowerCompletedGroupAlgebraIndex G) (a : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) a) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、有限段階間の遷移写像はスカラー倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_smul
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (a : ZMod (ℓ ^ j.1))
    (x : PrimePowerCompletedGroupAlgebraStage ℓ G j) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij (a • x) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) •
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij x := by
  rw [Algebra.smul_def, map_mul, primePowerCompletedGroupAlgebraTransition_algebraMap]
  rw [← Algebra.smul_def]

instance instCommRingPrimePowerCompletedCoeffGroupAlgebraLocal :
    CommRing (PrimePowerCompletedCoeff ℓ G) := by
  infer_instance

instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraFamily :
    SMul (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) where
  smul a x := fun i =>
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i)

instance instModulePrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraFamily :
    Module (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) where
  one_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedCoeff ℓ G)) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i)
    rw [primePowerCompletedCoeffProjection_one, one_smul]
  mul_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a * b)) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i))
    rw [primePowerCompletedCoeffProjection_mul, mul_smul]
  smul_zero a := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) = 0
    rw [smul_zero]
  smul_add a x y := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) +
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y i)) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y i)
    rw [smul_add]
  add_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a + b)) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i)
    rw [primePowerCompletedCoeffProjection_add, add_smul]
  zero_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedCoeff ℓ G)) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) = 0
    rw [primePowerCompletedCoeffProjection_zero, zero_smul]

instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebra :
    SMul (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebra ℓ G) where
  smul a x := ⟨fun i =>
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a) •
            (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)) •
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) := by
            simpa using
              primePowerCompletedGroupAlgebraTransition_smul
                (ℓ := ℓ) (G := G) hij
                (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)
                (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)
      _ =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) := by
            exact congrArg₂ HSMul.hSMul (a.2 i j hij) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_smul_primePowerCompletedGroupAlgebra
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    letI := instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebra
      (ℓ := ℓ) (G := G)
    ((a • x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      a • (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) =
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影はスカラー倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_smul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (a • x) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x := by
  rfl

instance instModulePrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebra :
    Module (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebra ℓ G) :=
  Function.Injective.module (PrimePowerCompletedCoeff ℓ G)
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    Subtype.val_injective
    (coe_smul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentation_coeffToGroupAlgebra
    (i : PrimePowerCompletedGroupAlgebraIndex G) (a : PrimePowerCompletedCoeff ℓ G) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
          (primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) a)) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a := by
  rw [primePowerCompletedGroupAlgebraProjection_coeffToGroupAlgebra]
  exact primePowerCompletedGroupAlgebraStageAugmentation_algebraMap (ℓ := ℓ) (G := G) i
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)

end

end FoxDifferential
