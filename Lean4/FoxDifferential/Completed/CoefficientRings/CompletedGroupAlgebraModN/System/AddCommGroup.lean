import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/System/AddCommGroup.lean
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


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instZeroModNCompletedGroupAlgebra : Zero (ModNCompletedGroupAlgebra n G) where
  zero := ⟨fun U => (0 : ModNCompletedGroupAlgebraStage n G U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
      (0 : ModNCompletedGroupAlgebraStage n G V) = 0
    exact map_zero (modNCompletedGroupAlgebraTransition n G hUV)⟩

instance instAddModNCompletedGroupAlgebra : Add (ModNCompletedGroupAlgebra n G) where
  add x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
        (show ModNCompletedGroupAlgebraStage n G U from y.1 U), by
    intro U V hUV
    calc
      modNCompletedGroupAlgebraTransition n G hUV
          ((show ModNCompletedGroupAlgebraStage n G V from x.1 V) +
            (show ModNCompletedGroupAlgebraStage n G V from y.1 V))
        =
          modNCompletedGroupAlgebraTransition n G hUV
              (show ModNCompletedGroupAlgebraStage n G V from x.1 V) +
            modNCompletedGroupAlgebraTransition n G hUV
              (show ModNCompletedGroupAlgebraStage n G V from y.1 V) := by
            rw [map_add]
      _ =
          (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
            (show ModNCompletedGroupAlgebraStage n G U from y.1 U) := by
            exact congrArg₂ HAdd.hAdd (x.2 U V hUV) (y.2 U V hUV)⟩

instance instAddZeroClassModNCompletedGroupAlgebra :
    AddZeroClass (ModNCompletedGroupAlgebra n G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext U
    change (0 : ModNCompletedGroupAlgebraStage n G U) +
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) =
        (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext U
    change (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
      (0 : ModNCompletedGroupAlgebraStage n G U) =
        (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    simp only [add_zero]

instance instNegModNCompletedGroupAlgebra : Neg (ModNCompletedGroupAlgebra n G) where
  neg x := ⟨fun U => -(show ModNCompletedGroupAlgebraStage n G U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        (-(show ModNCompletedGroupAlgebraStage n G V from x.1 V)) =
      -(show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 U V hUV)⟩

instance instSubModNCompletedGroupAlgebra : Sub (ModNCompletedGroupAlgebra n G) where
  sub x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) -
        (show ModNCompletedGroupAlgebraStage n G U from y.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        ((show ModNCompletedGroupAlgebraStage n G V from x.1 V) -
          (show ModNCompletedGroupAlgebraStage n G V from y.1 V)) =
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) -
        (show ModNCompletedGroupAlgebraStage n G U from y.1 U)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 U V hUV) (y.2 U V hUV)⟩

instance instSMulNatModNCompletedGroupAlgebra : SMul ℕ (ModNCompletedGroupAlgebra n G) where
  smul m x := ⟨fun U => m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        (m • (show ModNCompletedGroupAlgebraStage n G V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

instance instSMulIntModNCompletedGroupAlgebra : SMul ℤ (ModNCompletedGroupAlgebra n G) where
  smul m x := ⟨fun U => m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        (m • (show ModNCompletedGroupAlgebraStage n G V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

instance instAddCommGroupModNCompletedGroupAlgebraStage (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    AddCommGroup ((modNCompletedGroupAlgebraSystem n G).X U) := by
  dsimp [modNCompletedGroupAlgebraSystem, ModNCompletedGroupAlgebraStage]
  infer_instance

instance instAddCommGroupModNCompletedGroupAlgebraFamily :
    AddCommGroup ((i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) :=
  inferInstance

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zero_modNCompletedGroupAlgebra :
    ((0 : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) = 0 := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_add_modNCompletedGroupAlgebra
    (x y : ModNCompletedGroupAlgebra n G) :
    ((x + y : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) =
      x + y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_neg_modNCompletedGroupAlgebra
    (x : ModNCompletedGroupAlgebra n G) :
    ((-x : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) =
      -x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_sub_modNCompletedGroupAlgebra
    (x y : ModNCompletedGroupAlgebra n G) :
    ((x - y : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) =
      x - y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_nsmul_modNCompletedGroupAlgebra
    (m : ℕ) (x : ModNCompletedGroupAlgebra n G) :
    ((m • x : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) =
      m • x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zsmul_modNCompletedGroupAlgebra
    (m : ℤ) (x : ModNCompletedGroupAlgebra n G) :
    ((m • x : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i) =
      m • x := by
  funext U
  rfl

instance instAddCommGroupModNCompletedGroupAlgebra :
    AddCommGroup (ModNCompletedGroupAlgebra n G) :=
  Function.Injective.addCommGroup
    (fun x : ModNCompletedGroupAlgebra n G =>
      (x : (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) → (modNCompletedGroupAlgebraSystem n G).X i))
    Subtype.val_injective
    (coe_zero_modNCompletedGroupAlgebra (n := n) (G := G))
    (coe_add_modNCompletedGroupAlgebra (n := n) (G := G))
    (coe_neg_modNCompletedGroupAlgebra (n := n) (G := G))
    (coe_sub_modNCompletedGroupAlgebra (n := n) (G := G))
    (fun x m => coe_nsmul_modNCompletedGroupAlgebra (n := n) (G := G) m x)
    (fun x m => coe_zsmul_modNCompletedGroupAlgebra (n := n) (G := G) m x)

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_zero (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    modNCompletedGroupAlgebraProjection n G U (0 : ModNCompletedGroupAlgebra n G) = 0 := by
  change (0 : ModNCompletedGroupAlgebraStage n G U) = 0
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_add (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x y : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraProjection n G U (x + y) =
      modNCompletedGroupAlgebraProjection n G U x +
        modNCompletedGroupAlgebraProjection n G U y := by
  change (show ModNCompletedGroupAlgebraStage n G U from (x + y).1 U) =
    (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
      (show ModNCompletedGroupAlgebraStage n G U from y.1 U)
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_neg (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraProjection n G U (-x) =
      -modNCompletedGroupAlgebraProjection n G U x := by
  change (show ModNCompletedGroupAlgebraStage n G U from (-x).1 U) =
    -(show ModNCompletedGroupAlgebraStage n G U from x.1 U)
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_sub (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x y : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraProjection n G U (x - y) =
      modNCompletedGroupAlgebraProjection n G U x -
        modNCompletedGroupAlgebraProjection n G U y := by
  change (show ModNCompletedGroupAlgebraStage n G U from (x - y).1 U) =
    (show ModNCompletedGroupAlgebraStage n G U from x.1 U) -
      (show ModNCompletedGroupAlgebraStage n G U from y.1 U)
  rfl

omit [Fact (0 < n)] in

end

end FoxDifferential
