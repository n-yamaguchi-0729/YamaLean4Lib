import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/InClass/AddCommGroup.lean
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

instance instZeroModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Zero (ModNCompletedGroupAlgebraInClass n G C) where
  zero := ⟨fun U => (0 : ModNCompletedGroupAlgebraStageInClass n G C U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
      (0 : ModNCompletedGroupAlgebraStageInClass n G C V) = 0
    exact map_zero _⟩

instance instAddModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Add (ModNCompletedGroupAlgebraInClass n G C) where
  add x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) +
        (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U), by
    intro U V hUV
    calc
      modNCompletedGroupAlgebraTransitionInClass n G C hUV
          ((show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V) +
            (show ModNCompletedGroupAlgebraStageInClass n G C V from y.1 V))
        =
          modNCompletedGroupAlgebraTransitionInClass n G C hUV
            (show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V) +
          modNCompletedGroupAlgebraTransitionInClass n G C hUV
            (show ModNCompletedGroupAlgebraStageInClass n G C V from y.1 V) := by
            rw [map_add]
      _ =
          (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) +
            (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U) := by
            exact congrArg₂ HAdd.hAdd (x.2 U V hUV) (y.2 U V hUV)⟩

instance instAddZeroClassModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddZeroClass (ModNCompletedGroupAlgebraInClass n G C) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext U
    change (0 : ModNCompletedGroupAlgebraStageInClass n G C U) +
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) =
        (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext U
    change (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) +
      (0 : ModNCompletedGroupAlgebraStageInClass n G C U) =
        (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    simp only [add_zero]

instance instNegModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Neg (ModNCompletedGroupAlgebraInClass n G C) where
  neg x := ⟨fun U => -(show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (-(show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V)) =
      -(show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 U V hUV)⟩

instance instSubModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Sub (ModNCompletedGroupAlgebraInClass n G C) where
  sub x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) -
        (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        ((show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V) -
          (show ModNCompletedGroupAlgebraStageInClass n G C V from y.1 V)) =
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) -
        (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 U V hUV) (y.2 U V hUV)⟩

instance instSMulNatModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℕ (ModNCompletedGroupAlgebraInClass n G C) where
  smul m x := ⟨fun U =>
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (m • (show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

instance instSMulIntModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℤ (ModNCompletedGroupAlgebraInClass n G C) where
  smul m x := ⟨fun U =>
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (m • (show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zero_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    ((0 : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = 0 := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_add_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    ((x + y : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = x + y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_neg_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ModNCompletedGroupAlgebraInClass n G C) :
    ((-x : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = -x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_sub_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    ((x - y : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = x - y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_nsmul_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℕ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    ((m • x : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = m • x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 部分型から基礎にある完備群環への包含が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem coe_zsmul_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℤ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    ((m • x : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = m • x := by
  funext U
  rfl

instance instAddCommGroupModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddCommGroup (ModNCompletedGroupAlgebraInClass n G C) :=
  Function.Injective.addCommGroup
    (fun x : ModNCompletedGroupAlgebraInClass n G C =>
      (x :
        (U : CompletedGroupAlgebraIndexInClass G C) →
          ModNCompletedGroupAlgebraStageInClass n G C U))
    Subtype.val_injective
    (coe_zero_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (coe_add_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (coe_neg_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (coe_sub_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (fun x m => coe_nsmul_modNCompletedGroupAlgebraInClass (n := n) (G := G) C m x)
    (fun x m => coe_zsmul_modNCompletedGroupAlgebraInClass (n := n) (G := G) C m x)

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_zero
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U
      (0 : ModNCompletedGroupAlgebraInClass n G C) = 0 := by
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_add
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (x + y) =
      modNCompletedGroupAlgebraProjectionInClass n G C U x +
        modNCompletedGroupAlgebraProjectionInClass n G C U y := by
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_neg
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (-x) =
      -modNCompletedGroupAlgebraProjectionInClass n G C U x := by
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_sub
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (x - y) =
      modNCompletedGroupAlgebraProjectionInClass n G C U x -
        modNCompletedGroupAlgebraProjectionInClass n G C U y := by
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は自然数倍と両立する。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_nsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (m : ℕ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (m • x) =
      m • modNCompletedGroupAlgebraProjectionInClass n G C U x := by
  rfl

omit [Fact (0 < n)] in
/-- 法 n の係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は整数倍と両立する。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_zsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (m : ℤ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (m • x) =
      m • modNCompletedGroupAlgebraProjectionInClass n G C U x := by
  rfl

end

end FoxDifferential
