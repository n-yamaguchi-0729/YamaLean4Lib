import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Multiplicative

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/InClass/System/Ring/Projection.lean
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
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は単位元を単位元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_one
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i
        (1 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) = 1 := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は積を積へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_mul
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (x * y) =
      primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x *
        primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_zero
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i
      (0 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) = 0 := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_add
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (x + y) =
      primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x +
        primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_neg
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (-x) =
      -primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_sub
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (x - y) =
      primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x -
        primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は自然数倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_nsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (m • x) =
      m • primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は整数倍と両立する。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_zsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (m • x) =
      m • primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

end

end FoxDifferential
