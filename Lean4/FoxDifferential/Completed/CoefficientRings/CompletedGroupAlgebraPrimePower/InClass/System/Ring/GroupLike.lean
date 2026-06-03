import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Projection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/InClass/System/Ring/GroupLike.lean
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

/-- The class-restricted completed group-algebra element represented by a group element. -/
def primePowerCompletedGroupAlgebraOfInClass
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) (h : H) :
    PrimePowerCompletedGroupAlgebraInClass ell H C := by
  refine ⟨fun i => ?_, ?_⟩
  · exact
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h)
  · intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ell) (G := H) C hij
        (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ j.1))
          (CompletedGroupAlgebraQuotientInClass H C j.2)
          (QuotientGroup.mk h)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h)
    rw [primePowerCompletedGroupAlgebraTransitionInClass_of]
    rfl

/-- Evaluation formula for primePowerCompletedGroupAlgebraProjectionInClass_of. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_of
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass H C)
    (h : H) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
        (primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h) := by
  rfl

/-- 素冪係数段階で、指定された有限群クラスに属する段階について、群元から得られる group-like 元の有限段階像は単位元を単位元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraOfInClass_one
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) :
    primePowerCompletedGroupAlgebraOfInClass (ell := ell) (H := H) C 1 = 1 := by
  apply Subtype.ext
  funext i
  change primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (primePowerCompletedGroupAlgebraOfInClass (ell := ell) (H := H) C 1) =
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (1 : PrimePowerCompletedGroupAlgebraInClass ell H C)
  rw [primePowerCompletedGroupAlgebraProjectionInClass_of,
    primePowerCompletedGroupAlgebraProjectionInClass_one]
  simp only [MonoidAlgebra.of, MonoidAlgebra.single, QuotientGroup.mk_one, MonoidHom.coe_mk, OneHom.coe_mk,
  MonoidAlgebra.one_def]

/-- 素冪係数段階で、指定された有限群クラスに属する段階について、群元から得られる group-like 元の有限段階像は積を積へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraOfInClass_mul
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) (h₁ h₂ : H) :
    primePowerCompletedGroupAlgebraOfInClass (ell := ell) C (h₁ * h₂) =
      primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₁ *
        primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₂ := by
  apply Subtype.ext
  funext i
  change primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (primePowerCompletedGroupAlgebraOfInClass (ell := ell) C (h₁ * h₂)) =
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₁ *
        primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₂)
  rw [primePowerCompletedGroupAlgebraProjectionInClass_of,
    primePowerCompletedGroupAlgebraProjectionInClass_mul,
    primePowerCompletedGroupAlgebraProjectionInClass_of,
    primePowerCompletedGroupAlgebraProjectionInClass_of]
  simp only [MonoidAlgebra.of, QuotientGroup.mk_mul, MonoidHom.coe_mk, OneHom.coe_mk,
  MonoidAlgebra.single_mul_single, mul_one]

end

end FoxDifferential
