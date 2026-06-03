import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.Multiplicative

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/System/Ring/GroupLike.lean
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
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は単位元を単位元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_one
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedGroupAlgebra ℓ G) = 1 := by
  change (1 : PrimePowerCompletedGroupAlgebraStage ℓ G i) = 1
  rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は積を積へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_mul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x * y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x *
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (x * y).1 i) =
    (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) *
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- Definition of primePowerCompletedGroupAlgebraOf. -/
def primePowerCompletedGroupAlgebraOf
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (h : H) :
    PrimePowerCompletedGroupAlgebra ell H := by
  refine ⟨fun i => ?_, ?_⟩
  · exact
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
        (QuotientGroup.mk h)
  · intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ell) (G := H) hij
        (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ j.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H j.2)
          (QuotientGroup.mk h)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
        (QuotientGroup.mk h)
    rw [primePowerCompletedGroupAlgebraTransition_of]
    rfl

/-- Evaluation formula for primePowerCompletedGroupAlgebraProjection_of. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_of
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : PrimePowerCompletedGroupAlgebraIndex H) (h : H) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
        (primePowerCompletedGroupAlgebraOf (ell := ell) h) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
        (QuotientGroup.mk h) := by
  rfl

/-- 素冪係数段階で、群元から得られる group-like 元の有限段階像は単位元を単位元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraOf_one
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    primePowerCompletedGroupAlgebraOf (ell := ell) (1 : H) = 1 := by
  apply (primePowerCompletedGroupAlgebraSystem ell H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ell) (1 : H)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (1 : PrimePowerCompletedGroupAlgebra ell H)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_one]
  simp only [MonoidAlgebra.of, MonoidAlgebra.single, QuotientGroup.mk_one, MonoidHom.coe_mk, OneHom.coe_mk,
  MonoidAlgebra.one_def]

/-- 素冪係数段階で、群元から得られる group-like 元の有限段階像は積を積へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraOf_mul
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (h₁ h₂ : H) :
    primePowerCompletedGroupAlgebraOf (ell := ell) (h₁ * h₂) =
      primePowerCompletedGroupAlgebraOf (ell := ell) h₁ *
        primePowerCompletedGroupAlgebraOf (ell := ell) h₂ := by
  apply (primePowerCompletedGroupAlgebraSystem ell H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ell) (h₁ * h₂)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ell) h₁ *
        primePowerCompletedGroupAlgebraOf (ell := ell) h₂)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_mul,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_of]
  simp only [MonoidAlgebra.of, QuotientGroup.mk_mul, MonoidHom.coe_mk, OneHom.coe_mk,
  MonoidAlgebra.single_mul_single, mul_one]

end

end FoxDifferential
