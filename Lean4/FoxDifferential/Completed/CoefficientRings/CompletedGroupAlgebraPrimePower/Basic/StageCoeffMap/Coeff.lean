import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.CoeffMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Basic/StageCoeffMap/Coeff.lean
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

/-- Positivity of the prime-power moduli used throughout the compatibility layer. -/
theorem primePower_pos (ℓ a : ℕ) [Fact (0 < ℓ)] : 0 < ℓ ^ a :=
  pow_pos (Fact.out : 0 < ℓ) a

end

end FoxDifferential
