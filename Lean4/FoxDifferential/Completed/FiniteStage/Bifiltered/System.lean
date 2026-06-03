import FoxDifferential.Completed.FiniteStage.Bifiltered.Transition

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Bifiltered/System.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bifiltered finite Fox semidirect systems

This file records identity and composition laws for the simultaneous transition in the target
normal subgroup and the coefficient modulus.  The resulting API lets a later completed-density
argument use arbitrary cofinal finite quotient systems instead of a fixed target quotient.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]

section Identity

variable {N : Subgroup (FreeGroup X)} [N.Normal]
variable {n : ℕ} [Fact (0 < n)]

omit [DecidableEq X] in
/-- The target quotient map induced by the identity subgroup refinement is the identity. -/
@[simp]
theorem finiteFoxStageTargetQuotientMap_rfl :
    finiteFoxStageTargetQuotientMap (X := X) (N := N) (M := N) (le_rfl : N ≤ N) =
      MonoidHom.id (finiteFoxStageTargetQuotient (X := X) N) := by
  apply MonoidHom.ext
  intro q
  rcases QuotientGroup.mk'_surjective N q with ⟨w, hw⟩
  rw [← hw, finiteFoxStageTargetQuotientMap_mk]
  rfl

omit [DecidableEq X] [Fact (0 < n)] in
/-- The target group-algebra map induced by the identity subgroup refinement is the identity. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraMap_rfl :
    finiteFoxStageTargetGroupAlgebraMap (X := X) (N := N) (M := N) (le_rfl : N ≤ N) n =
      RingHom.id (finiteFoxStageTargetGroupAlgebra (X := X) N n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxStageTargetGroupAlgebraMap (X := X) (N := N) (M := N) (le_rfl : N ≤ N) n x =
        x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, hw⟩
    rw [← hw, finiteFoxStageTargetGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [map_intCast]

omit [DecidableEq X] [Fact (0 < n)] in
/-- The bifiltered transition along identity target refinement and identity coefficient reduction
is the identity semidirect map. -/
@[simp]
theorem finiteFoxStageBifilteredSemidirectMap_rfl :
    finiteFoxStageBifilteredSemidirectMap
        (X := X) (N := N) (M := N) (n := n) (m := n) (le_rfl : N ≤ N) dvd_rfl =
      MonoidHom.id (FiniteFoxStageSemidirect (X := X) N n) := by
  apply MonoidHom.ext
  intro y
  apply FiniteFoxStageSemidirect.ext
  · funext i
    change finiteFoxStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N) (M := N) (n := n) (m := n) (le_rfl : N ≤ N) dvd_rfl
        (y.left i) = y.left i
    rw [finiteFoxStageBifilteredTargetGroupAlgebraMap_apply,
      finiteFoxStageTargetGroupAlgebraCoeffMap_rfl]
    exact congrArg (fun f => f (y.left i)) finiteFoxStageTargetGroupAlgebraMap_rfl
  · change finiteFoxStageTargetQuotientMap (X := X) (N := N) (M := N)
        (le_rfl : N ≤ N) y.right = y.right
    exact congrArg (fun f => f y.right) finiteFoxStageTargetQuotientMap_rfl

end Identity

section Composition

variable {N₀ N₁ N₂ : Subgroup (FreeGroup X)}
variable [N₀.Normal] [N₁.Normal] [N₂.Normal]
variable (h₀₁ : N₀ ≤ N₁) (h₁₂ : N₁ ≤ N₂)
variable {n₀ n₁ n₂ : ℕ} [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)]
variable (h₀₁n : n₀ ∣ n₁) (h₁₂n : n₁ ∣ n₂)

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)] in
/-- Bifiltered target-group-algebra transitions compose. -/
@[simp 900]
theorem finiteFoxStageBifilteredTargetGroupAlgebraMap_comp :
    (finiteFoxStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n).comp
      (finiteFoxStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n) =
    finiteFoxStageBifilteredTargetGroupAlgebraMap
      (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((finiteFoxStageBifilteredTargetGroupAlgebraMap
          (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n).comp
        (finiteFoxStageBifilteredTargetGroupAlgebraMap
          (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n)) x =
      finiteFoxStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N₀ q with ⟨w, rfl⟩
    rw [RingHom.comp_apply, finiteFoxStageBifilteredTargetGroupAlgebraMap_of,
      finiteFoxStageBifilteredTargetGroupAlgebraMap_of,
      finiteFoxStageBifilteredTargetGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [map_add, hx, finiteFoxStageBifilteredTargetGroupAlgebraMap_apply, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [finiteFoxStageBifilteredTargetGroupAlgebraMap, map_intCast, RingHom.coe_comp, Function.comp_apply]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)] in
/-- Bifiltered coordinate-vector transitions compose pointwise. -/
theorem finiteFoxStageBifilteredCoordinateVectorMap_comp
    (v : finiteFoxStageCoordinateVector (X := X) N₀ n₂) :
    finiteFoxStageBifilteredCoordinateVectorMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n
        (finiteFoxStageBifilteredCoordinateVectorMap
          (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n v) =
      finiteFoxStageBifilteredCoordinateVectorMap
        (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) v := by
  funext i
  change
    finiteFoxStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n
      (finiteFoxStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n (v i)) =
    finiteFoxStageBifilteredTargetGroupAlgebraMap
      (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) (v i)
  exact congrArg (fun f => f (v i))
    (finiteFoxStageBifilteredTargetGroupAlgebraMap_comp
      (X := X) h₀₁ h₁₂ h₀₁n h₁₂n)

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)] in
/-- Bifiltered semidirect transitions compose. -/
@[simp 900]
theorem finiteFoxStageBifilteredSemidirectMap_comp :
    (finiteFoxStageBifilteredSemidirectMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n).comp
      (finiteFoxStageBifilteredSemidirectMap
        (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n) =
    finiteFoxStageBifilteredSemidirectMap
      (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) := by
  apply MonoidHom.ext
  intro y
  apply FiniteFoxStageSemidirect.ext
  · change
      finiteFoxStageBifilteredCoordinateVectorMap
          (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n
          (finiteFoxStageBifilteredCoordinateVectorMap
            (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n y.left) =
        finiteFoxStageBifilteredCoordinateVectorMap
          (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂)
          (dvd_trans h₀₁n h₁₂n) y.left
    exact finiteFoxStageBifilteredCoordinateVectorMap_comp
      (X := X) h₀₁ h₁₂ h₀₁n h₁₂n y.left
  · change
      finiteFoxStageTargetQuotientMap (X := X) h₁₂
        (finiteFoxStageTargetQuotientMap (X := X) h₀₁ y.right) =
      finiteFoxStageTargetQuotientMap (X := X) (le_trans h₀₁ h₁₂) y.right
    rcases QuotientGroup.mk'_surjective N₀ y.right with ⟨w, hw⟩
    rw [← hw]
    rw [finiteFoxStageTargetQuotientMap_mk, finiteFoxStageTargetQuotientMap_mk,
      finiteFoxStageTargetQuotientMap_mk]

end Composition

end

end FoxDifferential
