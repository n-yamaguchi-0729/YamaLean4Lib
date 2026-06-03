import FoxDifferential.Completed.FiniteStage.Stage.Source

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/CoeffMap/Target.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]
/-- Coefficient-reduction map on finite-stage target group algebras for a divisor `n ∣ m`. -/
def finiteFoxStageTargetGroupAlgebraCoeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    finiteFoxStageTargetGroupAlgebra (X := X) N m₀ →+*
      finiteFoxStageTargetGroupAlgebra (X := X) N n₀ :=
  modNCompletedGroupRingCoeffMap
    (n := n₀) (m := m₀) (finiteFoxStageTargetQuotient (X := X) N) hnm

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of target coefficient reduction on a represented quotient word. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_of
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := by
  simpa [finiteFoxStageTargetGroupAlgebraCoeffMap] using
    (modNCompletedGroupRingCoeffMap_of
      (n := n₀) (m := m₀)
      (H := finiteFoxStageTargetQuotient (X := X) N) hnm (QuotientGroup.mk' N w))

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of target coefficient reduction on a quotient basis element. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_of_quotient
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (q : finiteFoxStageTargetQuotient (X := X) N) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (finiteFoxStageTargetQuotient (X := X) N) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (finiteFoxStageTargetQuotient (X := X) N) q := by
  rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
  exact finiteFoxStageTargetGroupAlgebraCoeffMap_of (X := X) N hnm w

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of target coefficient reduction on a single basis coefficient. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_single_apply
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (q : finiteFoxStageTargetQuotient (X := X) N)
    (a : ModNCompletedCoeff m₀) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
  letI : Algebra (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) :=
    ZMod.algebra' (R := ModNCompletedCoeff n₀) (m := n₀) (n := m₀) hnm
  have hcoeff :
      algebraMap (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) a =
        modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a := by
    rfl
  rw [finiteFoxStageTargetGroupAlgebraCoeffMap]
  ext r
  simp only [modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.single, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidAlgebra.of_apply, Algebra.smul_def, MonoidAlgebra.coe_algebraMap,
  Function.comp_apply, hcoeff, MonoidAlgebra.single_mul_single, one_mul, mul_one]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Target coefficient reduction is the finsupp map-range operation on coefficients. -/
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_eq_mapRange
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm).toAddMonoidHom =
      (Finsupp.mapRange.addMonoidHom
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).toAddMonoidHom :
        finiteFoxStageTargetGroupAlgebra (X := X) N m₀ →+
          finiteFoxStageTargetGroupAlgebra (X := X) N n₀) := by
  apply Finsupp.addHom_ext
  intro q a
  change
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.single q a) =
      (Finsupp.mapRange.addMonoidHom
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).toAddMonoidHom :
        finiteFoxStageTargetGroupAlgebra (X := X) N m₀ →+
          finiteFoxStageTargetGroupAlgebra (X := X) N n₀)
        (Finsupp.single q a)
  rw [finiteFoxStageTargetGroupAlgebraCoeffMap_single_apply]
  simp only [Finsupp.mapRange.addMonoidHom, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
  AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.mapRange_single]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Pointwise formula for target coefficient reduction. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_apply
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (x : finiteFoxStageTargetGroupAlgebra (X := X) N m₀)
    (q : finiteFoxStageTargetQuotient (X := X) N) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm x q =
      modNCompletedCoeffMap (n := n₀) (m := m₀) hnm (x q) := by
  have h :=
    DFunLike.congr_fun
      (finiteFoxStageTargetGroupAlgebraCoeffMap_eq_mapRange
        (X := X) N hnm) x
  simpa [Finsupp.mapRange] using congrArg (fun y => y q) h

omit [DecidableEq X] [Fact (0 < n₀)] in
/-- Target coefficient reduction along `dvd_rfl` is the identity map. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_rfl
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) (n₀ := n₀) (m₀ := n₀) N dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) (n₀ := n₀) (m₀ := n₀) N
          dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
    rw [finiteFoxStageTargetGroupAlgebraCoeffMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [finiteFoxStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
  map_intCast]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Target coefficient reductions compose along divisibility. -/
@[simp 900]
theorem finiteFoxStageTargetGroupAlgebraCoeffMap_comp
    {k₀ : ℕ}
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (hmk : m₀ ∣ k₀) :
    (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
        (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hmk) =
      finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
          (finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hmk)) x =
        finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
    rw [RingHom.comp_apply, finiteFoxStageTargetGroupAlgebraCoeffMap_of,
      finiteFoxStageTargetGroupAlgebraCoeffMap_of, finiteFoxStageTargetGroupAlgebraCoeffMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [finiteFoxStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
  map_intCast, RingHom.coe_coe]




end

end FoxDifferential
