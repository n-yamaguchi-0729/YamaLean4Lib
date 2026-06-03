import FoxDifferential.Completed.FiniteStage.Stage.Naturality

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Source.lean
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

/-- A chosen free-group representative of a finite Fox source quotient element.

It supplies source-valued coefficients for the finite algebra argument; no canonicality is needed. -/
def finiteFoxStageSourceRepresentative
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    FreeGroup X :=
  Classical.choose
    (QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)

omit [DecidableEq X] [N.Normal] in
/-- The chosen representative maps back to the original source quotient element. -/
@[simp]
theorem finiteFoxStageSourceRepresentative_mk
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (finiteFoxStageSourceRepresentative (X := X) N n q) = q := by
  exact
    Classical.choose_spec
      (QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)

/-- Source-valued finite Fox coefficient attached to a source quotient element, using a chosen
free-group representative. -/
def finiteFoxStageSourceQuotientDerivative
    (i : X)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceGroupAlgebra (X := X) N n :=
  finiteFoxStageDerivative
    (X := X)
    (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    n i (finiteFoxStageSourceRepresentative (X := X) N n q)

/-- Source-valued finite Fox derivative on the source group algebra. It is defined by extending
the representative-based source coefficients linearly. -/
def finiteFoxStageSourceGroupAlgebraDerivative (i : X) :
    finiteFoxStageSourceGroupAlgebra (X := X) N n →ₗ[ModNCompletedCoeff n]
      finiteFoxStageSourceGroupAlgebra (X := X) N n :=
  Finsupp.linearCombination (ModNCompletedCoeff n)
    (finiteFoxStageSourceQuotientDerivative (X := X) N n i)

omit [N.Normal] in
/-- Evaluation of the source-valued finite Fox derivative on a source quotient basis element. -/
@[simp]
theorem finiteFoxStageSourceGroupAlgebraDerivative_of_quotient
    (i : X)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      finiteFoxStageSourceQuotientDerivative (X := X) N n i q := by
  change
      (Finsupp.linearCombination (ModNCompletedCoeff n)
        (finiteFoxStageSourceQuotientDerivative (X := X) N n i))
          (Finsupp.single q (1 : ModNCompletedCoeff n)) =
        finiteFoxStageSourceQuotientDerivative (X := X) N n i q
  rw [Finsupp.linearCombination_single, one_smul]

omit [N.Normal] in
/-- The source-valued finite Fox fundamental formula on a source quotient basis element. -/
theorem finiteFoxStageSourceGroupAlgebraDerivative_of_quotient_fundamental_formula
    [Fintype X]
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1 =
      ∑ i : X,
        finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (QuotientGroup.mk'
              (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of i)) - 1) := by
  let C : Subgroup (FreeGroup X) :=
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n
  let w : FreeGroup X :=
    finiteFoxStageSourceRepresentative (X := X) N n q
  have hw : QuotientGroup.mk' C w = q := by
    simpa [C, w] using finiteFoxStageSourceRepresentative_mk (X := X) N n q
  have h :=
    finiteFoxStageDerivative_fundamental_formula
      (X := X) (N := C) (n := n) w
  have hD (i : X) :
      finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
        finiteFoxStageDerivative (X := X) C n i w := by
    change
      (Finsupp.linearCombination (ModNCompletedCoeff n)
          (finiteFoxStageSourceQuotientDerivative (X := X) N n i))
        (Finsupp.single q (1 : ModNCompletedCoeff n)) =
        finiteFoxStageDerivative (X := X) C n i w
    rw [Finsupp.linearCombination_single, one_smul]
    simp only [finiteFoxStageSourceQuotientDerivative, C, w]
  calc
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1 =
        ∑ i : X,
          finiteFoxStageDerivative (X := X) C n i w *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) := by
      simpa [C, w, hw] using h
    _ =
        ∑ i : X,
          finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hD i]

omit [N.Normal] in
/-- Source-valued finite Fox fundamental formula on the full source group algebra. -/
theorem finiteFoxStageSourceGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    [Fintype X]
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) :
    x -
        algebraMap (ModNCompletedCoeff n)
          (finiteFoxStageSourceGroupAlgebra (X := X) N n)
          (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) =
      ∑ i : X,
        finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (QuotientGroup.mk'
              (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of i)) - 1) := by
  classical
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [map_zero, sub_self, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply,
  zero_mul, Finset.sum_const_zero]
  · intro x y hx hy
    let x0 : finiteFoxStageSourceGroupAlgebra (X := X) N n := x
    let y0 : finiteFoxStageSourceGroupAlgebra (X := X) N n := y
    have hx0 :
        x0 -
            algebraMap (ModNCompletedCoeff n)
              (finiteFoxStageSourceGroupAlgebra (X := X) N n)
              (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n x0) =
          ∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
      simpa [x0] using hx
    have hy0 :
        y0 -
            algebraMap (ModNCompletedCoeff n)
              (finiteFoxStageSourceGroupAlgebra (X := X) N n)
              (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n y0) =
          ∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i y0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
      simpa [y0] using hy
    change
      x0 + y0 -
          algebraMap (ModNCompletedCoeff n)
            (finiteFoxStageSourceGroupAlgebra (X := X) N n)
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (x0 + y0)) =
        ∑ i : X,
          finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i (x0 + y0) *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1)
    calc
      x0 + y0 -
          algebraMap (ModNCompletedCoeff n)
            (finiteFoxStageSourceGroupAlgebra (X := X) N n)
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (x0 + y0)) =
          (x0 -
              algebraMap (ModNCompletedCoeff n)
                (finiteFoxStageSourceGroupAlgebra (X := X) N n)
                (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n x0)) +
            (y0 -
              algebraMap (ModNCompletedCoeff n)
                (finiteFoxStageSourceGroupAlgebra (X := X) N n)
                (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n y0)) := by
        rw [map_add, map_add]
        abel
      _ = (∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1)) +
          (∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i y0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1)) := by
        rw [hx0, hy0]
      _ = ∑ i : X,
            (finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x0 +
              finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i y0) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_mul]
      _ = ∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i (x0 + y0) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_add]
  · intro q a
    have hq :=
      finiteFoxStageSourceGroupAlgebraDerivative_of_quotient_fundamental_formula
        (X := X) (N := N) (n := n) q
    rw [← Finsupp.smul_single_one q a]
    calc
      a • MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q -
          algebraMap (ModNCompletedCoeff n)
            (finiteFoxStageSourceGroupAlgebra (X := X) N n)
            (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n
              (a • MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)) =
          a •
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1) := by
        rw [map_smul]
        have haug :
            finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
              1 := by
          simpa using
            finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient
              (F := FreeGroup X) N n q
        rw [haug]
        rw [show a • (1 : ModNCompletedCoeff n) = a by simp only [smul_eq_mul, mul_one]]
        change
          a • MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q -
              algebraMap (ModNCompletedCoeff n)
                (finiteFoxStageSourceGroupAlgebra (X := X) N n) a =
            a •
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1)
        rw [smul_sub]
        congr 1
        simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  MonoidAlgebra.one_def, Algebra.smul_def, MonoidAlgebra.single_mul_single, mul_one]
      _ = a • (∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1)) := by
        rw [hq]
      _ = ∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
              (a • MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, smul_mul_assoc]

omit [DecidableEq X] in
/-- The source-to-target group-algebra map commutes with scalar multiplication by
`Z/nZ` coefficients. -/
theorem finiteFoxCommutatorPowerGroupAlgebraMap_smul
    (a : ModNCompletedCoeff n)
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a • x) =
      a • finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul]
  congr 1
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  finiteFoxCommutatorPowerGroupAlgebraMap_single_apply, map_one]

/-- Applying the source-to-target finite group-algebra map to the source-valued derivative gives
the existing target-valued finite Fox derivative. -/
theorem finiteFoxStageSourceGroupAlgebraDerivative_map_of_quotient
    (i : X)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) := by
  rw [finiteFoxStageSourceGroupAlgebraDerivative_of_quotient]
  let C : Subgroup (FreeGroup X) :=
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n
  let hCN : C ≤ N :=
    finiteFoxCommutatorPowerSubgroup_le_normal (F := FreeGroup X) N n
  let w : FreeGroup X :=
    finiteFoxStageSourceRepresentative (X := X) N n q
  have hw : QuotientGroup.mk' C w = q := by
    simpa [C, w] using finiteFoxStageSourceRepresentative_mk (X := X) N n q
  change
    finiteFoxStageTargetGroupAlgebraMap (X := X) hCN n
        (finiteFoxStageDerivative (X := X) C n i w) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
  rw [← hw, finiteFoxStageGroupAlgebraDerivative_of]
  exact finiteFoxStageDerivative_natural (X := X) hCN n i w

/-- Applying the source-to-target finite group-algebra map to the source-valued derivative agrees
with the target-valued finite Fox derivative on all source group-algebra elements. -/
theorem finiteFoxStageSourceGroupAlgebraDerivative_map
    (i : X) (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) :
    finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x) =
      finiteFoxStageGroupAlgebraDerivative (X := X) N n i x := by
  classical
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [map_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
    rw [map_add]
  · intro q a
    rw [← Finsupp.smul_single_one q a]
    rw [map_smul, finiteFoxCommutatorPowerGroupAlgebraMap_smul, map_smul]
    congr 1
    simpa [MonoidAlgebra.of] using
      finiteFoxStageSourceGroupAlgebraDerivative_map_of_quotient
        (X := X) (N := N) (n := n) i q


end

end FoxDifferential
