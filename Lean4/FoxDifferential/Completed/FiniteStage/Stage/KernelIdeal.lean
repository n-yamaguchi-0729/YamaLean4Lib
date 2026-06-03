import FoxDifferential.Completed.FiniteStage.Stage.Source

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/KernelIdeal.lean
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

omit [DecidableEq X] [N.Normal] in
/-- The source generator `[x_i]-1` belongs to the source augmentation ideal. -/
theorem finiteFoxStageSourceGeneratorSubOne_mem_sourceAugmentationIdeal
    (i : X) :
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (FreeGroup.of i)) - 1 ∈
      finiteFoxStageSourceAugmentationIdeal (X := X) N n := by
  rw [mem_finiteFoxStageSourceAugmentationIdeal]
  rw [map_sub,
    finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient,
    map_one, sub_self]

/-- Finite-stage Fox kernel input.

The proof uses the source-valued finite Fox fundamental formula.  The target derivative equations
put the source coefficients in `K_j`, while the source generator boundaries lie in `I_j`. -/
theorem finiteFoxStageGroupAlgebraMapKernel_mem_mulAugmentation_of_derivatives_eq_zero
    [Finite X]
    {x : finiteFoxStageSourceGroupAlgebra (X := X) N n}
    (hderivative :
      ∀ i : X, finiteFoxStageGroupAlgebraDerivative (X := X) N n i x = 0)
    (haugmentation :
      finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n x = 0) :
    x ∈ finiteFoxStageGroupAlgebraMapKernelMulAugmentationIdeal (X := X) N n := by
  classical
  letI := Fintype.ofFinite X
  have hcoeff_mem
      (i : X) :
      finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x ∈
        finiteFoxStageGroupAlgebraMapKernelIdeal (X := X) N n := by
    rw [mem_finiteFoxStageGroupAlgebraMapKernelIdeal]
    rw [finiteFoxStageSourceGroupAlgebraDerivative_map]
    exact hderivative i
  have hformula :=
    finiteFoxStageSourceGroupAlgebraDerivative_groupAlgebra_fundamental_formula
      (X := X) (N := N) (n := n) x
  have hx_sum :
      x =
        ∑ i : X,
          finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) := by
    calc
      x =
          x -
            algebraMap (ModNCompletedCoeff n)
              (finiteFoxStageSourceGroupAlgebra (X := X) N n) 0 := by
            simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  Finsupp.single_zero, sub_zero]
      _ =
          x -
            algebraMap (ModNCompletedCoeff n)
              (finiteFoxStageSourceGroupAlgebra (X := X) N n)
              (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n x) := by
            rw [haugmentation]
      _ =
          ∑ i : X,
            finiteFoxStageSourceGroupAlgebraDerivative (X := X) N n i x *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := hformula
  rw [hx_sum]
  exact
    (finiteFoxStageGroupAlgebraMapKernelMulAugmentationIdeal (X := X) N n).sum_mem
      (fun i _ =>
        Ideal.mul_mem_mul (hcoeff_mem i)
          (finiteFoxStageSourceGeneratorSubOne_mem_sourceAugmentationIdeal
            (X := X) N n i))



end

end FoxDifferential
