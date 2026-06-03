import FoxDifferential.Discrete.KernelBoundary.Homology

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/KernelBoundary/MagnusKernel.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Magnus-kernel theorem for universal differentials

For a surjective homomorphism, a kernel element whose universal differential vanishes lies
in the ordinary commutator subgroup of the kernel.  This is the algebraic kernel statement
used by Crowell and metabelian applications.

This file contains the final injectivity and kernel-membership consequences of the
kernel-augmentation homology comparison.
-/

namespace FoxDifferential

noncomputable section

namespace KernelAugmentation

variable {H G : Type} [Group H] [DecidableEq H] [Group G] [DecidableEq G]
variable {ψ : G →* H}

omit [DecidableEq H] in
omit [DecidableEq H] [DecidableEq G] in
theorem kernelAbelianizationBoundaryLinearOfSurjective_injective
    (hψ : Function.Surjective ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    Function.Injective (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ) := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  intro x y hxy
  have hcoinv :
      kernelAbelianizationToCoinvariantsLinear (ψ := ψ) x =
        kernelAbelianizationToCoinvariantsLinear (ψ := ψ) y := by
    calc
      kernelAbelianizationToCoinvariantsLinear (ψ := ψ) x =
          differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
            (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) := by
              symm
              exact differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_boundary
                (ψ := ψ) hψ x
      _ =
          differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
            (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ y) := by
              simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, Rep.of_ρ, hxy,
  kernelAbelianizationBoundaryLinearOfSurjective_apply]
      _ = kernelAbelianizationToCoinvariantsLinear (ψ := ψ) y := by
            exact differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_boundary
              (ψ := ψ) hψ y
  exact (kernelAbelianizationToCoinvariantsLinear_injective (H := H) (ψ := ψ) hψ) hcoinv

omit [DecidableEq H] [DecidableEq G] in
/-- Discrete Magnus-kernel form of the injectivity theorem: for a surjective `ψ`, if the
Crowell/Fox differential of a kernel element vanishes, then that element already lies in the
ordinary commutator subgroup of `ker ψ`. -/
theorem mem_commutator_ker_of_d_eq_zero_of_surjective
    (hψ : Function.Surjective ψ) (n : ψ.ker) (hn : universalDifferential ψ n.1 = 0) :
    n ∈ commutator ψ.ker := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  have hboundary_zero :
      kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
          (Additive.ofMul (Abelianization.of n)) =
        kernelAbelianizationBoundaryLinearOfSurjective ψ hψ 0 := by
    rw [kernelAbelianizationBoundaryLinearOfSurjective_of, hn]
    simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, map_zero]
  have hclass_zero :
      (Additive.ofMul (Abelianization.of n) : KernelAbelianizationAdd ψ) = 0 :=
    (FoxDifferential.KernelAugmentation.kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := H) (ψ := ψ) hψ) hboundary_zero
  have hclass_one : Abelianization.of n = 1 := by
    simpa using congrArg Additive.toMul hclass_zero
  exact (QuotientGroup.eq_one_iff (N := commutator ψ.ker) n).1 hclass_one

end KernelAugmentation

export KernelAugmentation
  (kernelAbelianizationBoundaryLinearOfSurjective_injective
    mem_commutator_ker_of_d_eq_zero_of_surjective)

end

end FoxDifferential
