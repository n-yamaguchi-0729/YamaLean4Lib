import CrowellExactSequence.FiniteFamilyExactness
import FoxDifferential.Discrete.KernelBoundary.Quotient
import FoxDifferential.Discrete.KernelBoundary.MagnusKernel
import FoxDifferential.Discrete.FoxCalculus.Coordinates

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Discrete/BlanchfieldLyndon.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Blanchfield--Lyndon public maps

This file writes the discrete Crowell exact sequence for a finite free presentation in
Blanchfield--Lyndon coordinates.  The middle term is identified with relative Fox coordinates,
and the tail map is the finite-family boundary map whose generators are `ψ(xᵢ)-1`.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

namespace FoxCalculus

variable {H : Type} [Group H]

/-- The coordinate equivalence for a finite free presentation
`ψ : FreeGroup (Fin r) →* H`.  It identifies the Crowell middle term with explicit
relative Fox coordinates. -/
def freeGroupPresentationMiddleCoordinateEquiv
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) :
    DifferentialModule ψ ≃ₗ[GroupRing H] (Fin r → GroupRing H) :=
  (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearEquivDifferential
    (H := H) (Fin r) ψ).symm

/-- The concrete BL tail generators `ψ(x_i) - 1` for a finite free presentation. -/
def freeGroupPresentationAugmentationGenerators
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) : Fin r → GroupRing H :=
  fun i => augmentationGenerator H (ψ (FreeGroup.of i))

/-- The concrete Blanchfield--Lyndon tail map in relative Fox coordinates. -/
def freeGroupPresentationBlanchfieldLyndonTailMap
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) :
    (Fin r → GroupRing H) →ₗ[GroupRing H] GroupRing H :=
  blanchfieldLyndonFiniteFamilyMap
    (R := GroupRing H)
    (freeGroupPresentationAugmentationGenerators (H := H) r ψ)

/-- Concrete finite-sum form of the BL tail map. -/
theorem freeGroupPresentationBlanchfieldLyndonTailMap_apply
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) (a : Fin r → GroupRing H) :
    freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r ψ a =
      ∑ i : Fin r, a i * augmentationGenerator H (ψ (FreeGroup.of i)) := by
  rw [freeGroupPresentationBlanchfieldLyndonTailMap, blanchfieldLyndonFiniteFamilyMap_apply]
  simp only [freeGroupPresentationAugmentationGenerators, augmentationGenerator_eq_groupRingBoundary,
  smul_eq_mul]

/-- The concrete BL head map: the Crowell head map written in relative Fox coordinates. -/
def freeGroupPresentationRelativeDerivativeHeadMap
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) (hψ : Function.Surjective ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    KernelAbelianizationAdd ψ →ₗ[GroupRing H] (Fin r → GroupRing H) := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  exact
    (freeGroupPresentationMiddleCoordinateEquiv (H := H) r ψ).toLinearMap.comp
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)

/-- On a kernel element, the concrete BL head map is the relative Fox derivative vector. -/
theorem freeGroupPresentationRelativeDerivativeHeadMap_of
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) (hψ : Function.Surjective ψ)
    (n : ψ.ker) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    freeGroupPresentationRelativeDerivativeHeadMap (H := H) r ψ hψ
        (Additive.ofMul (Abelianization.of n)) =
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := H) (Fin r) ψ n.1 := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  change
    (freeGroupPresentationMiddleCoordinateEquiv (H := H) r ψ).toLinearMap
        (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
          (Additive.ofMul (Abelianization.of n))) =
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := H) (Fin r) ψ n.1
  rw [kernelAbelianizationBoundaryLinearOfSurjective_of]
  change
    FoxDifferential.FoxCalculus.relativeDifferentialToFreeFoxCoordinates
        (H := H) (Fin r) ψ (universalDifferential ψ n.1) =
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := H) (Fin r) ψ n.1
  exact FoxDifferential.FoxCalculus.relativeDifferentialToFreeFoxCoordinates_d
    (H := H) (Fin r) ψ n.1

end FoxCalculus

open scoped BigOperators

namespace Morishita2024

variable {H : Type} [Group H]

/-- Discrete Crowell exact sequence for a surjective group homomorphism. -/
theorem crowellExactSequence_of_surjective
    {G : Type} [Group G]
    (psi : MonoidHom G H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    Function.Injective
        (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi) ∧
      Function.Exact
        (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)
        (toGroupRing psi) ∧
      Function.Exact (toGroupRing psi) (augmentation H) ∧
      Function.Surjective (augmentation H) := by
  letI := kernelAbelianizationModuleOfSurjective psi hpsi
  refine ⟨?_, ?_, exact_toGroupRing_augmentation (H := H) psi hpsi,
    augmentation_surjective (H := H)⟩
  · exact FoxDifferential.kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := H) (ψ := psi) hpsi
  · exact exact_kernelAbelianizationBoundaryLinearOfSurjective_toGroupRing (H := H) psi hpsi

/-- Discrete Blanchfield--Lyndon exact sequence for a surjective finite free presentation. -/
theorem freeGroupPresentation_blanchfieldLyndonExactSequence
    (r : Nat) (psi : MonoidHom (FreeGroup (Fin r)) H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    Function.Injective
        (FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap (H := H) r psi hpsi) ∧
      Function.Exact
        (FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap (H := H) r psi hpsi)
        (FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi) ∧
      Function.Exact
        (FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi)
        (augmentation H) ∧
      Function.Surjective (augmentation H) := by
  letI := kernelAbelianizationModuleOfSurjective psi hpsi
  let e : DifferentialModule psi ≃ₗ[GroupRing H] (Fin r → GroupRing H) :=
    FoxCalculus.freeGroupPresentationMiddleCoordinateEquiv (H := H) r psi
  let generators : Fin r → GroupRing H :=
    FoxCalculus.freeGroupPresentationAugmentationGenerators (H := H) r psi
  change
    Function.Injective
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)) ∧
      Function.Exact
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi))
        (blanchfieldLyndonFiniteFamilyMap (R := GroupRing H) generators) ∧
      Function.Exact
        (blanchfieldLyndonFiniteFamilyMap (R := GroupRing H) generators)
        (augmentation H) ∧
      Function.Surjective (augmentation H)
  have hfox :
      blanchfieldLyndonFiniteFamilyMap (R := GroupRing H) generators =
        (toGroupRing psi).comp e.symm.toLinearMap := by
    change
      FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi =
        (toGroupRing psi).comp
          (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap
            (H := H) (Fin r) psi)
    rw [FoxDifferential.FoxCalculus.toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap]
    apply LinearMap.ext
    intro a
    rw [FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap_apply]
    simp only [augmentationGenerator_eq_groupRingBoundary, FoxCalculus.relativeFreeGroupFoxBoundary,
  LinearMap.coe_mk, AddHom.coe_mk]
  have htoAug_exact :
      Function.Exact
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi))
        ((toAugmentationIdeal (H := H) psi).comp e.symm.toLinearMap) := by
    exact
      (LinearEquiv.conj_exact_iff_exact
        (f := kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)
        (g := toAugmentationIdeal (H := H) psi) e).2
        (exact_kernelAbelianizationBoundaryLinearOfSurjective_toAugmentationIdeal
          (H := H) psi hpsi)
  have hfree_inj :
      Function.Injective
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)) := by
    intro x y hxy
    apply FoxDifferential.kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := H) (ψ := psi) hpsi
    apply e.injective
    simpa using hxy
  refine ⟨hfree_inj, ?_, ?_, augmentation_surjective (H := H)⟩
  · rw [hfox, ← subtype_comp_toAugmentationIdeal (H := H) psi]
    exact
      (Function.Injective.comp_exact_iff_exact
        (R := GroupRing H) ((augmentationIdeal H).subtype_injective)).2
        htoAug_exact
  · rw [hfox]
    intro z
    constructor
    · intro hz
      rcases (exact_toGroupRing_augmentation (H := H) psi hpsi z).1 hz with ⟨x, hx⟩
      rcases e.symm.surjective x with ⟨y, rfl⟩
      exact ⟨y, hx⟩
    · rintro ⟨y, rfl⟩
      exact augmentation_toGroupRing_eq_zero (H := H) psi (e.symm y)

end Morishita2024

end

end CrowellExactSequence
