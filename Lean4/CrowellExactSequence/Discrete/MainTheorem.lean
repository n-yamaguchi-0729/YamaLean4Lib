import CrowellExactSequence.Discrete.BlanchfieldLyndon

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Discrete/MainTheorem.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Crowell main theorems

This file is the paper-facing entry point for the discrete main statements.  The conclusions
are packaged as four-term exact sequences, not as isolated surjectivity or middle-exactness
lemmas.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

variable {H : Type} [Group H]

/-- The discrete Crowell exact sequence for a surjective group homomorphism, packaged as the
full four-term exact sequence
`ker(psi)^ab -> A_psi -> Z[H] -> Z`. -/
theorem discreteCrowellExactSequence
    {G : Type} [Group G]
    (psi : MonoidHom G H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    IsFourTermExactSequence
      (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)
      (toGroupRing psi)
      (augmentation H) := by
  letI := kernelAbelianizationModuleOfSurjective psi hpsi
  exact Morishita2024.crowellExactSequence_of_surjective (H := H) psi hpsi

/-- The discrete Blanchfield--Lyndon coordinate exact sequence for a finite free presentation,
packaged as the full four-term exact sequence. -/
theorem discreteBlanchfieldLyndonExactSequence
    (r : Nat) (psi : MonoidHom (FreeGroup (Fin r)) H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    IsFourTermExactSequence
      (FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap (H := H) r psi hpsi)
      (FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi)
      (augmentation H) := by
  letI := kernelAbelianizationModuleOfSurjective psi hpsi
  exact Morishita2024.freeGroupPresentation_blanchfieldLyndonExactSequence (H := H) r psi hpsi

end

end CrowellExactSequence
