import ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedRelators

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/ReidemeisterSchreier/FiniteQuotient/Kernel.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite quotient Reidemeister-Schreier presentations

Specializes Reidemeister-Schreier rewriting to finite quotient targets, cleaned symbols, cleaned relators, target presentations, word certificates, and Tietze equivalences.
-/

namespace ReidemeisterSchreier.Discrete.ReidemeisterSchreier

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

/-- The inverse-map candidate on the kernel, before proving it kills the
relator subgroup. -/
noncomputable def tauKernelQuotientHom
    (R : Set (FreeGroup X)) :
    D.kernel →* FreeGroup (FiniteSchreierSymbol X Q) ⧸
      Subgroup.normalClosure (D.schreierRelators R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.schreierRelators R))
      (D.tau 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, tau_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.schreierRelators R))
          (D.tau 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.schreierRelators R))
          (D.tau 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.schreierRelators R))
          (D.tau 1 (l : FreeGroup X))
    rw [D.tau_mul_of_mem_kernel k.property]
    rfl

/-- The inverse-map candidate on the kernel for the raw presentation quotient,
before proving it kills the relator subgroup. -/
noncomputable def tauKernelPresentationQuotientHom
    (R : Set (FreeGroup X)) :
    D.kernel →* FreeGroup (FiniteSchreierSymbol X Q) ⧸
      Subgroup.normalClosure (D.presentationRelators R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.presentationRelators R))
      (D.tau 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, tau_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 (l : FreeGroup X))
    rw [D.tau_mul_of_mem_kernel k.property]
    rfl

/-- The inverse-map candidate on the kernel for the augmented raw presentation
quotient, before proving it kills the relator subgroup. -/
noncomputable def tauKernelAugmentedPresentationQuotientHom
    (R : Set (FreeGroup X)) :
    D.kernel →* FreeGroup (FiniteSchreierSymbol X Q) ⧸
      Subgroup.normalClosure (D.augmentedPresentationRelators R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.augmentedPresentationRelators R))
      (D.tau 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, tau_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 (l : FreeGroup X))
    rw [D.tau_mul_of_mem_kernel k.property]
    rfl

theorem tau_mem_schreierRelators
    {R : Set (FreeGroup X)} (q : Q) {r : FreeGroup X} (hr : r ∈ R) :
    D.tau q r ∈ D.schreierRelators R :=
  ⟨q, r, hr, rfl⟩

theorem tau_mem_quotientSectionRelators (q : Q) :
    D.tau 1 (D.quotientSection q) ∈ D.quotientSectionRelators :=
  ⟨q, rfl⟩

theorem presentationRelators_subset_augmentedPresentationRelators
    (R : Set (FreeGroup X)) :
    D.presentationRelators R ⊆ D.augmentedPresentationRelators R :=
  fun _ hq => Or.inl hq

theorem quotientSectionRelators_subset_augmentedPresentationRelators
    (R : Set (FreeGroup X)) :
    D.quotientSectionRelators ⊆ D.augmentedPresentationRelators R :=
  fun _ hq => Or.inr hq

end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete.ReidemeisterSchreier
