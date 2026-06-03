import FoxDifferential.Common.FiniteFamilyLinearMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/FiniteFamilyExactness.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-family coordinate exactness

This file isolates the finite-family linear maps that appear as Blanchfield--Lyndon
coordinate maps, together with the four-term exact-sequence predicate and transport lemmas
used by the discrete and profinite Crowell sequences.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

section BlanchfieldLyndonFiniteFamilyMap

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Blanchfield--Lyndon finite-family map associated to a chosen boundary-generating family. -/
abbrev blanchfieldLyndonFiniteFamilyMap (generators : X → M) :
    (X → R) →ₗ[R] M :=
  finiteFamilyLinearMap (R := R) generators

omit [DecidableEq X] in
/-- Evaluate a Blanchfield--Lyndon finite-family map as its defining finite sum. -/
theorem blanchfieldLyndonFiniteFamilyMap_apply (generators : X → M) (x : X → R) :
    blanchfieldLyndonFiniteFamilyMap (R := R) generators x = ∑ i, x i • generators i := rfl

/-- A Blanchfield--Lyndon finite-family map sends a coordinate basis vector to its generator. -/
@[simp]
theorem blanchfieldLyndonFiniteFamilyMap_single (generators : X → M) (i : X) :
    blanchfieldLyndonFiniteFamilyMap (R := R) generators (Pi.single i 1) = generators i :=
  finiteFamilyLinearMap_single (R := R) generators i

/-- The image of the Blanchfield--Lyndon finite-family map is the span of its
boundary-generating family. -/
theorem blanchfieldLyndonFiniteFamilyMap_range_eq_span (generators : X → M) :
    LinearMap.range (blanchfieldLyndonFiniteFamilyMap (R := R) generators) =
      Submodule.span R (Set.range generators) :=
  finiteFamilyLinearMap_range_eq_span (R := R) generators

/-- The Blanchfield--Lyndon finite-family map is surjective when its target family spans the
codomain. -/
theorem blanchfieldLyndonFiniteFamilyMap_surjective_of_span_eq_top
    (generators : X → M)
    (hspan : Submodule.span R (Set.range generators) = ⊤) :
    Function.Surjective (blanchfieldLyndonFiniteFamilyMap (R := R) generators) :=
  finiteFamilyLinearMap_surjective_of_span_eq_top (R := R) generators hspan

/-- The Blanchfield--Lyndon finite-family map is onto exactly when its boundary generators span. -/
theorem blanchfieldLyndonFiniteFamilyMap_surjective_iff_span_eq_top
    (generators : X → M) :
    Function.Surjective (blanchfieldLyndonFiniteFamilyMap (R := R) generators) ↔
      Submodule.span R (Set.range generators) = ⊤ :=
  finiteFamilyLinearMap_surjective_iff_span_eq_top (R := R) generators

end BlanchfieldLyndonFiniteFamilyMap

/-- A four-term exact sequence, stated at the function level.  This packages the assertions
`f` injective, exactness at the two middle terms, and surjectivity of the final map. -/
def IsFourTermExactSequence {A B C D : Type*} [Zero C] [Zero D]
    (f : A → B) (g : B → C) (h : C → D) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Exact g h ∧ Function.Surjective h

/-- Blanchfield--Lyndon coordinate exactness is the same four-term predicate, with a
paper-facing name for the coordinate form. -/
abbrev IsBlanchfieldLyndonExactSequence {A B C D : Type*} [Zero C] [Zero D]
    (f : A → B) (g : B → C) (h : C → D) : Prop :=
  IsFourTermExactSequence f g h

namespace IsFourTermExactSequence

variable {A B C D : Type*} [Zero C] [Zero D]
variable {f : A → B} {g : B → C} {h : C → D}

/-- Extract injectivity of the first map from a four-term exact sequence. -/
theorem injective (hexact : IsFourTermExactSequence f g h) :
    Function.Injective f :=
  hexact.1

/-- Extract exactness at the middle-left map from a four-term exact sequence. -/
theorem exact_head_tail (hexact : IsFourTermExactSequence f g h) :
    Function.Exact f g :=
  hexact.2.1

/-- Extract exactness at the augmentation-side map from a four-term exact sequence. -/
theorem exact_tail_augmentation (hexact : IsFourTermExactSequence f g h) :
    Function.Exact g h :=
  hexact.2.2.1

/-- Extract final surjectivity from a four-term exact sequence. -/
theorem tail_surjective (hexact : IsFourTermExactSequence f g h) :
    Function.Surjective h :=
  hexact.2.2.2

end IsFourTermExactSequence

namespace IsBlanchfieldLyndonExactSequence

variable {A B C D : Type*} [Zero C] [Zero D]
variable {f : A → B} {g : B → C} {h : C → D}

/-- Extract injectivity of the first map from a BL exact sequence. -/
theorem injective (hexact : IsBlanchfieldLyndonExactSequence f g h) :
    Function.Injective f :=
  hexact.1

/-- Extract exactness at the middle-left map from a BL exact sequence. -/
theorem exact_head_tail (hexact : IsBlanchfieldLyndonExactSequence f g h) :
    Function.Exact f g :=
  hexact.2.1

/-- Extract exactness at the augmentation-side map from a BL exact sequence. -/
theorem exact_tail_augmentation (hexact : IsBlanchfieldLyndonExactSequence f g h) :
    Function.Exact g h :=
  hexact.2.2.1

/-- Extract augmentation surjectivity from a BL exact sequence. -/
theorem augmentation_surjective (hexact : IsBlanchfieldLyndonExactSequence f g h) :
    Function.Surjective h :=
  hexact.2.2.2

end IsBlanchfieldLyndonExactSequence

section LinearEquivTransport

variable {R : Type*} [Semiring R]
variable {A B B' C D : Type*}
variable [AddCommMonoid B] [Module R B]
variable [AddCommMonoid B'] [Module R B']
variable [Zero C] [Zero D]

/-- Transport function exactness across a linear equivalence on the middle type. -/
theorem Function.Exact.linearEquiv_symm_comp_comp
    (e : B ≃ₗ[R] B') {f : A → B'} {g : B' → C}
    (hexact : Function.Exact f g) :
    Function.Exact (fun x : A => e.symm (f x)) (fun y : B => g (e y)) := by
  intro y
  constructor
  · intro hy
    rcases (hexact (e y)).1 hy with ⟨x, hx⟩
    exact ⟨x, by simp only [hx, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨x, hx⟩
    have hxy : f x = e y := by
      have hcongr := congrArg e hx
      simpa using hcongr
    exact (hexact (e y)).2 ⟨x, hxy⟩

/-- Transporting exactness across a linear equivalence is an equivalence of exactness statements. -/
theorem Function.Exact.linearEquiv_symm_comp_comp_iff
    (e : B ≃ₗ[R] B') {f : A → B'} {g : B' → C} :
    Function.Exact (fun x : A => e.symm (f x)) (fun y : B => g (e y)) ↔
      Function.Exact f g := by
  constructor
  · intro hexact
    simpa using
      (Function.Exact.linearEquiv_symm_comp_comp
        (e := e.symm)
        (f := fun x : A => e.symm (f x))
        (g := fun y : B => g (e y))
        hexact)
  · exact Function.Exact.linearEquiv_symm_comp_comp e

omit [Zero C] in
/-- Compose the tail map of an exact pair with a linear equivalence on the middle type. -/
theorem Function.Exact.comp_linearEquiv
    (e : B ≃ₗ[R] B') {g : B' → C} {h : C → D}
    (hexact : Function.Exact g h) :
    Function.Exact (fun y : B => g (e y)) h := by
  intro z
  constructor
  · intro hz
    rcases (hexact z).1 hz with ⟨y', hy'⟩
    rcases e.surjective y' with ⟨y, rfl⟩
    exact ⟨y, hy'⟩
  · rintro ⟨y, hy⟩
    exact (hexact z).2 ⟨e y, hy⟩

/-- Transport a full BL exact sequence across a linear equivalence on the coordinate middle term. -/
theorem IsBlanchfieldLyndonExactSequence.linearEquiv_symm_comp_comp
    (e : B ≃ₗ[R] B') {f : A → B'} {g : B' → C} {h : C → D}
    (hexact : IsBlanchfieldLyndonExactSequence f g h) :
    IsBlanchfieldLyndonExactSequence
      (fun x : A => e.symm (f x)) (fun y : B => g (e y)) h := by
  refine ⟨?_, ?_, ?_, hexact.2.2.2⟩
  · intro x y hxy
    apply hexact.1
    have hcongr := congrArg e hxy
    simpa using hcongr
  · exact Function.Exact.linearEquiv_symm_comp_comp e hexact.2.1
  · exact Function.Exact.comp_linearEquiv e hexact.2.2.1

end LinearEquivTransport

end

end CrowellExactSequence
