import FenchelNielsenZomorrodian.Discrete.Core.CompactFuchsianPresentation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Commutator.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Core/EllipticQuotientHom.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Fenchel and compact Fuchsian core definitions

Signatures, generator indices, presentations, elliptic generators, quotient homomorphisms, and family-signature transformations.
-/

open scoped BigOperators

namespace FenchelNielsen

def ellipticQuotientGeneratorImage
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (ξ : Fin σ.numPeriods → A) :
    FuchsianGenerator σ → A
  | .elliptic i => ξ i
  | .surfaceA _ => 1
  | .surfaceB _ => 1

theorem ellipticQuotientGeneratorImage_respects_relators
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (ξ : Fin σ.numPeriods → A)
    (hpow : ∀ i, ξ i ^ σ.periods i = 1)
    (hprod : ∏ i : Fin σ.numPeriods, ξ i = 1) :
    ∀ r ∈ relators σ, FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ) r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩ | rfl
  · simpa [xWord, ellipticQuotientGeneratorImage] using hpow i
  · dsimp [totalRelation]
    rw [map_mul, map_list_prod, map_list_prod]
    have hEll :
        (List.map (⇑(FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ)))
            (List.map (fun i => xWord σ i) (List.finRange σ.numPeriods))).prod = 1 := by
      rw [List.map_map]
      have hEllMap :
          (⇑(FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ)) ∘
              fun i : Fin σ.numPeriods => xWord σ i) = ξ := by
        funext i
        simp only [xWord, Function.comp_apply, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage]
      rw [hEllMap]
      calc
        (List.map ξ (List.finRange σ.numPeriods)).prod = ∏ i : Fin σ.numPeriods, ξ i := by
          simpa using (Fin.prod_univ_def (f := ξ)).symm
        _ = 1 := hprod
    have hComm :
        (List.map (⇑(FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ)))
            (List.map (fun j => ⁅aWord σ j, bWord σ j⁆)
              (List.finRange σ.orbitGenus))).prod = 1 := by
      rw [List.map_map]
      have hCommMap :
          (⇑(FreeGroup.lift (ellipticQuotientGeneratorImage σ ξ)) ∘
              fun j : Fin σ.orbitGenus => ⁅aWord σ j, bWord σ j⁆) =
            fun _ => (1 : A) := by
        funext j
        dsimp
        rw [map_commutatorElement]
        simp only [aWord, FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, bWord, commutatorElement_self]
      rw [hCommMap]
      simp only [List.map_const', List.length_finRange, List.prod_replicate, one_pow]
    rw [hEll, hComm]
    simp only [mul_one]

def ellipticQuotientHom
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (ξ : Fin σ.numPeriods → A)
    (hpow : ∀ i, ξ i ^ σ.periods i = 1)
    (hprod : ∏ i : Fin σ.numPeriods, ξ i = 1) :
    FuchsianPresentedGroup σ →* A :=
  PresentedGroup.toGroup (rels := relators σ)
    (f := ellipticQuotientGeneratorImage σ ξ)
    (ellipticQuotientGeneratorImage_respects_relators σ ξ hpow hprod)

@[simp] theorem ellipticQuotientHom_elliptic
    (σ : FuchsianSignature) {A : Type*} [CommGroup A]
    (ξ : Fin σ.numPeriods → A)
    (hpow : ∀ i, ξ i ^ σ.periods i = 1)
    (hprod : ∏ i : Fin σ.numPeriods, ξ i = 1)
    (i : Fin σ.numPeriods) :
    ellipticQuotientHom σ ξ hpow hprod
        (PresentedGroup.of (rels := relators σ) (FuchsianGenerator.elliptic i)) =
      ξ i := by
  simp only [ellipticQuotientHom, PresentedGroup.toGroup.of, ellipticQuotientGeneratorImage]

end FenchelNielsen
