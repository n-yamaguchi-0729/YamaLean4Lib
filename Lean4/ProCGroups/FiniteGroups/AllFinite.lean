import Mathlib.GroupTheory.QuotientGroup.Finite
import ProCGroups.FiniteGroups.Classes

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FiniteGroups/AllFinite.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite group classes

Defines finite group classes and their standard closure properties: quotients, finite subdirect products, subgroups, extensions, formations, and standard examples.
-/

namespace ProCGroups

universe u

namespace FiniteGroupClass

/-- The class of all finite groups. -/
def allFinite : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G
  finite_of_mem := fun hG => hG

/-- The class of all finite groups is an extension-closed formation. -/
theorem allFinite_formation : Formation allFinite := by
  refine ⟨?_, ?_⟩
  · intro G _ N _ hG
    letI : Finite G := hG
    exact Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · intro ι _ G _ H _ f hf _ hH
    letI : ∀ i, Finite (H i) := hH
    letI : Finite ((i : ι) → H i) := inferInstance
    exact Finite.of_injective f hf

/-- The class of all finite groups contains the trivial quotients. -/
instance allFinite_containsTrivialQuotients :
    ContainsTrivialQuotients (allFinite : FiniteGroupClass.{u}) :=
  allFinite_formation.containsTrivialQuotients

/-- The class of all finite groups is closed under isomorphism. -/
theorem allFinite_isomClosed : IsomClosed allFinite := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  letI : Finite G := hG
  exact Finite.of_equiv G e.toEquiv

/-- The class of all finite groups is closed under subgroups. -/
theorem allFinite_subgroupClosed : SubgroupClosed allFinite := by
  intro G _ H hG
  letI : Finite G := hG
  exact Finite.of_injective H.subtype Subtype.val_injective

/-- The class of all finite groups is closed under normal subgroups. -/
theorem allFinite_normalSubgroupClosed : NormalSubgroupClosed allFinite := by
  intro G _ N _ hG
  exact allFinite_subgroupClosed N hG

/-- The class of all finite groups is quotient closed. -/
theorem allFinite_quotientClosed : QuotientClosed allFinite :=
  allFinite_formation.quotientClosed

/-- The class of all finite groups is closed under finite subdirect products. -/
theorem allFinite_finiteSubdirectProductClosed : FiniteSubdirectProductClosed allFinite :=
  allFinite_formation.finiteSubdirectProductClosed

/-- The class of all finite groups is extension closed. -/
theorem allFinite_extensionClosed : ExtensionClosed allFinite := by
  intro E _ N _ hN hQ
  letI : Finite N := hN
  letI : Finite (E ⧸ N) := hQ
  exact Finite.of_subgroup_quotient N

/-- The class of all finite groups is hereditary. -/
theorem allFinite_hereditary : Hereditary allFinite := by
  refine ⟨?_⟩
  intro G H _ _ hH f hf
  letI : Finite H := hH
  exact Finite.of_injective f hf

end FiniteGroupClass

end ProCGroups
