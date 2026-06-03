import ProCGroups.FreeProC.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Generation/GeneratingFamilies.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topological generation

Develops topological generation, generating families, convergence-to-one criteria, quotient generation, and profinite generation lemmas.
-/

open scoped Cardinal

namespace ProCGroups.Generation

universe u

/-- An indexed topological generating family converging to `1`.

This is deliberately weaker than a free pro-`C` basis: it records only generation and convergence
of the image. -/
structure TopologicalGeneratingFamily
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  index : Type u
  toFun : index → G
  convergesToOne : _root_.ProCGroups.FreeProC.FamilyConvergesToOne (G := G) toFun
  generates : TopologicallyGenerates (G := G) (Set.range toFun)

namespace TopologicalGeneratingFamily

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instCoeFunTopologicalGeneratingFamily :
    CoeFun (TopologicalGeneratingFamily G) (fun family => family.index → G) where
  coe family := family.toFun

@[simp] theorem toFun_eq_coe (family : TopologicalGeneratingFamily G) :
    family.toFun = (family : family.index → G) := rfl

/-- The cardinality of the indexing type. -/
def cardinal (family : TopologicalGeneratingFamily G) : Cardinal :=
  Cardinal.mk family.index

end TopologicalGeneratingFamily

end ProCGroups.Generation
