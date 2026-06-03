import Mathlib.FieldTheory.IsAlgClosed.Basic
import ProCGroups.Completion.ProCIntegerPrimePower
import ProCGroups.FreeProC.Basic
import ProCGroups.ProC.GroupPredicates.Standard

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/CanonicalData.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u v

/-- The usual delta-basis map into a direct product. -/
noncomputable def deltaBasisMap
    {X : Type u} {A : Type v} [One A] (a : A) : X → (X → A) := by
  classical
  exact fun x y => if y = x then a else 1

@[simp]
theorem deltaBasisMap_apply_self
    {X : Type u} {A : Type v} [One A] (a : A) (x : X) :
    deltaBasisMap (X := X) (A := A) a x x = a := by
  classical
  simp only [deltaBasisMap, ↓reduceIte]

@[simp]
theorem deltaBasisMap_apply_ne
    {X : Type u} {A : Type v} [One A] (a : A) {x y : X} (h : y ≠ x) :
    deltaBasisMap (X := X) (A := A) a x y = 1 := by
  classical
  simp only [deltaBasisMap, h, ↓reduceIte]

theorem familyConvergesToOne_rankOneBasisMap
    {G : Type u} [Group G] [TopologicalSpace G] (g : G) :
    FamilyConvergesToOne (G := G) (Function.const PUnit g) := by
  exact FamilyConvergesToOne.of_finite_domain (G := G) (Function.const PUnit g)

theorem topologicallyGenerates_rankOneBasisMap
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {g : G}
    (hg : Generation.TopologicallyGenerates (G := G) ({g} : Set G)) :
    Generation.TopologicallyGenerates (G := G) (Set.range (Function.const PUnit g)) := by
  have hrange : Set.range (Function.const PUnit g) = ({g} : Set G) := by
    ext y
    simp only [mem_range, Function.const, exists_const, mem_singleton_iff, eq_comm]
  rw [hrange]
  exact hg

/-- The ordinary profinite integers, with their canonical generator, give the expected rank-one
profinite generating datum. -/
theorem profiniteInteger_rankOneGeneratingData :
    ∃ ι : PUnit →
        Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0})),
      ProCGroups.ProC.allFiniteProC (G :=
        Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))) ∧
        FamilyConvergesToOne (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))) ι ∧
        Generation.TopologicallyGenerates (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0})))
          (Set.range ι) := by
  let G : Type := Multiplicative
    (Completion.ProCIntegerLimitCarrier
      (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))
  let g : G := Completion.proCIntegerOne
    (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))
  refine ⟨Function.const PUnit g, ?_, ?_, ?_⟩
  · exact Completion.isProCGroup_multiplicative_proCInteger_allFinite.1
  · exact familyConvergesToOne_rankOneBasisMap (G := G) g
  · exact topologicallyGenerates_rankOneBasisMap
      (G := G) (g := g)
      Completion.topologicallyGenerates_singleton_proCIntegerOne_allFinite

/-- The pro-`p` integers, with their canonical generator, give the expected rank-one pro-`p`
generating datum. -/
theorem proPInteger_rankOneGeneratingData (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ ι : PUnit →
        Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0})),
      ProCGroups.ProC.proPProC p (G :=
        Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))) ∧
        FamilyConvergesToOne (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))) ι ∧
        Generation.TopologicallyGenerates (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0})))
          (Set.range ι) := by
  let G : Type := Multiplicative
    (Completion.ProCIntegerLimitCarrier
      (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))
  let g : G := Completion.proCIntegerOne
    (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))
  refine ⟨Function.const PUnit g, ?_, ?_, ?_⟩
  · exact Completion.isProPGroup_multiplicative_proCInteger_pGroup (p := p)
  · exact familyConvergesToOne_rankOneBasisMap (G := G) g
  · exact topologicallyGenerates_rankOneBasisMap
      (G := G) (g := g)
      (Completion.topologicallyGenerates_singleton_proCIntegerOne_pGroup (p := p))

namespace Applications
namespace FunctionFieldGalois

/-- Application-specific bundled data for a profinite group modeled on
`Gal(K(t)^alg/K(t))`.  This lives outside the reusable FreeProC API because the
Galois interpretation is extra mathematical input, not part of the abstract
free pro-`C` interface. -/
structure ModelData
    (K : Type u) [Field K] [IsAlgClosed K] where
  carrier : Type u
  instGroup : Group carrier
  instTopologicalSpace : TopologicalSpace carrier
  instIsTopologicalGroup : IsTopologicalGroup carrier
  isGaloisModel : Prop
  basis : Type u
  basisCard : Cardinal.mk basis = Cardinal.mk K
  basisMap : basis → carrier
  freeProfiniteBasis :
    IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.allFiniteProC) basis carrier basisMap

attribute [instance] ModelData.instGroup
attribute [instance] ModelData.instTopologicalSpace
attribute [instance] ModelData.instIsTopologicalGroup

end FunctionFieldGalois
end Applications

end ProCGroups.FreeProC
