import ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedTau

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/ReidemeisterSchreier/FiniteQuotient/CleanedRelators.lean
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

/-- The relator family obtained by rewriting original relators and then
deleting degenerate Schreier generators. -/
def cleanedSchreierRelators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.NondegenerateSchreierSymbol) :=
  { z | ∃ q : Q, ∃ r ∈ R, z = D.cleanedTau q r }

theorem mem_cleanedSchreierRelators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) {r : FreeGroup X} (hr : r ∈ R) :
    D.cleanedTau q r ∈ D.cleanedSchreierRelators R :=
  ⟨q, r, hr, rfl⟩

noncomputable def cleanedSchreierRelatorFinset
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq (FreeGroup D.NondegenerateSchreierSymbol)]
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup D.NondegenerateSchreierSymbol) :=
  (Finset.univ : Finset Q).biUnion
    (fun q => R.image (fun r => D.cleanedTau q r))

@[simp]
theorem mem_cleanedSchreierRelatorFinset
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq (FreeGroup D.NondegenerateSchreierSymbol)]
    (R : Finset (FreeGroup X)) (z : FreeGroup D.NondegenerateSchreierSymbol) :
    z ∈ D.cleanedSchreierRelatorFinset R ↔
      z ∈ D.cleanedSchreierRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  simp only [cleanedSchreierRelatorFinset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, eq_comm,
  true_and, cleanedSchreierRelators, SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq]

@[simp]
theorem coe_cleanedSchreierRelatorFinset
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq (FreeGroup D.NondegenerateSchreierSymbol)]
    (R : Finset (FreeGroup X)) :
    ({z | z ∈ D.cleanedSchreierRelatorFinset R} :
      Set (FreeGroup D.NondegenerateSchreierSymbol)) =
      D.cleanedSchreierRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  ext z
  simp only [mem_cleanedSchreierRelatorFinset, SetLike.setOf_mem_eq, Set.setOf_mem_eq]

theorem presentationRelatorsAfterDeletingDegenerate_eq_cleaned
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R =
      D.cleanedSchreierRelators R := by
  ext z
  change z ∈
      Presented.trivializeGeneratorsHom
          D.NondegenerateSchreierSymbol D.DegenerateSchreierSymbol ''
        (FreeGroup.freeGroupCongr
            (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol) ''
          D.schreierRelators R) ↔
    z ∈ D.cleanedSchreierRelators R
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    rcases hx with ⟨q, r, hr, rfl⟩
    exact ⟨q, r, hr, rfl⟩
  · rintro ⟨q, r, hr, rfl⟩
    exact
      ⟨FreeGroup.freeGroupCongr
          (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol)
          (D.tau q r),
        ⟨D.tau q r, ⟨q, r, hr, rfl⟩, rfl⟩, rfl⟩

/-- Relators forcing the chosen quotient representatives to rewrite to the
empty word.  These are automatic for a prefix-closed Schreier transversal, but
are useful for arbitrary finite quotient sections. -/
def quotientSectionRelators :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  { q | ∃ s : Q, q = D.tau 1 (D.quotientSection s) }

def augmentedPresentationRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  D.presentationRelators R ∪ D.quotientSectionRelators

noncomputable def schreierRelatorFinset
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact Finset.univ.biUnion (fun s : Q => R.image (D.tau s))

theorem mem_schreierRelatorFinset
    (R : Finset (FreeGroup X))
    (z : FreeGroup (FiniteSchreierSymbol X Q)) :
    z ∈ D.schreierRelatorFinset R ↔
      z ∈ D.schreierRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  classical
  simp only [schreierRelatorFinset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, eq_comm, true_and,
  schreierRelators, SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq]

noncomputable def degenerateSchreierRelatorFinset [Fintype X] :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact (((Finset.univ : Finset Q).product (Finset.univ : Finset X)).filter
    (fun z =>
      D.quotientSection (D.transition z.1 z.2) =
        D.quotientSection z.1 * FreeGroup.of z.2)).image
          (fun z => FreeGroup.of z)

theorem mem_degenerateSchreierRelatorFinset [Fintype X]
    (z : FreeGroup (FiniteSchreierSymbol X Q)) :
    z ∈ D.degenerateSchreierRelatorFinset ↔
      z ∈ D.degenerateSchreierRelators := by
  classical
  simp only [degenerateSchreierRelatorFinset, transition_eq, eq_comm, Finset.product_eq_sprod,
  Finset.univ_product_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
  degenerateSchreierRelators, Set.mem_setOf_eq]

noncomputable def presentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact D.schreierRelatorFinset R ∪ D.degenerateSchreierRelatorFinset

theorem mem_presentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X))
    (z : FreeGroup (FiniteSchreierSymbol X Q)) :
    z ∈ D.presentationRelatorFinset R ↔
      z ∈ D.presentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  classical
  simp only [presentationRelatorFinset, Finset.mem_union, mem_schreierRelatorFinset, SetLike.setOf_mem_eq,
  mem_degenerateSchreierRelatorFinset, presentationRelators, Set.mem_union]

theorem coe_presentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    ({z | z ∈ D.presentationRelatorFinset R} :
      Set (FreeGroup (FiniteSchreierSymbol X Q))) =
      D.presentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  ext z
  exact D.mem_presentationRelatorFinset R z

noncomputable def quotientSectionRelatorFinset :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact Finset.univ.image (fun s : Q => D.tau 1 (D.quotientSection s))

theorem mem_quotientSectionRelatorFinset
    (z : FreeGroup (FiniteSchreierSymbol X Q)) :
    z ∈ D.quotientSectionRelatorFinset ↔
      z ∈ D.quotientSectionRelators := by
  classical
  simp only [quotientSectionRelatorFinset, Finset.mem_image, Finset.mem_univ, eq_comm, true_and,
  quotientSectionRelators, Set.mem_setOf_eq]

noncomputable def augmentedPresentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact D.presentationRelatorFinset R ∪ D.quotientSectionRelatorFinset

theorem mem_augmentedPresentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X))
    (z : FreeGroup (FiniteSchreierSymbol X Q)) :
    z ∈ D.augmentedPresentationRelatorFinset R ↔
      z ∈ D.augmentedPresentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  classical
  simp only [augmentedPresentationRelatorFinset, Finset.mem_union, mem_presentationRelatorFinset,
  SetLike.setOf_mem_eq, mem_quotientSectionRelatorFinset, augmentedPresentationRelators, Set.mem_union]

theorem coe_augmentedPresentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    ({z | z ∈ D.augmentedPresentationRelatorFinset R} :
      Set (FreeGroup (FiniteSchreierSymbol X Q))) =
      D.augmentedPresentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  ext z
  exact D.mem_augmentedPresentationRelatorFinset R z

end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete.ReidemeisterSchreier
