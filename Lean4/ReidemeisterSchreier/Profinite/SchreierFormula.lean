import ReidemeisterSchreier.Profinite.OpenSubgroups.RankBound
import ReidemeisterSchreier.Profinite.OpenSubgroups.SchreierTransversals

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/SchreierFormula.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# ReidemeisterSchreier / Profinite / SchreierFormula

Focused module in the public source tree. It contains declarations used by the library roots and by downstream proof modules.
-/

open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC

universe u

/-- `G` admits a free pro-`C` model on a converging set. -/
def HasFreeProCConvergingSetModel
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
    Nonempty (Fdata.carrier ≃ₜ* G)

/-- `G` admits a free pro-`C` model on a converging set of cardinal `m`. -/
def HasFreeProCConvergingSetModelOfRank
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G]
    (m : Cardinal) : Prop :=
  ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
    Nonempty (Fdata.carrier ≃ₜ* G) ∧ Cardinal.mk Fdata.basis = m

section FormulaPredicates

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A group with topological rank `r` satisfies Schreier's formula at rank `r` if every open
normal subgroup has the expected rank transform. -/
def SatisfiesOpenNormalSchreierFormulaAtRank
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (r : ℕ) : Prop :=
  ∀ U : OpenNormalSubgroup G,
    Generation.topologicalRank ↥(U : Subgroup G) =
      (_root_.ReidemeisterSchreier.Schreier.rankTransform r (Nat.card (G ⧸ (U : Subgroup G))) : Cardinal)

/-- A group satisfies Schreier's formula if the rank transform holds at its finite topological
rank. -/
def SatisfiesOpenNormalSchreierFormula
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∃ r : ℕ,
    Generation.topologicalRank G = r ∧ SatisfiesOpenNormalSchreierFormulaAtRank (G := G) r

end FormulaPredicates

section ChosenLeftFamilies

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- The chosen left Schreier generator family attached to an open subgroup. -/
noncomputable def chosenLeftSchreierGeneratorFamily
    (H : OpenSubgroup F) :
    (F ⧸ (H : Subgroup F)) × X → ↥(H : Subgroup F) :=
  fun p =>
    leftSchreierGenerator
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι) p.1 p.2

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
@[simp] theorem chosenLeftSchreierGeneratorFamily_apply
    (H : OpenSubgroup F) (q : F ⧸ (H : Subgroup F)) (x : X) :
    chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) =
      leftSchreierGenerator
        (F := F) (H := H)
        (σ := openSubgroupLeftSchreierSection (F := F) H)
        (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
        (ι := ι) q x :=
  rfl

/-- The nontrivial chosen left Schreier generators attached to an open subgroup. -/
def chosenLeftSchreierGeneratorSet
    (H : OpenSubgroup F) : Set ↥(H : Subgroup F) :=
  leftSchreierGeneratorSet
    (F := F) (H := H)
    (σ := openSubgroupLeftSchreierSection (F := F) H)
    (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
    (ι := ι)

/-- The nontrivial chosen left Schreier pairs attached to an open subgroup. -/
def chosenLeftNontrivialSchreierPairs
    (H : OpenSubgroup F) : Type u :=
  leftNontrivialSchreierPairs
    (F := F) H
    (openSubgroupLeftSchreierSection (F := F) H)
    (openSubgroupLeftSchreierSection_rightInverse (F := F) H)
    ι

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
/-- The tautological map from chosen nontrivial left pairs to the chosen generator set. -/
noncomputable def chosenLeftNontrivialSchreierPairsToGeneratorSet
    (H : OpenSubgroup F) :
    chosenLeftNontrivialSchreierPairs (F := F) (ι := ι) H →
      ↥(chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) :=
  leftNontrivialSchreierPairsToGeneratorSet
    (F := F) H
    (openSubgroupLeftSchreierSection (F := F) H)
    (openSubgroupLeftSchreierSection_rightInverse (F := F) H)
    ι

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
@[simp] theorem chosenLeftNontrivialSchreierPairsToGeneratorSet_apply
    (H : OpenSubgroup F)
    (p : chosenLeftNontrivialSchreierPairs (F := F) (ι := ι) H) :
    ((chosenLeftNontrivialSchreierPairsToGeneratorSet (F := F) (ι := ι) H p :
        ↥(chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H)) : ↥(H : Subgroup F)) =
      chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H p.1 :=
  rfl

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem surjective_chosenLeftNontrivialSchreierPairsToGeneratorSet
    (H : OpenSubgroup F) :
    Function.Surjective
      (chosenLeftNontrivialSchreierPairsToGeneratorSet (F := F) (ι := ι) H) := by
  simpa [chosenLeftNontrivialSchreierPairsToGeneratorSet,
    chosenLeftNontrivialSchreierPairs, chosenLeftSchreierGeneratorSet] using
    (surjective_leftNontrivialSchreierPairsToGeneratorSet
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierGeneratorSet_subset_range
    (H : OpenSubgroup F) :
    chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H ⊆
      Set.range (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H) := by
  simpa [chosenLeftSchreierGeneratorSet, chosenLeftSchreierGeneratorFamily] using
    (leftSchreierGeneratorSet_subset_range
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem subgroupClosure_chosenLeftSchreierGeneratorSet_eq_closure_range
    (H : OpenSubgroup F) :
    Subgroup.closure (chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) =
      Subgroup.closure (Set.range
        (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H)) := by
  simpa [chosenLeftSchreierGeneratorSet, chosenLeftSchreierGeneratorFamily] using
    (subgroupClosure_leftSchreierGeneratorSet_eq_closure_range
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] in
theorem topologicallyGenerates_chosenLeftSchreierGeneratorSet_iff
    {H : OpenSubgroup F} :
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) ↔
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (Set.range (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H)) := by
  simpa [chosenLeftSchreierGeneratorSet, chosenLeftSchreierGeneratorFamily] using
      (topologicallyGenerates_leftSchreierGeneratorSet_iff
        (F := F) (H := H)
        (σ := openSubgroupLeftSchreierSection (F := F) H)
        (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
        (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierNextCoset_eq_of_mem
      (H : OpenSubgroup F) {q : F ⧸ (H : Subgroup F)} {x : X}
      (hx : ι x ∈ (H : Subgroup F)) :
      leftSchreierNextCoset (F := F) H (openSubgroupLeftSchreierSection (F := F) H) ι q x =
        q :=
    leftSchreierNextCoset_eq_of_mem
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (ι := ι)
      (openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      hx

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierNextCoset_eq_basepoint_of_mul_mem
      (H : OpenSubgroup F) {q : F ⧸ (H : Subgroup F)} {x : X}
      (hx : openSubgroupLeftSchreierSection (F := F) H q * ι x ∈ (H : Subgroup F)) :
      leftSchreierNextCoset (F := F) H (openSubgroupLeftSchreierSection (F := F) H) ι q x =
        QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) :=
    leftSchreierNextCoset_eq_basepoint_of_mul_mem
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (ι := ι)
      hx

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierGeneratorFamily_eq_of_mem
      (H : OpenSubgroup F) {q : F ⧸ (H : Subgroup F)} {x : X}
      (hx : ι x ∈ (H : Subgroup F)) :
      chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) = ⟨ι x, hx⟩ := by
    simpa [chosenLeftSchreierGeneratorFamily] using
      (leftSchreierGenerator_eq_of_mem
        (F := F) (H := H)
        (σ := openSubgroupLeftSchreierSection (F := F) H)
        (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
        (ι := ι)
        (q := q) (x := x) hx)

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierGeneratorFamily_eq_one
      (H : OpenSubgroup F) {q : F ⧸ (H : Subgroup F)} {x : X}
      (hx : ι x = 1) :
    chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) = 1 := by
  exact leftSchreierGenerator_eq_one
    (F := F) (H := H)
    (σ := openSubgroupLeftSchreierSection (F := F) H)
    (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
    (ι := ι) (q := q) (x := x) hx

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierGeneratorFamily_eq_one_iff
    {H : OpenSubgroup F} {q : F ⧸ (H : Subgroup F)} {x : X} :
    chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) = 1 ↔
      openSubgroupLeftSchreierSection (F := F) H
          (leftSchreierNextCoset (F := F) H
            (openSubgroupLeftSchreierSection (F := F) H) ι q x) =
        openSubgroupLeftSchreierSection (F := F) H q * ι x := by
  simpa [chosenLeftSchreierGeneratorFamily] using
    (leftSchreierGenerator_eq_one_iff
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι) (q := q) (x := x))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenLeftSchreierGeneratorFamily_eq_of_mul_mem
    (H : OpenSubgroup F) {q : F ⧸ (H : Subgroup F)} {x : X}
    (hx : openSubgroupLeftSchreierSection (F := F) H q * ι x ∈ (H : Subgroup F)) :
    chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) =
      ⟨openSubgroupLeftSchreierSection (F := F) H q * ι x, hx⟩ := by
  simpa [chosenLeftSchreierGeneratorFamily] using
    (leftSchreierGenerator_eq_of_mul_mem
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι)
      (openSubgroupLeftSchreierSection_one (F := F) H)
      (q := q) (x := x) hx)

omit [CompactSpace X] in
theorem continuous_chosenLeftSchreierNextCoset
    (H : OpenSubgroup F)
    (hιcont : Continuous ι) :
    Continuous (fun p : (F ⧸ (H : Subgroup F)) × X =>
      leftSchreierNextCoset (F := F) H (openSubgroupLeftSchreierSection (F := F) H) ι
        p.1 p.2) := by
  exact continuous_leftSchreierNextCoset
    (F := F) (H := H)
    (σ := openSubgroupLeftSchreierSection (F := F) H)
    (ι := ι)
    (continuous_openSubgroupLeftSchreierSection (F := F) H)
    hιcont

omit [CompactSpace X] in
theorem continuous_chosenLeftSchreierGeneratorFamily
    (H : OpenSubgroup F)
    (hιcont : Continuous ι) :
    Continuous (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H) := by
  simpa [chosenLeftSchreierGeneratorFamily] using
    (continuous_leftSchreierGenerator
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι)
      (continuous_openSubgroupLeftSchreierSection (F := F) H)
      hιcont)

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenLeftSchreierGeneratorSet_le
    (H : OpenSubgroup F) [CompactSpace F] [Finite X] :
    Nat.card (chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) ≤
      Nat.card (F ⧸ (H : Subgroup F)) * Nat.card X := by
  letI : Finite (F ⧸ (H : Subgroup F)) :=
    ProCGroups.openSubgroup_finiteQuotient (G := F) H
  exact natCard_leftSchreierGeneratorSet_le
    (F := F) (H := H)
    (σ := openSubgroupLeftSchreierSection (F := F) H)
    (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
    (ι := ι)

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenLeftNontrivialSchreierPairs_le
    (H : OpenSubgroup F) [CompactSpace F] [Finite X] :
    Nat.card (chosenLeftNontrivialSchreierPairs (F := F) (ι := ι) H) ≤
      Nat.card (F ⧸ (H : Subgroup F)) * Nat.card X := by
  letI : Finite (F ⧸ (H : Subgroup F)) :=
    ProCGroups.openSubgroup_finiteQuotient (G := F) H
  simpa [chosenLeftNontrivialSchreierPairs] using
    (natCard_leftNontrivialSchreierPairs_le
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenLeftSchreierGeneratorSet_le_nontrivialPairs
    (H : OpenSubgroup F) [CompactSpace F] [Finite X] :
    Nat.card (chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) ≤
      Nat.card (chosenLeftNontrivialSchreierPairs (F := F) (ι := ι) H) := by
  letI : Finite (F ⧸ (H : Subgroup F)) :=
    ProCGroups.openSubgroup_finiteQuotient (G := F) H
  simpa [chosenLeftSchreierGeneratorSet, chosenLeftNontrivialSchreierPairs] using
    (natCard_leftSchreierGeneratorSet_le_nontrivialPairs
      (F := F) (H := H)
      (σ := openSubgroupLeftSchreierSection (F := F) H)
      (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_range_chosenLeftSchreierGeneratorFamily_le_rankTransform
    [Finite X] {x0 : X} (hx0 : ι x0 = 1)
    (H : OpenSubgroup F) [CompactSpace F] :
    Nat.card (Set.range (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H)) ≤
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) := by
  letI : Nonempty X := ⟨x0⟩
  letI : Finite (F ⧸ (H : Subgroup F)) :=
    ProCGroups.openSubgroup_finiteQuotient (G := F) H
  let q0 : F ⧸ (H : Subgroup F) := QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)
  let κ' : Option ((F ⧸ (H : Subgroup F)) × {x : X // x ≠ x0}) → ↥(H : Subgroup F)
    | none => 1
    | some p => chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (p.1, p.2.1)
  have hbase :
      ∀ q : F ⧸ (H : Subgroup F),
        chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H (q, x0) = 1 := by
    intro q
    simpa [chosenLeftSchreierGeneratorFamily] using
      (leftSchreierGenerator_eq_one
        (F := F) (H := H)
        (σ := openSubgroupLeftSchreierSection (F := F) H)
        (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
        (ι := ι) (q := q) (x := x0) hx0)
  have hrange :
      Set.range (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H) =
        Set.range κ' := by
    ext y
    constructor
    · rintro ⟨⟨q, x⟩, rfl⟩
      by_cases hx : x = x0
      · refine ⟨none, ?_⟩
        subst hx
        simp only [ne_eq, chosenLeftSchreierGeneratorFamily_apply, hbase q, κ']
      · refine ⟨some (q, ⟨x, hx⟩), ?_⟩
        simp only [ne_eq, chosenLeftSchreierGeneratorFamily_apply, κ']
    · rintro ⟨p, rfl⟩
      cases p with
      | none =>
          exact ⟨(q0, x0), by simp only [hbase q0, ne_eq, chosenLeftSchreierGeneratorFamily_apply, κ']⟩
      | some p =>
          rcases p with ⟨q, x⟩
          exact ⟨(q, x), by simp only [ne_eq, chosenLeftSchreierGeneratorFamily_apply, κ']⟩
  have hcardCompl : Nat.card {x : X // x ≠ x0} = Nat.card X - 1 := by
    letI : Fintype X := Fintype.ofFinite X
    letI : Fintype {x : X // x = x0} := Fintype.ofFinite _
    letI : Fintype {x : X // x ≠ x0} := Fintype.ofFinite _
    simp only [ne_eq, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique]
  have hsucc : Nat.card X = Nat.card {x : X // x ≠ x0} + 1 := by
    exact (Nat.sub_eq_iff_eq_add Nat.card_pos).1 hcardCompl.symm
  calc
    Nat.card (Set.range (chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H)) =
      Nat.card (Set.range κ') := by
        rw [hrange]
    _ ≤ Nat.card (Option ((F ⧸ (H : Subgroup F)) × {x : X // x ≠ x0})) := by
      exact Finite.card_range_le κ'
    _ = Nat.card ((F ⧸ (H : Subgroup F)) × {x : X // x ≠ x0}) + 1 := by
      rw [Finite.card_option]
    _ = Nat.card (F ⧸ (H : Subgroup F)) * Nat.card {x : X // x ≠ x0} + 1 := by
      rw [Nat.card_prod]
    _ = 1 + Nat.card (F ⧸ (H : Subgroup F)) * Nat.card {x : X // x ≠ x0} := by
      rw [Nat.add_comm]
    _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) := by
      rw [hsucc, _root_.ReidemeisterSchreier.Schreier.rankTransform_succ]

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenLeftSchreierGeneratorSet_le_rankTransform
    [Finite X] {x0 : X} (hx0 : ι x0 = 1)
    (H : OpenSubgroup F) [CompactSpace F] :
    Nat.card (chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) ≤
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) := by
  let f := chosenLeftSchreierGeneratorFamily (F := F) (ι := ι) H
  have hsub : chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H ⊆ Set.range f := by
    simpa [chosenLeftSchreierGeneratorSet, f, chosenLeftSchreierGeneratorFamily] using
      (leftSchreierGeneratorSet_subset_range
        (F := F) (H := H)
        (σ := openSubgroupLeftSchreierSection (F := F) H)
        (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)
        (ι := ι))
  letI : Finite (Set.range f) := Set.finite_range f
  have hle :
      Nat.card (chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H) ≤
        Nat.card (Set.range f) := by
    exact Nat.card_le_card_of_injective
      (fun z : chosenLeftSchreierGeneratorSet (F := F) (ι := ι) H =>
        (⟨z.1, hsub z.2⟩ : Set.range f))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun y : Set.range f => (y : ↥(H : Subgroup F))) h)
  exact hle.trans
    (natCard_range_chosenLeftSchreierGeneratorFamily_le_rankTransform
      (F := F) (ι := ι) hx0 H)

end ChosenLeftFamilies

section ChosenRightFamilies

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- The chosen right Schreier generator family attached to an open subgroup. -/
noncomputable def chosenRightSchreierGeneratorFamily
    (H : OpenSubgroup F) :
    OpenSubgroupRightQuotient H × X → ↥(H : Subgroup F) :=
  fun p =>
    rightSchreierGenerator
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι) p.1 p.2

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
@[simp] theorem chosenRightSchreierGeneratorFamily_apply
    (H : OpenSubgroup F) (q : OpenSubgroupRightQuotient H) (x : X) :
    chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) =
      rightSchreierGenerator
        (F := F) (H := H)
        (τ := openSubgroupRightCosetSection (F := F) H)
        (hτ := openSubgroupRightCosetSection_spec (F := F) H)
        (ι := ι) q x :=
  rfl

/-- The nontrivial chosen right Schreier generators attached to an open subgroup. -/
def chosenRightSchreierGeneratorSet
    (H : OpenSubgroup F) : Set ↥(H : Subgroup F) :=
  rightSchreierGeneratorSet
    (F := F) (H := H)
    (τ := openSubgroupRightCosetSection (F := F) H)
    (hτ := openSubgroupRightCosetSection_spec (F := F) H)
    (ι := ι)

/-- The nontrivial chosen right Schreier pairs attached to an open subgroup. -/
def chosenRightNontrivialSchreierPairs
    (H : OpenSubgroup F) : Type u :=
  rightNontrivialSchreierPairs
    (F := F) H
    (openSubgroupRightCosetSection (F := F) H)
    (openSubgroupRightCosetSection_spec (F := F) H)
    ι

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
/-- The tautological map from chosen nontrivial right pairs to the chosen generator set. -/
noncomputable def chosenRightNontrivialSchreierPairsToGeneratorSet
    (H : OpenSubgroup F) :
    chosenRightNontrivialSchreierPairs (F := F) (ι := ι) H →
      ↥(chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) :=
  rightNontrivialSchreierPairsToGeneratorSet
    (F := F) H
    (openSubgroupRightCosetSection (F := F) H)
    (openSubgroupRightCosetSection_spec (F := F) H)
    ι

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
@[simp] theorem chosenRightNontrivialSchreierPairsToGeneratorSet_apply
    (H : OpenSubgroup F)
    (p : chosenRightNontrivialSchreierPairs (F := F) (ι := ι) H) :
    ((chosenRightNontrivialSchreierPairsToGeneratorSet (F := F) (ι := ι) H p :
        ↥(chosenRightSchreierGeneratorSet (F := F) (ι := ι) H)) : ↥(H : Subgroup F)) =
      chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H p.1 :=
  rfl

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem surjective_chosenRightNontrivialSchreierPairsToGeneratorSet
    (H : OpenSubgroup F) :
    Function.Surjective
      (chosenRightNontrivialSchreierPairsToGeneratorSet (F := F) (ι := ι) H) := by
  simpa [chosenRightNontrivialSchreierPairsToGeneratorSet,
    chosenRightNontrivialSchreierPairs, chosenRightSchreierGeneratorSet] using
    (surjective_rightNontrivialSchreierPairsToGeneratorSet
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierGeneratorSet_subset_range
    (H : OpenSubgroup F) :
    chosenRightSchreierGeneratorSet (F := F) (ι := ι) H ⊆
      Set.range (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H) := by
  simpa [chosenRightSchreierGeneratorSet, chosenRightSchreierGeneratorFamily] using
    (rightSchreierGeneratorSet_subset_range
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem subgroupClosure_chosenRightSchreierGeneratorSet_eq_closure_range
    (H : OpenSubgroup F) :
    Subgroup.closure (chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) =
      Subgroup.closure (Set.range
        (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H)) := by
  simpa [chosenRightSchreierGeneratorSet, chosenRightSchreierGeneratorFamily] using
    (subgroupClosure_rightSchreierGeneratorSet_eq_closure_range
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] in
theorem topologicallyGenerates_chosenRightSchreierGeneratorSet_iff
    {H : OpenSubgroup F} :
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) ↔
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (Set.range (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H)) := by
  simpa [chosenRightSchreierGeneratorSet, chosenRightSchreierGeneratorFamily] using
      (topologicallyGenerates_rightSchreierGeneratorSet_iff
        (F := F) (H := H)
        (τ := openSubgroupRightCosetSection (F := F) H)
        (hτ := openSubgroupRightCosetSection_spec (F := F) H)
        (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierNextCoset_basepoint_eq_of_mem
      (H : OpenSubgroup F) {x : X}
      (hx : ι x ∈ (H : Subgroup F)) :
      rightSchreierNextCoset (F := F) H ι (openSubgroupRightCoset H (1 : F)) x =
        openSubgroupRightCoset H (1 : F) :=
    rightSchreierNextCoset_basepoint_eq_of_mem
      (F := F) (H := H) (ι := ι) hx

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierNextCoset_eq_basepoint_of_mul_mem
      (H : OpenSubgroup F) {q : OpenSubgroupRightQuotient H} {x : X}
      (hx : openSubgroupRightCosetSection (F := F) H q * ι x ∈ (H : Subgroup F)) :
      rightSchreierNextCoset (F := F) H ι q x = openSubgroupRightCoset H (1 : F) :=
    rightSchreierNextCoset_eq_basepoint_of_mul_mem
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι)
      hx

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierGeneratorFamily_eq_one
      (H : OpenSubgroup F) {q : OpenSubgroupRightQuotient H} {x : X}
      (hx : ι x = 1) :
    chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) = 1 := by
  exact rightSchreierGenerator_eq_one
    (F := F) (H := H)
    (τ := openSubgroupRightCosetSection (F := F) H)
    (hτ := openSubgroupRightCosetSection_spec (F := F) H)
    (ι := ι) (q := q) (x := x) hx

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierGeneratorFamily_eq_one_iff
    {H : OpenSubgroup F} {q : OpenSubgroupRightQuotient H} {x : X} :
    chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) = 1 ↔
      openSubgroupRightCosetSection (F := F) H
          (rightSchreierNextCoset (F := F) H ι q x) =
        openSubgroupRightCosetSection (F := F) H q * ι x := by
  simpa [chosenRightSchreierGeneratorFamily] using
      (rightSchreierGenerator_eq_one_iff_nextCoset
        (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι) (q := q) (x := x))

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierGeneratorFamily_basepoint_eq_of_mem
      (H : OpenSubgroup F) {x : X}
      (hx : ι x ∈ (H : Subgroup F)) :
      chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H
          (openSubgroupRightCoset H (1 : F), x) =
        ⟨ι x, hx⟩ := by
    simpa [chosenRightSchreierGeneratorFamily] using
      (rightSchreierGenerator_basepoint_eq_of_mem
        (F := F) (H := H)
        (τ := openSubgroupRightCosetSection (F := F) H)
        (hτ := openSubgroupRightCosetSection_spec (F := F) H)
        (ι := ι)
        (openSubgroupRightCosetSection_one (F := F) H)
        (x := x) hx)

omit [TopologicalSpace X] [CompactSpace X] [IsTopologicalGroup F] in
theorem chosenRightSchreierGeneratorFamily_eq_of_mul_mem
    (H : OpenSubgroup F) {q : OpenSubgroupRightQuotient H} {x : X}
    (hx : openSubgroupRightCosetSection (F := F) H q * ι x ∈ (H : Subgroup F)) :
    chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H (q, x) =
      ⟨openSubgroupRightCosetSection (F := F) H q * ι x, hx⟩ := by
  simpa [chosenRightSchreierGeneratorFamily] using
    (rightSchreierGenerator_eq_of_mul_mem
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι)
      (openSubgroupRightCosetSection_one (F := F) H)
      (q := q) (x := x) hx)

omit [CompactSpace X] in
theorem continuous_chosenRightSchreierNextCoset
    (H : OpenSubgroup F)
    (hιcont : Continuous ι) :
    Continuous (fun p : OpenSubgroupRightQuotient H × X =>
      rightSchreierNextCoset (F := F) H ι p.1 p.2) := by
  exact continuous_rightSchreierNextCoset
    (F := F) (H := H)
    (ι := ι)
    hιcont

omit [CompactSpace X] in
theorem continuous_chosenRightSchreierGeneratorFamily
    (H : OpenSubgroup F)
    (hιcont : Continuous ι) :
    Continuous (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H) := by
  simpa [chosenRightSchreierGeneratorFamily] using
    (continuous_rightSchreierGenerator
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι)
      (continuous_openSubgroupRightCosetSection (F := F) H)
      hιcont)

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenRightSchreierGeneratorSet_le
    (H : OpenSubgroup F) [CompactSpace F] [Finite X] :
    Nat.card (chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) ≤
      Nat.card (OpenSubgroupRightQuotient H) * Nat.card X := by
  exact natCard_rightSchreierGeneratorSet_le
    (F := F) (H := H)
    (τ := openSubgroupRightCosetSection (F := F) H)
    (hτ := openSubgroupRightCosetSection_spec (F := F) H)
    (ι := ι)

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenRightNontrivialSchreierPairs_le
    (H : OpenSubgroup F) [CompactSpace F] [Finite X] :
    Nat.card (chosenRightNontrivialSchreierPairs (F := F) (ι := ι) H) ≤
      Nat.card (OpenSubgroupRightQuotient H) * Nat.card X := by
  letI : Finite (OpenSubgroupRightQuotient H) := finite_openSubgroupRightQuotient (F := F) H
  simpa [chosenRightNontrivialSchreierPairs] using
    (natCard_rightNontrivialSchreierPairs_le
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenRightSchreierGeneratorSet_le_nontrivialPairs
    (H : OpenSubgroup F) [CompactSpace F] [Finite X] :
    Nat.card (chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) ≤
      Nat.card (chosenRightNontrivialSchreierPairs (F := F) (ι := ι) H) := by
  letI : Finite (OpenSubgroupRightQuotient H) := finite_openSubgroupRightQuotient (F := F) H
  simpa [chosenRightSchreierGeneratorSet, chosenRightNontrivialSchreierPairs] using
    (natCard_rightSchreierGeneratorSet_le_nontrivialPairs
      (F := F) (H := H)
      (τ := openSubgroupRightCosetSection (F := F) H)
      (hτ := openSubgroupRightCosetSection_spec (F := F) H)
      (ι := ι))

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_range_chosenRightSchreierGeneratorFamily_le_rankTransform
    [Finite X] {x0 : X} (hx0 : ι x0 = 1)
    (H : OpenSubgroup F) [CompactSpace F] :
    Nat.card (Set.range (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H)) ≤
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (OpenSubgroupRightQuotient H)) := by
  letI : Nonempty X := ⟨x0⟩
  letI : Finite (OpenSubgroupRightQuotient H) := finite_openSubgroupRightQuotient (F := F) H
  let q0 : OpenSubgroupRightQuotient H := openSubgroupRightCoset H (1 : F)
  let κ' : Option (OpenSubgroupRightQuotient H × {x : X // x ≠ x0}) → ↥(H : Subgroup F)
    | none => 1
    | some p => chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H (p.1, p.2.1)
  have hbase :
      ∀ q : OpenSubgroupRightQuotient H,
        chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H (q, x0) = 1 := by
    intro q
    simpa [chosenRightSchreierGeneratorFamily] using
      (rightSchreierGenerator_eq_one
        (F := F) (H := H)
        (τ := openSubgroupRightCosetSection (F := F) H)
        (hτ := openSubgroupRightCosetSection_spec (F := F) H)
        (ι := ι) (q := q) (x := x0) hx0)
  have hrange :
      Set.range (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H) =
        Set.range κ' := by
    ext y
    constructor
    · rintro ⟨⟨q, x⟩, rfl⟩
      by_cases hx : x = x0
      · refine ⟨none, ?_⟩
        subst hx
        simp only [ne_eq, chosenRightSchreierGeneratorFamily_apply, hbase q, κ']
      · refine ⟨some (q, ⟨x, hx⟩), ?_⟩
        simp only [ne_eq, chosenRightSchreierGeneratorFamily_apply, κ']
    · rintro ⟨p, rfl⟩
      cases p with
      | none =>
          exact ⟨(q0, x0), by simp only [hbase q0, ne_eq, chosenRightSchreierGeneratorFamily_apply, κ']⟩
      | some p =>
          rcases p with ⟨q, x⟩
          exact ⟨(q, x), by simp only [ne_eq, chosenRightSchreierGeneratorFamily_apply, κ']⟩
  have hcardCompl : Nat.card {x : X // x ≠ x0} = Nat.card X - 1 := by
    letI : Fintype X := Fintype.ofFinite X
    letI : Fintype {x : X // x = x0} := Fintype.ofFinite _
    letI : Fintype {x : X // x ≠ x0} := Fintype.ofFinite _
    simp only [ne_eq, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique]
  have hsucc : Nat.card X = Nat.card {x : X // x ≠ x0} + 1 := by
    exact (Nat.sub_eq_iff_eq_add Nat.card_pos).1 hcardCompl.symm
  calc
    Nat.card (Set.range (chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H)) =
      Nat.card (Set.range κ') := by
        rw [hrange]
    _ ≤ Nat.card (Option (OpenSubgroupRightQuotient H × {x : X // x ≠ x0})) := by
      exact Finite.card_range_le κ'
    _ = Nat.card (OpenSubgroupRightQuotient H × {x : X // x ≠ x0}) + 1 := by
      rw [Finite.card_option]
    _ = Nat.card (OpenSubgroupRightQuotient H) * Nat.card {x : X // x ≠ x0} + 1 := by
      rw [Nat.card_prod]
    _ = 1 + Nat.card (OpenSubgroupRightQuotient H) * Nat.card {x : X // x ≠ x0} := by
      rw [Nat.add_comm]
    _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (OpenSubgroupRightQuotient H)) := by
      rw [hsucc, _root_.ReidemeisterSchreier.Schreier.rankTransform_succ]

omit [TopologicalSpace X] [CompactSpace X] in
theorem natCard_chosenRightSchreierGeneratorSet_le_rankTransform
    [Finite X] {x0 : X} (hx0 : ι x0 = 1)
    (H : OpenSubgroup F) [CompactSpace F] :
    Nat.card (chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) ≤
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (OpenSubgroupRightQuotient H)) := by
  let f := chosenRightSchreierGeneratorFamily (F := F) (ι := ι) H
  have hsub : chosenRightSchreierGeneratorSet (F := F) (ι := ι) H ⊆ Set.range f := by
    simpa [chosenRightSchreierGeneratorSet, f, chosenRightSchreierGeneratorFamily] using
      (rightSchreierGeneratorSet_subset_range
        (F := F) (H := H)
        (τ := openSubgroupRightCosetSection (F := F) H)
        (hτ := openSubgroupRightCosetSection_spec (F := F) H)
        (ι := ι))
  letI : Finite (Set.range f) := Set.finite_range f
  have hle :
      Nat.card (chosenRightSchreierGeneratorSet (F := F) (ι := ι) H) ≤
        Nat.card (Set.range f) := by
    exact Nat.card_le_card_of_injective
      (fun z : chosenRightSchreierGeneratorSet (F := F) (ι := ι) H =>
        (⟨z.1, hsub z.2⟩ : Set.range f))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun y : Set.range f => (y : ↥(H : Subgroup F))) h)
  exact hle.trans
    (natCard_range_chosenRightSchreierGeneratorFamily_le_rankTransform
      (F := F) (ι := ι) hx0 H)

end ChosenRightFamilies

end Profinite
end ReidemeisterSchreier
