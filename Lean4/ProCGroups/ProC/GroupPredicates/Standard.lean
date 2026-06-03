import ProCGroups.ProC.Category.Basic
import ProCGroups.ProC.InverseLimits.Predicates

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/GroupPredicates/Standard.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set
open scoped Topology

namespace ProCGroups.ProC

universe u

namespace ProCGroupPredicate

/-- On finite discrete groups, the finite quotient class induced by
`finiteGroupClassProCPredicate C` recovers `C`, provided `C` is quotient- and
isomorphism-closed. -/
theorem finiteQuotientClass_finiteGroupClassProCPredicate_iff
    {C : FiniteGroupClass.{u}}
    (hquot : FiniteGroupClass.QuotientClosed C)
    (hiso : FiniteGroupClass.IsomClosed C)
    {Q : Type u} [Group Q] [Finite Q] :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C).finiteQuotientClass Q ↔ C Q := by
  constructor
  · intro hQ
    letI : TopologicalSpace Q := ⊥
    letI : DiscreteTopology Q := ⟨rfl⟩
    letI : IsTopologicalGroup Q := inferInstance
    change Finite Q ∧ IsProCGroup C Q at hQ
    let Ubot : OpenNormalSubgroup Q :=
      { toOpenSubgroup := ⟨⊥, isOpen_discrete _⟩
        isNormal' := inferInstance }
    exact hiso ⟨QuotientGroup.quotientBot (G := Q)⟩
      (IsProCGroup.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
        hiso hquot hQ.2 Ubot)
  · intro hQ
    letI : TopologicalSpace Q := ⊥
    letI : DiscreteTopology Q := ⟨rfl⟩
    letI : IsTopologicalGroup Q := inferInstance
    exact ⟨FiniteGroupClass.finite hQ,
      IsProCGroup.of_finite_discrete (C := C) (G := Q) hquot hQ⟩

/-- Formation data transfers from a finite-group class `C` to the finite quotient class induced
by `finiteGroupClassProCPredicate C`. -/
def finiteQuotientFormation_finiteGroupClassProCPredicate
    (C : FiniteGroupClass.{u}) (hForm : FiniteGroupClass.Formation C) :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C).HasFiniteQuotientFormation where
  formation := by
    refine ⟨?_, ?_⟩
    · intro G _ N _ hG
      have hfiniteG : Finite G := by
        exact FiniteGroupClass.finite hG
      letI : Finite G := hfiniteG
      have hCG : C G :=
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1 hG
      exact
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed
          (Q := G ⧸ N)).2 (hForm.quotientClosed N hCG)
    · intro ι _ G _ H _ f hf hsurj hH
      have hfiniteH : ∀ i, Finite (H i) := by
        intro i
        exact FiniteGroupClass.finite (hH i)
      letI : ∀ i, Finite (H i) := hfiniteH
      have hCH : ∀ i, C (H i) := fun i =>
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1
          (hH i)
      have hCG : C G := hForm.finiteSubdirectProductClosed f hf hsurj hCH
      letI : Finite G := Finite.of_injective f hf
      exact
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).2 hCG

/-- Full formation data transfers from a finite-group class `C` to the finite quotient class
induced by `finiteGroupClassProCPredicate C`. -/
def finiteQuotientFullFormation_finiteGroupClassProCPredicate
    (C : FiniteGroupClass.{u}) (hFull : FiniteGroupClass.FullFormation C) :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C).HasFiniteQuotientFullFormation where
  fullFormation := by
    let hForm : FiniteGroupClass.Formation C := hFull.melnikovFormation.formation
    refine
      { melnikovFormation :=
          { formation :=
              (finiteQuotientFormation_finiteGroupClassProCPredicate C hForm).formation
            normalSubgroupClosed := ?_
            extensionClosed := ?_ }
        subgroupClosed := ?_ }
    · intro G _ N _ hG
      letI : Finite G := FiniteGroupClass.finite hG
      have hCG : C G :=
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1 hG
      have hCN : C N := hFull.melnikovFormation.normalSubgroupClosed N hCG
      letI : Finite N := FiniteGroupClass.finite hCN
      exact
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).2 hCN
    · intro E _ N _ hN hQ
      letI : Finite N := FiniteGroupClass.finite hN
      letI : Finite (E ⧸ N) := FiniteGroupClass.finite hQ
      have hCN : C N :=
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1 hN
      have hCQ : C (E ⧸ N) :=
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1 hQ
      have hCE : C E := hFull.melnikovFormation.extensionClosed N hCN hCQ
      letI : Finite E := FiniteGroupClass.finite hCE
      exact
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).2 hCE
    · intro G _ H hG
      letI : Finite G := FiniteGroupClass.finite hG
      have hCG : C G :=
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1 hG
      have hCH : C H := hFull.subgroupClosed H hCG
      letI : Finite H := FiniteGroupClass.finite hCH
      exact
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).2 hCH

/-- A finite-class pro-`C` predicate is determined by its finite quotient class whenever `C` is
a formation. -/
def determinedByFiniteQuotients_finiteGroupClassProCPredicate
    (C : FiniteGroupClass.{u}) (hForm : FiniteGroupClass.Formation C) :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C).DeterminedByFiniteQuotients where
    holds_of_isProCGroup := by
      intro G _ _ _ hG
      refine ⟨hG.isProfinite, ?_⟩
      intro W hW h1W
      rcases hG.hasOpenNormalBasisInClass W hW h1W with ⟨U, hUW, hCU⟩
      have hfinite : Finite (G ⧸ (U : Subgroup G)) := FiniteGroupClass.finite hCU
      letI : Finite (G ⧸ (U : Subgroup G)) := hfinite
      exact ⟨U, hUW,
        (finiteQuotientClass_finiteGroupClassProCPredicate_iff
          hForm.quotientClosed hForm.isomClosed).1 hCU⟩

end ProCGroupPredicate

/-- Procyclic profinite groups. -/
def procyclicProC : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate FiniteGroupClass.cyclic

/-- Proabelian profinite groups. -/
def proabelianProC : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate FiniteGroupClass.abelian

/-- Pronilpotent profinite groups. -/
def pronilpotentProC : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate FiniteGroupClass.nilpotent

/-- Prosolvable profinite groups. -/
def prosolvableProC : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate FiniteGroupClass.solvable

/-- Pro-`p` groups. -/
def proPProC (p : ℕ) : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate (FiniteGroupClass.pGroup p)

/-- Pro-`Σ` groups, for a set `Σ` of primes. -/
def proSigmaProC (sigma : Set ℕ) : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate (FiniteGroupClass.sigmaGroup sigma)

/-- On finite groups, the finite quotient class of `proSigmaProC` is exactly `sigmaGroup`. -/
theorem proSigmaProC_finiteQuotientClass_iff
    {sigma : Set ℕ} {Q : Type u} [Group Q] [Finite Q] :
    (proSigmaProC sigma).finiteQuotientClass Q ↔
      FiniteGroupClass.sigmaGroup sigma Q := by
  simpa [proSigmaProC] using
    (ProCGroupPredicate.finiteQuotientClass_finiteGroupClassProCPredicate_iff
      (FiniteGroupClass.sigmaGroup_quotientClosed sigma)
      (FiniteGroupClass.sigmaGroup_isomClosed sigma)
      (Q := Q))

/-- Proabelian groups of exponent dividing `n` on every finite quotient. -/
def abelianExponentProC (n : ℕ) : ProCGroupPredicate.{u} :=
  ProCGroups.ProC.finiteGroupClassProCPredicate (FiniteGroupClass.abelianExponent n)

/-- The proabelian predicate is stable under the finite-quotient formation operations. -/
instance proabelianProC_hasFiniteQuotientFormation :
  ProCGroupPredicate.HasFiniteQuotientFormation
      (proabelianProC : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.finiteQuotientFormation_finiteGroupClassProCPredicate
    FiniteGroupClass.abelian FiniteGroupClass.abelian_formation

/-- The proabelian predicate is determined by its finite quotients. -/
instance proabelianProC_determinedByFiniteQuotients :
  ProCGroupPredicate.DeterminedByFiniteQuotients
      (proabelianProC : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.determinedByFiniteQuotients_finiteGroupClassProCPredicate
    FiniteGroupClass.abelian FiniteGroupClass.abelian_formation

/-- The pro-p predicate is stable under the finite-quotient formation operations. -/
instance proPProC_hasFiniteQuotientFormation (p : ℕ) :
  ProCGroupPredicate.HasFiniteQuotientFormation
      (proPProC p : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.finiteQuotientFormation_finiteGroupClassProCPredicate
    (FiniteGroupClass.pGroup p) (FiniteGroupClass.pGroup_formation p)

/-- The pro-p predicate is determined by its finite quotients. -/
instance proPProC_determinedByFiniteQuotients (p : ℕ) :
  ProCGroupPredicate.DeterminedByFiniteQuotients
      (proPProC p : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.determinedByFiniteQuotients_finiteGroupClassProCPredicate
    (FiniteGroupClass.pGroup p) (FiniteGroupClass.pGroup_formation p)

/-- The pro-Sigma predicate is stable under the finite-quotient formation operations. -/
instance proSigmaProC_hasFiniteQuotientFormation (sigma : Set ℕ) :
  ProCGroupPredicate.HasFiniteQuotientFormation
      (proSigmaProC sigma : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.finiteQuotientFormation_finiteGroupClassProCPredicate
    (FiniteGroupClass.sigmaGroup sigma) (FiniteGroupClass.sigmaGroup_formation sigma)

/-- The pro-Sigma predicate has the full finite quotient formation structure. -/
instance proSigmaProC_hasFiniteQuotientFullFormation (sigma : Set ℕ) :
  ProCGroupPredicate.HasFiniteQuotientFullFormation
      (proSigmaProC sigma : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.finiteQuotientFullFormation_finiteGroupClassProCPredicate
    (FiniteGroupClass.sigmaGroup sigma) (FiniteGroupClass.sigmaGroup_fullFormation sigma)

/-- The pro-Sigma predicate is determined by its finite quotients. -/
instance proSigmaProC_determinedByFiniteQuotients (sigma : Set ℕ) :
  ProCGroupPredicate.DeterminedByFiniteQuotients
      (proSigmaProC sigma : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.determinedByFiniteQuotients_finiteGroupClassProCPredicate
    (FiniteGroupClass.sigmaGroup sigma) (FiniteGroupClass.sigmaGroup_formation sigma)

/-- The bounded-exponent abelian predicate is stable under finite-quotient formation operations. -/
instance abelianExponentProC_hasFiniteQuotientFormation (n : ℕ) :
  ProCGroupPredicate.HasFiniteQuotientFormation
      (abelianExponentProC n : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.finiteQuotientFormation_finiteGroupClassProCPredicate
    (FiniteGroupClass.abelianExponent n) (FiniteGroupClass.abelianExponent_formation n)

/-- The bounded-exponent abelian predicate is determined by its finite quotients. -/
instance abelianExponentProC_determinedByFiniteQuotients (n : ℕ) :
  ProCGroupPredicate.DeterminedByFiniteQuotients
      (abelianExponentProC n : ProCGroupPredicate.{u}) :=
  ProCGroupPredicate.determinedByFiniteQuotients_finiteGroupClassProCPredicate
    (FiniteGroupClass.abelianExponent n) (FiniteGroupClass.abelianExponent_formation n)

/-- The named procyclic predicate unfolds to `IsProcyclicGroup`. -/
@[simp]
theorem procyclicProC_holds_iff
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    procyclicProC (G := G) ↔ IsProcyclicGroup G :=
  Iff.rfl

/-- The named proabelian predicate unfolds to `IsProabelianGroup`. -/
@[simp]
theorem proabelianProC_holds_iff
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    proabelianProC (G := G) ↔ IsProabelianGroup G :=
  Iff.rfl

/-- The named pronilpotent predicate is equivalent to `IsPronilpotentGroup`. -/
@[simp]
theorem pronilpotentProC_holds_iff
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    pronilpotentProC (G := G) ↔ IsPronilpotentGroup G := by
  constructor
  · exact isPronilpotentGroup_of_isProC_nilpotent
  · exact IsPronilpotentGroup.toIsProC_nilpotent

/-- The named prosolvable predicate is equivalent to `IsProsolvableGroup`. -/
@[simp]
theorem prosolvableProC_holds_iff
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    prosolvableProC (G := G) ↔ IsProsolvableGroup G := by
  constructor
  · exact isProsolvableGroup_of_isProC_solvable
  · exact IsProsolvableGroup.toIsProC_solvable

/-- The named pro-`p` predicate unfolds to `IsProPGroup`. -/
@[simp]
theorem proPProC_holds_iff
    {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    proPProC p (G := G) ↔ IsProPGroup p G :=
  Iff.rfl

/-- The named pro-`Σ` predicate unfolds to `IsProSigmaGroup`. -/
@[simp]
theorem proSigmaProC_holds_iff
    {sigma : Set ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    proSigmaProC sigma (G := G) ↔ IsProSigmaGroup sigma G :=
  Iff.rfl

/-- The named bounded-exponent abelian predicate unfolds to the corresponding concrete pro-`C`
condition. -/
@[simp]
theorem abelianExponentProC_holds_iff
    {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    abelianExponentProC n (G := G) ↔
      IsProCGroup (FiniteGroupClass.abelianExponent n) G :=
  Iff.rfl

namespace IsProPGroup

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {G : Type u} [Group G] [TopologicalSpace G]

  /-- A pro-`p` group is pronilpotent. -/
  theorem isPronilpotentGroup (hG : IsProPGroup p G) : IsPronilpotentGroup G := by
    letI : IsTopologicalGroup G := hG.isTopologicalGroup
    refine ⟨hG.isProfinite, ?_⟩
    intro U
    exact
      (FiniteGroupClass.pGroup_to_nilpotent (p := p)
        (hG.quotient_mem (FiniteGroupClass.pGroup_formation p) U)).2

  /-- A pro-`p` group is prosolvable. -/
  theorem isProsolvableGroup (hG : IsProPGroup p G) : IsProsolvableGroup G := by
    letI : IsTopologicalGroup G := hG.isTopologicalGroup
    refine ⟨hG.isProfinite, ?_⟩
    intro U
    exact
      (FiniteGroupClass.pGroup_to_solvable (p := p)
        (hG.quotient_mem (FiniteGroupClass.pGroup_formation p) U)).2

end IsProPGroup

section

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

end

end ProCGroups.ProC
