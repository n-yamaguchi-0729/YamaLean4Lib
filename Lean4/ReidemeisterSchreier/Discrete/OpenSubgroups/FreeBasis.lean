import ReidemeisterSchreier.Discrete.OpenSubgroups.PrefixTree
import ReidemeisterSchreier.Quiver
import ReidemeisterSchreier.Schreier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/OpenSubgroups/FreeBasis.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Schreier bases for open subgroups of free groups

Constructs Schreier bases from right Schreier transversals using prefix trees, complement edges,
and nontrivial Schreier pairs as the preferred basis index.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups


/-- The total generator arrows in the action groupoid attached to a chosen free basis are indexed
by a pair consisting of a vertex and a basis element. -/
noncomputable def FreeGroupBasis.actionGroupoidGeneratorTotalEquiv
    {ι G A : Type u} [Group G] [MulAction G A] (b : FreeGroupBasis ι G) :
    letI : IsFreeGroupoid (CategoryTheory.ActionCategory G A) :=
      FreeGroupBasis.actionGroupoidIsFree b
    Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory G A)) ≃ A × ι := by
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory G A) :=
    FreeGroupBasis.actionGroupoidIsFree b
  refine
    { toFun := fun e => (e.left.back, e.hom.1)
      invFun := fun ai =>
        { left := show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory G A) from
            ((ai.1 : A) : CategoryTheory.ActionCategory G A)
          right := show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory G A) from
            ((b ai.2 • ai.1 : A) : CategoryTheory.ActionCategory G A)
          hom := ⟨ai.2, rfl⟩ }
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    cases e with
    | mk left right hom =>
        cases left with
        | mk _ a =>
            cases right with
            | mk _ a' =>
                cases hom with
                | mk i hi =>
                    dsimp
                    cases hi
                    rfl
  · intro ai
    rfl

/-- Complement edges of the symmetrized Schreier prefix tree.  These are the canonical indexing
objects for the Schreier free basis. -/
noncomputable abbrev schreierComplementEdges
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) : Type u := by
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  exact
    ↥(((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ :
        Set (Quiver.Total
          (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)))))

/-- The Schreier basis indexed by complement edges of the prefix tree. -/
noncomputable def schreierComplementEdgesBasis
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroupBasis (schreierComplementEdges (X := X) hT) L := by
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  exact
    (IsFreeGroupoid.SpanningTree.endBasis (schreierPrefixTree (X := X) hT)).map
      (schreierRootEndMulEquiv (X := X) hT)

/-- Auxiliary bridge from nontrivial Schreier pairs to the classical Schreier generator value set. -/
private noncomputable def nontrivialSchreierPairsEquivSchreierGeneratorSet
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    NontrivialSchreierPair (X := X) hT ≃ ↥(schreierGeneratorSet (X := X) hT) := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let C :
      Set (Quiver.Total
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    ((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ : Set _)
  let toSch : ↑C → ↥(schreierGeneratorSet (X := X) hT) := fun i =>
    ⟨schreierGenerator (X := X) hT (((i.1.left.back : T) : FreeGroup X)) i.1.hom.1,
      by
        refine ⟨
          ((i.1.left.back : T) : FreeGroup X), (i.1.left.back : T).property,
          i.1.hom.1, rfl, ?_⟩
        intro hgen
        exact i.2 (show i.1 ∈ Quiver.wideSubquiverEquivSetTotal
            (Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)) from
          schreierGenerator_eq_one_implies_mem_prefixTree (X := X) hT i.1.hom hgen)⟩
  let b : FreeGroupBasis ↑C L :=
    (IsFreeGroupoid.SpanningTree.endBasis (schreierPrefixTree (X := X) hT)).map
      (schreierRootEndMulEquiv (X := X) hT)
  have hval : ∀ i : ↑C, (b i : L) = (((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) := by
    intro i
    rw [FreeGroupBasis.map_apply, IsFreeGroupoid.SpanningTree.endBasis_apply]
    have htree : ∀ {a b : IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)}
        (e : a ⟶ b),
        e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b →
          (schreierLabelFunctor (X := X) hT).map (IsFreeGroupoid.of e) = (1 : L) := by
      intro a b e he
      exact schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e he
    have hloop := IsFreeGroupoid.SpanningTree.map_loopOfHom_eq_map
      (T := schreierPrefixTree (X := X) hT)
      (F := schreierLabelFunctor (X := X) hT)
      (hTree := by
        intro a b e he
        exact htree e he)
      (q := IsFreeGroupoid.of i.1.hom)
    let loop := IsFreeGroupoid.SpanningTree.loopOfHom (schreierPrefixTree (X := X) hT)
      (IsFreeGroupoid.of i.1.hom)
    have hrootEq : (schreierRootEndMulEquiv (X := X) hT loop : L) =
        (schreierLabelFunctor (X := X) hT).map loop := by
      apply Subtype.ext
      change loop.1 = (1 : FreeGroup X) * loop.1 * (1 : FreeGroup X)⁻¹
      simp only [CategoryTheory.actionAsFunctor_obj, CategoryTheory.actionAsFunctor_map, one_mul, inv_one, mul_one]
    exact hrootEq.trans <| hloop.trans <| schreierLabelFunctor_map_of (X := X) hT i.1.hom
  have hto_inj : Function.Injective toSch := by
    intro i j hij
    apply b.injective
    have hz : ((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L) =
        ((toSch j : ↥(schreierGeneratorSet (X := X) hT)) : L) := congrArg Subtype.val hij
    have hz_inv : (((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) =
        (((toSch j : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) := congrArg Inv.inv hz
    exact (hval i).trans (hz_inv.trans (hval j).symm)
  have hto_surj : Function.Surjective toSch := by
    intro z
    rcases z.2 with ⟨t, ht, x, hz, hne⟩
    let a : CategoryTheory.ActionCategory (FreeGroup X) T :=
      ((⟨t, ht⟩ : T) : CategoryTheory.ActionCategory (FreeGroup X) T)
    let b0 : CategoryTheory.ActionCategory (FreeGroup X) T :=
      (schreierRepresentative (X := X) hT (t * FreeGroup.of x) : T)
    let e :
        ((show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T) from a) ⟶
          b0) :=
      ⟨x, by
        rw [FreeGroup.inverseBasis_apply]
        change (FreeGroup.of x)⁻¹ • (show T from CategoryTheory.ActionCategory.back a) =
          (show T from CategoryTheory.ActionCategory.back b0)
        simpa [a, b0] using
          (schreierTransversalRightCosetAction_smul (X := X) hT (FreeGroup.of x)⁻¹ (⟨t, ht⟩ : T))⟩
    have he_not : ⟨a, b0, e⟩ ∈ C := by
      change ¬ e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b0
      intro he
      have hgen1_inv :
          (schreierGenerator (X := X) hT
            ((show T from CategoryTheory.ActionCategory.back a) : FreeGroup X) e.1)⁻¹ = 1 := by
        have htreeLabel :=
          schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e he
        rw [schreierLabelFunctor_map_of (X := X) hT e] at htreeLabel
        exact htreeLabel
      have hgen1 :
          schreierGenerator (X := X) hT
            ((show T from CategoryTheory.ActionCategory.back a) : FreeGroup X) e.1 = 1 :=
        inv_eq_one.mp hgen1_inv
      exact hne (by simpa [a, e, hz] using hgen1)
    refine ⟨⟨⟨a, b0, e⟩, he_not⟩, ?_⟩
    apply Subtype.ext
    simpa [toSch, a, e] using hz.symm
  let eC : ↑C ≃ ↥(schreierGeneratorSet (X := X) hT) := Equiv.ofBijective toSch ⟨hto_inj, hto_surj⟩
  let ePair :
      ↑C ≃ NontrivialSchreierPair (X := X) hT := by
    let eTotal :
        Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)) ≃
          T × X :=
      FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)
    refine
      { toFun := fun i =>
          ⟨eTotal i.1, by
            intro hgen
            have hgen' :
                schreierGenerator (X := X) hT
                  (((show T from CategoryTheory.ActionCategory.back i.1.left) : T) : FreeGroup X)
                  i.1.hom.1 = 1 := by
              simpa [eTotal] using hgen
            exact i.2 (show i.1 ∈ Quiver.wideSubquiverEquivSetTotal
                (Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)) from
              schreierGenerator_eq_one_implies_mem_prefixTree (X := X) hT i.1.hom hgen')⟩
        invFun := fun p =>
          let e := eTotal.symm p.1
          ⟨e, by
            intro he
            have htreeLabel :=
              schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e.hom
                (show e.hom ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)
                    e.left e.right from he)
            rw [schreierLabelFunctor_map_of (X := X) hT e.hom] at htreeLabel
            have hgen' :
                schreierGenerator (X := X) hT
                  (((show T from CategoryTheory.ActionCategory.back e.left) : T) : FreeGroup X)
                  e.hom.1 = 1 := inv_eq_one.mp htreeLabel
            exact p.2 (by simpa [eTotal] using hgen')⟩
        left_inv := by
          intro i
          apply Subtype.ext
          simp only [Equiv.symm_apply_apply, eTotal]
        right_inv := by
          intro p
          apply Subtype.ext
          simp only [ne_eq, Equiv.apply_symm_apply, eTotal]}
  exact ePair.symm.trans eC

/-- Complement edges are equivalent to nontrivial Schreier pairs. -/
noncomputable def schreierComplementEdgesEquivNontrivialPairs
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    schreierComplementEdges (X := X) hT ≃ NontrivialSchreierPair (X := X) hT := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let C :
      Set (Quiver.Total
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    ((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ : Set _)
  change ↑C ≃ NontrivialSchreierPair (X := X) hT
  let eTotal :
      Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)) ≃
        T × X :=
    FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)
  refine
    { toFun := fun i =>
        ⟨eTotal i.1, by
          intro hgen
          have hgen' :
              schreierGenerator (X := X) hT
                (((show T from CategoryTheory.ActionCategory.back i.1.left) : T) : FreeGroup X)
                i.1.hom.1 = 1 := by
            simpa [eTotal] using hgen
          exact i.2 (show i.1 ∈ Quiver.wideSubquiverEquivSetTotal
              (Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)) from
            (schreierGenerator_eq_one_iff_mem_prefixTree (X := X) hT i.1.hom).1 hgen')⟩
      invFun := fun p =>
        let e := eTotal.symm p.1
        ⟨e, by
          intro he
          have hgen' :
              schreierGenerator (X := X) hT
                (((show T from CategoryTheory.ActionCategory.back e.left) : T) : FreeGroup X)
                e.hom.1 = 1 :=
            (schreierGenerator_eq_one_iff_mem_prefixTree (X := X) hT e.hom).2
              (show e.hom ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)
                  e.left e.right from he)
          exact p.2 (by simpa [eTotal] using hgen')⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simp only [Equiv.symm_apply_apply, eTotal]
      right_inv := by
        intro p
        apply Subtype.ext
        simp only [ne_eq, Equiv.apply_symm_apply, eTotal]}

/-- The Schreier free basis indexed by nontrivial Schreier pairs.  This is the preferred
Schreier-basis API; the classical value-set basis is a reindexing of this one. -/
noncomputable def nontrivialSchreierPairBasis
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroupBasis (NontrivialSchreierPair (X := X) hT) L :=
  (schreierComplementEdgesBasis (X := X) hT).reindex
    (schreierComplementEdgesEquivNontrivialPairs (X := X) hT)

/-- The free group equivalence obtained directly from the preferred pair-indexed Schreier basis. -/
noncomputable def nontrivialSchreierPairBasisEquiv
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroup (NontrivialSchreierPair (X := X) hT) ≃* L :=
  (nontrivialSchreierPairBasis (X := X) hT).repr.symm

/-- The preferred pair-indexed basis equivalence sends each free generator to its Schreier
basis element. -/
@[simp] theorem nontrivialSchreierPairBasisEquiv_of
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (p : NontrivialSchreierPair (X := X) hT) :
    nontrivialSchreierPairBasisEquiv (X := X) hT (FreeGroup.of p) =
      nontrivialSchreierPairBasis (X := X) hT p := by
  apply (nontrivialSchreierPairBasis (X := X) hT).repr.injective
  calc
    (nontrivialSchreierPairBasis (X := X) hT).repr
        (nontrivialSchreierPairBasisEquiv (X := X) hT (FreeGroup.of p))
        = FreeGroup.of p := by simp only [nontrivialSchreierPairBasisEquiv, MulEquiv.apply_symm_apply]
    _ = (nontrivialSchreierPairBasis (X := X) hT).repr
        (nontrivialSchreierPairBasis (X := X) hT p) :=
      (FreeGroupBasis.repr_apply_coe (nontrivialSchreierPairBasis (X := X) hT) p).symm

private theorem nontrivialSchreierPairsEquivSchreierGeneratorSet_apply
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (p : NontrivialSchreierPair (X := X) hT) :
    ((nontrivialSchreierPairsEquivSchreierGeneratorSet (X := X) hT p :
        ↥(schreierGeneratorSet (X := X) hT)) : L) =
      schreierGenerator (X := X) hT ((p.1.1 : T) : FreeGroup X) p.1.2 := by
  rfl

/-- The Schreier-generator map is injective on nontrivial Schreier pairs. -/
theorem schreierGenerator_injective_of_nontrivial
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Function.Injective
      (nontrivialSchreierPairGenerator (X := X) hT) := by
  intro p q hpq
  apply (nontrivialSchreierPairsEquivSchreierGeneratorSet (X := X) hT).injective
  apply Subtype.ext
  simpa [nontrivialSchreierPairsEquivSchreierGeneratorSet_apply,
    nontrivialSchreierPairGenerator] using hpq

/-- A right Schreier transversal has cardinality equal to the corresponding right-coset index. -/
theorem natCard_schreierTransversal_eq_index
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite (Quotient (QuotientGroup.rightRel L))]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card T = Nat.card (Quotient (QuotientGroup.rightRel L)) := by
  exact Nat.card_congr hT.1.rightQuotientEquiv.symm

/-- Direct combinatorial count of complement edges in the Schreier prefix tree:
all labelled edges minus tree edges. -/
theorem natCard_schreierComplementEdges_eq_rankTransform_direct
    {X : Type u} [DecidableEq X] [Finite X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite T]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card (schreierComplementEdges (X := X) hT) =
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let Ttree :
      WideSubquiver
        (Quiver.Symmetrify
          (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    schreierPrefixTree (X := X) hT
  letI : Quiver.Arborescence Ttree := by
    dsimp [Ttree]
    infer_instance
  let totalGen :=
    Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))
  let covered : Set totalGen :=
    Quiver.wideSubquiverEquivSetTotal (Quiver.wideSubquiverSymmetrify Ttree)
  let rootT : T := ⟨(1 : FreeGroup X), hT.2.1⟩
  let root : CategoryTheory.ActionCategory (FreeGroup X) T :=
    CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T rootT
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype T := Fintype.ofFinite T
  haveI : Finite (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    Finite.of_equiv T (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T)
  haveI : Finite Ttree :=
    Finite.of_equiv (CategoryTheory.ActionCategory (FreeGroup X) T)
      (show _ ≃ Ttree from Equiv.refl _)
  haveI : Finite totalGen :=
    Finite.of_equiv (T × X)
      (FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)).symm
  letI : Fintype totalGen := Fintype.ofFinite totalGen
  letI : Fintype (schreierComplementEdges (X := X) hT) :=
    Fintype.ofFinite (schreierComplementEdges (X := X) hT)
  letI : Fintype {e : totalGen // e ∈ covered} :=
    Fintype.ofFinite {e : totalGen // e ∈ covered}
  letI : Fintype {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root} :=
    Fintype.ofFinite {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root}
  letI : Fintype {v : Ttree // v ≠ Quiver.root Ttree} :=
    Fintype.ofFinite {v : Ttree // v ≠ Quiver.root Ttree}
  haveI : Finite (Quiver.Total Ttree) :=
    Finite.of_equiv {v : Ttree // v ≠ Quiver.root Ttree}
      (Quiver.Arborescence.totalEquivNonRoot Ttree).symm
  letI : Fintype (Quiver.Total Ttree) := Fintype.ofFinite (Quiver.Total Ttree)
  have hYcard :
      Fintype.card (schreierComplementEdges (X := X) hT) =
        Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered} := by
    change
      Fintype.card {e : totalGen // e ∈ ((covered : Set totalGen)ᶜ)} =
        Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered}
    simpa only [Set.mem_compl_iff] using
      (Fintype.card_subtype_compl (fun e : totalGen => e ∈ covered) :
        Fintype.card {e : totalGen // ¬ e ∈ covered} =
          Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered})
  have hTotal :
      Fintype.card totalGen = Fintype.card T * Fintype.card X := by
    simpa [totalGen, Fintype.card_prod] using
      Fintype.card_congr
        (FreeGroupBasis.actionGroupoidGeneratorTotalEquiv
          (ι := X) (G := FreeGroup X) (A := T) (FreeGroup.inverseBasis X))
  let eObjNonRoot :
      {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root} ≃
        {t : T // t ≠ rootT} := {
    toFun := fun a => ⟨(CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T).symm a.1, by
      intro h
      apply a.2
      simpa [root] using congrArg (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T) h⟩
    invFun := fun t => ⟨CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T t.1, by
      intro h
      apply t.2
      simpa [root] using
        congrArg (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T).symm h⟩
    left_inv := by
      intro a
      apply Subtype.ext
      simp only [ne_eq, Equiv.apply_symm_apply]
    right_inv := by
      intro t
      apply Subtype.ext
      simp only [ne_eq, Equiv.symm_apply_apply]}
  haveI : Subsingleton {t : T // t = rootT} :=
    ⟨fun t t' => Subtype.ext (by simp only [t.property, t'.property])⟩
  have hOne :
      Fintype.card {t : T // t = rootT} = 1 := by
    exact Fintype.card_ofSubsingleton (⟨rootT, rfl⟩ : {t : T // t = rootT})
  have hTcompl :
      Fintype.card {t : T // t ≠ rootT} = Fintype.card T - 1 := by
    calc
      Fintype.card {t : T // t ≠ rootT}
          = Fintype.card T - Fintype.card {t : T // t = rootT} := by
              exact Fintype.card_subtype_compl (fun t : T => t = rootT)
      _ = Fintype.card T - 1 := by rw [hOne]
  have hNonRoot :
      Fintype.card {v : Ttree // v ≠ Quiver.root Ttree} = Fintype.card T - 1 := by
    simpa [Ttree, root, rootT] using (Fintype.card_congr eObjNonRoot).trans hTcompl
  have hCovered :
      Fintype.card {e : totalGen // e ∈ covered} = Fintype.card T - 1 := by
    calc
      Fintype.card {e : totalGen // e ∈ covered}
          = Fintype.card (Quiver.Total Ttree) := by
              simpa [totalGen, covered] using
                Fintype.card_congr (Quiver.coveredArrowEquivTotal Ttree)
      _ = Fintype.card {v : Ttree // v ≠ Quiver.root Ttree} := by
            simpa using Fintype.card_congr (Quiver.Arborescence.totalEquivNonRoot Ttree)
      _ = Fintype.card T - 1 := hNonRoot
  have hYcalcF :
      Fintype.card (schreierComplementEdges (X := X) hT) =
        Fintype.card T * Fintype.card X - (Fintype.card T - 1) := by
    rw [hYcard, hTotal, hCovered]
  have hYcalc :
      Nat.card (schreierComplementEdges (X := X) hT) =
        Nat.card T * Nat.card X - (Nat.card T - 1) := by
    simpa [Nat.card_eq_fintype_card] using hYcalcF
  by_cases hX0 : Nat.card X = 0
  · have hX0F : Fintype.card X = 0 := by
      simpa [Nat.card_eq_fintype_card] using hX0
    calc
      Nat.card (schreierComplementEdges (X := X) hT)
          = Nat.card T * Nat.card X - (Nat.card T - 1) := hYcalc
      _ = 0 := by simp only [Nat.card_eq_fintype_card, hX0F, mul_zero, zero_tsub]
      _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) := by
            simp only [Schreier.rankTransform, Nat.card_eq_fintype_card, hX0F, ↓reduceIte]
  · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hX0
    rw [hr] at hYcalc ⊢
    calc
      Nat.card (schreierComplementEdges (X := X) hT)
          = Nat.card T * (r + 1) - (Nat.card T - 1) := hYcalc
      _ = Nat.card T * r + Nat.card T - (Nat.card T - 1) := by
            rw [Nat.mul_succ]
      _ = Nat.card T * r + (Nat.card T - (Nat.card T - 1)) := by
            rw [Nat.add_sub_assoc (Nat.sub_le _ _)]
      _ = Nat.card T * r + 1 := by
            have hTpos : 0 < Nat.card T := by
              simpa [Nat.card_eq_fintype_card] using
                (Fintype.card_pos_iff.mpr ⟨rootT⟩)
            obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hTpos)
            rw [hn]
            simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, add_tsub_cancel_left]
      _ = 1 + Nat.card T * r := by
            rw [Nat.add_comm]
      _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (r + 1) (Nat.card T) := by
            rw [_root_.ReidemeisterSchreier.Schreier.rankTransform_succ]

/-- Direct Schreier-rank count for the preferred pair-indexed generator type. -/
theorem natCard_nontrivialSchreierPairs_eq_rankTransform_direct
    {X : Type u} [DecidableEq X] [Finite X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite T]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card (NontrivialSchreierPair (X := X) hT) =
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) := by
  calc
    Nat.card (NontrivialSchreierPair (X := X) hT)
        = Nat.card (schreierComplementEdges (X := X) hT) := by
            exact Nat.card_congr
              (schreierComplementEdgesEquivNontrivialPairs (X := X) hT).symm
    _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) :=
        natCard_schreierComplementEdges_eq_rankTransform_direct (X := X) (L := L) hT

/-- Direct Schreier-rank count with the index expressed as the usual left-coset quotient. -/
theorem natCard_nontrivialSchreierPairs_eq_rankTransform
    {X : Type u} [DecidableEq X] [Finite X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite (FreeGroup X ⧸ L)]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card (NontrivialSchreierPair (X := X) hT) =
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (FreeGroup X ⧸ L)) := by
  classical
  haveI : Finite (Quotient (QuotientGroup.rightRel L)) :=
    Finite.of_equiv (FreeGroup X ⧸ L)
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel L).symm
  haveI : Finite T :=
    Finite.of_equiv (Quotient (QuotientGroup.rightRel L)) hT.1.rightQuotientEquiv
  have hTcard :
      Nat.card T = Nat.card (FreeGroup X ⧸ L) := by
    calc
      Nat.card T = Nat.card (Quotient (QuotientGroup.rightRel L)) := by
        exact (Nat.card_congr hT.1.rightQuotientEquiv).symm
      _ = Nat.card (FreeGroup X ⧸ L) := by
        exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel L)
  calc
    Nat.card (NontrivialSchreierPair (X := X) hT)
        = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) :=
            natCard_nontrivialSchreierPairs_eq_rankTransform_direct (X := X) (L := L) hT
    _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (FreeGroup X ⧸ L)) := by
          rw [hTcard]

/-- A finite-index subgroup of a free group admits a free basis of Schreier-transformed
cardinality. -/
theorem exists_freeBasis_subgroupOfFreeGroup_of_rankTransform
    {X : Type u} {L : Subgroup (FreeGroup X)} [Finite X] [Finite (FreeGroup X ⧸ L)] :
    ∃ Y : Type u, Nonempty (FreeGroupBasis Y L) ∧
      Nat.card Y = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (FreeGroup X ⧸ L)) := by
  classical
  let A : Type u := FreeGroup X ⧸ L
  letI : MulAction (FreeGroup X) A :=
    inferInstanceAs (MulAction (FreeGroup X) (FreeGroup X ⧸ L))
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) A) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let root : CategoryTheory.ActionCategory (FreeGroup X) A :=
    CategoryTheory.ActionCategory.objEquiv (FreeGroup X) A (((1 : FreeGroup X) : A))
  let rootGen :
      Quiver.Symmetrify
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) A)) :=
    show Quiver.Symmetrify
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) A)) from
      (show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) A) from root)
  letI : Quiver.RootedConnected rootGen := by
    simpa [rootGen] using
      (IsFreeGroupoid.generators_connected
        (CategoryTheory.ActionCategory (FreeGroup X) A) root)
  let Ttree :
      WideSubquiver
        (Quiver.Symmetrify
          (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) A))) :=
    Quiver.geodesicSubtree rootGen
  letI : Quiver.Arborescence Ttree := Quiver.geodesicArborescence rootGen
  let Y :=
    (((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify Ttree)ᶜ : Set _))
  let b : FreeGroupBasis ↑Y L :=
    (IsFreeGroupoid.SpanningTree.endBasis Ttree).map <|
      by
        simpa [A, root, rootGen, Ttree] using
          (CategoryTheory.ActionCategory.endMulEquivSubgroup L)
  refine ⟨↑Y, ⟨b⟩, ?_⟩
  let totalGen :=
    Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) A))
  let covered : Set totalGen :=
    Quiver.wideSubquiverEquivSetTotal (Quiver.wideSubquiverSymmetrify Ttree)
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype A := Fintype.ofFinite A
  haveI : Finite (CategoryTheory.ActionCategory (FreeGroup X) A) :=
    Finite.of_equiv A (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) A)
  haveI : Finite Ttree :=
    Finite.of_equiv (CategoryTheory.ActionCategory (FreeGroup X) A)
      (show _ ≃ Ttree from Equiv.refl _)
  haveI : Finite totalGen :=
    Finite.of_equiv (A × X)
      (FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)).symm
  letI : Fintype totalGen := Fintype.ofFinite totalGen
  letI : Fintype ↑Y := Fintype.ofFinite ↑Y
  letI : Fintype {e : totalGen // e ∈ covered} := Fintype.ofFinite {e : totalGen // e ∈ covered}
  letI : Fintype {a : CategoryTheory.ActionCategory (FreeGroup X) A // a ≠ root} :=
    Fintype.ofFinite {a : CategoryTheory.ActionCategory (FreeGroup X) A // a ≠ root}
  letI : Fintype {v : Ttree // v ≠ Quiver.root Ttree} :=
    Fintype.ofFinite {v : Ttree // v ≠ Quiver.root Ttree}
  haveI : Finite (Quiver.Total Ttree) :=
    Finite.of_equiv {v : Ttree // v ≠ Quiver.root Ttree}
      (Quiver.Arborescence.totalEquivNonRoot Ttree).symm
  letI : Fintype (Quiver.Total Ttree) := Fintype.ofFinite (Quiver.Total Ttree)
  have hYcard :
      Fintype.card ↑Y = Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered} := by
    change
      Fintype.card {e : totalGen // e ∈ ((covered : Set totalGen)ᶜ)} =
        Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered}
    simpa only [Set.mem_compl_iff] using
      (Fintype.card_subtype_compl (fun e : totalGen => e ∈ covered) :
        Fintype.card {e : totalGen // ¬ e ∈ covered} =
          Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered})
  have hTotal :
      Fintype.card totalGen = Fintype.card A * Fintype.card X := by
    simpa [totalGen, Fintype.card_prod] using
      Fintype.card_congr
        (FreeGroupBasis.actionGroupoidGeneratorTotalEquiv
          (ι := X) (G := FreeGroup X) (A := A) (FreeGroup.inverseBasis X))
  let eObjNonRoot :
      {a : CategoryTheory.ActionCategory (FreeGroup X) A // a ≠ root} ≃
        {q : A // q ≠ (((1 : FreeGroup X) : A))} := {
    toFun := fun a => ⟨(CategoryTheory.ActionCategory.objEquiv (FreeGroup X) A).symm a.1, by
      intro h
      apply a.2
      simpa [root] using congrArg (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) A) h⟩
    invFun := fun q => ⟨CategoryTheory.ActionCategory.objEquiv (FreeGroup X) A q.1, by
      intro h
      apply q.2
      simpa [root] using
        congrArg (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) A).symm h⟩
    left_inv := by
      intro a
      apply Subtype.ext
      simp only [ne_eq, Equiv.apply_symm_apply]
    right_inv := by
      intro q
      apply Subtype.ext
      simp only [ne_eq, Equiv.symm_apply_apply]}
  haveI : Subsingleton {q : A // q = (((1 : FreeGroup X) : A))} :=
    ⟨fun q q' => Subtype.ext (by simp only [q.property, q'.property])⟩
  have hOne :
      Fintype.card {q : A // q = (((1 : FreeGroup X) : A))} = 1 := by
    exact
      Fintype.card_ofSubsingleton
        (⟨((1 : FreeGroup X) : A), rfl⟩ : {q : A // q = (((1 : FreeGroup X) : A))})
  have hAcompl :
      Fintype.card {q : A // q ≠ (((1 : FreeGroup X) : A))} = Fintype.card A - 1 := by
    calc
      Fintype.card {q : A // q ≠ (((1 : FreeGroup X) : A))}
          = Fintype.card A - Fintype.card {q : A // q = (((1 : FreeGroup X) : A))} := by
              exact Fintype.card_subtype_compl (fun q : A => q = (((1 : FreeGroup X) : A)))
      _ = Fintype.card A - 1 := by rw [hOne]
  have hNonRoot :
      Fintype.card {v : Ttree // v ≠ Quiver.root Ttree} = Fintype.card A - 1 := by
    simpa [Ttree, root, rootGen] using (Fintype.card_congr eObjNonRoot).trans hAcompl
  have hCovered :
      Fintype.card {e : totalGen // e ∈ covered} = Fintype.card A - 1 := by
    calc
      Fintype.card {e : totalGen // e ∈ covered}
          = Fintype.card (Quiver.Total Ttree) := by
              simpa [totalGen, covered] using
                Fintype.card_congr (Quiver.coveredArrowEquivTotal Ttree)
      _ = Fintype.card {v : Ttree // v ≠ Quiver.root Ttree} := by
            simpa using Fintype.card_congr (Quiver.Arborescence.totalEquivNonRoot Ttree)
      _ = Fintype.card A - 1 := hNonRoot
  have hYcalcF :
      Fintype.card ↑Y = Fintype.card A * Fintype.card X - (Fintype.card A - 1) := by
    rw [hYcard, hTotal, hCovered]
  have hYcalc :
      Nat.card ↑Y = Nat.card A * Nat.card X - (Nat.card A - 1) := by
    simpa [Nat.card_eq_fintype_card] using hYcalcF
  by_cases hX0 : Nat.card X = 0
  · haveI : IsEmpty X := Finite.card_eq_zero_iff.mp hX0
    have hId :
        (MonoidHom.id (FreeGroup X)) = (1 : FreeGroup X →* FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      exact isEmptyElim x
    have htriv : ∀ g : FreeGroup X, g = 1 := by
      intro g
      exact congrArg (fun f : FreeGroup X →* FreeGroup X => f g) hId
    haveI : Subsingleton (FreeGroup X) :=
      ⟨fun g h => by rw [htriv g, htriv h]⟩
    have hLtop : L = ⊤ := by
      ext g
      constructor
      · intro _
        trivial
      · intro _
        rw [htriv g]
        exact L.one_mem
    have hA1 : Nat.card A = 1 := by
      have hA1' : Nat.card (FreeGroup X ⧸ L) = 1 := by
        rw [hLtop]
        exact Nat.card_eq_one_iff_unique.mpr
          ⟨QuotientGroup.subsingleton_quotient_top, ⟨((1 : FreeGroup X) :
            FreeGroup X ⧸ (⊤ : Subgroup (FreeGroup X)))⟩⟩
      simpa [A] using hA1'
    rw [hX0, hA1] at hYcalc
    simpa [_root_.ReidemeisterSchreier.Schreier.rankTransform, hX0] using hYcalc
  · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hX0
    rw [hr] at hYcalc ⊢
    calc
      Nat.card ↑Y = Nat.card A * (r + 1) - (Nat.card A - 1) := hYcalc
      _ = Nat.card A * r + Nat.card A - (Nat.card A - 1) := by
            rw [Nat.mul_succ]
      _ = Nat.card A * r + (Nat.card A - (Nat.card A - 1)) := by
            rw [Nat.add_sub_assoc (Nat.sub_le _ _)]
      _ = Nat.card A * r + 1 := by
            have hApos : 0 < Nat.card A := by
              simpa [Nat.card_eq_fintype_card] using
                (Fintype.card_pos_iff.mpr ⟨((1 : FreeGroup X) : A)⟩)
            obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hApos)
            rw [hn]
            simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, add_tsub_cancel_left]
      _ = 1 + Nat.card A * r := by
            rw [Nat.add_comm]
      _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (r + 1) (Nat.card A) := by
            rw [_root_.ReidemeisterSchreier.Schreier.rankTransform_succ]


end ReidemeisterSchreier.Discrete.OpenSubgroups
