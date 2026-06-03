import ReidemeisterSchreier.Discrete.OpenSubgroups.FreeBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/OpenSubgroups/ClassicalGeneratorBasis.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Classical Schreier generator-set basis compatibility

This focused module keeps the classical value-set Schreier generator basis out of the public root.
The preferred public basis remains `nontrivialSchreierPairBasis`.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups

section ClassicalGeneratorBasis

namespace Internal

/-- A strengthened Schreier-basis existence statement exposing the value of the chosen basis map
on free generators. This inverse-valued statement records the internal basis orientation used by
the proof: the standard free generator corresponding to a Schreier generator `z` is sent to `z⁻¹`
in the subgroup. Use `exists_schreierBasisEquiv` for the positive-valued compatibility theorem. -/
private theorem IsRightSchreierTransversal.exists_inverseSchreierBasisEquiv
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    ∃ e : FreeGroup ↥(schreierGeneratorSet (X := X) hT) ≃* L,
      ∀ z : ↥(schreierGeneratorSet (X := X) hT),
        e (FreeGroup.of z) = (z : L)⁻¹ := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let C :
      Set (Quiver.Total
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    ((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ : Set _)
  let b : FreeGroupBasis ↑C L :=
    (IsFreeGroupoid.SpanningTree.endBasis (schreierPrefixTree (X := X) hT)).map
      (schreierRootEndMulEquiv (X := X) hT)
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
  have hval : ∀ i : ↑C, (b i : L) =
      (((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) := by
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
        (show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T) from
          a) ⟶ b0 :=
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
  refine ⟨(b.reindex eC).repr.symm, ?_⟩
  intro z
  have hbasis :
      (b.reindex eC).repr.symm (FreeGroup.of z) = (b.reindex eC) z := by
    apply (b.reindex eC).repr.injective
    calc
      (b.reindex eC).repr ((b.reindex eC).repr.symm (FreeGroup.of z))
          = FreeGroup.of z := by simp only [MulEquiv.apply_symm_apply]
      _ = (b.reindex eC).repr ((b.reindex eC) z) :=
        (FreeGroupBasis.repr_apply_coe (b.reindex eC) z).symm
  calc
    (b.reindex eC).repr.symm (FreeGroup.of z)
        = (b.reindex eC) z := hbasis
    _ = b (eC.symm z) := by
      rw [FreeGroupBasis.reindex_apply]
    _ = (((toSch (eC.symm z) : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) :=
      hval (eC.symm z)
    _ = (z : L)⁻¹ := by
      exact congrArg (fun w : ↥(schreierGeneratorSet (X := X) hT) => ((w : L)⁻¹))
        (eC.apply_symm_apply z)

end Internal

/-- Positive-valued Schreier-basis existence statement on the classical Schreier generator set.
Prefer `nontrivialSchreierPairBasisEquiv` in new public code. -/
theorem IsRightSchreierTransversal.exists_schreierBasisEquiv
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    ∃ e : FreeGroup ↥(schreierGeneratorSet (X := X) hT) ≃* L,
      ∀ z : ↥(schreierGeneratorSet (X := X) hT),
        e (FreeGroup.of z) = (z : L) := by
  classical
  rcases Internal.IsRightSchreierTransversal.exists_inverseSchreierBasisEquiv hT with
    ⟨eInverse, hInverse⟩
  let e : FreeGroup ↥(schreierGeneratorSet (X := X) hT) ≃* L :=
    (FreeGroup.generatorInversionEquiv ↥(schreierGeneratorSet (X := X) hT)).trans eInverse
  refine ⟨e, ?_⟩
  intro z
  dsimp [e]
  calc
    eInverse ((FreeGroup.of z)⁻¹) = (eInverse (FreeGroup.of z))⁻¹ := by simp only [map_inv]
    _ = ((z : L)⁻¹)⁻¹ := by rw [hInverse z]
    _ = (z : L) := inv_inv _

/-- Auxiliary inverse-valued free group equivalence on the classical Schreier generator value set.
This compatibility route is kept outside the public root; new code should use
`nontrivialSchreierPairBasisEquiv`. -/
noncomputable def schreierGeneratorInverseBasisEquiv
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroup ↥(schreierGeneratorSet (X := X) hT) ≃* L :=
  Classical.choose (Internal.IsRightSchreierTransversal.exists_inverseSchreierBasisEquiv hT)

/-- The inverse-valued classical generator-set equivalence sends a free generator to the inverse
of the represented Schreier generator. -/
theorem schreierGeneratorInverseBasisEquiv_of
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (z : ↥(schreierGeneratorSet (X := X) hT)) :
    schreierGeneratorInverseBasisEquiv (X := X) hT (FreeGroup.of z) = (z : L)⁻¹ :=
  Classical.choose_spec (Internal.IsRightSchreierTransversal.exists_inverseSchreierBasisEquiv hT) z

end ClassicalGeneratorBasis

end ReidemeisterSchreier.Discrete.OpenSubgroups
