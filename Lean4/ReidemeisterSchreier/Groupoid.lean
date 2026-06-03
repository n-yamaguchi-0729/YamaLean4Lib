import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Groupoid.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free groupoids and spanning tree bases

Groupoid-level free basis and spanning-tree constructions underlying the Nielsen-Schreier proof.
-/

open CategoryTheory CategoryTheory.SingleObj Quiver


/-- The complement of a chosen spanning tree in a free connected groupoid gives an explicit free
group basis of the root vertex group. This is the basis-level version of mathlib's
`SpanningTree.endIsFree`. -/
noncomputable def IsFreeGroupoid.SpanningTree.endBasis
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T] :
    FreeGroupBasis
      (((Quiver.wideSubquiverEquivSetTotal <| Quiver.wideSubquiverSymmetrify T)ᶜ : Set _))
      (End (show G from Quiver.root T)) := by
  classical
  refine FreeGroupBasis.ofUniqueLift
    (((Quiver.wideSubquiverEquivSetTotal <| Quiver.wideSubquiverSymmetrify T)ᶜ : Set _))
    (fun e => IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom))
    ?_
  intro X _ f
  let f' : Quiver.Labelling (IsFreeGroupoid.Generators G) X := fun a b e =>
    if h : e ∈ Quiver.wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
  refine ⟨F'.mapEnd _, ?_, ?_⟩
  · suffices
      ∀ {x y} (q : x ⟶ y),
        F'.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F'.map q : X) by
      rintro ⟨⟨a, b, e⟩, h⟩
      erw [Functor.mapEnd_apply]
      rw [this, hF']
      exact dif_neg h
    intro x y q
    suffices
      ∀ {a} (p : Quiver.Path (Quiver.root T) a),
        F'.map (IsFreeGroupoid.SpanningTree.homOfPath T p) = 1 by
      simp only [this, IsFreeGroupoid.SpanningTree.treeHom,
        CategoryTheory.SingleObj.comp_as_mul, inv_as_inv,
        IsFreeGroupoid.SpanningTree.loopOfHom, inv_one, mul_one, one_mul,
        Functor.map_inv, Functor.map_comp]
    intro a p
    induction p with
    | nil =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath, F'.map_id, id_as_one]
    | cons p e ih =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath, F'.map_comp,
          CategoryTheory.SingleObj.comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          have he : e ∈ Quiver.wideSubquiverSymmetrify T _ _ := by
            change T _ _ (Sum.inl e) ∨ T _ _ (Sum.inr e)
            exact Or.inl eT
          simp only [he, ↓reduceDIte, f']
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          have he : e ∈ Quiver.wideSubquiverSymmetrify T _ _ := by
            change T _ _ (Sum.inl e) ∨ T _ _ (Sum.inr e)
            exact Or.inr eT
          simp only [he, ↓reduceDIte, f']
  · intro E hE
    ext x
    change E x = F'.map x
    suffices
      (IsFreeGroupoid.SpanningTree.functorOfMonoidHom T E).map x = F'.map x by
      change E (IsFreeGroupoid.SpanningTree.loopOfHom T x) = F'.map x at this
      have hroot : IsFreeGroupoid.SpanningTree.treeHom T (Quiver.root T) = 𝟙 _ := by
        rw [IsFreeGroupoid.SpanningTree.treeHom_eq T Quiver.Path.nil]
        rfl
      have hx : E (IsFreeGroupoid.SpanningTree.loopOfHom T x) = E x := by
        have hloop :
            IsFreeGroupoid.SpanningTree.loopOfHom T x = x ≫ 𝟙 _ := by
          simp only [IsFreeGroupoid.SpanningTree.loopOfHom, hroot, IsIso.inv_id,
            Category.id_comp]
          rfl
        exact (congrArg E hloop).trans (congrArg E (Category.comp_id x))
      exact hx.symm.trans this
    congr
    apply uF'
    intro a b e
    change E (IsFreeGroupoid.SpanningTree.loopOfHom T _) = dite _ _ _
    split_ifs with h
    · rw [IsFreeGroupoid.SpanningTree.loopOfHom_eq_id T e h, ← End.one_def, E.map_one]
    · exact hE ⟨⟨a, b, e⟩, h⟩

lemma IsFreeGroupoid.SpanningTree.map_loopOfHom_eq_map
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {X : Type u} [Group X] (F : G ⥤ CategoryTheory.SingleObj X)
    (hTree : ∀ {a b : IsFreeGroupoid.Generators G} (e : a ⟶ b),
      e ∈ Quiver.wideSubquiverSymmetrify T a b → F.map (IsFreeGroupoid.of e) = 1) :
    ∀ {a b} (q : a ⟶ b), F.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F.map q : X) := by
  suffices
      ∀ {a} (p : Quiver.Path (Quiver.root T) a),
        F.map (IsFreeGroupoid.SpanningTree.homOfPath T p) = 1 by
    intro x y q
    simp only [this, IsFreeGroupoid.SpanningTree.treeHom,
      CategoryTheory.SingleObj.comp_as_mul, inv_as_inv,
      IsFreeGroupoid.SpanningTree.loopOfHom, inv_one, mul_one, one_mul,
      Functor.map_inv, Functor.map_comp]
  intro a p
  induction p with
  | nil =>
      rw [IsFreeGroupoid.SpanningTree.homOfPath, F.map_id, id_as_one]
  | cons p e ih =>
      rw [IsFreeGroupoid.SpanningTree.homOfPath, F.map_comp,
        CategoryTheory.SingleObj.comp_as_mul, ih, mul_one]
      rcases e with ⟨e | e, eT⟩
      · rw [hTree e (Or.inl eT)]
      · rw [F.map_inv, inv_as_inv, inv_eq_one, hTree e (Or.inr eT)]

@[simp] theorem FreeGroupBasis.ofUniqueLift_apply {X G : Type u} [Group G] (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a)
    (x : X) :
    FreeGroupBasis.ofUniqueLift X of h x = of x := by
  unfold FreeGroupBasis.ofUniqueLift
  change FreeGroup.lift of (FreeGroup.of x) = of x
  simp only [FreeGroup.lift_apply_of]

@[simp] lemma IsFreeGroupoid.SpanningTree.endBasis_apply
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    (e : (((Quiver.wideSubquiverEquivSetTotal <| Quiver.wideSubquiverSymmetrify T)ᶜ : Set _))) :
    IsFreeGroupoid.SpanningTree.endBasis T e =
      IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.1.hom) := by
  unfold IsFreeGroupoid.SpanningTree.endBasis FreeGroupBasis.ofUniqueLift
  change
    FreeGroup.lift (fun e =>
      IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.1.hom))
      (FreeGroup.of e) = IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.1.hom)
  simp only [Lean.Elab.WF.paramLet, FreeGroup.lift_apply_of]

