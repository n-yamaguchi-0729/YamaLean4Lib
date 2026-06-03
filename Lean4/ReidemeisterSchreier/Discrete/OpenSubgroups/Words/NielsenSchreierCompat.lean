import ReidemeisterSchreier.Groupoid

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/OpenSubgroups/Words/NielsenSchreierCompat.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free-word compatibility for Schreier theory

Free-group word lemmas, prefix-parent compatibility, Nielsen-Schreier calculations, and cancellation rules for Schreier generators.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups

section NielsenSchreierCompat

open scoped Pointwise
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

/-- A basis-level version of `IsFreeGroupoid.actionGroupoidIsFree`. Using an explicit
`FreeGroupBasis` keeps the generator labels under our control instead of passing through
`IsFreeGroup.Generators`. -/
noncomputable def FreeGroupBasis.actionGroupoidIsFree
    {ι G A : Type u} [Group G] [MulAction G A] (b : FreeGroupBasis ι G) :
    IsFreeGroupoid (ActionCategory G A) where
  quiverGenerators :=
    ⟨fun a b' => { i : ι // b i • a.back = b'.back }⟩
  of := fun (e : Subtype _) => ⟨b e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : ι → (A → X) ⋊[mulAutArrow] G := fun i =>
      ⟨fun a =>
          @f ⟨(), (b i)⁻¹ • a⟩ ⟨(), a⟩
            ⟨i, smul_inv_smul (b i) a⟩,
        b i⟩
    let F' : G →* (A → X) ⋊[mulAutArrow] G := b.lift f'
    have hF' : ∀ i, F' (b i) = f' i := congrFun (b.lift.left_inv f')
    refine ⟨uncurry F' ?_, ?_, ?_⟩
    · intro g
      suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id G by
        exact DFunLike.ext_iff.mp this g
      apply b.ext_hom
      intro i
      rw [MonoidHom.comp_apply, hF' i]
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b'⟩ ⟨i, h : b i • a = b'⟩
      change (F' (b i)).left _ = _
      rw [hF' i]
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have hcurried : curry E = F' := by
        apply b.ext_hom
        intro i
        ext a
        · convert hE ⟨(), (b i)⁻¹ • a⟩ ⟨(), a⟩ ⟨i, smul_inv_smul (b i) a⟩
          rw [hF' i]
        · rw [hF' i]
          rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intro t g
        simp only [← hcurried, uncurry_map, curry_apply_left, coe_back, homOfPair.val]
        rfl

lemma actionCategory_eq_of_back_eq {M X : Type u} [Monoid M] [MulAction M X]
    {u v : ActionCategory M X} (h : u.back = v.back) : u = v := by
  cases u
  cases v
  cases h
  rfl

end NielsenSchreierCompat

end ReidemeisterSchreier.Discrete.OpenSubgroups
