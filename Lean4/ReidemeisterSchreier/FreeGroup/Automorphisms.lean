import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/FreeGroup/Automorphisms.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free-group support

Automorphisms, signed-letter words, prefix-parent operations, and generator equivalences for free groups.
-/

namespace ReidemeisterSchreier

/-- The free-group automorphism sending every generator to its inverse. -/
noncomputable def FreeGroup.generatorInversionEquiv (X : Type u) : FreeGroup X ≃* FreeGroup X where
  toFun := FreeGroup.lift fun x => (FreeGroup.of x)⁻¹
  invFun := FreeGroup.lift fun x => (FreeGroup.of x)⁻¹
  left_inv := by
    intro g
    have h :
        (FreeGroup.lift fun x => (FreeGroup.of x)⁻¹).comp
            (FreeGroup.lift fun x => (FreeGroup.of x)⁻¹) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift_apply_of, map_inv, inv_inv,
  MonoidHom.id_apply]
    exact congrArg (fun f : FreeGroup X →* FreeGroup X => f g) h
  right_inv := by
    intro g
    have h :
        (FreeGroup.lift fun x => (FreeGroup.of x)⁻¹).comp
            (FreeGroup.lift fun x => (FreeGroup.of x)⁻¹) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift_apply_of, map_inv, inv_inv,
  MonoidHom.id_apply]
    exact congrArg (fun f : FreeGroup X →* FreeGroup X => f g) h
  map_mul' := by
    intro g h
    simp only [map_mul]

@[simp] theorem FreeGroup.generatorInversionEquiv_apply_of (X : Type u) (x : X) :
    FreeGroup.generatorInversionEquiv X (FreeGroup.of x) = (FreeGroup.of x)⁻¹ := by
  simp only [generatorInversionEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, FreeGroup.lift_apply_of]

@[simp] theorem FreeGroup.generatorInversionEquiv_symm (X : Type u) :
    (FreeGroup.generatorInversionEquiv X).symm = FreeGroup.generatorInversionEquiv X := by
  ext x
  rfl

/-- The automorphism of a free group sending every basis element to its inverse. -/
noncomputable def FreeGroupBasis.generatorInversionAut {ι G : Type u} [Group G]
    (b : FreeGroupBasis ι G) : G ≃* G where
  toFun := b.lift fun i => (b i)⁻¹
  invFun := b.lift fun i => (b i)⁻¹
  left_inv := by
    intro g
    have h :
        (b.lift fun i => (b i)⁻¹).comp (b.lift fun i => (b i)⁻¹) = MonoidHom.id G := by
      apply b.ext_hom
      intro i
      simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroupBasis.lift_apply_apply,
  FreeGroupBasis.repr_apply_coe, FreeGroup.lift_apply_of, map_inv, inv_inv, MonoidHom.id_apply]
    exact congrArg (fun f : G →* G => f g) h
  right_inv := by
    intro g
    have h :
        (b.lift fun i => (b i)⁻¹).comp (b.lift fun i => (b i)⁻¹) = MonoidHom.id G := by
      apply b.ext_hom
      intro i
      simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroupBasis.lift_apply_apply,
  FreeGroupBasis.repr_apply_coe, FreeGroup.lift_apply_of, map_inv, inv_inv, MonoidHom.id_apply]
    exact congrArg (fun f : G →* G => f g) h
  map_mul' := by
    intro g h
    simp only [FreeGroupBasis.lift_apply_apply, map_mul]

@[simp] theorem FreeGroupBasis.generatorInversionAut_apply {ι G : Type u} [Group G]
    (b : FreeGroupBasis ι G) (i : ι) :
    FreeGroupBasis.generatorInversionAut b (b i) = (b i)⁻¹ := by
  simp only [generatorInversionAut, MulEquiv.coe_mk, Equiv.coe_fn_mk, FreeGroupBasis.lift_apply_apply,
  FreeGroupBasis.repr_apply_coe, FreeGroup.lift_apply_of]

theorem FreeGroupBasis.generatorInversionAut_involutive {ι G : Type u} [Group G]
    (b : FreeGroupBasis ι G) :
    Function.Involutive (FreeGroupBasis.generatorInversionAut b) :=
  (FreeGroupBasis.generatorInversionAut b).left_inv

/-- The basis of a free group obtained by inverting the standard generators. -/
noncomputable def FreeGroup.inverseBasis (X : Type u) : FreeGroupBasis X (FreeGroup X) :=
  (FreeGroupBasis.ofFreeGroup X).map (FreeGroup.generatorInversionEquiv X)

@[simp] theorem FreeGroup.inverseBasis_apply {X : Type u} (x : X) :
    FreeGroup.inverseBasis X x = (FreeGroup.of x)⁻¹ := by
  change (FreeGroup.generatorInversionEquiv X) (FreeGroup.of x) = (FreeGroup.of x)⁻¹
  change FreeGroup.lift (fun y : X => (FreeGroup.of y)⁻¹) (FreeGroup.of x) = (FreeGroup.of x)⁻¹
  simp only [FreeGroup.lift_apply_of]

end ReidemeisterSchreier
