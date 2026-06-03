import FoxDifferential.Discrete.DifferentialModule.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/DifferentialModule/Universal.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete group-ring Fox calculus

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

variable {H G : Type*} [Group H] [Group G]

section UniversalProperty

variable {A : Type*} [AddCommGroup A] [Module (GroupRing H) A]

/-- A `ψ`-differential map is a map satisfying the Fox Leibniz rule. -/
abbrev IsDifferentialMap (ψ : G →* H) (δ : G → A) : Prop :=
  IsCrossedDifferential (groupRingScalar ψ) δ

/-- The linear map out of the free pre-module determined by `δ`. -/
def liftLinear (δ : G → A) : DifferentialPreModule H G →ₗ[GroupRing H] A :=
  Finsupp.linearCombination (GroupRing H) δ

omit [Group G] in
/-- The linear extension of a map evaluates on a single basis vector by scalar multiplication. -/
@[simp]
theorem liftLinear_single (δ : G → A) (g : G) (r : GroupRing H) :
    liftLinear δ (Finsupp.single g r) = r • δ g := by
  simp only [liftLinear, Finsupp.linearCombination_single]

/-- A crossed differential kills each defining relation of the universal differential module. -/
theorem liftLinear_relationElement
    (ψ : G →* H) (δ : G → A) (hδ : IsDifferentialMap (A := A) ψ δ) (g₁ g₂ : G) :
    liftLinear δ (relationElement ψ g₁ g₂) = 0 := by
  simp only [liftLinear, relationElement, MonoidAlgebra.of_apply, Finsupp.smul_single, smul_eq_mul, mul_one,
  map_sub, Finsupp.linearCombination_single, hδ g₁ g₂, groupRingScalar_apply, smul_add, one_smul, map_add, sub_self]

/-- The relation submodule is contained in the kernel of the linear extension of a crossed
differential. -/
theorem relationSubmodule_le_ker
    (ψ : G →* H) (δ : G → A) (hδ : IsDifferentialMap (A := A) ψ δ) :
    relationSubmodule ψ ≤ LinearMap.ker (liftLinear δ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g₁, g₂⟩, rfl⟩
  simpa [LinearMap.mem_ker] using liftLinear_relationElement (A := A) ψ δ hδ g₁ g₂

/-- The universal map induced by a `ψ`-differential map. -/
def lift (ψ : G →* H) (δ : G → A) (hδ : IsDifferentialMap (A := A) ψ δ) :
    DifferentialModule ψ →ₗ[GroupRing H] A :=
  (relationSubmodule ψ).liftQ (liftLinear δ) (relationSubmodule_le_ker (A := A) ψ δ hδ)

/-- The universal lift evaluates on `universalDifferential g` as the original crossed differential. -/
theorem lift_d (ψ : G →* H) (δ : G → A) (hδ : IsDifferentialMap (A := A) ψ δ) (g : G) :
    lift ψ δ hδ (universalDifferential ψ g) = δ g := by
  change
      (relationSubmodule ψ).liftQ (liftLinear δ)
          (relationSubmodule_le_ker (A := A) ψ δ hδ)
          ((relationSubmodule ψ).mkQ (Finsupp.single g 1)) = δ g
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  simp only [liftLinear_single, one_smul]

/-- Linear maps out of the universal differential module are equal when they agree on all
universal differentials. -/
@[ext]
theorem hom_ext (ψ : G →* H) {f g : DifferentialModule ψ →ₗ[GroupRing H] A}
    (hfg : ∀ g', f (universalDifferential ψ g') = g (universalDifferential ψ g')) : f = g := by
  apply Submodule.linearMap_qext _
  apply Finsupp.lhom_ext
  intro g' r
  have hsingle : ((relationSubmodule ψ).mkQ (Finsupp.single g' r) : DifferentialModule ψ) =
      r • universalDifferential ψ g' := by
    rw [← Finsupp.smul_single_one]
    rfl
  change f ((relationSubmodule ψ).mkQ (Finsupp.single g' r)) =
    g ((relationSubmodule ψ).mkQ (Finsupp.single g' r))
  rw [hsingle]
  simpa [map_smul] using congrArg (fun z => r • z) (hfg g')

/-- The universal lift is the unique linear map with prescribed values on universal
differentials. -/
theorem lift_unique
    (ψ : G →* H) (δ : G → A) (hδ : IsDifferentialMap (A := A) ψ δ)
    (f : DifferentialModule ψ →ₗ[GroupRing H] A)
    (hf : ∀ g, f (universalDifferential ψ g) = δ g) :
    f = lift (A := A) ψ δ hδ := by
  apply hom_ext ψ
  intro g
  rw [hf g, lift_d]

/-- Existence and uniqueness of the linear map representing a discrete Fox crossed
differential. -/
theorem existsUnique_lift
    (ψ : G →* H) (δ : G → A) (hδ : IsDifferentialMap (A := A) ψ δ) :
    ∃! f : DifferentialModule ψ →ₗ[GroupRing H] A, ∀ g, f (universalDifferential ψ g) = δ g := by
  refine ⟨lift (A := A) ψ δ hδ, ?_, ?_⟩
  · intro g
    exact lift_d (A := A) ψ δ hδ g
  · intro f hf
    exact lift_unique (A := A) ψ δ hδ f hf

/-- The crossed differential induced by a linear map out of the universal differential module. -/
def crossedDifferentialOfLinearMap
    (ψ : G →* H) (f : DifferentialModule ψ →ₗ[GroupRing H] A) : G → A :=
  fun g => f (universalDifferential ψ g)

/-- A linear map out of the universal differential module induces a crossed differential. -/
theorem crossedDifferentialOfLinearMap_isDifferentialMap
    (ψ : G →* H) (f : DifferentialModule ψ →ₗ[GroupRing H] A) :
    IsDifferentialMap (A := A) ψ (crossedDifferentialOfLinearMap (A := A) ψ f) := by
  intro g₁ g₂
  simp only [crossedDifferentialOfLinearMap, relationSubmodule_eq_crossedDifferentialRelationSubmodule,
  universalDifferential_mul, MonoidAlgebra.of_apply, map_add, map_smul, groupRingScalar_apply]

/-- Universal representation theorem for discrete Fox crossed differentials.

Crossed differentials `G -> A` with respect to `ψ : G ->* H` are the same as
`ℤ[H]`-linear maps out of the universal differential module `A_ψ`. -/
def crossedDifferentialEquivLinearMap (ψ : G →* H) :
    {δ : G → A // IsDifferentialMap (A := A) ψ δ} ≃
      (DifferentialModule ψ →ₗ[GroupRing H] A) where
  toFun δ := lift (A := A) ψ δ.1 δ.2
  invFun f :=
    ⟨crossedDifferentialOfLinearMap (A := A) ψ f,
      crossedDifferentialOfLinearMap_isDifferentialMap (A := A) ψ f⟩
  left_inv δ := by
    apply Subtype.ext
    funext g
    exact lift_d (A := A) ψ δ.1 δ.2 g
  right_inv f := by
    apply hom_ext ψ
    intro g
    exact lift_d (A := A) ψ (crossedDifferentialOfLinearMap (A := A) ψ f)
      (crossedDifferentialOfLinearMap_isDifferentialMap (A := A) ψ f) g

/-- Compatibility between the discrete representation theorem and the generic
crossed-differential-module representation theorem. -/
theorem crossedDifferentialEquivLinearMap_eq_generic
    (ψ : G →* H)
    (δ : {δ : G → A // IsDifferentialMap (A := A) ψ δ}) :
    crossedDifferentialEquivLinearMap (A := A) ψ δ =
      (crossedDifferentialModuleEquivLinearMap
        (A := A) (groupRingScalar ψ) δ).comp
        (differentialModuleEquivCrossedDifferentialModule ψ).toLinearMap := by
  apply hom_ext ψ
  intro g
  change
    lift (A := A) ψ δ.1 δ.2 (universalDifferential ψ g) =
      crossedDifferentialModuleLift (A := A) (groupRingScalar ψ) δ.1 δ.2
        (universalCrossedDifferential (groupRingScalar ψ) g)
  rw [lift_d, crossedDifferentialModuleLift_universal]

end UniversalProperty

end

end FoxDifferential
