import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ProCGroups.Completion.UniversalProperty
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import ProCGroups.ProC.Category.Basic
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Basic.lean
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

universe u v w

open ProCGroups

section

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}

/-- Free pro-`C` groups via a strengthened universal property.
The lifting property quantifies over all continuous maps into pro-`C` groups, rather than only
maps whose image generates the target. -/
structure IsFreeProCGroup
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F) : Prop where
  isProC : ProC (G := F)
  continuous_ι : Continuous ι
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      ProC (G := G) →
      ∀ (φ : X → G), Continuous φ →
        ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- A free pro-`C` group of rank `κ`, stated with the existing universal-property
interface. -/
def IsFreeProCGroupOfRank
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (κ : Cardinal.{u}) : Prop :=
  ∃ X : Type u, ∃ _ : TopologicalSpace X,
    Cardinal.mk X = κ ∧
      ∃ ι : X → F, IsFreeProCGroup (ProC := ProC) ι

/-- Concrete finite-class specialization of `IsFreeProCGroupOfRank`. -/
def IsFreeProCGroupOfClassRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (κ : Cardinal.{u}) : Prop :=
  IsFreeProCGroupOfRank
    (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) F κ

namespace IsFreeProCGroup

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- The lift supplied by the corresponding free pro-`C` universal property. -/
noncomputable def lift (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ) : F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ))

/-- The universal-property lift has the prescribed values on the chosen generators. -/
theorem lift_spec (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ) :
    Continuous (hι.lift hG φ hφ) ∧ ∀ x, hι.lift hG φ hφ (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ))

/-- The universal-property lift is unique among continuous maps with the prescribed values. -/
theorem lift_unique (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ := by
  rcases hι.existsUnique_lift hG φ hφ with ⟨g, _hg, huniq⟩
  have hchosen : hι.lift hG φ hφ = g := huniq _ (hι.lift_spec hG φ hφ)
  exact (huniq _ ⟨hf, hfac⟩).trans hchosen.symm

/-- The lift as a continuous monoid homomorphism. -/
noncomputable def liftHom (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ
  continuous_toFun := (hι.lift_spec hG φ hφ).1

/-- Forgetting continuity from `liftHom` gives the underlying universal-property lift. -/
@[simp] theorem liftHom_toMonoidHom (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ) :
    (hι.liftHom hG φ hφ).toMonoidHom = hι.lift hG φ hφ :=
  rfl

/-- `liftHom` has the prescribed value on each generator. -/
@[simp] theorem liftHom_apply (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ) (x : X) :
    hι.liftHom hG φ hφ (ι x) = φ x :=
  (hι.lift_spec hG φ hφ).2 x

/-- `liftHom` is uniquely determined by its values on the generators. -/
theorem liftHom_unique (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    {f : F →ₜ* G} (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.liftHom hG φ hφ := by
  ext y
  exact congrArg (fun g : F →* G => g y)
    (hι.lift_unique hG φ hφ f.continuous_toFun hfac)

/-- Continuous homomorphisms out of a free pro-`C` group are determined by the basis. -/
theorem hom_ext (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G))
    {f g : F →* G} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  let φ : X → G := fun x => f (ι x)
  have hφ : Continuous φ := hf.comp hι.continuous_ι
  have hf_lift : f = hι.lift hG φ hφ := hι.lift_unique hG φ hφ hf (by intro x; rfl)
  have hg_lift : g = hι.lift hG φ hφ :=
    hι.lift_unique hG φ hφ hg (by intro x; exact (hfg x).symm)
  exact hf_lift.trans hg_lift.symm

/-- Two universal-property lifts are equal when they agree on all generators. -/
theorem lift_eq_of_forall (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G))
    {φ ψ : X → G} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x, φ x = ψ x) :
    hι.lift hG φ hφ = hι.lift hG ψ hψ := by
  apply hι.hom_ext hG
    (hι.lift_spec hG φ hφ).1
    (hι.lift_spec hG ψ hψ).1
  intro x
  calc
    hι.lift hG φ hφ (ι x) = φ x := (hι.lift_spec hG φ hφ).2 x
    _ = ψ x := h x
    _ = hι.lift hG ψ hψ (ι x) := ((hι.lift_spec hG ψ hψ).2 x).symm

/-- The lift of the canonical generator map to the same free pro-`C` group is the identity. -/
@[simp] theorem lift_id (hι : IsFreeProCGroup (ProC := ProC) ι) :
    hι.lift hι.isProC ι hι.continuous_ι = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.isProC ι hι.continuous_ι continuous_id (by intro x; rfl)

/-- An endomorphism of a free pro-`C` group fixing the generators is the identity. -/
theorem endomorphism_eq_id (hι : IsFreeProCGroup (ProC := ProC) ι)
    {f : F →* F} (hf : Continuous f) (hfac : ∀ x, f (ι x) = ι x) :
    f = MonoidHom.id F := by
  exact hι.hom_ext hι.isProC hf continuous_id hfac

/-- Composition of free pro-`C` lifts is again the lift of the composed generator map. -/
theorem lift_comp (hι : IsFreeProCGroup (ProC := ProC) ι)
    {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hG : ProC (G := G))
    (hH : ProC (G := H))
    (φ : X → G) (hφ : Continuous φ)
    (ψ : G →* H) (hψ : Continuous ψ) :
    ψ.comp (hι.lift hG φ hφ) =
      hι.lift hH (fun x => ψ (φ x)) (hψ.comp hφ) := by
  apply hι.lift_unique hH (fun x => ψ (φ x)) (hψ.comp hφ)
    (hψ.comp (hι.lift_spec hG φ hφ).1)
  intro x
  simp only [MonoidHom.coe_comp, Function.comp_apply, (hι.lift_spec hG φ hφ).2 x]

/-- The lift as a morphism in the bundled category `ProCGrp`. -/
noncomputable def liftMorphism (hι : IsFreeProCGroup (ProC := ProC) ι)
    [ProCGroups.ProC.ProCGroup ProC F]
    (G : ProCGrp ProC) (φ : X → G) (hφ : Continuous φ) :
    ProCGrp.of ProC F ⟶ G :=
  CategoryTheory.ConcreteCategory.ofHom
    (C := ProCGrp ProC)
    (hι.liftHom (inferInstanceAs (ProCGroups.ProC.ProCGroup ProC G)).isProC φ hφ)

/-- The categorical lift morphism has the prescribed value on each generator. -/
@[simp] theorem liftMorphism_apply (hι : IsFreeProCGroup (ProC := ProC) ι)
    [ProCGroups.ProC.ProCGroup ProC F]
    (G : ProCGrp ProC) (φ : X → G) (hφ : Continuous φ) (x : X) :
    hι.liftMorphism G φ hφ (ι x) = φ x :=
  hι.liftHom_apply (inferInstanceAs (ProCGroups.ProC.ProCGroup ProC G)).isProC φ hφ x

/-- The categorical lift morphism is uniquely determined by its values on the generators. -/
theorem liftMorphism_unique (hι : IsFreeProCGroup (ProC := ProC) ι)
    [ProCGroups.ProC.ProCGroup ProC F]
    (G : ProCGrp ProC) (φ : X → G) (hφ : Continuous φ)
    {f : ProCGrp.of ProC F ⟶ G} (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.liftMorphism G φ hφ := by
  apply ProCGrp.hom_ext
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact congrArg (fun h : F →ₜ* G => h.toMonoidHom)
    (hι.liftHom_unique (inferInstanceAs (ProCGroups.ProC.ProCGroup ProC G)).isProC φ hφ
      (f := f.hom) hfac)

/-- Extensionality for morphisms out of a free pro-`C` group by checking generators. -/
theorem morphism_ext (hι : IsFreeProCGroup (ProC := ProC) ι)
    [ProCGroups.ProC.ProCGroup ProC F]
    {G : ProCGrp ProC} {f g : ProCGrp.of ProC F ⟶ G}
    (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  apply ProCGrp.hom_ext
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact hι.hom_ext (inferInstanceAs (ProCGroups.ProC.ProCGroup ProC G)).isProC
    f.hom.continuous_toFun g.hom.continuous_toFun hfg

/-- Precomposing the basis by a homeomorphism preserves the free pro-`C` universal property. -/
theorem precompHomeomorph
    {X' : Type u} [TopologicalSpace X']
    (hι : IsFreeProCGroup (ProC := ProC) ι) (e : X' ≃ₜ X) :
    IsFreeProCGroup (ProC := ProC) (fun x : X' => ι (e x)) := by
  have hrange : Set.range (fun x : X' => ι (e x)) = Set.range ι := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simp only [Homeomorph.apply_symm_apply]⟩
  refine
    { isProC := hι.isProC
      continuous_ι := hι.continuous_ι.comp e.continuous
      generates_range := by simpa [hrange] using hι.generates_range
      existsUnique_lift := ?_ }
  intro G _ _ _ hG φ hφ
  let φ' : X → G := fun x => φ (e.symm x)
  have hφ' : Continuous φ' := hφ.comp e.symm.continuous
  rcases hι.existsUnique_lift hG φ' hφ' with ⟨f, hf, huniq⟩
  refine ⟨f, ?_, ?_⟩
  · refine ⟨hf.1, ?_⟩
    intro x
    simpa [φ'] using hf.2 (e x)
  · intro g hg
    apply huniq
    refine ⟨hg.1, ?_⟩
    intro x
    simpa [φ'] using hg.2 (e.symm x)

/-- The canonical multiplicative homeomorphism between two free pro-`C` groups on the same
basis. -/
noncomputable def continuousMulEquivOfSameBasis
    {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
    {κ : X → F'}
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hκ : IsFreeProCGroup (ProC := ProC) κ) :
    F ≃ₜ* F' :=
  let f : F →* F' := hι.lift hκ.isProC κ hκ.continuous_ι
  let g : F' →* F := hκ.lift hι.isProC ι hι.continuous_ι
  let hf : Continuous f := (hι.lift_spec hκ.isProC κ hκ.continuous_ι).1
  let hg : Continuous g := (hκ.lift_spec hι.isProC ι hι.continuous_ι).1
  { toMulEquiv :=
      { toFun := f
        invFun := g
        left_inv := by
          intro y
          have hgf : g.comp f = MonoidHom.id F := by
            apply hι.endomorphism_eq_id (hg.comp hf)
            intro x
            dsimp [f, g]
            rw [(hι.lift_spec hκ.isProC κ hκ.continuous_ι).2 x]
            exact (hκ.lift_spec hι.isProC ι hι.continuous_ι).2 x
          exact congrArg (fun h : F →* F => h y) hgf
        right_inv := by
          intro y
          have hfg : f.comp g = MonoidHom.id F' := by
            apply hκ.endomorphism_eq_id (hf.comp hg)
            intro x
            dsimp [f, g]
            rw [(hκ.lift_spec hι.isProC ι hι.continuous_ι).2 x]
            exact (hι.lift_spec hκ.isProC κ hκ.continuous_ι).2 x
          exact congrArg (fun h : F' →* F' => h y) hfg
        map_mul' := f.map_mul }
    continuous_toFun := hf
    continuous_invFun := hg }

/-- The canonical equivalence between free pro-`C` groups with the same basis fixes each generator. -/
@[simp 900] theorem continuousMulEquivOfSameBasis_apply
    {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
    {κ : X → F'}
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hκ : IsFreeProCGroup (ProC := ProC) κ) (x : X) :
    hι.continuousMulEquivOfSameBasis hκ (ι x) = κ x := by
  simpa [continuousMulEquivOfSameBasis] using
    (hι.lift_spec hκ.isProC κ hκ.continuous_ι).2 x

/-- The inverse canonical equivalence between free pro-`C` groups with the same basis fixes each generator. -/
@[simp 900] theorem continuousMulEquivOfSameBasis_symm_apply
    {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
    {κ : X → F'}
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hκ : IsFreeProCGroup (ProC := ProC) κ) (x : X) :
    (hι.continuousMulEquivOfSameBasis hκ).symm (κ x) = ι x := by
  simpa [continuousMulEquivOfSameBasis] using
    (hκ.lift_spec hι.isProC ι hι.continuous_ι).2 x

/-- A homeomorphism of the basis extends to a continuous multiplicative automorphism of the
free pro-`C` group. This is the homeomorphism-valued core used in
Ribes--Zalesskii, Exercise 5.6.2(d). -/
noncomputable def continuousMulEquivOfBasisHomeomorph
    (hι : IsFreeProCGroup (ProC := ProC) ι) (e : X ≃ₜ X) :
    F ≃ₜ* F :=
  hι.continuousMulEquivOfSameBasis (hι.precompHomeomorph e)

@[simp 900] theorem continuousMulEquivOfBasisHomeomorph_apply
    (hι : IsFreeProCGroup (ProC := ProC) ι) (e : X ≃ₜ X) (x : X) :
    hι.continuousMulEquivOfBasisHomeomorph e (ι x) = ι (e x) := by
  simp only [continuousMulEquivOfBasisHomeomorph, continuousMulEquivOfSameBasis_apply]

@[simp 900] theorem continuousMulEquivOfBasisHomeomorph_symm_apply
    (hι : IsFreeProCGroup (ProC := ProC) ι) (e : X ≃ₜ X) (x : X) :
    (hι.continuousMulEquivOfBasisHomeomorph e).symm (ι x) = ι (e.symm x) := by
  simpa [continuousMulEquivOfBasisHomeomorph] using
    (hι.continuousMulEquivOfSameBasis_symm_apply (hι.precompHomeomorph e) (e.symm x))

end IsFreeProCGroup

/-- The homeomorphism of a topological `A`-space induced by one group element. -/
def mulActionHomeomorph
    (A : Type v) (X : Type u) [Group A] [TopologicalSpace A] [TopologicalSpace X]
    [MulAction A X] [ContinuousSMul A X] (a : A) : X ≃ₜ X where
  toEquiv :=
    { toFun := fun x => a • x
      invFun := fun x => a⁻¹ • x
      left_inv := by
        intro x
        calc
          a⁻¹ • (a • x) = (a⁻¹ * a) • x := by rw [mul_smul]
          _ = x := by simp only [inv_mul_cancel, one_smul]
      right_inv := by
        intro x
        calc
          a • (a⁻¹ • x) = (a * a⁻¹) • x := by rw [mul_smul]
          _ = x := by simp only [mul_inv_cancel, one_smul]}
  continuous_toFun := (continuous_const : Continuous fun _ : X => a).smul continuous_id
  continuous_invFun := (continuous_const : Continuous fun _ : X => a⁻¹).smul continuous_id

@[simp 900] theorem mulActionHomeomorph_apply
    (A : Type v) (X : Type u) [Group A] [TopologicalSpace A] [TopologicalSpace X]
    [MulAction A X] [ContinuousSMul A X] (a : A) (x : X) :
    mulActionHomeomorph A X a x = a • x :=
  rfl

@[simp 900] theorem mulActionHomeomorph_symm_apply
    (A : Type v) (X : Type u) [Group A] [TopologicalSpace A] [TopologicalSpace X]
    [MulAction A X] [ContinuousSMul A X] (a : A) (x : X) :
    (mulActionHomeomorph A X a).symm x = a⁻¹ • x :=
  rfl

namespace IsFreeProCGroup

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- A continuous action on the basis extends elementwise to continuous multiplicative
automorphisms of the free pro-`C` group. This packages the automorphism-valued part of
Ribes--Zalesskii, Exercise 5.6.2(d); the joint continuity of the resulting action is a separate
finite-quotient argument. -/
noncomputable def basisActionContinuousMulEquiv
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) (a : A) :
    F ≃ₜ* F :=
  hι.continuousMulEquivOfBasisHomeomorph (mulActionHomeomorph A X a)

@[simp 900] theorem basisActionContinuousMulEquiv_apply
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) (a : A) (x : X) :
    hι.basisActionContinuousMulEquiv a (ι x) = ι (a • x) := by
  simp only [basisActionContinuousMulEquiv, continuousMulEquivOfBasisHomeomorph_apply,
  mulActionHomeomorph_apply]

@[simp 900] theorem basisActionContinuousMulEquiv_symm_apply
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) (a : A) (x : X) :
    (hι.basisActionContinuousMulEquiv a).symm (ι x) = ι (a⁻¹ • x) := by
  simp only [basisActionContinuousMulEquiv, continuousMulEquivOfBasisHomeomorph_symm_apply,
  mulActionHomeomorph_symm_apply]

/-- The automorphism-valued homomorphism extending a continuous action on the basis of a free
pro-`C` group. -/
noncomputable def basisActionMulAutHom
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) :
    A →* MulAut F where
  toFun a := (hι.basisActionContinuousMulEquiv a).toMulEquiv
  map_one' := by
    ext y
    have hhom :
        (hι.basisActionContinuousMulEquiv (1 : A)).toMulEquiv.toMonoidHom =
          MonoidHom.id F := by
      apply hι.hom_ext hι.isProC
        (hι.basisActionContinuousMulEquiv (1 : A)).continuous_toFun
        continuous_id
      intro x
      simp only [mulActionHomeomorph_apply, one_smul, lift_id, MonoidHom.id_apply]
    exact congrArg (fun f : F →* F => f y) hhom
  map_mul' := by
    intro a b
    ext y
    have hcontComp :
        Continuous fun y : F =>
          hι.basisActionContinuousMulEquiv a (hι.basisActionContinuousMulEquiv b y) :=
      (hι.basisActionContinuousMulEquiv a).continuous_toFun.comp
        (hι.basisActionContinuousMulEquiv b).continuous_toFun
    have hhom :
        (hι.basisActionContinuousMulEquiv (a * b)).toMulEquiv.toMonoidHom =
          ((hι.basisActionContinuousMulEquiv a).toMulEquiv.toMonoidHom).comp
            ((hι.basisActionContinuousMulEquiv b).toMulEquiv.toMonoidHom) := by
      apply hι.hom_ext hι.isProC
        (hι.basisActionContinuousMulEquiv (a * b)).continuous_toFun
        hcontComp
      intro x
      calc
        hι.basisActionContinuousMulEquiv (a * b) (ι x) = ι ((a * b) • x) :=
          hι.basisActionContinuousMulEquiv_apply (a * b) x
        _ = ι (a • b • x) := by rw [mul_smul]
        _ = hι.basisActionContinuousMulEquiv a (ι (b • x)) := by
          exact (hι.basisActionContinuousMulEquiv_apply a (b • x)).symm
        _ = hι.basisActionContinuousMulEquiv a
            (hι.basisActionContinuousMulEquiv b (ι x)) := by
          rw [hι.basisActionContinuousMulEquiv_apply b x]
    exact congrArg (fun f : F →* F => f y) hhom

@[simp 900] theorem basisActionMulAutHom_apply
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) (a : A) (x : X) :
    hι.basisActionMulAutHom a (ι x) = ι (a • x) := by
  exact hι.basisActionContinuousMulEquiv_apply a x

/-- The algebraic action on a free pro-`C` group induced by a continuous action on its basis. -/
noncomputable def basisMulDistribMulAction
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) :
    MulDistribMulAction A F where
  smul a y := hι.basisActionMulAutHom a y
  one_smul y := by
    change hι.basisActionMulAutHom (1 : A) y = y
    simp only [map_one, MulAut.one_apply]
  mul_smul a b y := by
    change hι.basisActionMulAutHom (a * b) y =
      hι.basisActionMulAutHom a (hι.basisActionMulAutHom b y)
    simp only [map_mul, MulAut.mul_apply]
  smul_one a := by
    exact map_one (hι.basisActionMulAutHom a)
  smul_mul a y z := by
    exact map_mul (hι.basisActionMulAutHom a) y z

@[simp 900] theorem basisMulDistribMulAction_smul_generator
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsFreeProCGroup (ProC := ProC) ι) (a : A) (x : X) :
    letI : MulDistribMulAction A F := hι.basisMulDistribMulAction
    a • ι x = ι (a • x) := by
  letI : MulDistribMulAction A F := hι.basisMulDistribMulAction
  exact hι.basisActionMulAutHom_apply a x

/-- Tube-lemma form of the continuity input for Exercise 5.6.2(d): after composing with any
discrete pro-`C` target, the automorphisms induced by nearby basis-action parameters agree on a
neighborhood of the chosen parameter. -/
theorem basisActionContinuousMulEquiv_eventually_eq_of_discreteTarget
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    [CompactSpace X]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hQ : ProC (G := Q)) (φ : F →* Q) (hφ : Continuous φ) (a₀ : A) :
    ∃ U : Set A, IsOpen U ∧ a₀ ∈ U ∧
      ∀ a ∈ U,
        φ.comp (hι.basisActionContinuousMulEquiv a).toMulEquiv.toMonoidHom =
          φ.comp (hι.basisActionContinuousMulEquiv a₀).toMulEquiv.toMonoidHom := by
  let T : Set (A × X) := {p | φ (ι (p.1 • p.2)) = φ (ι (a₀ • p.2))}
  have hleft : Continuous fun p : A × X => φ (ι (p.1 • p.2)) := by
    exact hφ.comp (hι.continuous_ι.comp (continuous_fst.smul continuous_snd))
  have hright : Continuous fun p : A × X => φ (ι (a₀ • p.2)) := by
    exact hφ.comp
      (hι.continuous_ι.comp
        ((continuous_const : Continuous fun _ : A × X => a₀).smul continuous_snd))
  have hTopen : IsOpen T := by
    change IsOpen
      ((fun p : A × X => (φ (ι (p.1 • p.2)), φ (ι (a₀ • p.2)))) ⁻¹'
        {q : Q × Q | q.1 = q.2})
    exact (isOpen_discrete {q : Q × Q | q.1 = q.2}).preimage (hleft.prodMk hright)
  have hcontains : ({a₀} : Set A) ×ˢ (Set.univ : Set X) ⊆ T := by
    rintro ⟨a, x⟩ ⟨ha, _hx⟩
    change φ (ι (a • x)) = φ (ι (a₀ • x))
    rw [Set.mem_singleton_iff] at ha
    have ha' : a = a₀ := by simpa using ha
    rw [ha']
  rcases generalized_tube_lemma (s := ({a₀} : Set A)) isCompact_singleton
      (t := (Set.univ : Set X)) isCompact_univ hTopen hcontains with
    ⟨U, V, hUopen, _hVopen, hsingleU, hXV, hUV⟩
  refine ⟨U, hUopen, hsingleU (by simp only [mem_singleton_iff]), ?_⟩
  intro a ha
  have hcontinuous_a :
      Continuous (φ.comp (hι.basisActionContinuousMulEquiv a).toMulEquiv.toMonoidHom) := by
    simpa [MonoidHom.comp_apply] using
      hφ.comp (hι.basisActionContinuousMulEquiv a).continuous_toFun
  have hcontinuous_a₀ :
      Continuous (φ.comp (hι.basisActionContinuousMulEquiv a₀).toMulEquiv.toMonoidHom) := by
    simpa [MonoidHom.comp_apply] using
      hφ.comp (hι.basisActionContinuousMulEquiv a₀).continuous_toFun
  apply hι.hom_ext hQ hcontinuous_a hcontinuous_a₀
  intro x
  have hx : (a, x) ∈ T := hUV ⟨ha, hXV trivial⟩
  change φ (ι (a • x)) = φ (ι (a₀ • x)) at hx
  calc
    (φ.comp (hι.basisActionContinuousMulEquiv a).toMulEquiv.toMonoidHom) (ι x) =
        φ (ι (a • x)) := by
      exact congrArg φ (hι.basisActionContinuousMulEquiv_apply a x)
    _ = φ (ι (a₀ • x)) := hx
    _ = (φ.comp (hι.basisActionContinuousMulEquiv a₀).toMulEquiv.toMonoidHom) (ι x) := by
      exact (congrArg φ (hι.basisActionContinuousMulEquiv_apply a₀ x)).symm

/-- Composing the induced basis action on a free pro-`C` group with a discrete pro-`C` target is
jointly continuous. This is the finite-coordinate continuity statement used to prove the full
joint-continuity part of Exercise 5.6.2(d). -/
theorem continuous_discreteTarget_comp_basisActionContinuousMulEquiv
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    [CompactSpace X]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hQ : ProC (G := Q)) (φ : F →* Q) (hφ : Continuous φ) :
    Continuous fun p : A × F => φ (hι.basisActionContinuousMulEquiv p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases hι.basisActionContinuousMulEquiv_eventually_eq_of_discreteTarget
      (A := A) hQ φ hφ p.1 with
    ⟨U, hUopen, hpU, hUeq⟩
  let f : A × F → Q := fun q => φ (hι.basisActionContinuousMulEquiv p.1 q.2)
  have hf : ContinuousAt f p := by
    have hfcont : Continuous f :=
      (hφ.comp (hι.basisActionContinuousMulEquiv p.1).continuous_toFun).comp continuous_snd
    exact hfcont.continuousAt
  have hUprod : Prod.fst ⁻¹' U ∈ 𝓝 p :=
    (hUopen.preimage continuous_fst).mem_nhds hpU
  have hev :
      (fun q : A × F => φ (hι.basisActionContinuousMulEquiv q.1 q.2)) =ᶠ[𝓝 p] f := by
    filter_upwards [hUprod] with q hq
    exact congrArg (fun η : F →* Q => η q.2) (hUeq q.1 hq)
  exact hf.congr_of_eventuallyEq hev

/-- Exercise 5.6.2(d), concrete finite-class form: a continuous action on the profinite basis of
a free pro-`C` group extends to a jointly continuous action on the free group. The proof checks
continuity on the open-normal finite quotients and then uses the inverse-limit presentation of
the pro-`C` group. -/
theorem basisMulDistribMulAction_continuousSMul_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    [CompactSpace X]
    (hι : IsFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) ι) :
    letI : MulDistribMulAction A F := hι.basisMulDistribMulAction
    ContinuousSMul A F := by
  letI : MulDistribMulAction A F := hι.basisMulDistribMulAction
  refine ContinuousSMul.mk ?_
  let S := ProCGroups.ProC.openNormalSubgroupInClassSystem C F
  let e :=
    ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := F) hForm hι.isProC
  let act : A × F → F := fun p => p.1 • p.2
  let ψ : ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C F),
      A × F → S.X U :=
    fun U p => ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := F) U (act p)
  have hψcont : ∀ U, Continuous (ψ U) := by
    intro U
    letI : DiscreteTopology (S.X U) := by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := F)
          ((OrderDual.ofDual U).1 : OpenNormalSubgroup F))
    letI : IsTopologicalGroup (S.X U) := by infer_instance
    have hQ : (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := S.X U) := by
      letI : Finite (S.X U) := by
        dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
        exact hForm.finiteOnly (OrderDual.ofDual U).2
      exact ProCGroups.ProC.IsProCGroup.of_finite_discrete
        (C := C) (G := S.X U) hForm.quotientClosed (by
          simpa [S, ProCGroups.ProC.openNormalSubgroupInClassSystem] using
            (OrderDual.ofDual U).2)
    have hφcont :
        Continuous (ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := F) U) :=
      continuous_quotient_mk'
    simpa [ψ, act] using
      hι.continuous_discreteTarget_comp_basisActionContinuousMulEquiv
        (A := A) hQ
        (ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := F) U) hφcont
  have hψcompat : S.CompatibleMaps ψ := by
    intro U V hUV
    funext p
    exact congrFun
      (ProCGroups.ProC.openNormalSubgroupInClassProj_compatible (C := C) (G := F) U V hUV)
      (act p)
  have hcontinuous_lift : Continuous (S.inverseLimitLift ψ hψcompat) :=
    S.continuous_inverseLimitLift ψ hψcont hψcompat
  have heq : (fun p : A × F => e (act p)) = S.inverseLimitLift ψ hψcompat := by
    funext p
    apply S.ext
    intro U
    change S.projection U (e (act p)) = ψ U p
    simpa [e, ψ, act, S] using
      ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit_projection
        (C := C) (G := F) hForm hι.isProC U (act p)
  have hcontinuous_eact : Continuous fun p : A × F => e (act p) := by
    simpa [heq] using hcontinuous_lift
  have hcontinuous_act : Continuous act := by
    have hcomp : Continuous fun p : A × F => e.symm (e (act p)) :=
      e.continuous_invFun.comp hcontinuous_eact
    convert hcomp using 1
    funext p
    simp only [ContinuousMulEquiv.symm_apply_apply, act]
  simpa [act] using hcontinuous_act

end IsFreeProCGroup

/-- Pointed free pro-`C` groups via a strengthened universal property. -/
structure IsPointedFreeProCGroup
    {X : Type u} [TopologicalSpace X] (x0 : X)
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F) : Prop where
  isProC : ProC (G := F)
  continuous_ι : Continuous ι
  map_base : ι x0 = 1
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      ProC (G := G) →
      ∀ (φ : X → G), Continuous φ →
        φ x0 = 1 →
        ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

namespace IsPointedFreeProCGroup

variable {X : Type u} [TopologicalSpace X] {x0 : X}
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- The lift supplied by the corresponding free pro-`C` universal property. -/
noncomputable def lift (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    (hφ0 : φ x0 = 1) :
    F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hφ0))

/-- The universal-property lift has the prescribed values on the chosen generators. -/
theorem lift_spec (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    (hφ0 : φ x0 = 1) :
    Continuous (hι.lift hG φ hφ hφ0) ∧ ∀ x, hι.lift hG φ hφ hφ0 (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hφ0))

/-- The universal-property lift is unique among continuous maps with the prescribed values. -/
theorem lift_unique (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    (hφ0 : φ x0 = 1)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ hφ0 := by
  rcases hι.existsUnique_lift hG φ hφ hφ0 with ⟨g, _hg, huniq⟩
  have hchosen : hι.lift hG φ hφ hφ0 = g := huniq _ (hι.lift_spec hG φ hφ hφ0)
  exact (huniq _ ⟨hf, hfac⟩).trans hchosen.symm

/-- The pointed lift as a continuous monoid homomorphism. -/
noncomputable def liftHom (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    (hφ0 : φ x0 = 1) :
    F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ hφ0
  continuous_toFun := (hι.lift_spec hG φ hφ hφ0).1

/-- `liftHom` has the prescribed value on each generator. -/
@[simp] theorem liftHom_apply (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : Continuous φ)
    (hφ0 : φ x0 = 1) (x : X) :
    hι.liftHom hG φ hφ hφ0 (ι x) = φ x :=
  (hι.lift_spec hG φ hφ hφ0).2 x

/-- Extensionality for homomorphisms out of a free pro-`C` group by checking generators. -/
theorem hom_ext (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G))
    {f g : F →* G} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  let φ : X → G := fun x => f (ι x)
  have hφ : Continuous φ := hf.comp hι.continuous_ι
  have hφ0 : φ x0 = 1 := by simp only [hι.map_base, map_one, φ]
  have hf_lift : f = hι.lift hG φ hφ hφ0 :=
    hι.lift_unique hG φ hφ hφ0 hf (by intro x; rfl)
  have hg_lift : g = hι.lift hG φ hφ hφ0 :=
    hι.lift_unique hG φ hφ hφ0 hg (by intro x; exact (hfg x).symm)
  exact hf_lift.trans hg_lift.symm

/-- The lift of the canonical generator map to the same free pro-`C` group is the identity. -/
@[simp] theorem lift_id (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι) :
    hι.lift hι.isProC ι hι.continuous_ι hι.map_base = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.isProC ι hι.continuous_ι hι.map_base continuous_id
    (by intro x; rfl)

/-- An endomorphism of a free pro-`C` group fixing the generators is the identity. -/
theorem endomorphism_eq_id (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {f : F →* F} (hf : Continuous f) (hfac : ∀ x, f (ι x) = ι x) :
    f = MonoidHom.id F := by
  exact hι.hom_ext hι.isProC hf continuous_id hfac

/-- Composition of free pro-`C` lifts is again the lift of the composed generator map. -/
theorem lift_comp (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hG : ProC (G := G))
    (hH : ProC (G := H))
    (φ : X → G) (hφ : Continuous φ) (hφ0 : φ x0 = 1)
    (ψ : G →* H) (hψ : Continuous ψ) :
    ψ.comp (hι.lift hG φ hφ hφ0) =
      hι.lift hH (fun x => ψ (φ x)) (hψ.comp hφ) (by simp only [hφ0, map_one]) := by
  apply hι.lift_unique hH (fun x => ψ (φ x)) (hψ.comp hφ) (by simp only [hφ0, map_one])
    (hψ.comp (hι.lift_spec hG φ hφ hφ0).1)
  intro x
  simp only [MonoidHom.coe_comp, Function.comp_apply, (hι.lift_spec hG φ hφ hφ0).2 x]

/-- A basepoint-preserving continuous action on the pointed basis extends elementwise to
continuous multiplicative automorphisms of the pointed free pro-`C` group. -/
noncomputable def basisActionContinuousMulEquiv
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) (a : A) :
    F ≃ₜ* F := by
  let φ : X → F := fun x => ι (a • x)
  have hφ : Continuous φ := hι.continuous_ι.comp
    ((continuous_const : Continuous fun _ : X => a).smul continuous_id)
  have hφ0 : φ x0 = 1 := by
    dsimp [φ]
    rw [hbase a, hι.map_base]
  let ψ : X → F := fun x => ι (a⁻¹ • x)
  have hψ : Continuous ψ := hι.continuous_ι.comp
    ((continuous_const : Continuous fun _ : X => a⁻¹).smul continuous_id)
  have hψ0 : ψ x0 = 1 := by
    dsimp [ψ]
    rw [hbase a⁻¹, hι.map_base]
  let f : F →* F := hι.lift hι.isProC φ hφ hφ0
  let g : F →* F := hι.lift hι.isProC ψ hψ hψ0
  have hfcont : Continuous f := (hι.lift_spec hι.isProC φ hφ hφ0).1
  have hgcont : Continuous g := (hι.lift_spec hι.isProC ψ hψ hψ0).1
  have hfg : g.comp f = MonoidHom.id F := by
    refine hι.hom_ext hι.isProC (f := g.comp f) (g := MonoidHom.id F)
      (hgcont.comp hfcont) continuous_id ?_
    intro x
    calc
      (g.comp f) (ι x) = g (f (ι x)) := rfl
      _ = g (ι (a • x)) := by
        rw [(hι.lift_spec hι.isProC φ hφ hφ0).2 x]
      _ = ι (a⁻¹ • (a • x)) := by
        rw [(hι.lift_spec hι.isProC ψ hψ hψ0).2 (a • x)]
      _ = ι x := by
        rw [inv_smul_smul]
      _ = MonoidHom.id F (ι x) := rfl
  have hgf : f.comp g = MonoidHom.id F := by
    refine hι.hom_ext hι.isProC (f := f.comp g) (g := MonoidHom.id F)
      (hfcont.comp hgcont) continuous_id ?_
    intro x
    calc
      (f.comp g) (ι x) = f (g (ι x)) := rfl
      _ = f (ι (a⁻¹ • x)) := by
        rw [(hι.lift_spec hι.isProC ψ hψ hψ0).2 x]
      _ = ι (a • (a⁻¹ • x)) := by
        rw [(hι.lift_spec hι.isProC φ hφ hφ0).2 (a⁻¹ • x)]
      _ = ι x := by
        rw [smul_inv_smul]
      _ = MonoidHom.id F (ι x) := rfl
  exact
    { toMulEquiv :=
        { toFun := f
          invFun := g
          left_inv := by
            intro y
            exact congrArg (fun h : F →* F => h y) hfg
          right_inv := by
            intro y
            exact congrArg (fun h : F →* F => h y) hgf
          map_mul' := f.map_mul }
      continuous_toFun := hfcont
      continuous_invFun := hgcont }

@[simp 900] theorem basisActionContinuousMulEquiv_apply
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) (a : A) (x : X) :
    hι.basisActionContinuousMulEquiv hbase a (ι x) = ι (a • x) := by
  let φ : X → F := fun x => ι (a • x)
  have hφ : Continuous φ := hι.continuous_ι.comp
    ((continuous_const : Continuous fun _ : X => a).smul continuous_id)
  have hφ0 : φ x0 = 1 := by
    dsimp [φ]
    rw [hbase a, hι.map_base]
  unfold basisActionContinuousMulEquiv
  dsimp [φ]
  exact (hι.lift_spec hι.isProC φ hφ hφ0).2 x

@[simp 900] theorem basisActionContinuousMulEquiv_symm_apply
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) (a : A) (x : X) :
    (hι.basisActionContinuousMulEquiv hbase a).symm (ι x) = ι (a⁻¹ • x) := by
  let ψ : X → F := fun x => ι (a⁻¹ • x)
  have hψ : Continuous ψ := hι.continuous_ι.comp
    ((continuous_const : Continuous fun _ : X => a⁻¹).smul continuous_id)
  have hψ0 : ψ x0 = 1 := by
    dsimp [ψ]
    rw [hbase a⁻¹, hι.map_base]
  unfold basisActionContinuousMulEquiv
  dsimp [ψ]
  exact (hι.lift_spec hι.isProC ψ hψ hψ0).2 x

/-- The automorphism-valued homomorphism extending a basepoint-preserving action on the pointed
basis of a free pro-`C` group. -/
noncomputable def basisActionMulAutHom
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) :
    A →* MulAut F where
  toFun a := (hι.basisActionContinuousMulEquiv hbase a).toMulEquiv
  map_one' := by
    ext y
    have hhom :
        (hι.basisActionContinuousMulEquiv hbase (1 : A)).toMulEquiv.toMonoidHom =
          MonoidHom.id F := by
      refine hι.hom_ext hι.isProC
        (f := (hι.basisActionContinuousMulEquiv hbase (1 : A)).toMulEquiv.toMonoidHom)
        (g := MonoidHom.id F)
        (hι.basisActionContinuousMulEquiv hbase (1 : A)).continuous_toFun
        continuous_id ?_
      intro x
      change hι.basisActionContinuousMulEquiv hbase (1 : A) (ι x) =
        MonoidHom.id F (ι x)
      rw [hι.basisActionContinuousMulEquiv_apply hbase (1 : A) x, one_smul]
      rfl
    exact congrArg (fun f : F →* F => f y) hhom
  map_mul' := by
    intro a b
    ext y
    have hcontComp :
        Continuous fun y : F =>
          hι.basisActionContinuousMulEquiv hbase a
            (hι.basisActionContinuousMulEquiv hbase b y) :=
      (hι.basisActionContinuousMulEquiv hbase a).continuous_toFun.comp
        (hι.basisActionContinuousMulEquiv hbase b).continuous_toFun
    have hhom :
        (hι.basisActionContinuousMulEquiv hbase (a * b)).toMulEquiv.toMonoidHom =
          ((hι.basisActionContinuousMulEquiv hbase a).toMulEquiv.toMonoidHom).comp
            ((hι.basisActionContinuousMulEquiv hbase b).toMulEquiv.toMonoidHom) := by
      refine hι.hom_ext hι.isProC
        (f := (hι.basisActionContinuousMulEquiv hbase (a * b)).toMulEquiv.toMonoidHom)
        (g :=
          ((hι.basisActionContinuousMulEquiv hbase a).toMulEquiv.toMonoidHom).comp
            ((hι.basisActionContinuousMulEquiv hbase b).toMulEquiv.toMonoidHom))
        (hι.basisActionContinuousMulEquiv hbase (a * b)).continuous_toFun
        hcontComp ?_
      intro x
      calc
        hι.basisActionContinuousMulEquiv hbase (a * b) (ι x) = ι ((a * b) • x) :=
          hι.basisActionContinuousMulEquiv_apply hbase (a * b) x
        _ = ι (a • b • x) := by rw [mul_smul]
        _ = hι.basisActionContinuousMulEquiv hbase a (ι (b • x)) := by
          exact (hι.basisActionContinuousMulEquiv_apply hbase a (b • x)).symm
        _ = hι.basisActionContinuousMulEquiv hbase a
            (hι.basisActionContinuousMulEquiv hbase b (ι x)) := by
          rw [hι.basisActionContinuousMulEquiv_apply hbase b x]
    exact congrArg (fun f : F →* F => f y) hhom

@[simp 900] theorem basisActionMulAutHom_apply
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) (a : A) (x : X) :
    hι.basisActionMulAutHom hbase a (ι x) = ι (a • x) :=
  hι.basisActionContinuousMulEquiv_apply hbase a x

/-- The algebraic action on a pointed free pro-`C` group induced by a basepoint-preserving
continuous action on its pointed basis. -/
noncomputable def basisMulDistribMulAction
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) :
    MulDistribMulAction A F where
  smul a y := hι.basisActionMulAutHom hbase a y
  one_smul y := by
    change hι.basisActionMulAutHom hbase (1 : A) y = y
    simp only [map_one, MulAut.one_apply]
  mul_smul a b y := by
    change hι.basisActionMulAutHom hbase (a * b) y =
      hι.basisActionMulAutHom hbase a (hι.basisActionMulAutHom hbase b y)
    simp only [map_mul, MulAut.mul_apply]
  smul_one a := by
    exact map_one (hι.basisActionMulAutHom hbase a)
  smul_mul a y z := by
    exact map_mul (hι.basisActionMulAutHom hbase a) y z

@[simp 900] theorem basisMulDistribMulAction_smul_generator
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) (a : A) (x : X) :
    letI : MulDistribMulAction A F := hι.basisMulDistribMulAction hbase
    a • ι x = ι (a • x) := by
  letI : MulDistribMulAction A F := hι.basisMulDistribMulAction hbase
  exact hι.basisActionMulAutHom_apply hbase a x

/-- Pointed tube-lemma continuity input for Exercise 5.6.2(d). -/
theorem basisActionContinuousMulEquiv_eventually_eq_of_discreteTarget
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    [CompactSpace X]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0)
    (hQ : ProC (G := Q)) (φ : F →* Q) (hφ : Continuous φ) (a₀ : A) :
    ∃ U : Set A, IsOpen U ∧ a₀ ∈ U ∧
      ∀ a ∈ U,
        φ.comp (hι.basisActionContinuousMulEquiv hbase a).toMulEquiv.toMonoidHom =
          φ.comp (hι.basisActionContinuousMulEquiv hbase a₀).toMulEquiv.toMonoidHom := by
  let T : Set (A × X) := {p | φ (ι (p.1 • p.2)) = φ (ι (a₀ • p.2))}
  have hleft : Continuous fun p : A × X => φ (ι (p.1 • p.2)) := by
    exact hφ.comp (hι.continuous_ι.comp (continuous_fst.smul continuous_snd))
  have hright : Continuous fun p : A × X => φ (ι (a₀ • p.2)) := by
    exact hφ.comp
      (hι.continuous_ι.comp
        ((continuous_const : Continuous fun _ : A × X => a₀).smul continuous_snd))
  have hTopen : IsOpen T := by
    change IsOpen
      ((fun p : A × X => (φ (ι (p.1 • p.2)), φ (ι (a₀ • p.2)))) ⁻¹'
        {q : Q × Q | q.1 = q.2})
    exact (isOpen_discrete {q : Q × Q | q.1 = q.2}).preimage (hleft.prodMk hright)
  have hcontains : ({a₀} : Set A) ×ˢ (Set.univ : Set X) ⊆ T := by
    rintro ⟨a, x⟩ ⟨ha, _hx⟩
    change φ (ι (a • x)) = φ (ι (a₀ • x))
    rw [Set.mem_singleton_iff] at ha
    have ha' : a = a₀ := by simpa using ha
    rw [ha']
  rcases generalized_tube_lemma (s := ({a₀} : Set A)) isCompact_singleton
      (t := (Set.univ : Set X)) isCompact_univ hTopen hcontains with
    ⟨U, V, hUopen, _hVopen, hsingleU, hXV, hUV⟩
  refine ⟨U, hUopen, hsingleU (by simp only [mem_singleton_iff]), ?_⟩
  intro a ha
  have hcontinuous_a :
      Continuous (φ.comp (hι.basisActionContinuousMulEquiv hbase a).toMulEquiv.toMonoidHom) := by
    simpa [MonoidHom.comp_apply] using
      hφ.comp (hι.basisActionContinuousMulEquiv hbase a).continuous_toFun
  have hcontinuous_a₀ :
      Continuous (φ.comp (hι.basisActionContinuousMulEquiv hbase a₀).toMulEquiv.toMonoidHom) := by
    simpa [MonoidHom.comp_apply] using
      hφ.comp (hι.basisActionContinuousMulEquiv hbase a₀).continuous_toFun
  apply hι.hom_ext hQ hcontinuous_a hcontinuous_a₀
  intro x
  have hx : (a, x) ∈ T := hUV ⟨ha, hXV trivial⟩
  change φ (ι (a • x)) = φ (ι (a₀ • x)) at hx
  calc
    (φ.comp (hι.basisActionContinuousMulEquiv hbase a).toMulEquiv.toMonoidHom) (ι x) =
        φ (ι (a • x)) := by
      exact congrArg φ (hι.basisActionContinuousMulEquiv_apply hbase a x)
    _ = φ (ι (a₀ • x)) := hx
    _ = (φ.comp (hι.basisActionContinuousMulEquiv hbase a₀).toMulEquiv.toMonoidHom) (ι x) := by
      exact (congrArg φ (hι.basisActionContinuousMulEquiv_apply hbase a₀ x)).symm

/-- Composing the pointed induced basis action with a discrete pro-`C` target is jointly
continuous. -/
theorem continuous_discreteTarget_comp_basisActionContinuousMulEquiv
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    [CompactSpace X]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    (hι : IsPointedFreeProCGroup (ProC := ProC) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0)
    (hQ : ProC (G := Q)) (φ : F →* Q) (hφ : Continuous φ) :
    Continuous fun p : A × F => φ (hι.basisActionContinuousMulEquiv hbase p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases hι.basisActionContinuousMulEquiv_eventually_eq_of_discreteTarget
      (A := A) hbase hQ φ hφ p.1 with
    ⟨U, hUopen, hpU, hUeq⟩
  let f : A × F → Q := fun q => φ (hι.basisActionContinuousMulEquiv hbase p.1 q.2)
  have hf : ContinuousAt f p := by
    have hfcont : Continuous f :=
      (hφ.comp (hι.basisActionContinuousMulEquiv hbase p.1).continuous_toFun).comp continuous_snd
    exact hfcont.continuousAt
  have hUprod : Prod.fst ⁻¹' U ∈ 𝓝 p :=
    (hUopen.preimage continuous_fst).mem_nhds hpU
  have hev :
      (fun q : A × F => φ (hι.basisActionContinuousMulEquiv hbase q.1 q.2)) =ᶠ[𝓝 p] f := by
    filter_upwards [hUprod] with q hq
    exact congrArg (fun η : F →* Q => η q.2) (hUeq q.1 hq)
  exact hf.congr_of_eventuallyEq hev

/-- Pointed form of Exercise 5.6.2(d) for a finite-group class: a basepoint-preserving continuous
action on the pointed profinite basis extends to a jointly continuous action on the pointed free
pro-`C` group. -/
theorem basisMulDistribMulAction_continuousSMul_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {A : Type v} [Group A] [TopologicalSpace A] [MulAction A X] [ContinuousSMul A X]
    [CompactSpace X]
    (hι : IsPointedFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) x0 ι)
    (hbase : ∀ a : A, a • x0 = x0) :
    letI : MulDistribMulAction A F := hι.basisMulDistribMulAction hbase
    ContinuousSMul A F := by
  letI : MulDistribMulAction A F := hι.basisMulDistribMulAction hbase
  refine ContinuousSMul.mk ?_
  let S := ProCGroups.ProC.openNormalSubgroupInClassSystem C F
  let e :=
    ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := F) hForm hι.isProC
  let act : A × F → F := fun p => p.1 • p.2
  let ψ : ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C F),
      A × F → S.X U :=
    fun U p => ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := F) U (act p)
  have hψcont : ∀ U, Continuous (ψ U) := by
    intro U
    letI : DiscreteTopology (S.X U) := by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := F)
          ((OrderDual.ofDual U).1 : OpenNormalSubgroup F))
    letI : IsTopologicalGroup (S.X U) := by infer_instance
    have hQ : (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := S.X U) := by
      letI : Finite (S.X U) := by
        dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
        exact hForm.finiteOnly (OrderDual.ofDual U).2
      exact ProCGroups.ProC.IsProCGroup.of_finite_discrete
        (C := C) (G := S.X U) hForm.quotientClosed (by
          simpa [S, ProCGroups.ProC.openNormalSubgroupInClassSystem] using
            (OrderDual.ofDual U).2)
    have hφcont :
        Continuous (ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := F) U) :=
      continuous_quotient_mk'
    simpa [ψ, act] using
      hι.continuous_discreteTarget_comp_basisActionContinuousMulEquiv
        (A := A) hbase hQ
        (ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := F) U) hφcont
  have hψcompat : S.CompatibleMaps ψ := by
    intro U V hUV
    funext p
    exact congrFun
      (ProCGroups.ProC.openNormalSubgroupInClassProj_compatible (C := C) (G := F) U V hUV)
      (act p)
  have hcontinuous_lift : Continuous (S.inverseLimitLift ψ hψcompat) :=
    S.continuous_inverseLimitLift ψ hψcont hψcompat
  have heq : (fun p : A × F => e (act p)) = S.inverseLimitLift ψ hψcompat := by
    funext p
    apply S.ext
    intro U
    change S.projection U (e (act p)) = ψ U p
    simpa [e, ψ, act, S] using
      ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit_projection
        (C := C) (G := F) hForm hι.isProC U (act p)
  have hcontinuous_eact : Continuous fun p : A × F => e (act p) := by
    simpa [heq] using hcontinuous_lift
  have hcontinuous_act : Continuous act := by
    have hcomp : Continuous fun p : A × F => e.symm (e (act p)) :=
      e.continuous_invFun.comp hcontinuous_eact
    convert hcomp using 1
    funext p
    simp only [ContinuousMulEquiv.symm_apply_apply, act]
  simpa [act] using hcontinuous_act

end IsPointedFreeProCGroup

end

section

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}

/-- A family in a topological group converges to `1` when every open subgroup contains all but
finitely many indexed terms. -/
def FamilyConvergesToOne
    {X : Type v}
    {G : Type u} [Group G] [TopologicalSpace G]
    (μ : X → G) : Prop :=
  ∀ U : OpenSubgroup G, {x : X | μ x ∉ (U : Set G)}.Finite

namespace FamilyConvergesToOne

variable {X : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A family converging to `1` has range converging to `1` as a set. -/
theorem range {μ : X → G} (hμ : FamilyConvergesToOne (G := G) μ) :
    Generation.ConvergesToOne (G := G) (Set.range μ) := by
  intro U
  have hsubset :
      Set.range μ \ (U : Set G) ⊆ μ '' {x : X | μ x ∉ (U : Set G)} := by
    rintro y ⟨⟨x, rfl⟩, hxU⟩
    exact ⟨x, hxU, rfl⟩
  exact (hμ U).image μ |>.subset hsubset

/-- Convergence to `1` is preserved by a continuous homomorphism. -/
theorem comp
    {H : Type*} [TopologicalSpace H] [Group H]
    {μ : X → G}
    (hμ : FamilyConvergesToOne (G := G) μ) (f : G →ₜ* H) :
    FamilyConvergesToOne (G := H) (fun x => f (μ x)) := by
  intro U
  simpa using hμ (OpenSubgroup.comap (f := (f : G →* H)) f.continuous U)

/-- Range convergence implies family convergence for injectively indexed families. -/
theorem of_set_of_injective {μ : X → G}
    (hμ : Generation.ConvergesToOne (G := G) (Set.range μ))
    (hinj : Function.Injective μ) :
    FamilyConvergesToOne (G := G) μ := by
  intro U
  have himage :
      μ '' {x : X | μ x ∉ (U : Set G)} = Set.range μ \ (U : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hxU, rfl⟩
      exact ⟨⟨x, rfl⟩, hxU⟩
    · rintro ⟨⟨x, rfl⟩, hxU⟩
      exact ⟨x, hxU, rfl⟩
  letI : Finite (μ '' {x : X | μ x ∉ (U : Set G)}) := by
    rw [himage]
    exact (hμ U).to_subtype
  exact Finite.Set.finite_of_finite_image {x : X | μ x ∉ (U : Set G)} (by
    intro a _ b _ hab
    exact hinj hab)

/-- Families indexed by a finite type converge to `1`. -/
theorem of_finite_domain [Finite X] (μ : X → G) :
    FamilyConvergesToOne (G := G) μ := by
  intro U
  exact Set.finite_univ.subset (by intro x _; trivial)

end FamilyConvergesToOne

/-- A family which both converges to `1` and topologically generates the target. -/
structure ConvergingGeneratingMap
    (X : Type v)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  toFun : X → G
  convergesToOne : FamilyConvergesToOne (G := G) toFun
  generates : Generation.TopologicallyGenerates (G := G) (Set.range toFun)

namespace ConvergingGeneratingMap

variable {X Y : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instCoeFunConvergingGeneratingMap :
    CoeFun (ConvergingGeneratingMap X G) (fun _ => X → G) where
  coe φ := φ.toFun

@[simp] theorem toFun_eq_coe (φ : ConvergingGeneratingMap X G) :
    φ.toFun = (φ : X → G) := rfl

/-- Reindexing along an equivalence preserves family convergence and generation. -/
def reindex (φ : ConvergingGeneratingMap X G) (e : Y ≃ X) :
    ConvergingGeneratingMap Y G where
  toFun := fun y => φ (e y)
  convergesToOne := by
    intro U
    have hsubset :
        {y : Y | φ (e y) ∉ (U : Set G)} ⊆
          e.symm '' {x : X | φ x ∉ (U : Set G)} := by
      intro y hy
      exact ⟨e y, hy, by simp only [Equiv.symm_apply_apply]⟩
    exact (φ.convergesToOne U).image e.symm |>.subset hsubset
  generates := by
    have hrange : Set.range (fun y : Y => φ (e y)) = Set.range (φ : X → G) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨e y, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨e.symm x, by simp only [Equiv.apply_symm_apply]⟩
    simpa [hrange] using φ.generates

theorem generatesAndConvergesToOne (φ : ConvergingGeneratingMap X G) :
    Generation.GeneratesAndConvergesToOne (G := G) (Set.range (φ : X → G)) :=
  ⟨φ.generates, φ.convergesToOne.range⟩

end ConvergingGeneratingMap

/-- Generated-target extension property for a pro-`C` group on a topological space.

This is weaker than the free pro-`C` universal property: it only asks for extensions to targets
generated by the chosen map. -/
class HasGeneratingTargetExtensionProperty
    (X : Type u) [TopologicalSpace X]
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F) : Prop where
  isProC : ProC (G := F)
  continuous_ι : Continuous ι
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      ProC (G := G) →
      ∀ (φ : X → G), Continuous φ →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- The true free pro-`C` universal property implies the generated-target extension property. -/
theorem generatingTargetExtensionProperty_of_free
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsFreeProCGroup (ProC := ProC) ι) :
    HasGeneratingTargetExtensionProperty (ProC := ProC) X F ι := by
  refine
    { isProC := hι.isProC
      continuous_ι := hι.continuous_ι
      generates_range := hι.generates_range
      existsUnique_lift := ?_ }
  intro G _ _ _ hG φ hφ _hgen
  exact hι.existsUnique_lift hG φ hφ

namespace HasGeneratingTargetExtensionProperty

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- Recover the usual free pro-`C` universal property from the older generated-target interface,
provided the pro-`C` predicate is stable under closed subgroups.

The proof corestricts an arbitrary target map to the closed subgroup it topologically generates,
uses the generated-target extension property there, and then composes with the inclusion. -/
theorem toFreeProperty
    (hι : HasGeneratingTargetExtensionProperty (ProC := ProC) X F ι)
    (hClosedSubgroups :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC (G := G) → (H : ClosedSubgroup G) →
          ProC (G := ↥(H : Subgroup G))) :
    IsFreeProCGroup (ProC := ProC) ι := by
  refine
    { isProC := hι.isProC
      continuous_ι := hι.continuous_ι
      generates_range := hι.generates_range
      existsUnique_lift := ?_ }
  intro G _ _ _ hG φ hφ
  let K : ClosedSubgroup G := Generation.closedSubgroupGenerated (G := G) (Set.range φ)
  let φK : X → ↥(K : Subgroup G) := Generation.closedSubgroupGeneratedMap (G := G) φ
  have hφKcont : Continuous φK := by
    exact Continuous.subtype_mk hφ (fun x => (φK x).2)
  have hφKgen :
      Generation.TopologicallyGenerates (G := ↥(K : Subgroup G)) (Set.range φK) := by
    simpa [φK] using
      (Generation.closedSubgroupGeneratedMap_topologicallyGenerates (G := G) φ)
  have hK : ProC (G := ↥(K : Subgroup G)) := hClosedSubgroups hG K
  rcases hι.existsUnique_lift hK φK hφKcont hφKgen with
    ⟨fK, hfK, huniqK⟩
  let incl : ↥(K : Subgroup G) →* G := (K : Subgroup G).subtype
  let f : F →* G := incl.comp fK
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · exact continuous_subtype_val.comp hfK.1
  · intro x
    exact congrArg Subtype.val (hfK.2 x)
  · intro g hg
    have hg_mem : ∀ y : F, g y ∈ (K : Subgroup G) := by
      let L : Subgroup F := Subgroup.comap g (K : Subgroup G)
      have hLclosed : IsClosed ((L : Subgroup F) : Set F) := by
        change IsClosed (g ⁻¹' ((K : Subgroup G) : Set G))
        exact K.isClosed'.preimage hg.1
      have hsub : Subgroup.closure (Set.range ι) ≤ L := by
        rw [Subgroup.closure_le]
        rintro y ⟨x, rfl⟩
        change g (ι x) ∈ (K : Subgroup G)
        simpa [K, hg.2 x] using
          (Subgroup.le_topologicalClosure (Subgroup.closure (Set.range φ))
            (Subgroup.subset_closure ⟨x, rfl⟩))
      have htop : (⊤ : Subgroup F) ≤ L := by
        have hcl : (Subgroup.closure (Set.range ι)).topologicalClosure ≤ L :=
          Subgroup.topologicalClosure_minimal _ hsub hLclosed
        have hgen : (Subgroup.closure (Set.range ι)).topologicalClosure = ⊤ := hι.generates_range
        simpa [hgen] using hcl
      intro y
      exact htop trivial
    let gK : F →* ↥(K : Subgroup G) :=
      { toFun := fun y => ⟨g y, hg_mem y⟩
        map_one' := by
          apply Subtype.ext
          simp only [map_one, OneMemClass.coe_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp only [map_mul, MulMemClass.mk_mul_mk]}
    have hgKcont : Continuous gK :=
      Continuous.subtype_mk hg.1 hg_mem
    have hgKfac : ∀ x, gK (ι x) = φK x := by
      intro x
      apply Subtype.ext
      exact hg.2 x
    have hgK_eq : gK = fK := huniqK gK ⟨hgKcont, hgKfac⟩
    apply MonoidHom.ext
    intro y
    change g y = fK y
    calc
      g y = (gK y : G) := rfl
      _ = (fK y : G) := by rw [hgK_eq]
      _ = f y := rfl

end HasGeneratingTargetExtensionProperty

/-- The generated-target extension property is the true free pro-`C` universal property when the
class of pro-`C` groups is stable under closed subgroups. -/
theorem free_of_generatingTargetExtensionProperty_of_closedSubgroups
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : HasGeneratingTargetExtensionProperty (ProC := ProC) X F ι)
    (hClosedSubgroups :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC (G := G) → (H : ClosedSubgroup G) →
          ProC (G := ↥(H : Subgroup G))) :
    IsFreeProCGroup (ProC := ProC) ι :=
  hι.toFreeProperty hClosedSubgroups

/-- Pointed free pro-`C` group on a pointed topological space. -/
class IsPointedFreeProCGroupOn
    (X : Type u) [TopologicalSpace X] (x0 : X)
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F) : Prop where
  isProC : ProC (G := F)
  continuous_ι : Continuous ι
  map_base : ι x0 = 1
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      ProC (G := G) →
      ∀ (φ : X → G), Continuous φ → φ x0 = 1 →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- Free pro-`C` group on a set converging to `1`. -/
class IsFreeProCGroupOnConvergingSet
    (X : Type v)
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F) : Prop where
  isProC : ProC (G := F)
  convergesToOne : FamilyConvergesToOne (G := F) ι
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      ProC (G := G) →
      ∀ (φ : X → G), FamilyConvergesToOne (G := G) φ →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- The canonical map of a free pro-`C` group on a topological space is injective whenever the
predicate supplies enough separating pro-`C` targets. -/
theorem freeProCGroupOn_injective
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hsep :
      ∀ ⦃x y : X⦄, x ≠ y →
        ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
          ProC (G := A) ∧
            ∃ φ : X → A, Continuous φ ∧
              Generation.TopologicallyGenerates (G := A) (Set.range φ) ∧ φ x ≠ φ y) :
    Function.Injective ι := by
  intro x y hEq
  by_contra hxy
  rcases hsep hxy with ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, φ, hφ, hgenφ, hφxy⟩
  rcases hι.existsUnique_lift hA φ hφ with ⟨f, hf, _huniq⟩
  have hcontr : φ x = φ y := by
    simpa [hf.2 x, hf.2 y] using congrArg f hEq
  exact hφxy hcontr

/-- Under an explicit nontrivial cyclic pro-`C` target hypothesis, the identity does not lie in
the image of the topological basis of a free pro-`C` group. -/
theorem one_not_mem_range_of_freeProCGroupOn
    {X : Type u} [TopologicalSpace X] [Nonempty X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsFreeProCGroup (ProC := ProC) ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
        ProC (G := A) ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    (1 : F) ∉ Set.range ι := by
  intro h1
  rcases h1 with ⟨x, hx⟩
  rcases hnontrivial with ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, a, ha1, hgena⟩
  let φ : X → A := fun _ => a
  have hφ : Continuous φ := continuous_const
  have hrange : Set.range φ = ({a} : Set A) := by
    ext b
    constructor
    · rintro ⟨y, rfl⟩
      simp only [mem_singleton_iff, φ]
    · intro hb
      rw [Set.mem_singleton_iff] at hb
      subst b
      exact ⟨Classical.choice ‹Nonempty X›, rfl⟩
  have hgenφ : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    simpa [hrange] using hgena
  rcases hι.existsUnique_lift hA φ hφ with ⟨f, hf, _huniq⟩
  have haeq : a = 1 := by
    simpa [φ, hx] using (hf.2 x).symm
  exact ha1 haeq

/-- Under an explicit nontrivial cyclic pro-`C` target hypothesis, the identity does not lie in a
basis converging to `1`. -/
theorem one_not_mem_range_of_freeProCGroupOnConvergingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
        ProC (G := A) ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    (1 : F) ∉ Set.range ι := by
  classical
  intro h1
  rcases h1 with ⟨x, hx⟩
  rcases hnontrivial with ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, a, ha1, hgena⟩
  let φ : X → A := fun z => if z = x then a else 1
  have hφconv : FamilyConvergesToOne (G := A) φ := by
    intro U
    have hsubset : {z : X | φ z ∉ (U : Set A)} ⊆ ({x} : Set X) := by
      intro z hz
      by_cases hzx : z = x
      · simp only [hzx, mem_singleton_iff]
      · exfalso
        exact hz (by simp only [hzx, ↓reduceIte, SetLike.mem_coe, one_mem, φ])
    exact (Set.finite_singleton x).subset hsubset
  have hφgen : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    have hsub : ({a} : Set A) ⊆ Set.range φ := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨x, by simp only [↓reduceIte, φ]⟩
    exact Generation.topologicallyGenerates_mono (G := A) hgena hsub
  rcases hι.existsUnique_lift hA φ hφconv hφgen with ⟨f, hf, _⟩
  have haeq : a = 1 := by
    simpa [φ, hx] using (hf.2 x).symm
  exact ha1 haeq

/-- Under the same nontrivial cyclic-target hypothesis, the basis map for a free pro-`C` group on
a set converging to `1` is injective. -/
theorem freeProCGroupOnConvergingSet_injective
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
        ProC (G := A) ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    Function.Injective ι := by
  classical
  intro x y hEq
  by_contra hxy
  rcases hnontrivial with ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, a, ha1, hgena⟩
  have hyx : y ≠ x := by
    intro hyx'
    exact hxy hyx'.symm
  let φ : X → A := fun z => if z = x then a else 1
  have hφconv : FamilyConvergesToOne (G := A) φ := by
    intro U
    have hsubset : {z : X | φ z ∉ (U : Set A)} ⊆ ({x} : Set X) := by
      intro z hz
      by_cases hzx : z = x
      · simp only [hzx, mem_singleton_iff]
      · exfalso
        exact hz (by simp only [hzx, ↓reduceIte, SetLike.mem_coe, one_mem, φ])
    exact (Set.finite_singleton x).subset hsubset
  have hφgen : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    have hsub : ({a} : Set A) ⊆ Set.range φ := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨x, by simp only [↓reduceIte, φ]⟩
    exact Generation.topologicallyGenerates_mono (G := A) hgena hsub
  rcases hι.existsUnique_lift hA φ hφconv hφgen with ⟨f, hf, _⟩
  have hfa : f (ι x) = a := by
    simpa [φ] using hf.2 x
  have hf1 : f (ι y) = 1 := by
    simpa [φ, hyx] using hf.2 y
  have haeq : a = 1 := by
    rw [← hfa, ← hf1]
    exact congrArg f hEq
  exact ha1 haeq

/-- A nontrivial cyclic topological group has a nontrivial singleton topological generator. -/
theorem exists_nontrivial_singleton_topologicalGenerator
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [IsCyclic A] [Nontrivial A] :
    ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  have ha1 : a ≠ 1 := by
    intro hEq
    have hallOne : ∀ x : A, x = 1 := by
      intro x
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha x)
      simpa [hEq] using hn.symm
    exact not_subsingleton A ⟨fun x y => by rw [hallOne x, hallOne y]⟩
  refine ⟨a, ha1, ?_⟩
  rw [Generation.TopologicallyGenerates]
  apply top_unique
  intro x _
  exact Subgroup.le_topologicalClosure _ <| by
    simpa [Subgroup.zpowers_eq_closure] using ha x

/-- A concrete finite-group class containing a nontrivial finite cyclic group admits a
nontrivial topologically cyclic pro-`C` model. -/
theorem exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A) :
    ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := A) ∧
        ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) := by
  rcases hcyc with ⟨A, _instGroupA, _instFiniteA, hCA, hAcyc, hAnontriv⟩
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := ⟨rfl⟩
  let _ : IsTopologicalGroup A := by infer_instance
  letI : IsCyclic A := hAcyc
  letI : Nontrivial A := hAnontriv
  have hAProC : (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := A) := by
    exact ProCGroups.ProC.IsProCGroup.of_finite_discrete
      (C := C) (G := A) hquot hCA
  rcases exists_nontrivial_singleton_topologicalGenerator (A := A) with ⟨a, ha1, hgena⟩
  exact ⟨A, inferInstance, inferInstance, inferInstance, hAProC, a, ha1, hgena⟩

/-- For a finite-rank free pro-`C` group, any generating family with the same finite cardinality
is again a converging-set basis. -/
theorem finite_generatingFamily_is_basis
    {X : Type u} {Y : Type u}
    [Finite X] [Finite Y]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F} {μ : Y → F}
    (hF : ProCGroups.IsProfiniteGroup F)
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (hcard : Cardinal.mk X = Cardinal.mk Y)
    (hgen : Generation.TopologicallyGenerates (G := F) (Set.range μ)) :
    IsFreeProCGroupOnConvergingSet (ProC := ProC) Y F μ := by
  classical
  letI : CompactSpace F := ProCGroups.IsProfiniteGroup.compactSpace hF
  letI : T2Space F := ProCGroups.IsProfiniteGroup.t2Space hF
  letI : TotallyDisconnectedSpace F := ProCGroups.IsProfiniteGroup.totallyDisconnectedSpace hF
  have hXY : Nonempty (X ≃ Y) := by
    simpa [← Cardinal.eq] using hcard
  let eXY : X ≃ Y := Classical.choice hXY
  let ψ : X → F := fun x => μ (eXY x)
  have hψconv : FamilyConvergesToOne (G := F) ψ := by
    exact FamilyConvergesToOne.of_finite_domain (G := F) ψ
  have hψgen : Generation.TopologicallyGenerates (G := F) (Set.range ψ) := by
    have hrange : Set.range ψ = Set.range μ := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨eXY x, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨eXY.symm y, by simp only [Equiv.apply_symm_apply, ψ]⟩
    simpa [hrange] using hgen
  rcases hι.existsUnique_lift hι.isProC ψ hψconv hψgen with ⟨σ, hσ, hσuniq⟩
  have hrangeμ : Set.range μ ⊆ (σ.range : Set F) := by
    rintro z ⟨y, rfl⟩
    exact ⟨ι (eXY.symm y), by simpa [ψ] using hσ.2 (eXY.symm y)⟩
  have hσgen : Generation.TopologicallyGenerates (G := F) ((σ.range : Set F)) :=
    Generation.topologicallyGenerates_mono (G := F) hgen hrangeμ
  have hσclosed : IsClosed ((σ.range : Set F)) := by
    simpa using (isCompact_range hσ.1).isClosed
  have hσclosure_le : (σ.range : Subgroup F).topologicalClosure ≤ σ.range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
  have hσclosure_top : (σ.range : Subgroup F).topologicalClosure = ⊤ := by
    have htop :
        (Subgroup.closure (σ.range : Set F)).topologicalClosure = (⊤ : Subgroup F) := by
      simpa [Generation.TopologicallyGenerates] using hσgen
    have hclosure_eq : (σ.range : Subgroup F) = Subgroup.closure (σ.range : Set F) := by
      simpa using (Subgroup.closure_eq (σ.range)).symm
    rw [hclosure_eq]
    exact htop
  have hσrange_top : σ.range = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z ∈ ((σ.range : Subgroup F).topologicalClosure : Set F) := by
      rw [hσclosure_top]
      simp only [Subgroup.coe_top, mem_univ]
    exact hσclosure_le hz'
  have hσsurj : Function.Surjective σ := by
    intro z
    have hz : z ∈ (σ.range : Set F) := by
      simp only [hσrange_top, Subgroup.coe_top, mem_univ]
    simpa using hz
  let σc : ContinuousMonoidHom F F :=
    { toMonoidHom := σ
      continuous_toFun := hσ.1 }
  have hFG : _root_.ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated F := by
    letI : Fintype Y := Fintype.ofFinite Y
    refine ⟨Finset.univ.image μ, ?_⟩
    simpa [Finset.coe_image] using hgen
  rcases
      (_root_.ProCGroups.FiniteGeneration.surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
        (G := F)) hFG σc hσsurj with
    ⟨e, he⟩
  refine ⟨hι.isProC, ?_, hgen, ?_⟩
  · exact FamilyConvergesToOne.of_finite_domain (G := F) μ
  · intro G _ _ _ hG φ hφ hgenφ
    let φX : X → G := fun x => φ (eXY x)
    have hφXconv : FamilyConvergesToOne (G := G) φX := by
      exact FamilyConvergesToOne.of_finite_domain (G := G) φX
    have hφXgen : Generation.TopologicallyGenerates (G := G) (Set.range φX) := by
      have hrange : Set.range φX = Set.range φ := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨eXY x, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨eXY.symm y, by simp only [Equiv.apply_symm_apply, φX]⟩
      simpa [hrange] using hgenφ
    rcases hι.existsUnique_lift hG φX hφXconv hφXgen with ⟨fX, hfX, hfXuniq⟩
    let fY : F →* G := fX.comp e.symm.toMonoidHom
    refine ⟨fY, ⟨hfX.1.comp e.symm.continuous, ?_⟩, ?_⟩
    · intro y
      have hpre : e.symm (μ y) = ι (eXY.symm y) := by
        apply e.injective
        calc
          e (e.symm (μ y)) = μ y := by simp only [ContinuousMulEquiv.apply_symm_apply]
          _ = σ (ι (eXY.symm y)) := by
              symm
              simpa [ψ] using hσ.2 (eXY.symm y)
          _ = e (ι (eXY.symm y)) := by simpa [σc] using (he (ι (eXY.symm y))).symm
      calc
        fY (μ y) = fX (e.symm (μ y)) := rfl
        _ = fX (ι (eXY.symm y)) := by rw [hpre]
        _ = φX (eXY.symm y) := hfX.2 (eXY.symm y)
        _ = φ y := by simp only [Equiv.apply_symm_apply, φX]
    · intro g hg
      have hcomp : g.comp e.toMonoidHom = fX := by
        apply hfXuniq
        refine ⟨hg.1.comp e.continuous, ?_⟩
        intro x
        calc
          (g.comp e.toMonoidHom) (ι x) = g (e (ι x)) := rfl
          _ = g (σ (ι x)) := by
              exact congrArg g (by simpa [σc] using he (ι x))
          _ = g (μ (eXY x)) := by
              exact congrArg g (by simpa [ψ] using hσ.2 x)
          _ = φ (eXY x) := hg.2 (eXY x)
          _ = φX x := rfl
      ext z
      have hz := congrArg (fun k : F →* G => k (e.symm z)) hcomp
      have hz' : g (e (e.symm z)) = fX (e.symm z) := by
        change (g.comp e.toMonoidHom) (e.symm z) = fX (e.symm z)
        exact hz
      calc
        g z = g (e (e.symm z)) := by
          exact congrArg g (e.apply_symm_apply z).symm
        _ = fX (e.symm z) := hz'
        _ = fY z := rfl

/-- Concrete finite-group-class specialization of `finite_generatingFamily_is_basis`. -/
theorem finite_generatingFamily_is_basis_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    {X : Type u} {Y : Type u}
    [Finite X] [Finite Y]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F} {μ : Y → F}
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (hcard : Cardinal.mk X = Cardinal.mk Y)
    (hgen : Generation.TopologicallyGenerates (G := F) (Set.range μ)) :
    IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) Y F μ := by
  exact finite_generatingFamily_is_basis
    (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
    (hF := ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hι.isProC)
    hι hcard hgen

/-- Concrete finite-group-class specialization when a nontrivial cyclic target is available. -/
theorem finite_generatingFamily_is_basis_of_finiteGroupClass_cyclic
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} {Y : Type u}
    [Finite X] [Finite Y]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F} {μ : Y → F}
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (hcard : Cardinal.mk X = Cardinal.mk Y)
    (hgen : Generation.TopologicallyGenerates (G := F) (Set.range μ)) :
    IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) Y F μ := by
  rcases exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass C hquot hcyc with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, a, ha1, hgena⟩
  exact finite_generatingFamily_is_basis
    (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
    (hF := ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hι.isProC)
    hι hcard hgen

/-- If a continuous homomorphism has range containing a topological generating set, then it is
surjective between profinite groups. -/
theorem surjective_hom_of_rangeContainsGeneratingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hF : ProCGroups.IsProfiniteGroup F)
    (hG : ProCGroups.IsProfiniteGroup G)
    {ι : X → G}
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range ι))
    {σ : F →* G} (hσ : Continuous σ)
    (hsub : Set.range ι ⊆ (σ.range : Set G)) :
    Function.Surjective σ := by
  letI : CompactSpace F := ProCGroups.IsProfiniteGroup.compactSpace hF
  letI : T2Space G := ProCGroups.IsProfiniteGroup.t2Space hG
  have hσgen : Generation.TopologicallyGenerates (G := G) ((σ.range : Set G)) :=
    Generation.topologicallyGenerates_mono (G := G) hgen hsub
  have hσclosed : IsClosed ((σ.range : Set G)) := by
    simpa using (isCompact_range hσ).isClosed
  have hσclosure_le : (σ.range : Subgroup G).topologicalClosure ≤ σ.range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
  have hσclosure_top : (σ.range : Subgroup G).topologicalClosure = ⊤ := by
    have htop :
        (Subgroup.closure (σ.range : Set G)).topologicalClosure = (⊤ : Subgroup G) := by
      simpa [Generation.TopologicallyGenerates] using hσgen
    have hclosure_eq : (σ.range : Subgroup G) = Subgroup.closure (σ.range : Set G) := by
      simpa using (Subgroup.closure_eq (σ.range)).symm
    rw [hclosure_eq]
    exact htop
  have hσrange_top : σ.range = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z ∈ ((σ.range : Subgroup G).topologicalClosure : Set G) := by
      rw [hσclosure_top]
      simp only [Subgroup.coe_top, mem_univ]
    exact hσclosure_le hz'
  intro z
  have hz : z ∈ (σ.range : Set G) := by
    simp only [hσrange_top, Subgroup.coe_top, mem_univ]
  simpa using hz

/-- A topologically finitely generated free pro-`C` group on a converging set has finite basis,
provided `C` admits a nontrivial cyclic pro-`C` target. -/
theorem finite_of_topologicallyFinitelyGenerated_freeProCGroupOnConvergingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hFprof : ProCGroups.IsProfiniteGroup F)
    (hfg : FiniteGeneration.TopologicallyFinitelyGenerated F)
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
        ProC (G := A) ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    Finite X := by
  classical
  by_cases hXfin : Finite X
  · exact hXfin
  · have hXinf : Infinite X := by
      by_contra hXnotinf
      exact hXfin (not_infinite_iff_finite.mp hXnotinf)
    letI : Infinite X := hXinf
    letI : Nonempty X := Infinite.nonempty (α := X)
    letI : CompactSpace F := ProCGroups.IsProfiniteGroup.compactSpace hFprof
    letI : T2Space F := ProCGroups.IsProfiniteGroup.t2Space hFprof
    letI : TotallyDisconnectedSpace F := ProCGroups.IsProfiniteGroup.totallyDisconnectedSpace hFprof
    have hFspace : InverseSystems.IsProfiniteSpace F :=
      (InverseSystems.isProfiniteSpace_iff_compact_t2_totallyDisconnected (X := F)).2
        ⟨inferInstance, inferInstance, inferInstance⟩
    rcases
        (FiniteGeneration.topologicallyFinitelyGenerated_iff_exists_topologicallyGeneratedByAtMost
          (G := F)).mp hfg with
      ⟨_n, s, _hsle, hgen⟩
    have hsle : Cardinal.mk ↥s ≤ Cardinal.mk X := by
      exact (show Cardinal.mk ↥s < Cardinal.mk X from calc
        Cardinal.mk ↥s < Cardinal.aleph0 := by
          exact (Cardinal.mk_lt_aleph0_iff).2 (Finite.of_fintype ↥s)
        _ ≤ Cardinal.mk X := Cardinal.aleph0_le_mk X).le
    have hsle' : Cardinal.mk ↥s ≤ Cardinal.mk (Set.univ : Set X) := by
      simpa using hsle
    obtain ⟨p, _hpSub, hpCard⟩ := (Cardinal.le_mk_iff_exists_subset
      (c := Cardinal.mk ↥s) (s := (Set.univ : Set X))).1 hsle'
    have hpEquiv : Nonempty (p ≃ ↥s) := by
      simpa [← Cardinal.eq] using hpCard
    let e : p ≃ ↥s := Classical.choice hpEquiv
    have hpfinite : p.Finite :=
      Set.finite_coe_iff.mp (Finite.of_equiv (↥s) e.symm)
    let φ : X → F := fun x => if hx : x ∈ p then (e ⟨x, hx⟩ : F) else 1
    have hφconv : FamilyConvergesToOne (G := F) φ := by
      intro U
      have hsubset : {x : X | φ x ∉ (U : Set F)} ⊆ p := by
        intro x hx
        by_cases hxp : x ∈ p
        · exact hxp
        · exfalso
          exact hx (by simp only [hxp, ↓reduceDIte, SetLike.mem_coe, one_mem, φ])
      exact hpfinite.subset hsubset
    have hφgen : Generation.TopologicallyGenerates (G := F) (Set.range φ) := by
      have hsub : (s : Set F) ⊆ Set.range φ := by
        intro z hz
        let a : ↥s := ⟨z, hz⟩
        refine ⟨(e.symm a).1, ?_⟩
        have hp : (e.symm a).1 ∈ p := (e.symm a).2
        simp only [hp, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply, φ, a]
      exact Generation.topologicallyGenerates_mono (G := F) hgen hsub
    rcases hι.existsUnique_lift hι.isProC φ hφconv hφgen with ⟨σ, hσ, _⟩
    have hφsubσ : Set.range φ ⊆ (σ.range : Set F) := by
      rintro z ⟨x, rfl⟩
      exact ⟨ι x, hσ.2 x⟩
    have hσsurj : Function.Surjective σ :=
      surjective_hom_of_rangeContainsGeneratingSet
        (hF := hFprof) (hG := hFprof) hφgen hσ.1 hφsubσ
    let σc : ContinuousMonoidHom F F := {
      toMonoidHom := σ
      continuous_toFun := hσ.1
    }
    rcases
        (FiniteGeneration.surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
          (G := F))
          hfg σc hσsurj with
      ⟨eσ, heσ⟩
    have hσinj : Function.Injective σ := by
      intro a b hab
      have h' : eσ a = eσ b := by
        calc
          eσ a = σ a := by simpa [σc] using heσ a
          _ = σ b := hab
          _ = eσ b := by simpa [σc] using (heσ b).symm
      exact eσ.injective h'
    have hιinj : Function.Injective ι :=
      freeProCGroupOnConvergingSet_injective (hι := hι) hnontrivial
    have hφinj : Function.Injective φ := by
      intro x y hxy
      apply hιinj
      apply hσinj
      calc
        σ (ι x) = φ x := hσ.2 x
        _ = φ y := hxy
        _ = σ (ι y) := (hσ.2 y).symm
    have hφsub : Set.range φ ⊆ (s : Set F) ∪ ({1} : Set F) := by
      rintro z ⟨x, rfl⟩
      by_cases hxp : x ∈ p
      · left
        simp only [hxp, ↓reduceDIte, Subtype.coe_prop, φ]
      · right
        simp only [hxp, ↓reduceDIte, mem_singleton_iff, φ]
    have hφfin : (Set.range φ).Finite :=
      (s.finite_toSet.union (Set.finite_singleton (1 : F))).subset hφsub
    have hXlt : Cardinal.mk X < Cardinal.aleph0 := by
      calc
        Cardinal.mk X = Cardinal.mk (Set.range φ) := by
          simpa using (Cardinal.mk_range_eq φ hφinj).symm
        _ < Cardinal.aleph0 := by
          exact (Cardinal.mk_lt_aleph0_iff).2 hφfin.to_subtype
    exact False.elim (hXfin ((Cardinal.mk_lt_aleph0_iff).1 hXlt))

/-- A fixed free pro-`C` group on a set converging to `1` admits a continuous epimorphism onto any
profinite pro-`C` target generated by the image of its basis. -/
theorem exists_freeProCGroupOnConvergingSet_surjecting
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hF : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (hFprof : ProCGroups.IsProfiniteGroup F)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G))
    (hGprof : ProCGroups.IsProfiniteGroup G)
    (φ : X → G)
    (hφ : FamilyConvergesToOne (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    ∃ ψ : F →* G, Continuous ψ ∧ Function.Surjective ψ ∧ ∀ x, ψ (ι x) = φ x := by
  rcases hF.existsUnique_lift hG φ hφ hgen with ⟨ψ, hψ, _⟩
  have hsub : Set.range φ ⊆ (ψ.range : Set G) := by
    rintro z ⟨x, rfl⟩
    exact ⟨ι x, hψ.2 x⟩
  have hψsurj : Function.Surjective ψ :=
    surjective_hom_of_rangeContainsGeneratingSet
      (hF := hFprof) (hG := hGprof) hgen hψ.1 hsub
  exact ⟨ψ, hψ.1, hψsurj, hψ.2⟩

/-- The pro-`C` completion of the abstract free group on a finite basis is free pro-`C` on that
basis. -/
theorem proCCompletionOfAbstractFreeGroup_is_free
    {X : Type u} [Finite X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    {Fhat : Type u} [Group Fhat] [TopologicalSpace Fhat] [IsTopologicalGroup Fhat]
    {ι : FreeGroup X →ₜ* Fhat}
    (hι : ProCGroups.Completion.IsProCCompletion ProC (FreeGroup X) Fhat ι) :
    IsFreeProCGroupOnConvergingSet (ProC := ProC) X Fhat
      (fun x => ι (FreeGroup.of x)) := by
  refine ⟨hι.isProC, ?_, ?_, ?_⟩
  · exact FamilyConvergesToOne.of_finite_domain (G := Fhat)
      (fun x : X => ι (FreeGroup.of x))
  · have himage :
        ι '' Set.range (FreeGroup.of : X → FreeGroup X) =
          Set.range (fun x : X => ι (FreeGroup.of x)) := by
      simpa [Function.comp] using
        (Set.range_comp ι (FreeGroup.of : X → FreeGroup X)).symm
    have hclosure :
        Subgroup.closure (Set.range fun x : X => ι (FreeGroup.of x)) =
          ι.toMonoidHom.range := by
      calc
        Subgroup.closure (Set.range fun x : X => ι (FreeGroup.of x))
            = Subgroup.map ι.toMonoidHom
                (Subgroup.closure (Set.range (FreeGroup.of : X → FreeGroup X))) := by
              simpa [himage] using
                (ι.toMonoidHom.map_closure (Set.range (FreeGroup.of : X → FreeGroup X))).symm
        _ = ι.toMonoidHom.range := by
          rw [FreeGroup.closure_range_of X, MonoidHom.range_eq_map]
    rw [Generation.TopologicallyGenerates, hclosure]
    rw [SetLike.ext'_iff, Subgroup.topologicalClosure_coe, Subgroup.coe_top]
    simpa [DenseRange, MonoidHom.coe_range, dense_iff_closure_eq] using hι.denseRange
  · intro G _ _ _ hG φ _hφ hgen
    let φfree : FreeGroup X →ₜ* G :=
      { toMonoidHom := FreeGroup.lift φ
        continuous_toFun := by
          simpa using (continuous_of_discreteTopology : Continuous (FreeGroup.lift φ)) }
    let φhat : Fhat →ₜ* G := hι.lift hG φfree
    refine ⟨φhat.toMonoidHom, ?_, ?_⟩
    · refine ⟨φhat.continuous_toFun, ?_⟩
      intro x
      have hfac := congrArg (fun ψ : FreeGroup X →ₜ* G => ψ (FreeGroup.of x))
        (hι.lift_spec hG φfree)
      have hfree : φfree (FreeGroup.of x) = φ x := by
        change FreeGroup.lift φ (FreeGroup.of x) = φ x
        simp only [FreeGroup.lift_apply_of]
      exact hfac.trans hfree
    · intro g hg
      let gCont : Fhat →ₜ* G := { toMonoidHom := g, continuous_toFun := hg.1 }
      have hfac' : gCont.comp ι = φfree := by
        apply ContinuousMonoidHom.toMonoidHom_injective
        ext x
        change g (ι (FreeGroup.of x)) = FreeGroup.lift φ (FreeGroup.of x)
        exact (hg.2 x).trans (by simp only [FreeGroup.lift_apply_of])
      exact congrArg ContinuousMonoidHom.toMonoidHom (hι.lift_unique hG φfree hfac')

namespace IsFreeProCGroupOnConvergingSet

variable {X : Type v}
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable {ι : X → F}

/-- The lift supplied by the corresponding free pro-`C` universal property. -/
noncomputable def lift
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : FamilyConvergesToOne (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hgen))

/-- The universal-property lift has the prescribed values on the chosen generators. -/
theorem lift_spec
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : FamilyConvergesToOne (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    Continuous (hι.lift hG φ hφ hgen) ∧
      ∀ x, hι.lift hG φ hφ hgen (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hgen))

/-- The universal-property lift is unique among continuous maps with the prescribed values. -/
theorem lift_unique
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : FamilyConvergesToOne (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ))
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ hgen := by
  rcases hι.existsUnique_lift hG φ hφ hgen with ⟨g, _hg, huniq⟩
  have hchosen : hι.lift hG φ hφ hgen = g := huniq _ (hι.lift_spec hG φ hφ hgen)
  exact (huniq _ ⟨hf, hfac⟩).trans hchosen.symm

/-- For a concrete finite-group class, the generated-target universal property of a free
pro-`C` group on a converging set extends any target map that converges to `1`.

The proof corestricts the target map to the closed subgroup it topologically generates. This is
the form needed for retractions that collapse all but finitely many basis elements. -/
theorem existsUnique_lift_of_convergesToOne_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := G))
    (φ : X → G) (hφ : FamilyConvergesToOne (G := G) φ) :
    ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x := by
  classical
  let K : ClosedSubgroup G := Generation.closedSubgroupGenerated (G := G) (Set.range φ)
  let φK : X → ↥(K : Subgroup G) := Generation.closedSubgroupGeneratedMap (G := G) φ
  have hφKconv : FamilyConvergesToOne (G := ↥(K : Subgroup G)) φK := by
    intro U
    have hU_nhds : ((U : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G)) ∈
        𝓝 (1 : ↥(K : Subgroup G)) :=
      U.isOpen'.mem_nhds U.one_mem'
    rcases
        (mem_nhds_subtype ((K : Subgroup G) : Set G) (1 : ↥(K : Subgroup G))
          ((U : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))).1 hU_nhds with
      ⟨W₀, hW₀_nhds, hW₀U⟩
    rcases mem_nhds_iff.mp hW₀_nhds with ⟨W, hWU₀, hWopen, h1W⟩
    rcases hG.hasOpenNormalBasisInClass W hWopen h1W with ⟨V, hVW, _hCV⟩
    have hsub :
        {x : X | φK x ∉ (U : Set ↥(K : Subgroup G))} ⊆
          {x : X | φ x ∉ ((V.toOpenSubgroup : OpenSubgroup G) : Set G)} := by
      intro x hx hxV
      exact hx (hW₀U (by
        change φ x ∈ W₀
        exact hWU₀ (hVW hxV)))
    exact (hφ V.toOpenSubgroup).subset hsub
  have hφKgen :
      Generation.TopologicallyGenerates (G := ↥(K : Subgroup G)) (Set.range φK) := by
    simpa [φK] using
      (Generation.closedSubgroupGeneratedMap_topologicallyGenerates (G := G) φ)
  have hK :
      (ProCGroups.ProC.finiteGroupClassProCPredicate C)
        (G := ↥(K : Subgroup G)) :=
    ProCGroups.ProC.IsProCGroup.of_closedSubgroup hIso hSub hQuot hG K
  rcases hι.existsUnique_lift hK φK hφKconv hφKgen with ⟨fK, hfK, huniqK⟩
  let incl : ↥(K : Subgroup G) →* G := (K : Subgroup G).subtype
  let f : F →* G := incl.comp fK
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · exact continuous_subtype_val.comp hfK.1
  · intro x
    exact congrArg Subtype.val (hfK.2 x)
  · intro g hg
    have hgK_mem : ∀ y : F, g y ∈ (K : Subgroup G) := by
      intro y
      have hy :
          y ∈ (Generation.closedSubgroupGenerated (G := F) (Set.range ι) : Subgroup F) := by
        change y ∈ ((Subgroup.closure (Set.range ι)).topologicalClosure : Subgroup F)
        rw [hι.generates_range]
        simp only [Subgroup.mem_top]
      have hgy :=
        Generation.map_mem_closedSubgroupGenerated_image
          (G := F) (H := G)
          ({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G)
          (X := Set.range ι) hy
      have himage :
          (({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G) ''
              Set.range ι) = Set.range φ := by
        ext z
        constructor
        · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, (hg.2 x).symm⟩
        · rintro ⟨x, rfl⟩
          exact ⟨ι x, ⟨x, rfl⟩, hg.2 x⟩
      simpa [K, himage] using hgy
    let gK : F →* ↥(K : Subgroup G) :=
      { toFun := fun y => ⟨g y, hgK_mem y⟩
        map_one' := by
          apply Subtype.ext
          simp only [map_one, OneMemClass.coe_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp only [map_mul, MulMemClass.mk_mul_mk]}
    have hgKcont : Continuous gK := by
      exact Continuous.subtype_mk hg.1 (fun y => (gK y).2)
    have hgKfac : ∀ x, gK (ι x) = φK x := by
      intro x
      apply Subtype.ext
      exact hg.2 x
    have hgK_eq : gK = fK := huniqK gK ⟨hgKcont, hgKfac⟩
    ext y
    exact congrArg Subtype.val (congrArg (fun f : F →* ↥(K : Subgroup G) => f y) hgK_eq)

/-- Continuous-homomorphism form of
`existsUnique_lift_of_convergesToOne_of_finiteGroupClass`. -/
theorem existsUnique_liftHom_of_convergesToOne_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := G))
    (φ : X → G) (hφ : FamilyConvergesToOne (G := G) φ) :
    ∃! f : F →ₜ* G, ∀ x, f (ι x) = φ x := by
  rcases existsUnique_lift_of_convergesToOne_of_finiteGroupClass
      C hIso hSub hQuot hι hG φ hφ with
    ⟨f, hf, huniq⟩
  let fc : F →ₜ* G :=
    { toMonoidHom := f
      continuous_toFun := hf.1 }
  refine ⟨fc, hf.2, ?_⟩
  intro g hg
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact huniq g.toMonoidHom ⟨g.continuous, hg⟩

/-- In a free pro-`Σ` group with nonempty `Σ`, a free generator has no positive torsion. -/
theorem generator_pow_ne_one_of_sigma
    {σ : Set ℕ} (hσ : ∃ p, p ∈ σ ∧ Nat.Prime p)
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
          (ProCGroups.FiniteGroupClass.sigmaGroup σ)) X F ι)
    (i : X) (N : ℕ) (hN : 0 < N) :
    (ι i) ^ N ≠ 1 := by
  classical
  rcases hσ with ⟨p, hpσ, hp⟩
  let M := p ^ (N + 1)
  have hMpos : 0 < M := pow_pos hp.pos (N + 1)
  have hsigmaM : ProCGroups.FiniteGroupClass.IsSigmaNumber σ M :=
    ProCGroups.FiniteGroupClass.IsSigmaNumber.prime_pow_of_mem
      (sigma := σ) (p := p) (k := N + 1) hpσ hp
  let T := ULift.{u} (Multiplicative (ZMod M))
  letI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  letI : Finite T := by
    let e : T ≃ Multiplicative (ZMod M) := Equiv.ulift
    exact Finite.of_equiv (Multiplicative (ZMod M)) e.symm
  letI : TopologicalSpace T := ⊥
  letI : DiscreteTopology T := ⟨rfl⟩
  letI : IsTopologicalGroup T := by infer_instance
  let φ : X → T :=
    fun j => if j = i then ULift.up (Multiplicative.ofAdd (1 : ZMod M)) else 1
  have hφconv : FamilyConvergesToOne (G := T) φ := by
    intro U
    refine (Set.finite_singleton i).subset ?_
    intro j hj
    by_cases hji : j = i
    · simp only [hji, Set.mem_singleton_iff]
    · have hφj : φ j = 1 := by simp only [hji, ↓reduceIte, φ]
      have hmem : φ j ∈ (U : Set T) := by simp only [hφj, SetLike.mem_coe, one_mem]
      exact False.elim (hj hmem)
  have hTclass : ProCGroups.FiniteGroupClass.sigmaGroup σ T :=
    ProCGroups.FiniteGroupClass.sigmaGroup_cyclicZMod (sigma := σ) hMpos hsigmaM
  have hT :
      (ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.sigmaGroup σ)) (G := T) :=
    ProCGroups.ProC.IsProCGroup.of_finite_discrete
      (C := ProCGroups.FiniteGroupClass.sigmaGroup σ)
      (G := T)
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed σ)
      hTclass
  rcases hι.existsUnique_liftHom_of_convergesToOne_of_finiteGroupClass
      (ProCGroups.FiniteGroupClass.sigmaGroup σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed σ)
      hT φ hφconv with
    ⟨f, hf, _⟩
  intro hpow
  have hf_pow : f ((ι i) ^ N) = 1 := by simp only [hpow, map_one]
  have hcalc : f ((ι i) ^ N) = ULift.up (Multiplicative.ofAdd (N : ZMod M)) := by
    calc
      f ((ι i) ^ N) = (f (ι i)) ^ N := by simp only [map_pow]
      _ = (φ i) ^ N := by rw [hf i]
      _ = (ULift.up (Multiplicative.ofAdd (1 : ZMod M))) ^ N := by simp only [↓reduceIte, φ]
      _ = ULift.up (Multiplicative.ofAdd (N : ZMod M)) := by
        apply ULift.ext
        change (Multiplicative.ofAdd (1 : ZMod M)) ^ N =
          Multiplicative.ofAdd (N : ZMod M)
        change Multiplicative.ofAdd ((N : ℕ) • (1 : ZMod M)) =
          Multiplicative.ofAdd (N : ZMod M)
        simp only [nsmul_eq_mul, mul_one]
  have hlt_pow : N < p ^ (N + 1) :=
    lt_of_lt_of_le
      (Nat.lt_pow_self (n := N) (a := p) hp.one_lt)
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ N))
  have hNmod : (N : ZMod M) ≠ 0 := by
    intro hzero
    have hdiv : M ∣ N := (ZMod.natCast_eq_zero_iff N M).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt hN hlt_pow) hdiv
  have hofAdd_ne : ULift.up (Multiplicative.ofAdd (N : ZMod M)) ≠ (1 : T) := by
    intro h
    have hdown : Multiplicative.ofAdd (N : ZMod M) = 1 := congrArg ULift.down h
    have hz : (N : ZMod M) = 0 := by
      change Multiplicative.ofAdd (N : ZMod M) =
        Multiplicative.ofAdd (0 : ZMod M) at hdown
      exact Multiplicative.ofAdd.injective hdown
    exact hNmod hz
  exact hofAdd_ne (hcalc.symm.trans hf_pow)

/-- Integer-power form of `generator_pow_ne_one_of_sigma`. -/
theorem generator_zpow_ne_one_of_sigma
    {σ : Set ℕ} (hσ : ∃ p, p ∈ σ ∧ Nat.Prime p)
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
          (ProCGroups.FiniteGroupClass.sigmaGroup σ)) X F ι)
    (i : X) (n : ℤ) (hn : n ≠ 0) :
    (ι i) ^ n ≠ 1 := by
  intro hzn
  have hnat_pos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hnat_ne :
      (ι i) ^ n.natAbs ≠ 1 :=
    hι.generator_pow_ne_one_of_sigma hσ i n.natAbs hnat_pos
  apply hnat_ne
  by_cases hnonneg : 0 ≤ n
  · have hnat : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hnonneg
    simpa [zpow_natCast, hnat] using hzn
  · have hneg : n < 0 := lt_of_not_ge hnonneg
    have hnat : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hneg.le
    have hzn' : (ι i) ^ (-n) = 1 := by
      calc
        (ι i) ^ (-n) = ((ι i) ^ n)⁻¹ := by rw [zpow_neg]
        _ = 1 := by simp only [hzn, inv_one]
    simpa [zpow_natCast, hnat] using hzn'

/-- The continuous homomorphism supplied by the free pro-`C` universal property. -/
noncomputable def liftHom
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : FamilyConvergesToOne (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ hgen
  continuous_toFun := (hι.lift_spec hG φ hφ hgen).1

/-- Bundled version of `liftHom`, taking a converging generating map as a single argument. -/
noncomputable def liftConvergingGeneratingMap
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : ConvergingGeneratingMap X G) :
    F →ₜ* G :=
  hι.liftHom hG φ φ.convergesToOne φ.generates

/-- The bundled lift has the prescribed value on each generator. -/
@[simp] theorem liftConvergingGeneratingMap_apply
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : ConvergingGeneratingMap X G) (x : X) :
    hι.liftConvergingGeneratingMap hG φ (ι x) = φ x := by
  change hι.lift hG φ φ.convergesToOne φ.generates (ι x) = φ x
  exact (hι.lift_spec hG φ φ.convergesToOne φ.generates).2 x

/-- `liftHom` has the prescribed value on each generator. -/
@[simp] theorem liftHom_apply
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ProC (G := G)) (φ : X → G)
    (hφ : FamilyConvergesToOne (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) (x : X) :
    hι.liftHom hG φ hφ hgen (ι x) = φ x :=
  (hι.lift_spec hG φ hφ hgen).2 x

section FiniteSupportRetracts

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable [hVar : Fact (ProCGroups.FiniteGroupClass.Variety C)]
variable [hIso : Fact (ProCGroups.FiniteGroupClass.IsomClosed C)]
variable {X : Type v} [DecidableEq X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- The unique continuous endomorphism of a free pro-`C` group that keeps the finite set `S`
of basis elements and sends the remaining basis elements to `1`. -/
theorem existsUnique_collapseToFinset_of_finiteGroupClass
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    ∃! φ : F →ₜ* F, ∀ x, φ (ι x) = if x ∈ S then ι x else 1 := by
  have hconv :
      FamilyConvergesToOne (G := F) (fun x => if x ∈ S then ι x else 1) := by
    intro U
    classical
    refine S.finite_toSet.subset ?_
    intro x hx
    by_cases hxS : x ∈ S
    · exact hxS
    · exfalso
      exact hx (by simp only [hxS, ↓reduceIte, SetLike.mem_coe, one_mem])
  exact
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet.existsUnique_liftHom_of_convergesToOne_of_finiteGroupClass
      C hIso.out hVar.out.subgroupClosed hVar.out.quotientClosed
      hι hι.isProC (fun x => if x ∈ S then ι x else 1) hconv

/-- The finite-support retraction of a free pro-`C` group onto the closed subgroup generated by a
finite set of basis elements. -/
noncomputable def collapseToFinset
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    F →ₜ* F :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S))

@[simp] theorem collapseToFinset_apply_mem
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    {S : Finset X} {x : X} (hx : x ∈ S) :
    hι.collapseToFinset S (ι x) = ι x := by
  simpa [hx, collapseToFinset] using
    (Classical.choose_spec
      (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S)) x)

@[simp] theorem collapseToFinset_apply_not_mem
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    {S : Finset X} {x : X} (hx : x ∉ S) :
    hι.collapseToFinset S (ι x) = 1 := by
  simpa [hx, collapseToFinset] using
    (Classical.choose_spec
      (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S)) x)

@[simp] theorem collapseToFinset_idempotent
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    (hι.collapseToFinset S).comp (hι.collapseToFinset S) =
      hι.collapseToFinset S := by
  let hFprof : ProCGroups.IsProfiniteGroup F :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hι.isProC
  letI : T2Space F := hFprof.t2Space
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ContinuousMonoidHom.comp_toFun, hx, collapseToFinset_apply_mem]
  · simp only [ContinuousMonoidHom.comp_toFun, hx, not_false_eq_true, collapseToFinset_apply_not_mem, map_one]

/-- A homomorphism that kills every basis element outside `S` is unchanged after precomposition
with the finite-support retraction. -/
theorem comp_collapseToFinset_eq_of_eq_one_outside
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (φ : F →ₜ* G) (S : Finset X)
    (hφ : ∀ x, x ∉ S → φ (ι x) = 1) :
    φ.comp (hι.collapseToFinset S) = φ := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ContinuousMonoidHom.comp_toFun, hx, collapseToFinset_apply_mem]
  · simp only [ContinuousMonoidHom.comp_toFun, hx, not_false_eq_true, collapseToFinset_apply_not_mem, map_one,
  hφ x hx]

/-- The map from the free pro-`C` group onto the range of its finite-support retraction. -/
noncomputable def collapseToFinsetRange
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    F →ₜ* ↥((hι.collapseToFinset S : F →* F).range) :=
  { toMonoidHom := (hι.collapseToFinset S : F →* F).rangeRestrict
    continuous_toFun :=
      (hι.collapseToFinset S).continuous.subtype_mk (fun x => ⟨x, rfl⟩) }

/-- The inclusion of the range of a finite-support retraction back into the ambient free group. -/
noncomputable def collapseToFinsetInclusion
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    ↥((hι.collapseToFinset S : F →* F).range) →ₜ* F :=
  { toMonoidHom := ((hι.collapseToFinset S : F →* F).range).subtype
    continuous_toFun := continuous_subtype_val }

/-- The range of the finite-support retraction, viewed as the finite-basis retract. -/
abbrev FinsetSupportRetract
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) : Type u :=
  ↥((hι.collapseToFinset S : F →* F).range)

/-- The finite basis of the finite-support retract. -/
noncomputable def finsetSupportBasis
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    S → hι.FinsetSupportRetract S := by
  intro x
  refine ⟨ι x.1, ?_⟩
  exact ⟨ι x.1, hι.collapseToFinset_apply_mem x.2⟩

/-- The range of the finite-support retraction is closed. -/
theorem isClosed_range_collapseToFinset
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    IsClosed (((hι.collapseToFinset S : F →* F).range : Set F)) := by
  let hFprof : ProCGroups.IsProfiniteGroup F :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hι.isProC
  letI : T2Space F := hFprof.t2Space
  let r : F →ₜ* F := hι.collapseToFinset S
  let Fix : Subgroup F := (r : F →* F).eqLocus (MonoidHom.id F)
  have hFixClosed : IsClosed (Fix : Set F) := by
    change IsClosed {x : F | r x = x}
    exact isClosed_eq r.continuous continuous_id
  have hFixEq : Fix = (r : F →* F).range := by
    ext x
    constructor
    · intro hx
      exact ⟨x, by simpa using hx⟩
    · rintro ⟨y, rfl⟩
      change r (r y) = r y
      exact congrArg (fun ψ : F →ₜ* F => ψ y) (hι.collapseToFinset_idempotent S)
  simpa [r, Fix, hFixEq] using hFixClosed

/-- The finite-support retract is again a pro-`C` group. -/
theorem isProCGroup_finsetSupportRetract
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C)
      (G := hι.FinsetSupportRetract S) := by
  exact
    ProCGroups.ProC.IsProCGroup.of_isClosed_subgroup
      hIso.out hVar.out.subgroupClosed hVar.out.quotientClosed
      hι.isProC ((hι.collapseToFinset S : F →* F).range)
      (hι.isClosed_range_collapseToFinset S)

/-- The finite-support retract is free pro-`C` on its retained finite basis. -/
theorem isFreeProCGroupOnConvergingSet_finsetSupportBasis
    (hι :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (S : Finset X) :
    IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
      S (hι.FinsetSupportRetract S) (hι.finsetSupportBasis S) := by
  let R : Type u := hι.FinsetSupportRetract S
  let B : S → R := hι.finsetSupportBasis S
  let rRange : F →ₜ* R := hι.collapseToFinsetRange S
  let rIncl : R →ₜ* F := hι.collapseToFinsetInclusion S
  refine ⟨hι.isProCGroup_finsetSupportRetract S, ?_, ?_, ?_⟩
  · simpa [B] using FamilyConvergesToOne.of_finite_domain (G := R) B
  ·
    have hgen :
        Generation.TopologicallyGenerates (G := R) (Set.range B) := by
      let Img : Set R := rRange '' Set.range ι
      have hsurj : Function.Surjective rRange := by
        exact MonoidHom.rangeRestrict_surjective (hι.collapseToFinset S : F →* F)
      have hImgGen : Generation.TopologicallyGenerates (G := R) Img := by
        exact
          Generation.topologicallyGenerates_image_of_continuousSurjective
            (f := rRange.toMonoidHom) rRange.continuous hsurj hι.generates_range
      have hBsub : Set.range B ⊆ Img := by
        intro y hy
        rcases hy with ⟨x, rfl⟩
        refine ⟨ι x.1, ⟨x.1, rfl⟩, ?_⟩
        apply Subtype.ext
        change (hι.collapseToFinset S (ι x.1) : F) = ι x.1
        exact hι.collapseToFinset_apply_mem x.2
      have hImgSub : Img ⊆ ((Subgroup.closure (Set.range B) : Subgroup R) : Set R) := by
        intro y hy
        rcases hy with ⟨x, ⟨j, rfl⟩, rfl⟩
        by_cases hj : j ∈ S
        · exact
            Subgroup.subset_closure ⟨⟨j, hj⟩, by
              apply Subtype.ext
              change ι j = (hι.collapseToFinset S (ι j) : F)
              exact (hι.collapseToFinset_apply_mem hj).symm⟩
        · have hy1 : rRange (ι j) = 1 := by
            apply Subtype.ext
            change (hι.collapseToFinset S (ι j) : F) = 1
            exact hι.collapseToFinset_apply_not_mem hj
          rw [hy1]
          exact (Subgroup.closure (Set.range B)).one_mem
      have hclosureEq :
          Subgroup.closure Img = Subgroup.closure (Set.range B) := by
        apply le_antisymm
        · exact (Subgroup.closure_le (K := Subgroup.closure (Set.range B))).2 hImgSub
        · exact Subgroup.closure_mono hBsub
      change (Subgroup.closure (Set.range B)).topologicalClosure = ⊤
      change (Subgroup.closure Img).topologicalClosure = ⊤ at hImgGen
      rw [← hclosureEq]
      exact hImgGen
    simpa [B] using hgen
  · intro G _ _ _ hG φ hφ hgen
    let φext : X → G := fun x => if hx : x ∈ S then φ ⟨x, hx⟩ else 1
    have hφext : FamilyConvergesToOne (G := G) φext := by
      intro U
      refine S.finite_toSet.subset ?_
      intro x hx
      by_cases hxS : x ∈ S
      · exact hxS
      · exfalso
        exact hx (by simp only [hxS, ↓reduceDIte, SetLike.mem_coe, one_mem, φext])
    have hφextgen : Generation.TopologicallyGenerates (G := G) (Set.range φext) := by
      have hsub : Set.range φ ⊆ Set.range φext := by
        intro y hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨x.1, by simp only [x.2, ↓reduceDIte, Subtype.coe_eta, φext]⟩
      exact Generation.topologicallyGenerates_mono (G := G) hgen hsub
    let Φ : F →ₜ* G := hι.liftHom hG φext hφext hφextgen
    have hΦspec : ∀ x, Φ (ι x) = φext x := by
      intro x
      exact hι.liftHom_apply hG φext hφext hφextgen x
    let Φbar : R →ₜ* G :=
      { toMonoidHom := Φ.toMonoidHom.comp rIncl.toMonoidHom
        continuous_toFun := Φ.continuous.comp rIncl.continuous }
    have hΦbar : ∀ x : S, Φbar (B x) = φ x := by
      intro x
      change Φ (ι x.1) = φ x
      simpa [φext, B, Φbar, rIncl, collapseToFinsetInclusion, finsetSupportBasis] using
        hΦspec x.1
    refine ⟨Φbar.toMonoidHom, ⟨Φbar.continuous, hΦbar⟩, ?_⟩
    intro ψ hψ
    let ψc : R →ₜ* G :=
      { toMonoidHom := ψ
        continuous_toFun := hψ.1 }
    have hψcomp : ψc.comp rRange = Φ := by
      let hGprof : ProCGroups.IsProfiniteGroup G :=
        ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hG
      letI : T2Space G := hGprof.t2Space
      apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ S
      · have hψx : ψc (rRange (ι x)) = φ ⟨x, hx⟩ := by
          have hBasis : rRange (ι x) = B ⟨x, hx⟩ := by
            apply Subtype.ext
            change (hι.collapseToFinset S (ι x) : F) = ι x
            exact hι.collapseToFinset_apply_mem hx
          exact hBasis ▸ hψ.2 ⟨x, hx⟩
        have hΦx : Φ (ι x) = φ ⟨x, hx⟩ := by
          simpa [φext, hx] using hΦspec x
        exact hψx.trans hΦx.symm
      · have hrx : rRange (ι x) = 1 := by
          apply Subtype.ext
          change (hι.collapseToFinset S (ι x) : F) = 1
          exact hι.collapseToFinset_apply_not_mem hx
        have hΦx : Φ (ι x) = 1 := by
          simpa [φext, hx] using hΦspec x
        calc
          ψc (rRange (ι x)) = ψc 1 := by rw [hrx]
          _ = 1 := by simp only [map_one]
          _ = Φ (ι x) := hΦx.symm
    have hΦbarcomp : Φbar.comp rRange = Φ := by
      let hGprof : ProCGroups.IsProfiniteGroup G :=
        ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hG
      letI : T2Space G := hGprof.t2Space
      ext y
      change Φ (hι.collapseToFinset S y) = Φ y
      have hfix :
          Φ.comp (hι.collapseToFinset S) = Φ := by
        exact hι.comp_collapseToFinset_eq_of_eq_one_outside Φ S (by
          intro x hx
          simpa [φext, hx] using hΦspec x)
      exact congrArg (fun f : F →ₜ* G => f y) hfix
    have hsurj : Function.Surjective rRange := by
      exact MonoidHom.rangeRestrict_surjective (hι.collapseToFinset S : F →* F)
    ext z
    rcases hsurj z with ⟨y, rfl⟩
    have hEq : ψc.comp rRange = Φbar.comp rRange := hψcomp.trans hΦbarcomp.symm
    exact congrArg (fun f : F →ₜ* G => f y) hEq

  /-- If `S ⊆ T`, then collapsing first to `T` and then to `S` is the same as
  collapsing directly to `S`. This is the basic compatibility relation for the finite-basis
  projections. -/
  theorem collapseToFinset_small_comp_large_of_subset
      (hι :
        IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
      {S T : Finset X} (hST : S ⊆ T) :
      (hι.collapseToFinset S).comp (hι.collapseToFinset T) =
        hι.collapseToFinset S := by
    let hFprof : ProCGroups.IsProfiniteGroup F :=
      ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hι.isProC
    letI : T2Space F := hFprof.t2Space
    apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
    rintro _ ⟨x, rfl⟩
    by_cases hxS : x ∈ S
    · have hxT : x ∈ T := hST hxS
      simp only [ContinuousMonoidHom.comp_toFun, hxT, collapseToFinset_apply_mem, hxS]
    · by_cases hxT : x ∈ T
      · simp only [ContinuousMonoidHom.comp_toFun, hxT, collapseToFinset_apply_mem, hxS, not_false_eq_true,
  collapseToFinset_apply_not_mem]
      · simp only [ContinuousMonoidHom.comp_toFun, hxT, not_false_eq_true, collapseToFinset_apply_not_mem, map_one,
  hxS]

  /-- If `S ⊆ T`, then collapsing to `S` and then to `T` is again the collapse to `S`.
  Equivalently, the finite-support image for `S` is fixed by every larger finite-support
  projection. -/
  theorem collapseToFinset_large_comp_small_of_subset
      (hι :
        IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
      {S T : Finset X} (hST : S ⊆ T) :
      (hι.collapseToFinset T).comp (hι.collapseToFinset S) =
        hι.collapseToFinset S := by
    let hFprof : ProCGroups.IsProfiniteGroup F :=
      ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hι.isProC
    letI : T2Space F := hFprof.t2Space
    apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
    rintro _ ⟨x, rfl⟩
    by_cases hxS : x ∈ S
    · have hxT : x ∈ T := hST hxS
      simp only [ContinuousMonoidHom.comp_toFun, hxS, collapseToFinset_apply_mem, hxT]
    · simp only [ContinuousMonoidHom.comp_toFun, hxS, not_false_eq_true, collapseToFinset_apply_not_mem, map_one]

  /-- The transition map from the finite-support retract for `T` to the one for `S`, for
  `S ⊆ T`. It is the projection obtained by including the `T`-retract into the ambient free
  pro-`C` group and then collapsing to `S`. -/
  noncomputable def finsetSupportTransition
      (hι :
        IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
      {S T : Finset X} (_hST : S ⊆ T) :
      hι.FinsetSupportRetract T →ₜ* hι.FinsetSupportRetract S :=
    { toMonoidHom := (hι.collapseToFinsetRange S).toMonoidHom.comp
        (hι.collapseToFinsetInclusion T).toMonoidHom
      continuous_toFun :=
        (hι.collapseToFinsetRange S).continuous.comp
          (hι.collapseToFinsetInclusion T).continuous }

  @[simp] theorem finsetSupportTransition_apply_basis
      (hι :
        IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
      {S T : Finset X} (hST : S ⊆ T) (x : S) :
      hι.finsetSupportTransition hST
          (hι.finsetSupportBasis T ⟨x.1, hST x.2⟩) =
        hι.finsetSupportBasis S x := by
    apply Subtype.ext
    change hι.collapseToFinset S (ι x.1) = ι x.1
    exact hι.collapseToFinset_apply_mem x.2

  /-- Compatibility of the ambient projection `F → R_T` with the transition
  `R_T → R_S`. -/
  theorem finsetSupportTransition_comp_collapseToFinsetRange
      (hι :
        IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
      {S T : Finset X} (hST : S ⊆ T) :
      (hι.finsetSupportTransition hST).comp (hι.collapseToFinsetRange T) =
        hι.collapseToFinsetRange S := by
    ext x
    change hι.collapseToFinset S (hι.collapseToFinset T x) =
      hι.collapseToFinset S x
    exact congrArg (fun f : F →ₜ* F => f x)
      (hι.collapseToFinset_small_comp_large_of_subset hST)

  end FiniteSupportRetracts

/-- Continuous homomorphisms out of a free pro-`C` group on a converging generating set are
determined by their values on the chosen generators. -/
theorem hom_ext
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
    {f g : F →ₜ* G} (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  exact Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
    (by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hfg x)

/-- The lift of the canonical generator map to the same free pro-`C` group is the identity. -/
@[simp 900] theorem lift_id
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι) :
    hι.lift hι.isProC ι hι.convergesToOne hι.generates_range = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.isProC ι hι.convergesToOne hι.generates_range continuous_id
    (by intro x; rfl)

/-- Precomposing the converging generating set by an equivalence preserves the free pro-`C` universal property. -/
theorem precompEquiv
    {X' : Type w}
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι) (e : X' ≃ X) :
    IsFreeProCGroupOnConvergingSet (ProC := ProC) X' F (fun x : X' => ι (e x)) := by
  have hrange : Set.range (fun x : X' => ι (e x)) = Set.range ι := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simp only [Equiv.apply_symm_apply]⟩
  refine
    { isProC := hι.isProC
      convergesToOne := by
        intro U
        have hsubset :
            {x : X' | ι (e x) ∉ (U : Set F)} ⊆
              e.symm '' {x : X | ι x ∉ (U : Set F)} := by
          intro x hx
          exact ⟨e x, hx, by simp only [Equiv.symm_apply_apply]⟩
        exact (hι.convergesToOne U).image e.symm |>.subset hsubset
      generates_range := by simpa [hrange] using hι.generates_range
      existsUnique_lift := ?_ }
  intro G _ _ _ hG φ hφ hgen
  let φ' : X → G := fun x => φ (e.symm x)
  have hrangeφ : Set.range φ' = Set.range φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, by simp only [Equiv.symm_apply_apply, φ']⟩
  have hφ' : FamilyConvergesToOne (G := G) φ' := by
    intro U
    have hsubset :
        {x : X | φ (e.symm x) ∉ (U : Set G)} ⊆
          e '' {x : X' | φ x ∉ (U : Set G)} := by
      intro x hx
      exact ⟨e.symm x, hx, by simp only [Equiv.apply_symm_apply]⟩
    exact (hφ U).image e |>.subset hsubset
  have hgen' : Generation.TopologicallyGenerates (G := G) (Set.range φ') := by
    simpa [hrangeφ] using hgen
  rcases hι.existsUnique_lift hG φ' hφ' hgen' with ⟨f, hf, huniq⟩
  refine ⟨f, ?_, ?_⟩
  · refine ⟨hf.1, ?_⟩
    intro x
    simpa [φ'] using hf.2 (e x)
  · intro g hg
    apply huniq
    refine ⟨hg.1, ?_⟩
    intro x
    simpa [φ'] using hg.2 (e.symm x)

/-- An endomorphism of a free pro-`C` group fixing the generators is the identity. -/
theorem endomorphism_eq_id
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {f : F →* F} (hf : Continuous f) (hfac : ∀ x, f (ι x) = ι x) :
    f = MonoidHom.id F := by
  exact (hι.lift_unique hι.isProC ι hι.convergesToOne hι.generates_range hf hfac).trans
    hι.lift_id

/-- The canonical multiplicative homeomorphism between two free pro-`C` groups on the same
converging basis. -/
noncomputable def continuousMulEquivOfSameBasis
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
    {κ : X → F'}
    (hκ : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F' κ) :
    F ≃ₜ* F' :=
  let f : F →* F' := hι.lift hκ.isProC κ hκ.convergesToOne hκ.generates_range
  let g : F' →* F := hκ.lift hι.isProC ι hι.convergesToOne hι.generates_range
  let hf : Continuous f := (hι.lift_spec hκ.isProC κ hκ.convergesToOne hκ.generates_range).1
  let hg : Continuous g := (hκ.lift_spec hι.isProC ι hι.convergesToOne hι.generates_range).1
  { toMulEquiv :=
      { toFun := f
        invFun := g
        left_inv := by
          intro y
          have hgf : g.comp f = MonoidHom.id F := by
            apply hι.endomorphism_eq_id (hg.comp hf)
            intro x
            dsimp [f, g]
            rw [(hι.lift_spec hκ.isProC κ hκ.convergesToOne hκ.generates_range).2 x]
            exact (hκ.lift_spec hι.isProC ι hι.convergesToOne hι.generates_range).2 x
          exact congrArg (fun h : F →* F => h y) hgf
        right_inv := by
          intro y
          have hfg : f.comp g = MonoidHom.id F' := by
            apply hκ.endomorphism_eq_id (hf.comp hg)
            intro x
            dsimp [f, g]
            rw [(hκ.lift_spec hι.isProC ι hι.convergesToOne hι.generates_range).2 x]
            exact (hι.lift_spec hκ.isProC κ hκ.convergesToOne hκ.generates_range).2 x
          exact congrArg (fun h : F' →* F' => h y) hfg
        map_mul' := f.map_mul }
    continuous_toFun := hf
    continuous_invFun := hg }

/-- The canonical equivalence between free pro-`C` groups with the same basis fixes each generator. -/
@[simp 900] theorem continuousMulEquivOfSameBasis_apply
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
    {κ : X → F'}
    (hκ : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F' κ) (x : X) :
    hι.continuousMulEquivOfSameBasis hκ (ι x) = κ x := by
  simpa [continuousMulEquivOfSameBasis] using
    (hι.lift_spec hκ.isProC κ hκ.convergesToOne hκ.generates_range).2 x

/-- The inverse canonical equivalence between free pro-`C` groups with the same basis fixes each generator. -/
@[simp 900] theorem continuousMulEquivOfSameBasis_symm_apply
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
    {κ : X → F'}
    (hκ : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F' κ) (x : X) :
    (hι.continuousMulEquivOfSameBasis hκ).symm (κ x) = ι x := by
  simpa [continuousMulEquivOfSameBasis] using
    (hκ.lift_spec hι.isProC ι hι.convergesToOne hι.generates_range).2 x

/-- Transport the free pro-`C` structure on a converging set across a continuous multiplicative
equivalence of ambient groups. -/
theorem ofContinuousMulEquiv
    (hι : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (e : F ≃ₜ* F')
    (hF' : ProC (G := F')) :
    IsFreeProCGroupOnConvergingSet (ProC := ProC) X F' (fun x => e (ι x)) := by
  have hrange : Set.range (fun x : X => e (ι x)) = e '' Set.range ι := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ι x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  refine
    { isProC := hF'
      convergesToOne := ?_
      generates_range := ?_
      existsUnique_lift := ?_ }
  ·
    intro U
    let V : OpenSubgroup F := OpenSubgroup.comap e.toMonoidHom e.continuous U
    have hsubset :
        {x : X | e (ι x) ∉ (U : Set F')} ⊆ {x : X | ι x ∉ (V : Set F)} := by
      intro x hx hxV
      exact hx (by simpa [V] using hxV)
    exact (hι.convergesToOne V).subset hsubset
  · rw [hrange]
    exact ProCGroups.Generation.topologicallyGenerates_continuousMulEquiv_image
      (G := F) (H := F') e hι.generates_range
  · intro G _ _ _ hG φ hφ hgen
    rcases hι.existsUnique_lift hG φ hφ hgen with ⟨f, hf, huniq⟩
    let f' : F' →* G := f.comp e.symm.toMonoidHom
    refine ⟨f', ?_, ?_⟩
    · refine ⟨hf.1.comp e.symm.continuous, ?_⟩
      intro x
      change f (e.symm (e (ι x))) = φ x
      rw [e.symm_apply_apply]
      exact hf.2 x
    · intro g hg
      have hgcomp : g.comp e.toMonoidHom = f := by
        apply huniq
        refine ⟨hg.1.comp e.continuous, ?_⟩
        intro x
        simpa using hg.2 x
      ext y
      rcases e.surjective y with ⟨x, rfl⟩
      change g (e x) = f (e.symm (e x))
      rw [e.symm_apply_apply]
      exact congrArg (fun h : F →* G => h x) hgcomp

end IsFreeProCGroupOnConvergingSet

/-- Packaged carrier for a free pro-`C` group on a set converging to `1`. -/
structure FreeProCGroupOnConvergingSetData
    (ProC : ProCGroups.ProC.ProCGroupPredicate) where
  basis : Type u
  carrier : Type u
  instGroup : Group carrier
  instTopologicalSpace : TopologicalSpace carrier
  instIsTopologicalGroup : IsTopologicalGroup carrier
  inclusion : basis → carrier
  isFree : IsFreeProCGroupOnConvergingSet (ProC := ProC) basis carrier inclusion

attribute [instance] FreeProCGroupOnConvergingSetData.instGroup
attribute [instance] FreeProCGroupOnConvergingSetData.instTopologicalSpace
attribute [instance] FreeProCGroupOnConvergingSetData.instIsTopologicalGroup

/-- The cardinality of a finite converging-set basis is the topological rank of the free
pro-`C` group, provided the finite class has a nontrivial cyclic quotient witness. -/
theorem basisCard_eq_topologicalRank_of_finiteBasis
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    (Fdata : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C))
    [Finite Fdata.basis] :
    Cardinal.mk Fdata.basis = Generation.topologicalRank Fdata.carrier := by
  classical
  let hFprof : ProCGroups.IsProfiniteGroup Fdata.carrier :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C Fdata.isFree.isProC
  letI : Fintype Fdata.basis := Fintype.ofFinite Fdata.basis
  rcases exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass C hquot hcyc with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, hA, a, ha1, hgena⟩
  have hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A),
        (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := A) ∧
          ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) :=
    ⟨A, inferInstance, inferInstance, inferInstance, hA, a, ha1, hgena⟩
  have hιinj : Function.Injective Fdata.inclusion :=
    freeProCGroupOnConvergingSet_injective Fdata.isFree hnontrivial
  have hfg : _root_.ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated Fdata.carrier := by
    refine ⟨Finset.univ.image Fdata.inclusion, ?_⟩
    simpa [Finset.coe_image] using Fdata.isFree.generates_range
  have hdle :
      Generation.topologicalRank Fdata.carrier ≤ (Fintype.card Fdata.basis : Cardinal) := by
    calc
      Generation.topologicalRank Fdata.carrier ≤ Cardinal.mk (Set.range Fdata.inclusion) := by
        change sInf {κ : Cardinal |
          ∃ X : Set Fdata.carrier,
            Generation.GeneratesAndConvergesToOne (G := Fdata.carrier) X ∧
              Cardinal.mk X = κ} ≤ Cardinal.mk (Set.range Fdata.inclusion)
        exact csInf_le' ⟨Set.range Fdata.inclusion,
            ⟨Fdata.isFree.generates_range, Fdata.isFree.convergesToOne.range⟩,
          rfl⟩
      _ = Cardinal.mk Fdata.basis := by
        simpa using (Cardinal.mk_range_eq Fdata.inclusion hιinj)
      _ = (Fintype.card Fdata.basis : Cardinal) := by simp only [Cardinal.mk_fintype]
  have hdlt : Generation.topologicalRank Fdata.carrier < Cardinal.aleph0 := by
    exact lt_of_le_of_lt hdle (Cardinal.natCast_lt_aleph0 (n := Fintype.card Fdata.basis))
  let d : ℕ := Cardinal.toNat (Generation.topologicalRank Fdata.carrier)
  have hdEq : Generation.topologicalRank Fdata.carrier = d := by
    symm
    exact Cardinal.cast_toNat_of_lt_aleph0 hdlt
  have hdleNat : d ≤ Fintype.card Fdata.basis := by
    simpa [d, Nat.card_eq_fintype_card] using
      Cardinal.toNat_le_toNat hdle
        (Cardinal.natCast_lt_aleph0 (n := Fintype.card Fdata.basis))
  by_cases hd0 : d = 0
  · have hdEq0 : Generation.topologicalRank Fdata.carrier = 0 := by simpa [d, hd0] using hdEq
    letI : CompactSpace Fdata.carrier := ProCGroups.IsProfiniteGroup.compactSpace hFprof
    letI : T2Space Fdata.carrier := ProCGroups.IsProfiniteGroup.t2Space hFprof
    letI : TotallyDisconnectedSpace Fdata.carrier :=
      ProCGroups.IsProfiniteGroup.totallyDisconnectedSpace hFprof
    have hgen0 :
        _root_.ProCGroups.FiniteGeneration.TopologicallyGeneratedByAtMost
          (G := Fdata.carrier) 0 :=
      _root_.ProCGroups.FiniteGeneration.topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat
        (G := Fdata.carrier) hFprof hdEq0
    rcases hgen0 with ⟨s, hs, hsgen⟩
    have hs0 : s.card = 0 := Nat.eq_zero_of_le_zero hs
    have hsempty : s = ∅ := Finset.card_eq_zero.mp hs0
    have htriv : ∀ x : Fdata.carrier, x = 1 := by
      intro x
      have hxmem :
            x ∈
              ((Subgroup.closure
                  (((s : Finset Fdata.carrier) : Set Fdata.carrier))).topologicalClosure :
                Set Fdata.carrier) := by
        rw [Generation.TopologicallyGenerates] at hsgen
        rw [hsgen]
        simp only [Subgroup.coe_top, mem_univ]
      simpa [hsempty, Subgroup.coe_topologicalClosure_bot, closure_singleton] using hxmem
    have hEmpty : IsEmpty Fdata.basis := by
      refine ⟨fun b => ?_⟩
      have hb1 : Fdata.inclusion b = 1 := htriv (Fdata.inclusion b)
      exact
        (one_not_mem_range_of_freeProCGroupOnConvergingSet
          (hι := Fdata.isFree) hnontrivial) ⟨b, hb1⟩
    letI : IsEmpty Fdata.basis := hEmpty
    have hcard0 : Cardinal.mk Fdata.basis = 0 := by simp only [Cardinal.mk_eq_zero]
    rw [hdEq0]
    exact hcard0
  · have hdPos : 0 < d := Nat.pos_of_ne_zero hd0
    rcases _root_.ProCGroups.FiniteGeneration.exists_generatingTuple_of_topologicalRank_le_of_finite
        (G := Fdata.carrier) hfg
        (show Generation.topologicalRank Fdata.carrier ≤ d by simp only [hdEq, le_refl]) with
      ⟨φ, hφgen⟩
    let i0 : Fin d := ⟨0, hdPos⟩
    have hdleNat' : Fintype.card (Fin d) ≤ Fintype.card Fdata.basis := by
      simpa using hdleNat
    have hEmb : Nonempty (Fin d ↪ Fdata.basis) := by
      exact Function.Embedding.nonempty_of_card_le (α := Fin d) (β := Fdata.basis) hdleNat'
    have hConst : Nonempty (Fdata.basis → Fin d) := ⟨fun _ => i0⟩
    rcases (Function.exists_surjective_iff).2 ⟨hConst, hEmb⟩ with ⟨q, hqsurj⟩
    let ψ : Fdata.basis → Fdata.carrier := fun b => φ (q b)
    have hψconv : FamilyConvergesToOne (G := Fdata.carrier) ψ := by
      exact FamilyConvergesToOne.of_finite_domain (G := Fdata.carrier) ψ
    have hψrange : Set.range ψ = Set.range φ := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨q b, rfl⟩
      · rintro ⟨i, rfl⟩
        rcases hqsurj i with ⟨b, rfl⟩
        exact ⟨b, rfl⟩
    have hψgen : Generation.TopologicallyGenerates (G := Fdata.carrier) (Set.range ψ) := by
      simpa [hψrange] using hφgen
    rcases Fdata.isFree.existsUnique_lift Fdata.isFree.isProC ψ hψconv hψgen with
      ⟨σ, hσ, _⟩
    letI : CompactSpace Fdata.carrier := ProCGroups.IsProfiniteGroup.compactSpace hFprof
    letI : T2Space Fdata.carrier := ProCGroups.IsProfiniteGroup.t2Space hFprof
    have hσsub : Set.range φ ⊆ (σ.range : Set Fdata.carrier) := by
      rintro z ⟨i, rfl⟩
      rcases hqsurj i with ⟨b, hb⟩
      refine ⟨Fdata.inclusion b, ?_⟩
      simpa [ψ, hb] using hσ.2 b
    have hσsurj : Function.Surjective σ := by
      have hσgen :
          Generation.TopologicallyGenerates (G := Fdata.carrier)
            ((σ.range : Set Fdata.carrier)) :=
        Generation.topologicallyGenerates_mono (G := Fdata.carrier) hφgen hσsub
      have hσclosed : IsClosed ((σ.range : Set Fdata.carrier)) := by
        simpa using (isCompact_range hσ.1).isClosed
      have hσclosure_le : (σ.range : Subgroup Fdata.carrier).topologicalClosure ≤ σ.range :=
        Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
      have hσclosure_top : (σ.range : Subgroup Fdata.carrier).topologicalClosure = ⊤ := by
        have htop :
            (Subgroup.closure (σ.range : Set Fdata.carrier)).topologicalClosure =
              (⊤ : Subgroup Fdata.carrier) := by
          simpa [Generation.TopologicallyGenerates] using hσgen
        have hclosure_eq :
            (σ.range : Subgroup Fdata.carrier) =
              Subgroup.closure (σ.range : Set Fdata.carrier) := by
          simpa using (Subgroup.closure_eq (σ.range)).symm
        rw [hclosure_eq]
        exact htop
      have hσrange_top : σ.range = ⊤ := by
        apply top_unique
        intro z hz
        have hz' :
            z ∈
              ((σ.range : Subgroup Fdata.carrier).topologicalClosure :
                Set Fdata.carrier) := by
          rw [hσclosure_top]
          simp only [Subgroup.coe_top, mem_univ]
        exact hσclosure_le hz'
      intro z
      have hz : z ∈ (σ.range : Set Fdata.carrier) := by
        simp only [hσrange_top, Subgroup.coe_top, mem_univ]
      simpa using hz
    let σc : ContinuousMonoidHom Fdata.carrier Fdata.carrier :=
      { toMonoidHom := σ
        continuous_toFun := hσ.1 }
    letI : TotallyDisconnectedSpace Fdata.carrier :=
      ProCGroups.IsProfiniteGroup.totallyDisconnectedSpace hFprof
    rcases
        (_root_.ProCGroups.FiniteGeneration.surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
          (G := Fdata.carrier) hfg σc hσsurj) with
      ⟨eσ, heσ⟩
    have hσinj : Function.Injective σ := by
      intro a b hab
      have h' : eσ a = eσ b := by
        calc
          eσ a = σ a := by simpa [σc] using heσ a
          _ = σ b := hab
          _ = eσ b := by simpa [σc] using (heσ b).symm
      exact eσ.injective h'
    have hqinj : Function.Injective q := by
      intro b₁ b₂ hb
      apply hιinj
      apply hσinj
      calc
        σ (Fdata.inclusion b₁) = ψ b₁ := hσ.2 b₁
        _ = φ (q b₁) := rfl
        _ = φ (q b₂) := by simp only [hb]
        _ = ψ b₂ := rfl
        _ = σ (Fdata.inclusion b₂) := (hσ.2 b₂).symm
    have hcardEq : Fintype.card Fdata.basis = d := by
      have hcardLe : Fintype.card Fdata.basis ≤ d := by
        simpa using Fintype.card_le_of_injective q hqinj
      exact le_antisymm hcardLe hdleNat
    calc
      Cardinal.mk Fdata.basis = (Fintype.card Fdata.basis : Cardinal) := by simp only [Cardinal.mk_fintype]
      _ = d := by exact_mod_cast hcardEq
      _ = Generation.topologicalRank Fdata.carrier := hdEq.symm

/-- A pointed free pro-`C` object can be replaced by a free pro-`C` model on a set converging to
`1`.

This is the explicit bridge between pointed hypotheses and a Reidemeister-Schreier basis output
phrased as a converging-set basis model. -/
def PointedToConvergingSetBasisBridge
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u}) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F},
      IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι →
        ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
          Nonempty (Fdata.carrier ≃ₜ* F)

/-- Apply a `PointedToConvergingSetBasisBridge` to a pointed free pro-`C` object. -/
theorem freeOnPointedSpace_has_convergingSetBasis_of_bridge
    (hBridge : PointedToConvergingSetBasisBridge ProC)
    {X : Type u} [TopologicalSpace X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
      Nonempty (Fdata.carrier ≃ₜ* F) :=
  hBridge hι

/-- Finite discrete pointed case of the pointed-to-converging-set bridge: remove the basepoint
from the pointed generating family. -/
theorem freeOnFinitePointedDiscreteSpace_has_convergingSetBasis
    {X : Type u} [TopologicalSpace X] [DiscreteTopology X] [Finite X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι) :
    IsFreeProCGroupOnConvergingSet
      (ProC := ProC) {x : X // x ≠ x0} F (fun x => ι x) := by
  classical
  let μ : {x : X // x ≠ x0} → F := fun x => ι x
  refine ⟨hι.isProC, ?_, ?_, ?_⟩
  · exact FamilyConvergesToOne.of_finite_domain (G := F) μ
  · have hrange : Set.range ι = Set.range μ ∪ ({1} : Set F) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x = x0
        · right
          simpa [hx] using hι.map_base
        · left
          exact ⟨⟨x, hx⟩, rfl⟩
      · intro hz
        rcases hz with hz | hz
        · rcases hz with ⟨x, rfl⟩
          exact ⟨x, rfl⟩
        · exact ⟨x0, hι.map_base.trans (by simpa using hz.symm)⟩
    have hgen' :
        Generation.TopologicallyGenerates (G := F) (Set.range μ ∪ ({1} : Set F)) := by
      simpa [μ, hrange] using hι.generates_range
    exact (Generation.topologicallyGenerates_union_one_iff (G := F) (X := Set.range μ)).1 hgen'
  · intro G _ _ _ hG φ _hφconv hgenφ
    let φhat : X → G := fun x => if h : x = x0 then 1 else φ ⟨x, h⟩
    have hφhat : Continuous φhat := continuous_of_discreteTopology
    have hφhat0 : φhat x0 = 1 := by
      simp only [ne_eq, ↓reduceDIte, φhat]
    have hrange : Set.range φhat = Set.range φ ∪ ({1} : Set G) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x = x0
        · right
          simp only [ne_eq, hx, ↓reduceDIte, mem_singleton_iff, φhat]
        · left
          exact ⟨⟨x, hx⟩, by simp only [ne_eq, hx, ↓reduceDIte, φhat]⟩
      · intro hz
        rcases hz with hz | hz
        · rcases hz with ⟨x, rfl⟩
          exact ⟨x, by simp only [ne_eq, x.2, ↓reduceDIte, Subtype.coe_eta, φhat]⟩
        · exact ⟨x0, by simpa [φhat] using hz.symm⟩
    have hφhatgen :
        Generation.TopologicallyGenerates (G := G) (Set.range φhat) := by
      have hgen' :
          Generation.TopologicallyGenerates (G := G) (Set.range φ ∪ ({1} : Set G)) := by
        exact (Generation.topologicallyGenerates_union_one_iff (G := G) (X := Set.range φ)).2 hgenφ
      simpa [φhat, hrange] using hgen'
    rcases hι.existsUnique_lift hG φhat hφhat hφhat0 hφhatgen with ⟨f, hf, huniq⟩
    refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
    · intro x
      simpa [μ, φhat, x.2] using hf.2 (x : X)
    · intro g hg
      apply huniq g
      refine ⟨hg.1, ?_⟩
      intro x
      by_cases hx : x = x0
      · calc
          g (ι x) = g (ι x0) := by rw [hx]
          _ = g 1 := by rw [hι.map_base]
          _ = 1 := map_one g
          _ = φhat x := by simp only [ne_eq, hx, ↓reduceDIte, φhat]
      · simpa [μ, φhat, hx] using hg.2 ⟨x, hx⟩

/-- Finite discrete pointed case, bundled as a finite converging-set basis model. -/
theorem freeOnFinitePointedDiscreteSpace_has_finiteConvergingSetBasis
    {X : Type u} [TopologicalSpace X] [DiscreteTopology X] [Finite X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
      Nonempty (Fdata.carrier ≃ₜ* F) ∧ Finite Fdata.basis := by
  let B : Type u := {x : X // x ≠ x0}
  let Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC) :=
    { basis := B
      carrier := F
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := fun x => ι x
      isFree :=
        freeOnFinitePointedDiscreteSpace_has_convergingSetBasis
          (ProC := ProC) (X := X) (x0 := x0) (F := F) (ι := ι) hι }
  refine ⟨Fdata, ⟨ContinuousMulEquiv.refl F⟩, ?_⟩
  dsimp [Fdata, B]
  infer_instance

end

end ProCGroups.FreeProC
