import Mathlib.GroupTheory.Coprod.Basic
import ProCGroups.Categorical.PushoutSquares
import ProCGroups.Completion.UniversalProperty
import ProCGroups.ProC.GroupPredicates.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProducts/UniversalProperty.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C products

Constructs free pro-C products from finite admissible quotients and proves the universal property and comparison isomorphisms.
-/

open scoped Monoid.Coprod

namespace ProCGroups.FreeProducts

universe u v

section AbstractFreeProducts

variable {G₁ : Type u} {G₂ : Type u} {F : Type u}
variable [Group G₁] [Group G₂] [Group F]

/-- Binary free products, expressed through the usual universal property. -/
structure IsFreeProduct (ι₁ : G₁ →* F) (ι₂ : G₂ →* F) : Prop where
  existsUnique_lift :
    ∀ {K : Type u} [Group K] (φ₁ : G₁ →* K) (φ₂ : G₂ →* K),
      ∃! φ : F →* K, φ.comp ι₁ = φ₁ ∧ φ.comp ι₂ = φ₂

namespace IsFreeProduct

variable {ι₁ : G₁ →* F} {ι₂ : G₂ →* F}

/-- Chosen descent morphism from a binary free product object. -/
noncomputable def lift (hF : IsFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] (φ₁ : G₁ →* K) (φ₂ : G₂ →* K) : F →* K :=
  Classical.choose (ExistsUnique.exists (hF.existsUnique_lift φ₁ φ₂))

/-- The chosen free-product descent morphism has the prescribed composites. -/
theorem lift_spec (hF : IsFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] (φ₁ : G₁ →* K) (φ₂ : G₂ →* K) :
    (hF.lift φ₁ φ₂).comp ι₁ = φ₁ ∧ (hF.lift φ₁ φ₂).comp ι₂ = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hF.existsUnique_lift φ₁ φ₂))

/-- Left composite of the chosen free-product descent morphism. -/
@[simp] theorem lift_left (hF : IsFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] (φ₁ : G₁ →* K) (φ₂ : G₂ →* K) :
    (hF.lift φ₁ φ₂).comp ι₁ = φ₁ :=
  (hF.lift_spec φ₁ φ₂).1

/-- Right composite of the chosen free-product descent morphism. -/
@[simp] theorem lift_right (hF : IsFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] (φ₁ : G₁ →* K) (φ₂ : G₂ →* K) :
    (hF.lift φ₁ φ₂).comp ι₂ = φ₂ :=
  (hF.lift_spec φ₁ φ₂).2

/-- Uniqueness of the chosen free-product descent morphism. -/
theorem lift_unique (hF : IsFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] (φ₁ : G₁ →* K) (φ₂ : G₂ →* K)
    {ψ : F →* K} (hψ : ψ.comp ι₁ = φ₁ ∧ ψ.comp ι₂ = φ₂) :
    ψ = hF.lift φ₁ φ₂ := by
  rcases hF.existsUnique_lift φ₁ φ₂ with ⟨u, hu, huuniq⟩
  have hchosen : hF.lift φ₁ φ₂ = u := huuniq _ (hF.lift_spec φ₁ φ₂)
  exact (huuniq _ hψ).trans hchosen.symm

/-- The distinguished descent map from a free product object to itself is the identity. -/
@[simp] theorem lift_self (hF : IsFreeProduct ι₁ ι₂) :
    hF.lift ι₁ ι₂ = MonoidHom.id F := by
  symm
  exact hF.lift_unique ι₁ ι₂ ⟨rfl, rfl⟩

/-- Extensionality of homomorphisms out of a free product object. -/
theorem hom_ext (hF : IsFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] {ψ ψ' : F →* K}
    (h₁ : ψ.comp ι₁ = ψ'.comp ι₁) (h₂ : ψ.comp ι₂ = ψ'.comp ι₂) :
    ψ = ψ' := by
  have hψ : ψ = hF.lift (K := K) (ψ.comp ι₁) (ψ.comp ι₂) := by
    exact hF.lift_unique (K := K) (ψ.comp ι₁) (ψ.comp ι₂) ⟨rfl, rfl⟩
  have hψ' : ψ' = hF.lift (K := K) (ψ.comp ι₁) (ψ.comp ι₂) := by
    exact hF.lift_unique (K := K) (ψ.comp ι₁) (ψ.comp ι₂) ⟨h₁.symm, h₂.symm⟩
  exact hψ.trans hψ'.symm

variable {F' : Type u} [Group F']
variable {ι₁' : G₁ →* F'} {ι₂' : G₂ →* F'}

/-- Canonical comparison morphism between two free product objects on the same pair of factors. -/
noncomputable def compare (hF : IsFreeProduct ι₁ ι₂) : F →* F' :=
  hF.lift ι₁' ι₂'

/-- Left composite of the canonical comparison map between free product objects. -/
@[simp 900] theorem compare_left (hF : IsFreeProduct ι₁ ι₂) :
    (hF.compare (ι₁' := ι₁') (ι₂' := ι₂')).comp ι₁ = ι₁' :=
  hF.lift_left ι₁' ι₂'

/-- Right composite of the canonical comparison map between free product objects. -/
@[simp 900] theorem compare_right (hF : IsFreeProduct ι₁ ι₂) :
    (hF.compare (ι₁' := ι₁') (ι₂' := ι₂')).comp ι₂ = ι₂' :=
  hF.lift_right ι₁' ι₂'

/-- The canonical comparison map from a free product object to itself is the identity. -/
@[simp 900] theorem compare_self (hF : IsFreeProduct ι₁ ι₂) :
    hF.compare (ι₁' := ι₁) (ι₂' := ι₂) = MonoidHom.id F := by
  exact hF.lift_self

variable {F'' : Type u} [Group F'']
variable {ι₁'' : G₁ →* F''} {ι₂'' : G₂ →* F''}

/-- Composition of free-product comparison maps is the expected direct comparison map. -/
theorem compare_comp (hF : IsFreeProduct ι₁ ι₂)
    (hF' : IsFreeProduct ι₁' ι₂') :
    (hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp
        (hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F') =
      (hF.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F →* F'') := by
  apply hF.hom_ext
  · calc
      ((hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp
          (hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F')).comp ι₁
          = (hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp
              ((hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F').comp ι₁) := by rfl
      _ = (hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp ι₁' := by
        rw [hF.compare_left (ι₁' := ι₁') (ι₂' := ι₂')]
      _ = ι₁'' := hF'.compare_left (ι₁' := ι₁'') (ι₂' := ι₂'')
      _ = (hF.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F →* F'').comp ι₁ :=
        (hF.compare_left (ι₁' := ι₁'') (ι₂' := ι₂'')).symm
  · calc
      ((hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp
          (hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F')).comp ι₂
          = (hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp
              ((hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F').comp ι₂) := by rfl
      _ = (hF'.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F' →* F'').comp ι₂' := by
        rw [hF.compare_right (ι₁' := ι₁') (ι₂' := ι₂')]
      _ = ι₂'' := hF'.compare_right (ι₁' := ι₁'') (ι₂' := ι₂'')
      _ = (hF.compare (ι₁' := ι₁'') (ι₂' := ι₂'') : F →* F'').comp ι₂ :=
        (hF.compare_right (ι₁' := ι₁'') (ι₂' := ι₂'')).symm

/-- Any two binary free product objects on the same factors are canonically isomorphic. -/
noncomputable def equiv (hF : IsFreeProduct ι₁ ι₂) (hF' : IsFreeProduct ι₁' ι₂') :
    F ≃* F' :=
  MonoidHom.toMulEquiv
    (hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F')
    (hF'.compare (ι₁' := ι₁) (ι₂' := ι₂) : F' →* F)
    (by
      calc
        (hF'.compare (ι₁' := ι₁) (ι₂' := ι₂) : F' →* F).comp
            (hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F') =
            (hF.compare (ι₁' := ι₁) (ι₂' := ι₂) : F →* F) := by
          simpa using hF.compare_comp (ι₁'' := ι₁) (ι₂'' := ι₂) hF'
        _ = MonoidHom.id F := hF.compare_self)
    (by
      calc
        (hF.compare (ι₁' := ι₁') (ι₂' := ι₂') : F →* F').comp
            (hF'.compare (ι₁' := ι₁) (ι₂' := ι₂) : F' →* F) =
            (hF'.compare (ι₁' := ι₁') (ι₂' := ι₂') : F' →* F') := by
          simpa using hF'.compare_comp (ι₁'' := ι₁') (ι₂'' := ι₂') hF
        _ = MonoidHom.id F' := hF'.compare_self)

/-- Left composite of the canonical equivalence between free product objects. -/
@[simp] theorem equiv_left (hF : IsFreeProduct ι₁ ι₂) (hF' : IsFreeProduct ι₁' ι₂') :
    (hF.equiv hF').toMonoidHom.comp ι₁ = ι₁' := by
  exact hF.compare_left (ι₁' := ι₁') (ι₂' := ι₂')

/-- Right composite of the canonical equivalence between free product objects. -/
@[simp] theorem equiv_right (hF : IsFreeProduct ι₁ ι₂) (hF' : IsFreeProduct ι₁' ι₂') :
    (hF.equiv hF').toMonoidHom.comp ι₂ = ι₂' := by
  exact hF.compare_right (ι₁' := ι₁') (ι₂' := ι₂')

/-- Left-leg formula for the inverse canonical free-product equivalence. -/
theorem equiv_symm_left (hF : IsFreeProduct ι₁ ι₂) (hF' : IsFreeProduct ι₁' ι₂') :
    (hF.equiv hF').symm.toMonoidHom.comp ι₁' = ι₁ := by
  change (hF'.compare (ι₁' := ι₁) (ι₂' := ι₂) : F' →* F).comp ι₁' = ι₁
  exact hF'.compare_left (ι₁' := ι₁) (ι₂' := ι₂)

/-- Right-leg formula for the inverse canonical free-product equivalence. -/
theorem equiv_symm_right (hF : IsFreeProduct ι₁ ι₂) (hF' : IsFreeProduct ι₁' ι₂') :
    (hF.equiv hF').symm.toMonoidHom.comp ι₂' = ι₂ := by
  change (hF'.compare (ι₁' := ι₁) (ι₂' := ι₂) : F' →* F).comp ι₂' = ι₂
  exact hF'.compare_right (ι₁' := ι₁) (ι₂' := ι₂)

/-- A binary free product is a pushout over the trivial group. -/
theorem isPushoutSquare (hF : IsFreeProduct ι₁ ι₂) :
    ProCGroups.Categorical.IsPushoutSquare
      (1 : ULift.{u, 0} Unit →* G₁) (1 : ULift.{u, 0} Unit →* G₂) ι₁ ι₂ := by
  constructor
  · ext u
    cases u
    simp only [MonoidHom.comp_one, MonoidHom.one_apply]
  · intro K _ φ₁ φ₂ _hφ
    refine ⟨hF.lift φ₁ φ₂, hF.lift_spec φ₁ φ₂, ?_⟩
    intro ψ hψ
    exact hF.lift_unique φ₁ φ₂ hψ

/-- A pushout over the trivial group satisfies the binary free-product universal property. -/
theorem of_isPushoutSquare
    (hpo : ProCGroups.Categorical.IsPushoutSquare
      (1 : ULift.{u, 0} Unit →* G₁) (1 : ULift.{u, 0} Unit →* G₂) ι₁ ι₂) :
    IsFreeProduct ι₁ ι₂ := by
  refine ⟨?_⟩
  intro K _ φ₁ φ₂
  have hφ : φ₁.comp (1 : ULift.{u, 0} Unit →* G₁) =
      φ₂.comp (1 : ULift.{u, 0} Unit →* G₂) := by
    ext u
    cases u
    simp only [MonoidHom.comp_one, MonoidHom.one_apply]
  simpa using hpo.2 φ₁ φ₂ hφ

end IsFreeProduct

/-- Free-product universal property for mathlib's concrete coproduct model. -/
theorem coprod_isFreeProduct (G₁ : Type u) (G₂ : Type u) [Group G₁] [Group G₂] :
    IsFreeProduct
      (Monoid.Coprod.inl : G₁ →* G₁ ∗ G₂)
      (Monoid.Coprod.inr : G₂ →* G₁ ∗ G₂) := by
  refine ⟨?_⟩
  intro K _ φ₁ φ₂
  refine ⟨Monoid.Coprod.lift φ₁ φ₂, ?_, ?_⟩
  · exact ⟨Monoid.Coprod.lift_comp_inl φ₁ φ₂, Monoid.Coprod.lift_comp_inr φ₁ φ₂⟩
  · intro ψ hψ
    exact Monoid.Coprod.lift_unique hψ.1 hψ.2

/-- The concrete coproduct model is a pushout over the trivial group. -/
theorem coprod_isPushoutSquare (G₁ : Type u) (G₂ : Type u) [Group G₁] [Group G₂] :
    ProCGroups.Categorical.IsPushoutSquare
      (1 : ULift.{u, 0} Unit →* G₁) (1 : ULift.{u, 0} Unit →* G₂)
      (Monoid.Coprod.inl : G₁ →* G₁ ∗ G₂)
      (Monoid.Coprod.inr : G₂ →* G₁ ∗ G₂) :=
  (coprod_isFreeProduct G₁ G₂).isPushoutSquare

/-- Binary free products are exactly pushouts over the trivial group. -/
theorem isFreeProduct_iff_isPushoutSquare {ι₁ : G₁ →* F} {ι₂ : G₂ →* F} :
    IsFreeProduct ι₁ ι₂ ↔
      ProCGroups.Categorical.IsPushoutSquare
        (1 : ULift.{u, 0} Unit →* G₁) (1 : ULift.{u, 0} Unit →* G₂) ι₁ ι₂ :=
  ⟨IsFreeProduct.isPushoutSquare, IsFreeProduct.of_isPushoutSquare⟩

/-- Indexed free products, expressed through the usual universal property. -/
structure IsFreeProductFamily {A : Type u} (G : A → Type u) [∀ a, Group (G a)]
    {F : Type u} [Group F] (ι : ∀ a, G a →* F) : Prop where
  existsUnique_lift :
    ∀ {K : Type u} [Group K] (φ : ∀ a, G a →* K),
      ∃! ψ : F →* K, ∀ a, ψ.comp (ι a) = φ a

namespace IsFreeProductFamily

variable {A : Type u} {G : A → Type u} [∀ a, Group (G a)]
variable {F : Type u} [Group F]
variable {ι : ∀ a, G a →* F}

/-- Chosen descent morphism from a family free-product object. -/
noncomputable def lift (hF : IsFreeProductFamily G ι)
    {K : Type u} [Group K] (φ : ∀ a, G a →* K) : F →* K :=
  Classical.choose (ExistsUnique.exists (hF.existsUnique_lift φ))

/-- Component formula for the chosen family free-product descent morphism. -/
@[simp] theorem lift_ι (hF : IsFreeProductFamily G ι)
    {K : Type u} [Group K] (φ : ∀ a, G a →* K) (a : A) :
    (hF.lift φ).comp (ι a) = φ a :=
  Classical.choose_spec (ExistsUnique.exists (hF.existsUnique_lift φ)) a

/-- Uniqueness of the chosen family free-product descent morphism. -/
theorem lift_unique (hF : IsFreeProductFamily G ι)
    {K : Type u} [Group K] (φ : ∀ a, G a →* K)
    {ψ : F →* K} (hψ : ∀ a, ψ.comp (ι a) = φ a) :
    ψ = hF.lift φ := by
  rcases hF.existsUnique_lift φ with ⟨u, hu, huuniq⟩
  have hchosen : hF.lift φ = u := huuniq _ (fun a => hF.lift_ι φ a)
  exact (huuniq _ hψ).trans hchosen.symm

/-- The distinguished descent map from a family free-product object to itself is the identity. -/
@[simp] theorem lift_self (hF : IsFreeProductFamily G ι) :
    hF.lift ι = MonoidHom.id F := by
  symm
  exact hF.lift_unique ι (fun _ => rfl)

/-- Extensionality of homomorphisms out of a family free-product object. -/
theorem hom_ext (hF : IsFreeProductFamily G ι)
    {K : Type u} [Group K] {ψ ψ' : F →* K}
    (h : ∀ a, ψ.comp (ι a) = ψ'.comp (ι a)) :
    ψ = ψ' := by
  have hψ : ψ = hF.lift (fun a => ψ.comp (ι a)) := by
    exact hF.lift_unique (fun a => ψ.comp (ι a)) (fun _ => rfl)
  have hψ' : ψ' = hF.lift (fun a => ψ.comp (ι a)) := by
    exact hF.lift_unique (fun a => ψ.comp (ι a)) (fun a => (h a).symm)
  exact hψ.trans hψ'.symm

variable {F' : Type u} [Group F']
variable {ι' : ∀ a, G a →* F'}

/-- Canonical comparison morphism between two family free-product objects on the same factors. -/
noncomputable def compare (hF : IsFreeProductFamily G ι) : F →* F' :=
  hF.lift ι'

/-- Component formula for the canonical comparison map between family free-product objects. -/
@[simp 900] theorem compare_ι (hF : IsFreeProductFamily G ι) (a : A) :
    (hF.compare (ι' := ι')).comp (ι a) = ι' a :=
  hF.lift_ι ι' a

/-- The canonical comparison map from a family free-product object to itself is the identity. -/
@[simp 900] theorem compare_self (hF : IsFreeProductFamily G ι) :
    hF.compare (ι' := ι) = MonoidHom.id F := by
  exact hF.lift_self

variable {F'' : Type u} [Group F'']
variable {ι'' : ∀ a, G a →* F''}

/-- Composition of family free-product comparison maps is the expected direct comparison map. -/
theorem compare_comp (hF : IsFreeProductFamily G ι)
    (hF' : IsFreeProductFamily G ι') :
    (hF'.compare (ι' := ι'') : F' →* F'').comp
        (hF.compare (ι' := ι') : F →* F') =
      (hF.compare (ι' := ι'') : F →* F'') := by
  apply hF.hom_ext
  intro a
  calc
    ((hF'.compare (ι' := ι'') : F' →* F'').comp
        (hF.compare (ι' := ι') : F →* F')).comp (ι a)
        = (hF'.compare (ι' := ι'') : F' →* F'').comp
            ((hF.compare (ι' := ι') : F →* F').comp (ι a)) := by rfl
    _ = (hF'.compare (ι' := ι'') : F' →* F'').comp (ι' a) := by
      rw [hF.compare_ι (ι' := ι') a]
    _ = ι'' a := hF'.compare_ι (ι' := ι'') a
    _ = (hF.compare (ι' := ι'') : F →* F'').comp (ι a) :=
      (hF.compare_ι (ι' := ι'') a).symm

/-- Any two family free-product objects on the same factors are canonically isomorphic. -/
noncomputable def equiv (hF : IsFreeProductFamily G ι) (hF' : IsFreeProductFamily G ι') :
    F ≃* F' :=
  MonoidHom.toMulEquiv
    (hF.compare (ι' := ι') : F →* F') (hF'.compare (ι' := ι) : F' →* F)
    (by
      calc
        (hF'.compare (ι' := ι) : F' →* F).comp (hF.compare (ι' := ι') : F →* F') =
            (hF.compare (ι' := ι) : F →* F) := by
          simpa using hF.compare_comp (ι'' := ι) hF'
        _ = MonoidHom.id F := hF.compare_self)
    (by
      calc
        (hF.compare (ι' := ι') : F →* F').comp (hF'.compare (ι' := ι) : F' →* F) =
            (hF'.compare (ι' := ι') : F' →* F') := by
          simpa using hF'.compare_comp (ι'' := ι') hF
        _ = MonoidHom.id F' := hF'.compare_self)

/-- Component formula for the canonical equivalence between family free-product objects. -/
@[simp] theorem equiv_ι (hF : IsFreeProductFamily G ι) (hF' : IsFreeProductFamily G ι')
    (a : A) :
    (hF.equiv hF').toMonoidHom.comp (ι a) = ι' a := by
  exact hF.compare_ι (ι' := ι') a

/-- Component formula for the inverse canonical equivalence between family free-product objects. -/
theorem equiv_symm_ι (hF : IsFreeProductFamily G ι) (hF' : IsFreeProductFamily G ι')
    (a : A) :
    (hF.equiv hF').symm.toMonoidHom.comp (ι' a) = ι a := by
  change (hF'.compare (ι' := ι) : F' →* F).comp (ι' a) = ι a
  exact hF'.compare_ι (ι' := ι) a

end IsFreeProductFamily

end AbstractFreeProducts

section TopologicalFreeProducts

variable {G₁ : Type u} {G₂ : Type u} {F : Type u}
variable [Group G₁] [TopologicalSpace G₁]
variable [Group G₂] [TopologicalSpace G₂]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- A topology on an abstract binary free product compatible with the usual continuous universal
property. This is the interface needed to turn a pro-`C` completion of the topological free product
into a free pro-`C` product. -/
structure IsTopologicalFreeProduct (ι₁ : G₁ →ₜ* F) (ι₂ : G₂ →ₜ* F) : Prop where
  isFreeProduct : IsFreeProduct ι₁.toMonoidHom ι₂.toMonoidHom
  lift_continuous :
    ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K],
      ∀ (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K),
        Continuous (isFreeProduct.lift φ₁.toMonoidHom φ₂.toMonoidHom)

namespace IsTopologicalFreeProduct

variable {ι₁ : G₁ →ₜ* F} {ι₂ : G₂ →ₜ* F}

/-- The continuous lift out of a topological free product. -/
noncomputable def lift (hF : IsTopologicalFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) : F →ₜ* K where
  toMonoidHom := hF.isFreeProduct.lift φ₁.toMonoidHom φ₂.toMonoidHom
  continuous_toFun := hF.lift_continuous φ₁ φ₂

omit [IsTopologicalGroup F] in
/-- The lift from a topological free product restricts to the prescribed map on the left factor. -/
@[simp] theorem lift_left (hF : IsTopologicalFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift φ₁ φ₂).comp ι₁ = φ₁ := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact hF.isFreeProduct.lift_left φ₁.toMonoidHom φ₂.toMonoidHom

omit [IsTopologicalGroup F] in
/-- The lift from a topological free product restricts to the prescribed map on the right factor. -/
@[simp 900] theorem lift_right (hF : IsTopologicalFreeProduct ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift φ₁ φ₂).comp ι₂ = φ₂ := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact hF.isFreeProduct.lift_right φ₁.toMonoidHom φ₂.toMonoidHom

end IsTopologicalFreeProduct

end TopologicalFreeProducts

section FreeProCProducts

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {G₁ : Type u} {G₂ : Type u} {F : Type u}
variable [Group G₁] [TopologicalSpace G₁]
variable [Group G₂] [TopologicalSpace G₂]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- Binary free pro-`C` products via the strengthened universal property used elsewhere in the
project: every pair of continuous homomorphisms into a pro-`C` target extends uniquely. -/
structure IsFreeProCProduct (ι₁ : G₁ →ₜ* F) (ι₂ : G₂ →ₜ* F) : Prop where
  isProC : ProC (G := F)
  existsUnique_lift :
    ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K],
      ProC (G := K) →
      ∀ (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K),
        ∃! φ : F →ₜ* K, φ.comp ι₁ = φ₁ ∧ φ.comp ι₂ = φ₂

/-- The mapping property part of a binary free pro-`C` product. -/
def HasFreeProCProductMappingProperty (ι₁ : G₁ →ₜ* F) (ι₂ : G₂ →ₜ* F) : Prop :=
  ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K],
    ProC (G := K) →
    ∀ (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K),
      ∃! φ : F →ₜ* K, φ.comp ι₁ = φ₁ ∧ φ.comp ι₂ = φ₂

/-- A stricter free pro-`C` product statement in which the factors are also pro-`C` objects. -/
structure IsFreeProCProductOfProCObjects
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    (ι₁ : G₁ →ₜ* F) (ι₂ : G₂ →ₜ* F) : Prop where
  left_isProC : ProC (G := G₁)
  right_isProC : ProC (G := G₂)
  product_isProC : ProC (G := F)
  property : HasFreeProCProductMappingProperty (ProC := ProC) ι₁ ι₂

namespace IsFreeProCProduct

variable {ι₁ : G₁ →ₜ* F} {ι₂ : G₂ →ₜ* F}

/-- Chosen descent morphism from a binary free pro-`C` product object. -/
noncomputable def lift (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) : F →ₜ* K :=
  Classical.choose (ExistsUnique.exists (hF.existsUnique_lift hK φ₁ φ₂))

/-- The chosen free pro-`C` descent morphism has the prescribed composites. -/
theorem lift_spec (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift hK φ₁ φ₂).comp ι₁ = φ₁ ∧ (hF.lift hK φ₁ φ₂).comp ι₂ = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hF.existsUnique_lift hK φ₁ φ₂))

/-- Left composite of the chosen free pro-`C` descent morphism. -/
@[simp] theorem lift_left (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift hK φ₁ φ₂).comp ι₁ = φ₁ :=
  (hF.lift_spec hK φ₁ φ₂).1

/-- Right composite of the chosen free pro-`C` descent morphism. -/
@[simp] theorem lift_right (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift hK φ₁ φ₂).comp ι₂ = φ₂ :=
  (hF.lift_spec hK φ₁ φ₂).2

/-- Uniqueness of the chosen free pro-`C` descent morphism. -/
theorem lift_unique (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K)
    {ψ : F →ₜ* K} (hψ : ψ.comp ι₁ = φ₁ ∧ ψ.comp ι₂ = φ₂) :
    ψ = hF.lift hK φ₁ φ₂ := by
  rcases hF.existsUnique_lift hK φ₁ φ₂ with ⟨u, hu, huuniq⟩
  have hchosen : hF.lift hK φ₁ φ₂ = u := huuniq _ (hF.lift_spec hK φ₁ φ₂)
  exact (huuniq _ hψ).trans hchosen.symm

/-- The distinguished descent map from a free pro-`C` product object to itself is the identity. -/
@[simp] theorem lift_self (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂) :
    hF.lift hF.isProC ι₁ ι₂ = ContinuousMonoidHom.id F := by
  symm
  exact hF.lift_unique hF.isProC ι₁ ι₂ ⟨rfl, rfl⟩

/-- Extensionality of continuous homomorphisms out of a free pro-`C` product object. -/
theorem hom_ext (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    {ψ ψ' : F →ₜ* K}
    (h₁ : ψ.comp ι₁ = ψ'.comp ι₁) (h₂ : ψ.comp ι₂ = ψ'.comp ι₂) :
    ψ = ψ' := by
  have hψ : ψ = hF.lift (K := K) hK (ψ.comp ι₁) (ψ.comp ι₂) := by
    exact hF.lift_unique (K := K) hK (ψ.comp ι₁) (ψ.comp ι₂) ⟨rfl, rfl⟩
  have hψ' : ψ' = hF.lift (K := K) hK (ψ.comp ι₁) (ψ.comp ι₂) := by
    exact hF.lift_unique (K := K) hK (ψ.comp ι₁) (ψ.comp ι₂) ⟨h₁.symm, h₂.symm⟩
  exact hψ.trans hψ'.symm

variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable {ι₁' : G₁ →ₜ* F'} {ι₂' : G₂ →ₜ* F'}

/-- Canonical comparison morphism between two free pro-`C` product objects on the same factors. -/
noncomputable def compare (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    F →ₜ* F' :=
  hF.lift hF'.isProC ι₁' ι₂'

/-- Left composite of the canonical comparison map between free pro-`C` product objects. -/
@[simp 900] theorem compare_left (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    (hF.compare hF').comp ι₁ = ι₁' :=
  hF.lift_left hF'.isProC ι₁' ι₂'

/-- Right composite of the canonical comparison map between free pro-`C` product objects. -/
@[simp 900] theorem compare_right (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    (hF.compare hF').comp ι₂ = ι₂' :=
  hF.lift_right hF'.isProC ι₁' ι₂'

/-- The canonical comparison map from a free pro-`C` product object to itself is the identity. -/
@[simp 900] theorem compare_self (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂) :
    hF.compare hF = ContinuousMonoidHom.id F := by
  exact hF.lift_self

variable {F'' : Type u} [Group F''] [TopologicalSpace F''] [IsTopologicalGroup F'']
variable {ι₁'' : G₁ →ₜ* F''} {ι₂'' : G₂ →ₜ* F''}

/-- Composition of free pro-`C` comparison maps is the expected direct comparison map. -/
theorem compare_comp (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂')
    (hF'' : IsFreeProCProduct (ProC := ProC) ι₁'' ι₂'') :
    (hF'.compare hF'').comp (hF.compare hF') = hF.compare hF'' := by
  apply hF.hom_ext hF''.isProC
  · calc
      ((hF'.compare hF'').comp (hF.compare hF')).comp ι₁
          = (hF'.compare hF'').comp ((hF.compare hF').comp ι₁) := by rfl
      _ = (hF'.compare hF'').comp ι₁' := by rw [hF.compare_left hF']
      _ = ι₁'' := hF'.compare_left hF''
      _ = (hF.compare hF'').comp ι₁ := (hF.compare_left hF'').symm
  · calc
      ((hF'.compare hF'').comp (hF.compare hF')).comp ι₂
          = (hF'.compare hF'').comp ((hF.compare hF').comp ι₂) := by rfl
      _ = (hF'.compare hF'').comp ι₂' := by rw [hF.compare_right hF']
      _ = ι₂'' := hF'.compare_right hF''
      _ = (hF.compare hF'').comp ι₂ := (hF.compare_right hF'').symm

/-- Any two binary free pro-`C` product objects on the same factors are canonically equivalent as
topological groups. -/
noncomputable def equiv (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    F ≃ₜ* F' := by
  let φ : F →ₜ* F' := hF.compare hF'
  let ψ : F' →ₜ* F := hF'.compare hF
  have hleft : ψ.comp φ = ContinuousMonoidHom.id F := by
    calc
      ψ.comp φ = hF.compare hF := by
        simpa [φ, ψ] using hF.compare_comp hF' hF
      _ = ContinuousMonoidHom.id F := hF.compare_self
  have hright : φ.comp ψ = ContinuousMonoidHom.id F' := by
    calc
      φ.comp ψ = hF'.compare hF' := by
        simpa [φ, ψ] using hF'.compare_comp hF hF'
      _ = ContinuousMonoidHom.id F' := hF'.compare_self
  refine ContinuousMulEquiv.mk'
    (Homeomorph.mk
      (MonoidHom.toMulEquiv φ.toMonoidHom ψ.toMonoidHom
        (by simpa using congrArg ContinuousMonoidHom.toMonoidHom hleft)
        (by simpa using congrArg ContinuousMonoidHom.toMonoidHom hright))
      φ.continuous_toFun ψ.continuous_toFun)
    ?_
  intro x y
  exact φ.map_mul x y

/-- Left composite of the canonical free pro-`C` product equivalence. -/
@[simp] theorem equiv_left (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    ((hF.equiv hF' : F →ₜ* F').comp ι₁) = ι₁' := by
  exact hF.compare_left hF'

/-- Right composite of the canonical free pro-`C` product equivalence. -/
@[simp] theorem equiv_right (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    ((hF.equiv hF' : F →ₜ* F').comp ι₂) = ι₂' := by
  exact hF.compare_right hF'

/-- Left-leg formula for the inverse canonical free pro-`C` product equivalence. -/
theorem equiv_symm_left (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    (((hF.equiv hF').symm : F' →ₜ* F).comp ι₁') = ι₁ := by
  change (hF'.compare hF).comp ι₁' = ι₁
  exact hF'.compare_left hF

/-- Right-leg formula for the inverse canonical free pro-`C` product equivalence. -/
theorem equiv_symm_right (hF : IsFreeProCProduct (ProC := ProC) ι₁ ι₂)
    (hF' : IsFreeProCProduct (ProC := ProC) ι₁' ι₂') :
    (((hF.equiv hF').symm : F' →ₜ* F).comp ι₂') = ι₂ := by
  change (hF'.compare hF).comp ι₂' = ι₂
  exact hF'.compare_right hF

end IsFreeProCProduct

namespace IsTopologicalFreeProduct

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {G₁ : Type u} {G₂ : Type u} {F₀ : Type u} {Fhat : Type u}
variable [Group G₁] [TopologicalSpace G₁]
variable [Group G₂] [TopologicalSpace G₂]
variable [Group F₀] [TopologicalSpace F₀] [IsTopologicalGroup F₀]
variable [Group Fhat] [TopologicalSpace Fhat] [IsTopologicalGroup Fhat]
variable {j₁ : G₁ →ₜ* F₀} {j₂ : G₂ →ₜ* F₀} {η : F₀ →ₜ* Fhat}

/-- The left factor map into a pro-`C` completion of a topological free product model. -/
def completionInl
    (_hη : ProCGroups.Completion.IsProCCompletion ProC F₀ Fhat η)
    (j₁ : G₁ →ₜ* F₀) : G₁ →ₜ* Fhat :=
  η.comp j₁

/-- The right factor map into a pro-`C` completion of a topological free product model. -/
def completionInr
    (_hη : ProCGroups.Completion.IsProCCompletion ProC F₀ Fhat η)
    (j₂ : G₂ →ₜ* F₀) : G₂ →ₜ* Fhat :=
  η.comp j₂

/-- The completed left inclusion evaluates to the corresponding generator in the completed free product. -/
@[simp 900] theorem completionInl_apply
    (hη : ProCGroups.Completion.IsProCCompletion ProC F₀ Fhat η)
    (j₁ : G₁ →ₜ* F₀) (x : G₁) :
    completionInl (ProC := ProC) hη j₁ x = η (j₁ x) :=
  rfl

/-- The completed right inclusion evaluates to the corresponding generator in the completed free product. -/
@[simp 900] theorem completionInr_apply
    (hη : ProCGroups.Completion.IsProCCompletion ProC F₀ Fhat η)
    (j₂ : G₂ →ₜ* F₀) (x : G₂) :
    completionInr (ProC := ProC) hη j₂ x = η (j₂ x) :=
  rfl

/-- A pro-`C` completion of a topological free product model is a free pro-`C` product. This is
the construction theorem separating the topological-free-product model from the pro-`C`
reflection/completion step. -/
theorem isFreeProCProduct_of_completion
    (hF₀ : IsTopologicalFreeProduct j₁ j₂)
    (hη : ProCGroups.Completion.IsProCCompletion ProC F₀ Fhat η) :
    IsFreeProCProduct (ProC := ProC)
      (completionInl (ProC := ProC) hη j₁)
      (completionInr (ProC := ProC) hη j₂) := by
  refine ⟨hη.isProC, ?_⟩
  intro K _ _ _ hK φ₁ φ₂
  let ψ₀ : F₀ →ₜ* K :=
    { toMonoidHom := hF₀.isFreeProduct.lift φ₁.toMonoidHom φ₂.toMonoidHom
      continuous_toFun := hF₀.lift_continuous φ₁ φ₂ }
  rcases hη.existsUnique_lift hK ψ₀ with ⟨Ψ, hΨ, huniq⟩
  refine ⟨Ψ, ?_, ?_⟩
  · constructor
    · ext x
      have hfacx := congrArg (fun f : F₀ →ₜ* K => f (j₁ x)) hΨ
      have hleftx :=
        congrArg (fun f : G₁ →* K => f x)
          (hF₀.isFreeProduct.lift_left φ₁.toMonoidHom φ₂.toMonoidHom)
      calc
        Ψ (completionInl (ProC := ProC) hη j₁ x) = Ψ (η (j₁ x)) := rfl
        _ = ψ₀ (j₁ x) := hfacx
        _ = φ₁ x := hleftx
    · ext x
      have hfacx := congrArg (fun f : F₀ →ₜ* K => f (j₂ x)) hΨ
      have hrightx :=
        congrArg (fun f : G₂ →* K => f x)
          (hF₀.isFreeProduct.lift_right φ₁.toMonoidHom φ₂.toMonoidHom)
      calc
        Ψ (completionInr (ProC := ProC) hη j₂ x) = Ψ (η (j₂ x)) := rfl
        _ = ψ₀ (j₂ x) := hfacx
        _ = φ₂ x := hrightx
  · intro Χ hΧ
    apply huniq
    apply ContinuousMonoidHom.toMonoidHom_injective
    apply hF₀.isFreeProduct.hom_ext
    · ext x
      have hΧx := congrArg (fun f : G₁ →ₜ* K => f x) hΧ.1
      have hleftx :=
        congrArg (fun f : G₁ →* K => f x)
          (hF₀.isFreeProduct.lift_left φ₁.toMonoidHom φ₂.toMonoidHom)
      calc
        ((Χ.comp η).toMonoidHom.comp j₁.toMonoidHom) x =
            (Χ.comp (completionInl (ProC := ProC) hη j₁)) x := rfl
        _ = φ₁ x := hΧx
        _ = ψ₀ (j₁ x) := hleftx.symm
    · ext x
      have hΧx := congrArg (fun f : G₂ →ₜ* K => f x) hΧ.2
      have hrightx :=
        congrArg (fun f : G₂ →* K => f x)
          (hF₀.isFreeProduct.lift_right φ₁.toMonoidHom φ₂.toMonoidHom)
      calc
        ((Χ.comp η).toMonoidHom.comp j₂.toMonoidHom) x =
            (Χ.comp (completionInr (ProC := ProC) hη j₂)) x := rfl
        _ = φ₂ x := hΧx
        _ = ψ₀ (j₂ x) := hrightx.symm

/-- Existence form of `isFreeProCProduct_of_completion`, exposing the completed factor maps as
the constructed coproduct legs. -/
theorem exists_isFreeProCProduct_of_completion
    (hF₀ : IsTopologicalFreeProduct j₁ j₂)
    (hη : ProCGroups.Completion.IsProCCompletion ProC F₀ Fhat η) :
    ∃ (ι₁hat : G₁ →ₜ* Fhat) (ι₂hat : G₂ →ₜ* Fhat),
      IsFreeProCProduct (ProC := ProC) ι₁hat ι₂hat :=
  ⟨completionInl (ProC := ProC) hη j₁,
    completionInr (ProC := ProC) hη j₂,
    isFreeProCProduct_of_completion (ProC := ProC) hF₀ hη⟩

end IsTopologicalFreeProduct

namespace IsFreeProfiniteProduct

variable {G₁ : Type u} {G₂ : Type u} {F : Type u}
variable [Group G₁] [TopologicalSpace G₁]
variable [Group G₂] [TopologicalSpace G₂]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι₁ : G₁ →ₜ* F} {ι₂ : G₂ →ₜ* F}

/-- The underlying profiniteness of a free profinite product object. -/
theorem isProfiniteGroup
    (hF : IsFreeProCProduct (ProC := ProCGroups.ProC.allFiniteProC) ι₁ ι₂) :
    IsProfiniteGroup F :=
  hF.isProC

/-- A binary free profinite product is a pushout over the trivial profinite group. -/
theorem hasProfiniteTestPushoutProperty
    (hF : IsFreeProCProduct (ProC := ProCGroups.ProC.allFiniteProC) ι₁ ι₂) :
    ProCGroups.Categorical.HasProfiniteTestPushoutProperty
      (1 : ULift.{u, 0} Unit →ₜ* G₁) (1 : ULift.{u, 0} Unit →ₜ* G₂) ι₁ ι₂ := by
  constructor
  · ext u
    cases u
    simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.one_toFun, map_one]
  · intro K _ _ _ hK φ₁ φ₂ _hφ
    refine ⟨hF.lift hK φ₁ φ₂, hF.lift_spec hK φ₁ φ₂, ?_⟩
    intro ψ hψ
    exact hF.lift_unique hK φ₁ φ₂ hψ

/-- A profinite pushout over the trivial group satisfies the binary free profinite-product
universal property. -/
theorem of_hasProfiniteTestPushoutProperty (hF : IsProfiniteGroup F)
    (hpo : ProCGroups.Categorical.HasProfiniteTestPushoutProperty
      (1 : ULift.{u, 0} Unit →ₜ* G₁) (1 : ULift.{u, 0} Unit →ₜ* G₂) ι₁ ι₂) :
    IsFreeProCProduct (ProC := ProCGroups.ProC.allFiniteProC) ι₁ ι₂ := by
  refine ⟨hF, ?_⟩
  intro K _ _ _ hK φ₁ φ₂
  have hφ : φ₁.comp (1 : ULift.{u, 0} Unit →ₜ* G₁) =
      φ₂.comp (1 : ULift.{u, 0} Unit →ₜ* G₂) := by
    ext u
    cases u
    simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.one_toFun, map_one]
  simpa using hpo.2 hK φ₁ φ₂ hφ

/-- Binary free profinite products are exactly profinite pushouts over the trivial group. -/
theorem iff_hasProfiniteTestPushoutProperty (hF : IsProfiniteGroup F) :
    IsFreeProCProduct (ProC := ProCGroups.ProC.allFiniteProC) ι₁ ι₂ ↔
      ProCGroups.Categorical.HasProfiniteTestPushoutProperty
        (1 : ULift.{u, 0} Unit →ₜ* G₁) (1 : ULift.{u, 0} Unit →ₜ* G₂) ι₁ ι₂ :=
  ⟨hasProfiniteTestPushoutProperty, of_hasProfiniteTestPushoutProperty hF⟩

end IsFreeProfiniteProduct

/-- Indexed free pro-`C` products via the strengthened universal property used elsewhere in the
project. This is the family-indexed analogue needed by Kurosh-type decompositions. -/
structure IsFreeProCProductFamily {A : Type u} (G : A → Type u)
    [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : ∀ a, G a →ₜ* F) : Prop where
  isProC : ProC (G := F)
  existsUnique_lift :
    ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K],
      ProC (G := K) →
      ∀ (φ : ∀ a, G a →ₜ* K),
        ∃! ψ : F →ₜ* K, ∀ a, ψ.comp (ι a) = φ a

namespace IsFreeProCProductFamily

variable {A : Type u} {G : A → Type u}
variable [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : ∀ a, G a →ₜ* F}

/-- Chosen descent morphism from a family free pro-`C` product object. -/
noncomputable def lift (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ : ∀ a, G a →ₜ* K) : F →ₜ* K :=
  Classical.choose (ExistsUnique.exists (hF.existsUnique_lift hK φ))

/-- Component formula for the chosen family free pro-`C` descent morphism. -/
@[simp] theorem lift_ι (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ : ∀ a, G a →ₜ* K) (a : A) :
    (hF.lift hK φ).comp (ι a) = φ a :=
  Classical.choose_spec (ExistsUnique.exists (hF.existsUnique_lift hK φ)) a

/-- Uniqueness of the chosen family free pro-`C` descent morphism. -/
theorem lift_unique (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ : ∀ a, G a →ₜ* K)
    {ψ : F →ₜ* K} (hψ : ∀ a, ψ.comp (ι a) = φ a) :
    ψ = hF.lift hK φ := by
  rcases hF.existsUnique_lift hK φ with ⟨u, hu, huuniq⟩
  have hchosen : hF.lift hK φ = u := huuniq _ (fun a => hF.lift_ι hK φ a)
  exact (huuniq _ hψ).trans hchosen.symm

/-- The distinguished descent map from a family free pro-`C` product object to itself is the
identity. -/
@[simp] theorem lift_self (hF : IsFreeProCProductFamily (ProC := ProC) G ι) :
    hF.lift hF.isProC ι = ContinuousMonoidHom.id F := by
  symm
  exact hF.lift_unique hF.isProC ι (fun _ => rfl)

/-- Extensionality of continuous homomorphisms out of a family free pro-`C` product object. -/
theorem hom_ext (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    {ψ ψ' : F →ₜ* K}
    (h : ∀ a, ψ.comp (ι a) = ψ'.comp (ι a)) :
    ψ = ψ' := by
  have hψ : ψ = hF.lift hK (fun a => ψ.comp (ι a)) := by
    exact hF.lift_unique hK (fun a => ψ.comp (ι a)) (fun _ => rfl)
  have hψ' : ψ' = hF.lift hK (fun a => ψ.comp (ι a)) := by
    exact hF.lift_unique hK (fun a => ψ.comp (ι a)) (fun a => (h a).symm)
  exact hψ.trans hψ'.symm

variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable {ι' : ∀ a, G a →ₜ* F'}

/-- Canonical comparison morphism between two family free pro-`C` product objects on the same
factors. -/
noncomputable def compare
    (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsFreeProCProductFamily (ProC := ProC) G ι') :
    F →ₜ* F' :=
  hF.lift hF'.isProC ι'

/-- Component formula for the canonical comparison map between family free pro-`C` product
objects. -/
@[simp 900] theorem compare_ι
    (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsFreeProCProductFamily (ProC := ProC) G ι') (a : A) :
    (hF.compare hF').comp (ι a) = ι' a :=
  hF.lift_ι hF'.isProC ι' a

/-- The canonical comparison map from a family free pro-`C` product object to itself is the
identity. -/
@[simp 900] theorem compare_self (hF : IsFreeProCProductFamily (ProC := ProC) G ι) :
    hF.compare hF = ContinuousMonoidHom.id F := by
  exact hF.lift_self

variable {F'' : Type u} [Group F''] [TopologicalSpace F''] [IsTopologicalGroup F'']
variable {ι'' : ∀ a, G a →ₜ* F''}

/-- Composition of family free pro-`C` comparison maps is the expected direct comparison map. -/
theorem compare_comp
    (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsFreeProCProductFamily (ProC := ProC) G ι')
    (hF'' : IsFreeProCProductFamily (ProC := ProC) G ι'') :
    (hF'.compare hF'').comp (hF.compare hF') = hF.compare hF'' := by
  apply hF.hom_ext hF''.isProC
  intro a
  calc
    ((hF'.compare hF'').comp (hF.compare hF')).comp (ι a)
        = (hF'.compare hF'').comp ((hF.compare hF').comp (ι a)) := by rfl
    _ = (hF'.compare hF'').comp (ι' a) := by rw [hF.compare_ι hF' a]
    _ = ι'' a := hF'.compare_ι hF'' a
    _ = (hF.compare hF'').comp (ι a) := (hF.compare_ι hF'' a).symm

/-- Any two family free pro-`C` product objects on the same factors are canonically equivalent as
topological groups. -/
noncomputable def equiv
    (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsFreeProCProductFamily (ProC := ProC) G ι') :
    F ≃ₜ* F' := by
  let φ : F →ₜ* F' := hF.compare hF'
  let ψ : F' →ₜ* F := hF'.compare hF
  have hleft : ψ.comp φ = ContinuousMonoidHom.id F := by
    calc
      ψ.comp φ = hF.compare hF := by
        simpa [φ, ψ] using hF.compare_comp hF' hF
      _ = ContinuousMonoidHom.id F := hF.compare_self
  have hright : φ.comp ψ = ContinuousMonoidHom.id F' := by
    calc
      φ.comp ψ = hF'.compare hF' := by
        simpa [φ, ψ] using hF'.compare_comp hF hF'
      _ = ContinuousMonoidHom.id F' := hF'.compare_self
  refine ContinuousMulEquiv.mk'
    (Homeomorph.mk
      (MonoidHom.toMulEquiv φ.toMonoidHom ψ.toMonoidHom
        (by simpa using congrArg ContinuousMonoidHom.toMonoidHom hleft)
        (by simpa using congrArg ContinuousMonoidHom.toMonoidHom hright))
      φ.continuous_toFun ψ.continuous_toFun)
    ?_
  intro x y
  exact φ.map_mul x y

/-- Component formula for the canonical equivalence between family free pro-`C` product objects. -/
@[simp] theorem equiv_ι
    (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsFreeProCProductFamily (ProC := ProC) G ι') (a : A) :
    ((hF.equiv hF' : F →ₜ* F').comp (ι a)) = ι' a := by
  exact hF.compare_ι hF' a

/-- Component formula for the inverse canonical equivalence between family free pro-`C` product
objects. -/
theorem equiv_symm_ι
    (hF : IsFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsFreeProCProductFamily (ProC := ProC) G ι') (a : A) :
    (((hF.equiv hF').symm : F' →ₜ* F).comp (ι' a)) = ι a := by
  change (hF'.compare hF).comp (ι' a) = ι a
  exact hF'.compare_ι hF a

end IsFreeProCProductFamily

/-- A family of continuous homomorphisms converges to `1` if every open subgroup of the target
contains the image of all but finitely many components. This is the convergence hypothesis used in
the indexed-family free pro-`C` product universal property. -/
def ContinuousHomFamilyConvergesToOne {A : Type u} (G : A → Type u)
    [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)]
    {K : Type u} [Group K] [TopologicalSpace K]
    (φ : ∀ a, G a →ₜ* K) : Prop :=
  ∀ U : OpenSubgroup K, {a | ¬ (φ a).toMonoidHom.range ≤ (U : Subgroup K)}.Finite

namespace ContinuousHomFamilyConvergesToOne

variable {A : Type u} {G : A → Type u}
variable [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)]
variable {K : Type u} [Group K] [TopologicalSpace K]
variable {L : Type u} [Group L] [TopologicalSpace L]
variable {φ : ∀ a, G a →ₜ* K}

/-- Postcomposing a convergent family of homomorphisms with a continuous homomorphism preserves
convergence to `1`. -/
theorem comp (hφ : ContinuousHomFamilyConvergesToOne G φ) (ψ : K →ₜ* L) :
    ContinuousHomFamilyConvergesToOne G (fun a => ψ.comp (φ a)) := by
  intro U
  let V : OpenSubgroup K := OpenSubgroup.comap (f := ψ.toMonoidHom) ψ.continuous_toFun U
  refine (hφ V).subset ?_
  intro a ha hle
  apply ha
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hxV : φ a x ∈ (V : Subgroup K) := hle ⟨x, rfl⟩
  simpa [V] using hxV

end ContinuousHomFamilyConvergesToOne

/-- Indexed free pro-`C` products in the infinite indexed-family form: the universal property
is tested only against families of maps converging to `1`, and the distinguished inclusions
themselves converge to `1`. -/
structure IsIndexedFreeProCProductFamily {A : Type u} (G : A → Type u)
    [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : ∀ a, G a →ₜ* F) : Prop where
  isProC : ProC (G := F)
  inclusionsConverge : ContinuousHomFamilyConvergesToOne G ι
  existsUnique_lift :
    ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K],
      ProC (G := K) →
      ∀ (φ : ∀ a, G a →ₜ* K),
        ContinuousHomFamilyConvergesToOne G φ →
          ∃! ψ : F →ₜ* K, ∀ a, ψ.comp (ι a) = φ a

namespace IsIndexedFreeProCProductFamily

variable {A : Type u} {G : A → Type u}
variable [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : ∀ a, G a →ₜ* F}

/-- Chosen descent morphism from an indexed-family free pro-`C` product object. -/
noncomputable def lift (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ : ∀ a, G a →ₜ* K)
    (hφ : ContinuousHomFamilyConvergesToOne G φ) : F →ₜ* K :=
  Classical.choose (ExistsUnique.exists (hF.existsUnique_lift hK φ hφ))

/-- Component formula for the chosen indexed-family descent morphism. -/
@[simp] theorem lift_ι (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ : ∀ a, G a →ₜ* K)
    (hφ : ContinuousHomFamilyConvergesToOne G φ) (a : A) :
    (hF.lift hK φ hφ).comp (ι a) = φ a :=
  Classical.choose_spec (ExistsUnique.exists (hF.existsUnique_lift hK φ hφ)) a

/-- Uniqueness of the chosen indexed-family descent morphism. -/
theorem lift_unique (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    (φ : ∀ a, G a →ₜ* K)
    (hφ : ContinuousHomFamilyConvergesToOne G φ)
    {ψ : F →ₜ* K} (hψ : ∀ a, ψ.comp (ι a) = φ a) :
    ψ = hF.lift hK φ hφ := by
  rcases hF.existsUnique_lift hK φ hφ with ⟨u, hu, huuniq⟩
  have hchosen : hF.lift hK φ hφ = u := huuniq _ (fun a => hF.lift_ι hK φ hφ a)
  exact (huuniq _ hψ).trans hchosen.symm

/-- The distinguished descent map from an indexed-family free pro-`C` product object to
itself is the identity. -/
@[simp] theorem lift_self (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι) :
    hF.lift hF.isProC ι hF.inclusionsConverge = ContinuousMonoidHom.id F := by
  symm
  exact hF.lift_unique hF.isProC ι hF.inclusionsConverge (fun _ => rfl)

/-- Extensionality of continuous homomorphisms out of an indexed-family free pro-`C`
product object. -/
theorem hom_ext (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hK : ProC (G := K))
    {ψ ψ' : F →ₜ* K}
    (h : ∀ a, ψ.comp (ι a) = ψ'.comp (ι a)) :
    ψ = ψ' := by
  have hconv :
      ContinuousHomFamilyConvergesToOne G (fun a => ψ.comp (ι a)) :=
    hF.inclusionsConverge.comp ψ
  have hψ : ψ = hF.lift hK (fun a => ψ.comp (ι a)) hconv := by
    exact hF.lift_unique hK (fun a => ψ.comp (ι a)) hconv (fun _ => rfl)
  have hψ' : ψ' = hF.lift hK (fun a => ψ.comp (ι a)) hconv := by
    exact hF.lift_unique hK (fun a => ψ.comp (ι a)) hconv (fun a => (h a).symm)
  exact hψ.trans hψ'.symm

variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable {ι' : ∀ a, G a →ₜ* F'}

/-- Canonical comparison morphism between two indexed-family free pro-`C` product objects
on the same factors. -/
noncomputable def compare
    (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι') :
    F →ₜ* F' :=
  hF.lift hF'.isProC ι' hF'.inclusionsConverge

/-- Component formula for the canonical comparison map between indexed-family free pro-`C`
product objects. -/
@[simp 900] theorem compare_ι
    (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι') (a : A) :
    (hF.compare hF').comp (ι a) = ι' a :=
  hF.lift_ι hF'.isProC ι' hF'.inclusionsConverge a

/-- The canonical comparison map from an indexed-family free pro-`C` product object to
itself is the identity. -/
@[simp 900] theorem compare_self (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι) :
    hF.compare hF = ContinuousMonoidHom.id F := by
  exact hF.lift_self

variable {F'' : Type u} [Group F''] [TopologicalSpace F''] [IsTopologicalGroup F'']
variable {ι'' : ∀ a, G a →ₜ* F''}

/-- Composition of indexed-family free pro-`C` comparison maps is the expected direct
comparison map. -/
theorem compare_comp
    (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι')
    (hF'' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι'') :
    (hF'.compare hF'').comp (hF.compare hF') = hF.compare hF'' := by
  apply hF.hom_ext hF''.isProC
  intro a
  calc
    ((hF'.compare hF'').comp (hF.compare hF')).comp (ι a)
        = (hF'.compare hF'').comp ((hF.compare hF').comp (ι a)) := by rfl
    _ = (hF'.compare hF'').comp (ι' a) := by rw [hF.compare_ι hF' a]
    _ = ι'' a := hF'.compare_ι hF'' a
    _ = (hF.compare hF'').comp (ι a) := (hF.compare_ι hF'' a).symm

/-- Any two indexed-family free pro-`C` product objects on the same factors are canonically
equivalent as topological groups. -/
noncomputable def equiv
    (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι') :
    F ≃ₜ* F' := by
  let φ : F →ₜ* F' := hF.compare hF'
  let ψ : F' →ₜ* F := hF'.compare hF
  have hleft : ψ.comp φ = ContinuousMonoidHom.id F := by
    calc
      ψ.comp φ = hF.compare hF := by
        simpa [φ, ψ] using hF.compare_comp hF' hF
      _ = ContinuousMonoidHom.id F := hF.compare_self
  have hright : φ.comp ψ = ContinuousMonoidHom.id F' := by
    calc
      φ.comp ψ = hF'.compare hF' := by
        simpa [φ, ψ] using hF'.compare_comp hF hF'
      _ = ContinuousMonoidHom.id F' := hF'.compare_self
  refine ContinuousMulEquiv.mk'
    (Homeomorph.mk
      (MonoidHom.toMulEquiv φ.toMonoidHom ψ.toMonoidHom
        (by simpa using congrArg ContinuousMonoidHom.toMonoidHom hleft)
        (by simpa using congrArg ContinuousMonoidHom.toMonoidHom hright))
      φ.continuous_toFun ψ.continuous_toFun)
    ?_
  intro x y
  exact φ.map_mul x y

/-- Component formula for the canonical equivalence between indexed-family free pro-`C`
product objects. -/
@[simp] theorem equiv_ι
    (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι') (a : A) :
    ((hF.equiv hF' : F →ₜ* F').comp (ι a)) = ι' a := by
  exact hF.compare_ι hF' a

/-- Component formula for the inverse canonical equivalence between indexed-family free
pro-`C` product objects. -/
theorem equiv_symm_ι
    (hF : IsIndexedFreeProCProductFamily (ProC := ProC) G ι)
    (hF' : IsIndexedFreeProCProductFamily (ProC := ProC) G ι') (a : A) :
    (((hF.equiv hF').symm : F' →ₜ* F).comp (ι' a)) = ι a := by
  change (hF'.compare hF).comp (ι' a) = ι a
  exact hF'.compare_ι hF a

end IsIndexedFreeProCProductFamily

end FreeProCProducts

end ProCGroups.FreeProducts
