import ProCGroups.ProC.Category.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Category/Pushouts.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open CategoryTheory

universe u

namespace ProCGrp

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {G G' H H₁ H₂ : ProCGrp ProC}

/-- A pushout square in the bundled category `ProCGrp ProC`. -/
def IsPushoutSquare
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (α₁ : H₁ ⟶ G) (α₂ : H₂ ⟶ G) : Prop :=
  β₁ ≫ α₁ = β₂ ≫ α₂ ∧
    ∀ ⦃K : ProCGrp ProC⦄ (φ₁ : H₁ ⟶ K) (φ₂ : H₂ ⟶ K),
      β₁ ≫ φ₁ = β₂ ≫ φ₂ →
        ∃! φ : G ⟶ K, α₁ ≫ φ = φ₁ ∧ α₂ ≫ φ = φ₂

/-- Chosen morphism induced by a pro-`C` pushout universal property. -/
noncomputable def pushoutDesc
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {K : ProCGrp ProC}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (φ₁ : H₁ ⟶ K) (φ₂ : H₂ ⟶ K)
    (hφ : β₁ ≫ φ₁ = β₂ ≫ φ₂) : G ⟶ K :=
  Classical.choose (ExistsUnique.exists (hpo.2 φ₁ φ₂ hφ))

/-- The chosen pushout descent map has the prescribed composites. -/
theorem pushoutDesc_spec
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {K : ProCGrp ProC}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (φ₁ : H₁ ⟶ K) (φ₂ : H₂ ⟶ K)
    (hφ : β₁ ≫ φ₁ = β₂ ≫ φ₂) :
    α₁ ≫ pushoutDesc hpo φ₁ φ₂ hφ = φ₁ ∧
      α₂ ≫ pushoutDesc hpo φ₁ φ₂ hφ = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hpo.2 φ₁ φ₂ hφ))

/-- The pushout descent map has the prescribed left composite. -/
@[simp] theorem pushoutDesc_left
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {K : ProCGrp ProC}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (φ₁ : H₁ ⟶ K) (φ₂ : H₂ ⟶ K)
    (hφ : β₁ ≫ φ₁ = β₂ ≫ φ₂) :
    α₁ ≫ pushoutDesc hpo φ₁ φ₂ hφ = φ₁ :=
  (pushoutDesc_spec hpo φ₁ φ₂ hφ).1

/-- The pushout descent map has the prescribed right composite. -/
@[simp] theorem pushoutDesc_right
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {K : ProCGrp ProC}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (φ₁ : H₁ ⟶ K) (φ₂ : H₂ ⟶ K)
    (hφ : β₁ ≫ φ₁ = β₂ ≫ φ₂) :
    α₂ ≫ pushoutDesc hpo φ₁ φ₂ hφ = φ₂ :=
  (pushoutDesc_spec hpo φ₁ φ₂ hφ).2

/-- Uniqueness of the chosen pushout descent map. -/
theorem pushoutDesc_unique
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {K : ProCGrp ProC}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (φ₁ : H₁ ⟶ K) (φ₂ : H₂ ⟶ K)
    (hφ : β₁ ≫ φ₁ = β₂ ≫ φ₂)
    {ψ : G ⟶ K}
    (hψ : α₁ ≫ ψ = φ₁ ∧ α₂ ≫ ψ = φ₂) :
    ψ = pushoutDesc hpo φ₁ φ₂ hφ := by
  rcases hpo.2 φ₁ φ₂ hφ with ⟨u, hu, huuniq⟩
  have hψ' : ψ = u := huuniq _ hψ
  have hdesc : pushoutDesc hpo φ₁ φ₂ hφ = u :=
    huuniq _ (pushoutDesc_spec hpo φ₁ φ₂ hφ)
  exact hψ'.trans hdesc.symm

/-- The self-descent map of a pushout object is the identity. -/
@[simp] theorem pushoutDesc_self
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂) :
    pushoutDesc hpo α₁ α₂ hpo.1 = 𝟙 G := by
  symm
  exact pushoutDesc_unique hpo α₁ α₂ hpo.1 (ψ := 𝟙 G) (by simp only [Category.comp_id, and_self])

/-- Extensionality of morphisms out of a pro-`C` pushout object. -/
theorem pushout_hom_ext
    {β₁ : H ⟶ H₁} {β₂ : H ⟶ H₂}
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {K : ProCGrp ProC}
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    {ψ ψ' : G ⟶ K}
    (h₁ : α₁ ≫ ψ = α₁ ≫ ψ')
    (h₂ : α₂ ≫ ψ = α₂ ≫ ψ') :
    ψ = ψ' := by
  have hφ : β₁ ≫ (α₁ ≫ ψ) = β₂ ≫ (α₂ ≫ ψ) := by
    calc
      β₁ ≫ (α₁ ≫ ψ) = (β₁ ≫ α₁) ≫ ψ := by simp only [Category.assoc]
      _ = (β₂ ≫ α₂) ≫ ψ := by rw [hpo.1]
      _ = β₂ ≫ (α₂ ≫ ψ) := by simp only [Category.assoc]
  have hψ :
      ψ = pushoutDesc hpo (α₁ ≫ ψ) (α₂ ≫ ψ) hφ := by
    exact pushoutDesc_unique hpo (α₁ ≫ ψ) (α₂ ≫ ψ) hφ (ψ := ψ) ⟨rfl, rfl⟩
  have hψ' :
      ψ' = pushoutDesc hpo (α₁ ≫ ψ) (α₂ ≫ ψ) hφ := by
    exact pushoutDesc_unique hpo (α₁ ≫ ψ) (α₂ ≫ ψ) hφ
      (ψ := ψ') ⟨h₁.symm, h₂.symm⟩
  exact hψ.trans hψ'.symm

/-- Canonical comparison map between two pro-`C` pushout objects of the same cospan. -/
noncomputable def pushoutMapOfIsPushout
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {α₁' : H₁ ⟶ G'} {α₂' : H₂ ⟶ G'}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (hpo' : IsPushoutSquare β₁ β₂ α₁' α₂') :
    G ⟶ G' :=
  pushoutDesc hpo α₁' α₂' hpo'.1

/-- The comparison map from a pushout object to itself is the identity. -/
@[simp] theorem pushoutMapOfIsPushout_self
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂) :
    pushoutMapOfIsPushout β₁ β₂ hpo hpo = 𝟙 G := by
  exact pushoutDesc_self (hpo := hpo)

/-- The comparison map between pushout objects respects the left structure map. -/
@[simp] theorem pushoutMapOfIsPushout_left
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {α₁' : H₁ ⟶ G'} {α₂' : H₂ ⟶ G'}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (hpo' : IsPushoutSquare β₁ β₂ α₁' α₂') :
    α₁ ≫ pushoutMapOfIsPushout β₁ β₂ hpo hpo' = α₁' :=
  pushoutDesc_left hpo α₁' α₂' hpo'.1

/-- The comparison map between pushout objects respects the right structure map. -/
@[simp] theorem pushoutMapOfIsPushout_right
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {α₁' : H₁ ⟶ G'} {α₂' : H₂ ⟶ G'}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (hpo' : IsPushoutSquare β₁ β₂ α₁' α₂') :
    α₂ ≫ pushoutMapOfIsPushout β₁ β₂ hpo hpo' = α₂' :=
  pushoutDesc_right hpo α₁' α₂' hpo'.1

/-- Any two pro-`C` pushout objects of the same cospan are canonically isomorphic. -/
noncomputable def pushoutIsoOfIsPushout
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {α₁' : H₁ ⟶ G'} {α₂' : H₂ ⟶ G'}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (hpo' : IsPushoutSquare β₁ β₂ α₁' α₂') :
    G ≅ G' where
  hom := pushoutMapOfIsPushout β₁ β₂ hpo hpo'
  inv := pushoutMapOfIsPushout β₁ β₂ hpo' hpo
  hom_inv_id := by
    apply pushout_hom_ext hpo
    · calc
        α₁ ≫ pushoutMapOfIsPushout β₁ β₂ hpo hpo' ≫
            pushoutMapOfIsPushout β₁ β₂ hpo' hpo =
              α₁' ≫ pushoutMapOfIsPushout β₁ β₂ hpo' hpo := by
          rw [← Category.assoc, pushoutMapOfIsPushout_left]
        _ = α₁ := pushoutMapOfIsPushout_left β₁ β₂ hpo' hpo
    · calc
        α₂ ≫ pushoutMapOfIsPushout β₁ β₂ hpo hpo' ≫
            pushoutMapOfIsPushout β₁ β₂ hpo' hpo =
              α₂' ≫ pushoutMapOfIsPushout β₁ β₂ hpo' hpo := by
          rw [← Category.assoc, pushoutMapOfIsPushout_right]
        _ = α₂ := pushoutMapOfIsPushout_right β₁ β₂ hpo' hpo
  inv_hom_id := by
    apply pushout_hom_ext hpo'
    · calc
        α₁' ≫ pushoutMapOfIsPushout β₁ β₂ hpo' hpo ≫
            pushoutMapOfIsPushout β₁ β₂ hpo hpo' =
              α₁ ≫ pushoutMapOfIsPushout β₁ β₂ hpo hpo' := by
          rw [← Category.assoc, pushoutMapOfIsPushout_left]
        _ = α₁' := pushoutMapOfIsPushout_left β₁ β₂ hpo hpo'
    · calc
        α₂' ≫ pushoutMapOfIsPushout β₁ β₂ hpo' hpo ≫
            pushoutMapOfIsPushout β₁ β₂ hpo hpo' =
              α₂ ≫ pushoutMapOfIsPushout β₁ β₂ hpo hpo' := by
          rw [← Category.assoc, pushoutMapOfIsPushout_right]
        _ = α₂' := pushoutMapOfIsPushout_right β₁ β₂ hpo hpo'

/-- The canonical pushout isomorphism respects the left structure map. -/
@[simp] theorem pushoutIsoOfIsPushout_hom_left
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {α₁' : H₁ ⟶ G'} {α₂' : H₂ ⟶ G'}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (hpo' : IsPushoutSquare β₁ β₂ α₁' α₂') :
    α₁ ≫ (pushoutIsoOfIsPushout β₁ β₂ hpo hpo').hom = α₁' :=
  pushoutMapOfIsPushout_left β₁ β₂ hpo hpo'

/-- The canonical pushout isomorphism respects the right structure map. -/
@[simp] theorem pushoutIsoOfIsPushout_hom_right
    {α₁ : H₁ ⟶ G} {α₂ : H₂ ⟶ G}
    {α₁' : H₁ ⟶ G'} {α₂' : H₂ ⟶ G'}
    (β₁ : H ⟶ H₁) (β₂ : H ⟶ H₂)
    (hpo : IsPushoutSquare β₁ β₂ α₁ α₂)
    (hpo' : IsPushoutSquare β₁ β₂ α₁' α₂') :
    α₂ ≫ (pushoutIsoOfIsPushout β₁ β₂ hpo hpo').hom = α₂' :=
  pushoutMapOfIsPushout_right β₁ β₂ hpo hpo'

end ProCGrp
