import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.GroupTheory.QuotientGroup.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Categorical/AlgebraicPullbacks.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pullbacks, pushouts, and quotient comparison

Concrete algebraic and topological pullbacks and pushouts of groups and profinite groups, with comparison maps, universal properties, kernel criteria, and quotient pullback equivalences.
-/

namespace ProCGroups.Categorical

open CategoryTheory Limits
open scoped Pointwise

universe u v

section

variable {A G H H₁ H₂ : Type u} {K : Type v}
variable [Group A] [Group G] [Group H] [Group H₁] [Group H₂] [Group K]

/-- Concrete pullback subgroup of `β₁` and `β₂`.
-/
def FiberProduct.subgroup (β₁ : H₁ →* H) (β₂ : H₂ →* H) : Subgroup (H₁ × H₂) where
  carrier := { x | β₁ x.1 = β₂ x.2 }
  one_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_one, map_one, Prod.snd_one]
  mul_mem' := by
    intro x y hx hy
    change β₁ x.1 = β₂ x.2 at hx
    change β₁ y.1 = β₂ y.2 at hy
    simpa [map_mul] using congrArg₂ (· * ·) hx hy
  inv_mem' := by
    intro x hx
    simpa [map_inv, hx]

/-- Concrete pullback attached to `β₁` and `β₂`.
-/
abbrev FiberProduct.carrier (β₁ : H₁ →* H) (β₂ : H₂ →* H) :=
  ↥(FiberProduct.subgroup β₁ β₂)

/-- Membership criterion for the concrete pullback subgroup. -/
@[simp] theorem mem_pullbackSubgroup_iff {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {x : H₁ × H₂} :
    x ∈ FiberProduct.subgroup β₁ β₂ ↔ β₁ x.1 = β₂ x.2 :=
  Iff.rfl

/-- The first projection from the concrete pullback. -/
def FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H) : FiberProduct.carrier β₁ β₂ →* H₁ where
  toFun := fun x => x.1.1
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The second projection from the concrete pullback. -/
def FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H) : FiberProduct.carrier β₁ β₂ →* H₂ where
  toFun := fun x => x.1.2
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The canonical homomorphism into the concrete pullback. -/
def FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) : K →* FiberProduct.carrier β₁ β₂ where
  toFun := fun k => ⟨(φ₁ k, φ₂ k), h k⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, OneMemClass.coe_one, Prod.mk_eq_one, and_self]
  map_mul' := by
    intro x y
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, Prod.mk_mul_mk]

/-- The canonical pullback lift evaluates coordinatewise. -/
@[simp] theorem pullbackLift_apply (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    FiberProduct.lift β₁ β₂ φ₁ φ₂ h k = ⟨(φ₁ k, φ₂ k), h k⟩ :=
  rfl

/-- The first coordinate of the canonical pullback lift. -/
@[simp] theorem pullbackFst_pullbackLift_apply (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    FiberProduct.fst β₁ β₂ (FiberProduct.lift β₁ β₂ φ₁ φ₂ h k) = φ₁ k :=
  rfl

/-- The second coordinate of the canonical pullback lift. -/
@[simp] theorem pullbackSnd_pullbackLift_apply (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    FiberProduct.snd β₁ β₂ (FiberProduct.lift β₁ β₂ φ₁ φ₂ h k) = φ₂ k :=
  rfl

/-- The concrete group pullback as a categorical pullback cone in `GrpCat`. -/
def FiberProduct.cone (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    PullbackCone (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
  PullbackCone.mk
    (GrpCat.ofHom (FiberProduct.fst β₁ β₂))
    (GrpCat.ofHom (FiberProduct.snd β₁ β₂))
    (by
      apply GrpCat.hom_ext
      ext x
      exact x.2)

/-- The concrete group pullback cone is a limit cone in `GrpCat`. -/
def FiberProduct.isLimitCone (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    IsLimit (FiberProduct.cone β₁ β₂) := by
  refine PullbackCone.IsLimit.mk (by
    apply GrpCat.hom_ext
    ext x
    exact x.2) ?lift ?fac_left ?fac_right ?uniq
  · intro s
    exact GrpCat.ofHom <|
      FiberProduct.lift β₁ β₂ s.fst.hom s.snd.hom (fun x => by
        have hcondition :
            (s.fst ≫ GrpCat.ofHom β₁).hom =
              (s.snd ≫ GrpCat.ofHom β₂).hom :=
          congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition
        exact DFunLike.congr_fun hcondition x)
  · intro s
    apply GrpCat.hom_ext
    rfl
  · intro s
    apply GrpCat.hom_ext
    rfl
  · intro s m hfst hsnd
    apply GrpCat.hom_ext
    ext x
    · have hfst' :
          (m ≫ GrpCat.ofHom (FiberProduct.fst β₁ β₂)).hom = s.fst.hom :=
        congrArg (fun f : s.pt ⟶ GrpCat.of H₁ => f.hom) hfst
      exact DFunLike.congr_fun hfst' x
    · have hsnd' :
          (m ≫ GrpCat.ofHom (FiberProduct.snd β₁ β₂)).hom = s.snd.hom :=
        congrArg (fun f : s.pt ⟶ GrpCat.of H₂ => f.hom) hsnd
      exact DFunLike.congr_fun hsnd' x

/-- The kernel of the canonical map into a concrete pullback is the intersection of the two
coordinate kernels. -/
@[simp] theorem ker_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.lift β₁ β₂ φ₁ φ₂ h).ker = φ₁.ker ⊓ φ₂.ker := by
  ext k
  change FiberProduct.lift β₁ β₂ φ₁ φ₂ h k = 1 ↔ φ₁ k = 1 ∧ φ₂ k = 1
  constructor
  · intro hk
    exact ⟨congrArg (fun z => FiberProduct.fst β₁ β₂ z) hk,
      congrArg (fun z => FiberProduct.snd β₁ β₂ z) hk⟩
  · rintro ⟨h₁, h₂⟩
    apply Subtype.ext
    exact Prod.ext h₁ h₂

/-- The canonical map into a concrete pullback is injective exactly when the coordinate kernels
intersect trivially. -/
theorem pullbackLift_injective_iff (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    Function.Injective (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) ↔ φ₁.ker ⊓ φ₂.ker = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_pullbackLift]

/-- The sum of the coordinate kernels is always contained in the kernel of the common composite. -/
theorem ker_sup_le_ker_comp_of_comp_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    φ₁.ker ⊔ φ₂.ker ≤ (β₁.comp φ₁).ker := by
  rw [sup_le_iff]
  constructor
  · intro k hk
    change β₁ (φ₁ k) = 1
    have hk' : φ₁ k = 1 := by simpa using hk
    simp only [hk', map_one]
  · intro k hk
    calc
      β₁ (φ₁ k) = β₂ (φ₂ k) := DFunLike.congr_fun hcomp k
      _ = 1 := by
        have hk' : φ₂ k = 1 := by simpa using hk
        simp only [hk', map_one]

/-- The standard kernel condition for surjectivity onto a pullback. -/
def HasPullbackKernelCriterion
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂) : Prop :=
  β₁.comp φ₁ = β₂.comp φ₂ ∧ (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker

/-- The compatibility equality contained in `HasPullbackKernelCriterion`. -/
theorem HasPullbackKernelCriterion.comp_eq
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {φ₁ : K →* H₁} {φ₂ : K →* H₂}
    (h : HasPullbackKernelCriterion β₁ β₂ φ₁ φ₂) :
    β₁.comp φ₁ = β₂.comp φ₂ :=
  h.1

/-- The kernel equality contained in `HasPullbackKernelCriterion`. -/
theorem HasPullbackKernelCriterion.ker_eq
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {φ₁ : K →* H₁} {φ₂ : K →* H₂}
    (h : HasPullbackKernelCriterion β₁ β₂ φ₁ φ₂) :
    (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker :=
  h.2

/-- The canonical map into a concrete pullback is surjective exactly when the composite kernel is
contained in the sum of the coordinate kernels. -/
theorem pullbackLift_surjective_iff_ker_comp_le_sup_ker
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun k => DFunLike.congr_fun hcomp k)) ↔
      (β₁.comp φ₁).ker ≤ φ₁.ker ⊔ φ₂.ker := by
  constructor
  · intro hsurj k hk
    let z : FiberProduct.carrier β₁ β₂ :=
      ⟨(φ₁ k, 1), by
        change β₁ (φ₁ k) = β₂ 1
        simpa using hk⟩
    rcases hsurj z with ⟨a, ha⟩
    have hφ₁a : φ₁ a = φ₁ k := by
      exact congrArg (fun y => FiberProduct.fst β₁ β₂ y) ha
    have hφ₂a : φ₂ a = 1 := by
      exact congrArg (fun y => FiberProduct.snd β₁ β₂ y) ha
    have ha_ker₂ : a ∈ φ₂.ker := by
      simpa using hφ₂a
    have ha_inv_mul_ker₁ : a⁻¹ * k ∈ φ₁.ker := by
      change φ₁ (a⁻¹ * k) = 1
      simp only [map_mul, map_inv, hφ₁a, inv_mul_cancel]
    have hprod : a * (a⁻¹ * k) ∈ φ₁.ker ⊔ φ₂.ker :=
      (φ₁.ker ⊔ φ₂.ker).mul_mem
        ((le_sup_right : φ₂.ker ≤ φ₁.ker ⊔ φ₂.ker) ha_ker₂)
        ((le_sup_left : φ₁.ker ≤ φ₁.ker ⊔ φ₂.ker) ha_inv_mul_ker₁)
    simpa [mul_assoc] using hprod
  · intro hker_le z
    rcases hφ₁ z.1.1 with ⟨a₁, ha₁⟩
    rcases hφ₂ z.1.2 with ⟨a₂, ha₂⟩
    have hEq : β₁ (φ₁ a₁) = β₁ (φ₁ a₂) := by
      calc
        β₁ (φ₁ a₁) = β₁ z.1.1 := by simp only [ha₁]
        _ = β₂ z.1.2 := z.2
        _ = β₂ (φ₂ a₂) := by simp only [ha₂]
        _ = β₁ (φ₁ a₂) := by
          exact (DFunLike.congr_fun hcomp a₂).symm
    have hgker : a₁ * a₂⁻¹ ∈ (β₁.comp φ₁).ker := by
      change β₁ (φ₁ (a₁ * a₂⁻¹)) = 1
      simp only [map_mul, map_inv, hEq, mul_inv_cancel]
    have hgjoin : a₁ * a₂⁻¹ ∈ (φ₁.ker : Subgroup K) ⊔ (φ₂.ker : Subgroup K) :=
      hker_le hgker
    have hgjoin' : a₁ * a₂⁻¹ ∈ ((φ₁.ker : Set K) * (φ₂.ker : Set K)) := by
      rw [← Subgroup.mul_normal (φ₁.ker) (φ₂.ker)]
      simpa [SetLike.mem_coe] using hgjoin
    rcases (show ∃ y ∈ (φ₁.ker : Set K), ∃ z ∈ (φ₂.ker : Set K),
        y * z = a₁ * a₂⁻¹ from by
          simpa [Set.mem_mul] using hgjoin') with ⟨k₁, hk₁, k₂, hk₂, hkprod⟩
    have hk₁' : φ₁ k₁ = 1 := by simpa using hk₁
    have hk₂' : φ₂ k₂ = 1 := by simpa using hk₂
    have haeq : a₁ = k₁ * k₂ * a₂ := by
      calc
        a₁ = (a₁ * a₂⁻¹) * a₂ := by simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = (k₁ * k₂) * a₂ := by rw [hkprod]
        _ = k₁ * k₂ * a₂ := by simp only [mul_assoc]
    refine ⟨k₂ * a₂, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · calc
        φ₁ (k₂ * a₂) = φ₁ (k₁ * k₂ * a₂) := by
          simp only [map_mul, mul_assoc, hk₁', one_mul]
        _ = φ₁ a₁ := by rw [haeq]
        _ = z.1.1 := ha₁
    · calc
        φ₂ (k₂ * a₂) = φ₂ k₂ * φ₂ a₂ := by rw [map_mul]
        _ = 1 * φ₂ a₂ := by simp only [hk₂', one_mul]
        _ = z.1.2 := by simp only [ha₂, one_mul]

/-- The canonical map into a concrete pullback is surjective exactly when the composite kernel is
the sum of the coordinate kernels. -/
theorem pullbackLift_surjective_iff_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun k => DFunLike.congr_fun hcomp k)) ↔
      (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker := by
  constructor
  · intro hsurj
    exact le_antisymm
      ((pullbackLift_surjective_iff_ker_comp_le_sup_ker
        β₁ β₂ φ₁ φ₂ hφ₁ hφ₂ hcomp).1 hsurj)
      (ker_sup_le_ker_comp_of_comp_eq β₁ β₂ φ₁ φ₂ hcomp)
  · intro hker
    exact (pullbackLift_surjective_iff_ker_comp_le_sup_ker
      β₁ β₂ φ₁ φ₂ hφ₁ hφ₂ hcomp).2 (by
        intro k hk
        rw [← hker]
        exact hk)

/-- The named kernel criterion gives surjectivity of the canonical map into the pullback. -/
theorem pullbackLift_surjective_of_hasPullbackKernelCriterion
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcrit : HasPullbackKernelCriterion β₁ β₂ φ₁ φ₂) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun k => DFunLike.congr_fun hcrit.comp_eq k)) := by
  exact (pullbackLift_surjective_iff_ker_eq
    β₁ β₂ φ₁ φ₂ hφ₁ hφ₂ hcrit.comp_eq).2 hcrit.ker_eq

/-- The first projection composed with the canonical pullback lift is `φ₁`. -/
@[simp] theorem pullbackFst_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.fst β₁ β₂).comp (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₁ := by
  ext k
  rfl

/-- The second projection composed with the canonical pullback lift is `φ₂`. -/
@[simp] theorem pullbackSnd_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.snd β₁ β₂).comp (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₂ := by
  ext k
  rfl

/-- If `φ₁` is injective, then the canonical map into the concrete pullback is injective. -/
theorem pullbackLift_injective_of_left_injective (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k))
    (hφ₁ : Function.Injective φ₁) :
    Function.Injective (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) := by
  intro x y hxy
  apply hφ₁
  simpa using congrArg (fun z => FiberProduct.fst β₁ β₂ z) hxy

/-- If `φ₂` is injective, then the canonical map into the concrete pullback is injective. -/
theorem pullbackLift_injective_of_right_injective (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k))
    (hφ₂ : Function.Injective φ₂) :
    Function.Injective (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) := by
  intro x y hxy
  apply hφ₂
  simpa using congrArg (fun z => FiberProduct.snd β₁ β₂ z) hxy

/-- FiberProduct.carrier squares in the category of groups.
-/
def IsPullbackSquare (α₁ : G →* H₁) (α₂ : G →* H₂)
    (β₁ : H₁ →* H) (β₂ : H₂ →* H) : Prop :=
  β₁.comp α₁ = β₂.comp α₂ ∧
    ∀ ⦃K : Type v⦄ [Group K] (φ₁ : K →* H₁) (φ₂ : K →* H₂),
      β₁.comp φ₁ = β₂.comp φ₂ →
      ∃! φ : K →* G, α₁.comp φ = φ₁ ∧ α₂.comp φ = φ₂

/-- A commutative square of groups as a categorical pullback cone in `GrpCat`. -/
def groupPullbackSquareCone (α₁ : G →* H₁) (α₂ : G →* H₂)
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hcomm : β₁.comp α₁ = β₂.comp α₂) :
    PullbackCone (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
  PullbackCone.mk (GrpCat.ofHom α₁) (GrpCat.ofHom α₂) (by
    apply GrpCat.hom_ext
    exact hcomm)

/-- Chosen morphism induced by the pullback universal property. -/
noncomputable def IsPullbackSquare.desc
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) : K →* G :=
  Classical.choose (ExistsUnique.exists (hpb.2 φ₁ φ₂ hφ))

/-- Specification of the chosen pullback descent map. -/
theorem IsPullbackSquare.desc_spec
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₁.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) = φ₁ ∧
      α₂.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hpb.2 φ₁ φ₂ hφ))

/-- Left composite of the chosen pullback descent map. -/
@[simp 900] theorem IsPullbackSquare.desc_left
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₁.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) = φ₁ :=
  (IsPullbackSquare.desc_spec hpb φ₁ φ₂ hφ).1

/-- Right composite of the chosen pullback descent map. -/
@[simp 900] theorem IsPullbackSquare.desc_right
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₂.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) = φ₂ :=
  (IsPullbackSquare.desc_spec hpb φ₁ φ₂ hφ).2

/-- Uniqueness of the chosen pullback descent map. -/
theorem IsPullbackSquare.desc_uniq
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂)
    {ψ : K →* G}
    (hψ : α₁.comp ψ = φ₁ ∧ α₂.comp ψ = φ₂) :
    ψ = IsPullbackSquare.desc hpb φ₁ φ₂ hφ := by
  rcases hpb.2 φ₁ φ₂ hφ with ⟨u, hu, huuniq⟩
  have hψ' : ψ = u := huuniq _ hψ
  have hdesc : IsPullbackSquare.desc hpb φ₁ φ₂ hφ = u :=
    huuniq _ (IsPullbackSquare.desc_spec hpb φ₁ φ₂ hφ)
  exact hψ'.trans hdesc.symm

/-- The hand-written group pullback property gives a categorical `IsLimit` cone in `GrpCat`. -/
noncomputable def isLimit_groupPullbackSquareCone_of_isPullbackSquare
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂) :
    IsLimit (groupPullbackSquareCone α₁ α₂ β₁ β₂ hpb.1) := by
  refine PullbackCone.IsLimit.mk (by
    apply GrpCat.hom_ext
    exact hpb.1) ?lift ?fac_left ?fac_right ?uniq
  · intro s
    exact GrpCat.ofHom <|
      IsPullbackSquare.desc hpb s.fst.hom s.snd.hom (by
        exact congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition)
  · intro s
    apply GrpCat.hom_ext
    exact IsPullbackSquare.desc_left hpb s.fst.hom s.snd.hom
      (by exact congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition)
  · intro s
    apply GrpCat.hom_ext
    exact IsPullbackSquare.desc_right hpb s.fst.hom s.snd.hom
      (by exact congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition)
  · intro s m hfst hsnd
    apply GrpCat.hom_ext
    apply IsPullbackSquare.desc_uniq hpb s.fst.hom s.snd.hom
      (by exact congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition)
    constructor
    · exact congrArg (fun f : s.pt ⟶ GrpCat.of H₁ => f.hom) hfst
    · exact congrArg (fun f : s.pt ⟶ GrpCat.of H₂ => f.hom) hsnd

/-- A categorical `IsLimit` cone in `GrpCat` gives the hand-written group pullback property. -/
noncomputable def isPullbackSquare_of_isLimit_groupPullbackSquareCone
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    (hcomm : β₁.comp α₁ = β₂.comp α₂)
    (hlim : IsLimit (groupPullbackSquareCone α₁ α₂ β₁ β₂ hcomm)) :
    IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂ := by
  refine ⟨hcomm, ?_⟩
  intro K _ φ₁ φ₂ hφ
  let s : PullbackCone (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
    PullbackCone.mk (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂) (by
      apply GrpCat.hom_ext
      exact hφ)
  let φ : K →* G := (PullbackCone.IsLimit.lift hlim (GrpCat.ofHom φ₁)
    (GrpCat.ofHom φ₂) (by
      apply GrpCat.hom_ext
      exact hφ)).hom
  refine ⟨φ, ?_, ?_⟩
  · constructor
    · exact congrArg (fun f : GrpCat.of K ⟶ GrpCat.of H₁ => f.hom)
        (PullbackCone.IsLimit.lift_fst hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂) (by
          apply GrpCat.hom_ext
          exact hφ))
    · exact congrArg (fun f : GrpCat.of K ⟶ GrpCat.of H₂ => f.hom)
        (PullbackCone.IsLimit.lift_snd hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂) (by
          apply GrpCat.hom_ext
          exact hφ))
  · intro ψ hψ
    exact congrArg (fun f : GrpCat.of K ⟶ GrpCat.of G => f.hom) <| by
      change GrpCat.ofHom ψ =
        PullbackCone.IsLimit.lift hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂) (by
          apply GrpCat.hom_ext
          exact hφ)
      apply PullbackCone.IsLimit.hom_ext hlim
      · apply GrpCat.hom_ext
        calc
          (GrpCat.ofHom ψ ≫ (groupPullbackSquareCone α₁ α₂ β₁ β₂ hcomm).fst).hom =
              α₁.comp ψ := rfl
          _ = φ₁ := hψ.1
          _ = (GrpCat.ofHom φ₁).hom := rfl
          _ =
              (PullbackCone.IsLimit.lift hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂) (by
                    apply GrpCat.hom_ext
                    exact hφ) ≫
                  (groupPullbackSquareCone α₁ α₂ β₁ β₂ hcomm).fst).hom := by
                symm
                exact congrArg (fun f : GrpCat.of K ⟶ GrpCat.of H₁ => f.hom)
                  (PullbackCone.IsLimit.lift_fst hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂)
                    (by
                      apply GrpCat.hom_ext
                      exact hφ))
      · apply GrpCat.hom_ext
        calc
          (GrpCat.ofHom ψ ≫ (groupPullbackSquareCone α₁ α₂ β₁ β₂ hcomm).snd).hom =
              α₂.comp ψ := rfl
          _ = φ₂ := hψ.2
          _ = (GrpCat.ofHom φ₂).hom := rfl
          _ =
              (PullbackCone.IsLimit.lift hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂) (by
                    apply GrpCat.hom_ext
                    exact hφ) ≫
                  (groupPullbackSquareCone α₁ α₂ β₁ β₂ hcomm).snd).hom := by
                symm
                exact congrArg (fun f : GrpCat.of K ⟶ GrpCat.of H₂ => f.hom)
                  (PullbackCone.IsLimit.lift_snd hlim (GrpCat.ofHom φ₁) (GrpCat.ofHom φ₂)
                    (by
                      apply GrpCat.hom_ext
                      exact hφ))

/-- Same-universe hand-written group pullback squares are exactly categorical limit cones in
`GrpCat`, up to the choice of `IsLimit` data. -/
theorem isPullbackSquare_iff_nonempty_isLimit_groupPullbackSquareCone
    {α₁ : G →* H₁} {α₂ : G →* H₂}
    {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    (hcomm : β₁.comp α₁ = β₂.comp α₂) :
    IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂ ↔
      Nonempty (IsLimit (groupPullbackSquareCone α₁ α₂ β₁ β₂ hcomm)) := by
  constructor
  · intro hpb
    exact ⟨isLimit_groupPullbackSquareCone_of_isPullbackSquare hpb⟩
  · rintro ⟨hlim⟩
    exact isPullbackSquare_of_isLimit_groupPullbackSquareCone hcomm hlim

/-- Two homomorphisms into the concrete pullback are equal once both coordinates agree. -/
theorem FiberProduct.hom_ext {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    {ψ ψ' : K →* FiberProduct.carrier β₁ β₂}
    (h₁ : ∀ k, FiberProduct.fst β₁ β₂ (ψ k) = FiberProduct.fst β₁ β₂ (ψ' k))
    (h₂ : ∀ k, FiberProduct.snd β₁ β₂ (ψ k) = FiberProduct.snd β₁ β₂ (ψ' k)) :
    ψ = ψ' := by
  apply MonoidHom.ext
  intro k
  exact Subtype.ext <| Prod.ext (h₁ k) (h₂ k)

namespace FiberProduct

/-- Transport a concrete fiber product across equal cospan maps. -/
def congr {β₁ β₁' : H₁ →* H} {β₂ β₂' : H₂ →* H}
    (h₁ : β₁ = β₁') (h₂ : β₂ = β₂') :
    carrier β₁ β₂ ≃* carrier β₁' β₂' := by
  subst β₁'
  subst β₂'
  exact MulEquiv.refl _

/-- The first projection composed with a fiber-product lift is the left map. -/
@[simp 900] theorem fst_lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (fst β₁ β₂).comp (lift β₁ β₂ φ₁ φ₂ h) = φ₁ :=
  pullbackFst_pullbackLift β₁ β₂ φ₁ φ₂ h

/-- The second projection composed with a fiber-product lift is the right map. -/
@[simp 900] theorem snd_lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (snd β₁ β₂).comp (lift β₁ β₂ φ₁ φ₂ h) = φ₂ :=
  pullbackSnd_pullbackLift β₁ β₂ φ₁ φ₂ h

@[simp 900] theorem fst_lift_apply (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    fst β₁ β₂ (lift β₁ β₂ φ₁ φ₂ h k) = φ₁ k :=
  rfl

@[simp 900] theorem snd_lift_apply (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    snd β₁ β₂ (lift β₁ β₂ φ₁ φ₂ h k) = φ₂ k :=
  rfl

end FiberProduct

/-- The concrete pullback is reconstructed from its two projections by the canonical lift. -/
@[simp 900] theorem pullbackLift_eta {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (ψ : K →* FiberProduct.carrier β₁ β₂) :
    FiberProduct.lift β₁ β₂
      ((FiberProduct.fst β₁ β₂).comp ψ)
      ((FiberProduct.snd β₁ β₂).comp ψ)
      (fun k => by exact (ψ k).2) = ψ := by
  apply FiberProduct.hom_ext
  · intro k
    rfl
  · intro k
    rfl

/-- The concrete pullback satisfies the pullback universal property.
-/
theorem pullback_isPullback (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    IsPullbackSquare (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂) β₁ β₂ := by
  refine ⟨?_, ?_⟩
  · ext x
    exact x.2
  · intro K _ φ₁ φ₂ hφ
    let hφfun : ∀ k : K, β₁ (φ₁ k) = β₂ (φ₂ k) := fun k =>
      DFunLike.congr_fun hφ k
    refine ⟨FiberProduct.lift (K := K) β₁ β₂ φ₁ φ₂ hφfun, ?_, ?_⟩
    · exact ⟨pullbackFst_pullbackLift (K := K) β₁ β₂ φ₁ φ₂ hφfun,
        pullbackSnd_pullbackLift (K := K) β₁ β₂ φ₁ φ₂ hφfun⟩
    · intro ψ hψ
      have hfst :
          (FiberProduct.fst β₁ β₂).comp ψ =
            (FiberProduct.fst β₁ β₂).comp
              (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
        calc
          (FiberProduct.fst β₁ β₂).comp ψ = φ₁ := hψ.1
          _ =
              (FiberProduct.fst β₁ β₂).comp
                (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
              symm
              exact pullbackFst_pullbackLift β₁ β₂ φ₁ φ₂
                (fun k => DFunLike.congr_fun hφ k)
      have hsnd :
          (FiberProduct.snd β₁ β₂).comp ψ =
            (FiberProduct.snd β₁ β₂).comp
              (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
        calc
          (FiberProduct.snd β₁ β₂).comp ψ = φ₂ := hψ.2
          _ =
              (FiberProduct.snd β₁ β₂).comp
                (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
              symm
              exact pullbackSnd_pullbackLift β₁ β₂ φ₁ φ₂
                (fun k => DFunLike.congr_fun hφ k)
      exact FiberProduct.hom_ext
        (fun k => by
          exact congrArg (fun f : K →* H₁ => f k) hfst)
        (fun k => by
          exact congrArg (fun f : K →* H₂ => f k) hsnd)

/-- Symmetry of the concrete pullback. -/
def pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    FiberProduct.carrier β₁ β₂ ≃* FiberProduct.carrier β₂ β₁ where
  toFun := fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩
  invFun := fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  map_mul' := by
    intro x y
    apply Subtype.ext
    rfl

/-- The first projection after swapping equals the original second projection. -/
@[simp] theorem pullbackFst_pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (x : FiberProduct.carrier β₁ β₂) :
    FiberProduct.fst β₂ β₁ (pullbackSwap β₁ β₂ x) = FiberProduct.snd β₁ β₂ x :=
  rfl

/-- The second projection after swapping equals the original first projection. -/
@[simp] theorem pullbackSnd_pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (x : FiberProduct.carrier β₁ β₂) :
    FiberProduct.snd β₂ β₁ (pullbackSwap β₁ β₂ x) = FiberProduct.fst β₁ β₂ x :=
  rfl

/-- The symmetry equivalence is involutive. -/
@[simp] theorem pullbackSwap_symm (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    (pullbackSwap β₁ β₂).symm = pullbackSwap β₂ β₁ :=
  rfl

/-- If `β₂` is surjective, then the first pullback projection is surjective. -/
theorem pullbackFst_surjective_of_right_surjective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₂ : Function.Surjective β₂) :
    Function.Surjective (FiberProduct.fst β₁ β₂) := by
  intro x
  rcases hβ₂ (β₁ x) with ⟨y, hy⟩
  refine ⟨⟨(x, y), ?_⟩, rfl⟩
  simp only [mem_pullbackSubgroup_iff, hy]

/-- If `β₁` is surjective, then the second pullback projection is surjective. -/
theorem pullbackSnd_surjective_of_left_surjective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₁ : Function.Surjective β₁) :
    Function.Surjective (FiberProduct.snd β₁ β₂) := by
  intro y
  rcases hβ₁ (β₂ y) with ⟨x, hx⟩
  refine ⟨⟨(x, y), ?_⟩, rfl⟩
  simp only [mem_pullbackSubgroup_iff, hx]

/-- If `β₂` is injective, then the first pullback projection is injective. -/
theorem pullbackFst_injective_of_right_injective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₂ : Function.Injective β₂) :
    Function.Injective (FiberProduct.fst β₁ β₂) := by
  intro x y hxy
  apply Subtype.ext
  exact Prod.ext hxy <| hβ₂ <| by
    calc
      β₂ x.1.2 = β₁ x.1.1 := x.2.symm
      _ = β₁ y.1.1 := by simpa using congrArg β₁ hxy
      _ = β₂ y.1.2 := y.2

/-- If `β₁` is injective, then the second pullback projection is injective. -/
theorem pullbackSnd_injective_of_left_injective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₁ : Function.Injective β₁) :
    Function.Injective (FiberProduct.snd β₁ β₂) := by
  intro x y hxy
  apply Subtype.ext
  exact Prod.ext (hβ₁ <| by
      calc
        β₁ x.1.1 = β₂ x.1.2 := x.2
        _ = β₂ y.1.2 := by simpa using congrArg β₂ hxy
        _ = β₁ y.1.1 := y.2.symm) hxy

/-- A square with a bijective comparison map to the concrete pullback is a pullback square. -/
theorem isPullbackSquare_of_bijective_toConcretePullback
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (τ : G →* FiberProduct.carrier β₁ β₂)
    (hτ : Function.Bijective τ)
    (h₁ : (FiberProduct.fst β₁ β₂).comp τ = α₁)
    (h₂ : (FiberProduct.snd β₁ β₂).comp τ = α₂) :
    IsPullbackSquare α₁ α₂ β₁ β₂ := by
  classical
  refine ⟨?_, ?_⟩
  · ext g
    have hτ₁ : FiberProduct.fst β₁ β₂ (τ g) = α₁ g := by
      simpa using congrArg (fun f : G →* H₁ => f g) h₁
    have hτ₂ : FiberProduct.snd β₁ β₂ (τ g) = α₂ g := by
      simpa using congrArg (fun f : G →* H₂ => f g) h₂
    calc
      β₁ (α₁ g) = β₁ (FiberProduct.fst β₁ β₂ (τ g)) := by rw [← hτ₁]
      _ = β₂ (FiberProduct.snd β₁ β₂ (τ g)) := (τ g).2
      _ = β₂ (α₂ g) := by rw [hτ₂]
  · intro K _ φ₁ φ₂ hφ
    let e : G ≃* FiberProduct.carrier β₁ β₂ := MulEquiv.ofBijective τ hτ
    let hφfun : ∀ k : K, β₁ (φ₁ k) = β₂ (φ₂ k) := fun k =>
      DFunLike.congr_fun hφ k
    let θ : K →* FiberProduct.carrier β₁ β₂ :=
      FiberProduct.lift (K := K) β₁ β₂ φ₁ φ₂ hφfun
    refine ⟨e.symm.toMonoidHom.comp θ, ?_, ?_⟩
    · constructor
      · ext k
        have hτ₁ : FiberProduct.fst β₁ β₂ (τ (e.symm (θ k))) = α₁ (e.symm (θ k)) := by
          simpa using congrArg (fun f : G →* H₁ => f (e.symm (θ k))) h₁
        calc
          α₁ (e.symm (θ k)) = FiberProduct.fst β₁ β₂ (τ (e.symm (θ k))) := by
            simpa using hτ₁.symm
          _ = FiberProduct.fst β₁ β₂ (θ k) := by
            rw [show τ (e.symm (θ k)) = θ k from e.apply_symm_apply (θ k)]
          _ = φ₁ k := by
            change
              FiberProduct.fst β₁ β₂
                (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k) = φ₁ k
            rfl
      · ext k
        have hτ₂ : FiberProduct.snd β₁ β₂ (τ (e.symm (θ k))) = α₂ (e.symm (θ k)) := by
          simpa using congrArg (fun f : G →* H₂ => f (e.symm (θ k))) h₂
        calc
          α₂ (e.symm (θ k)) = FiberProduct.snd β₁ β₂ (τ (e.symm (θ k))) := by
            simpa using hτ₂.symm
          _ = FiberProduct.snd β₁ β₂ (θ k) := by
            rw [show τ (e.symm (θ k)) = θ k from e.apply_symm_apply (θ k)]
          _ = φ₂ k := by
            change
              FiberProduct.snd β₁ β₂
                (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k) = φ₂ k
            rfl
    · intro ψ hψ
      have hcoord : τ.comp ψ = θ := by
        apply FiberProduct.hom_ext
        · intro k
          have hτ₁ : FiberProduct.fst β₁ β₂ (τ (ψ k)) = α₁ (ψ k) := by
            simpa using congrArg (fun f : G →* H₁ => f (ψ k)) h₁
          have hψ₁ : α₁ (ψ k) = φ₁ k := by
            simpa using congrArg (fun f : K →* H₁ => f k) hψ.1
          calc
            FiberProduct.fst β₁ β₂ ((τ.comp ψ) k) = α₁ (ψ k) := by
              simpa [MonoidHom.comp_apply] using hτ₁
            _ = φ₁ k := hψ₁
            _ = FiberProduct.fst β₁ β₂ (θ k) := by
              change
                φ₁ k =
                  FiberProduct.fst β₁ β₂
                    (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k)
              rfl
        · intro k
          have hτ₂ : FiberProduct.snd β₁ β₂ (τ (ψ k)) = α₂ (ψ k) := by
            simpa using congrArg (fun f : G →* H₂ => f (ψ k)) h₂
          have hψ₂ : α₂ (ψ k) = φ₂ k := by
            simpa using congrArg (fun f : K →* H₂ => f k) hψ.2
          calc
            FiberProduct.snd β₁ β₂ ((τ.comp ψ) k) = α₂ (ψ k) := by
              simpa [MonoidHom.comp_apply] using hτ₂
            _ = φ₂ k := hψ₂
            _ = FiberProduct.snd β₁ β₂ (θ k) := by
              change
                φ₂ k =
                  FiberProduct.snd β₁ β₂
                    (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k)
              rfl
      ext k
      apply hτ.1
      calc
        τ (ψ k) = (τ.comp ψ) k := by rfl
        _ = θ k := by
          exact congrArg (fun f : K →* FiberProduct.carrier β₁ β₂ => f k) hcoord
        _ = τ ((e.symm.toMonoidHom.comp θ) k) := by
          change θ k = τ (e.symm (θ k))
          symm
          exact e.apply_symm_apply (θ k)

/-- The canonical map from an abstract pullback square into the concrete subgroup pullback. -/
def IsPullbackSquare.toConcretePullback
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂) :
    G →* FiberProduct.carrier β₁ β₂ :=
  FiberProduct.lift β₁ β₂ α₁ α₂ (fun g => by
    exact DFunLike.congr_fun hpb.1 g)

/-- The canonical comparison map from the concrete pullback to itself is the identity.
-/
@[simp 900] theorem IsPullbackSquare.toConcretePullback_self
    (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    IsPullbackSquare.toConcretePullback (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂) β₁ β₂
        (pullback_isPullback.{u, u} β₁ β₂) =
      MonoidHom.id (FiberProduct.carrier β₁ β₂) := by
  simpa [IsPullbackSquare.toConcretePullback] using
    (pullbackLift_eta (β₁ := β₁) (β₂ := β₂) (ψ := MonoidHom.id (FiberProduct.carrier β₁ β₂)))

/-- The first coordinate of the canonical comparison map recovers `α₁`. -/
@[simp 900] theorem IsPullbackSquare.fst_toConcretePullback
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂) :
    (FiberProduct.fst β₁ β₂).comp (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb) = α₁ := by
  ext g
  rfl

/-- The second coordinate of the canonical comparison map recovers `α₂`. -/
@[simp 900] theorem IsPullbackSquare.snd_toConcretePullback
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂) :
    (FiberProduct.snd β₁ β₂).comp (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb) = α₂ := by
  ext g
  rfl

/-- Any abstract pullback square is canonically bijective to the concrete pullback. -/
theorem IsPullbackSquare.bijective_toConcretePullback
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂) :
    Function.Bijective (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb) := by
  let ψ : FiberProduct.carrier β₁ β₂ →* G :=
    IsPullbackSquare.desc hpb (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂)
      ((pullback_isPullback.{u, u} β₁ β₂).1)
  have hψfst : α₁.comp ψ = FiberProduct.fst β₁ β₂ := by
    change
      α₁.comp
          (IsPullbackSquare.desc hpb (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂)
            ((pullback_isPullback.{u, u} β₁ β₂).1)) =
        FiberProduct.fst β₁ β₂
    exact IsPullbackSquare.desc_left hpb (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂)
      ((pullback_isPullback.{u, u} β₁ β₂).1)
  have hψsnd : α₂.comp ψ = FiberProduct.snd β₁ β₂ := by
    change
      α₂.comp
          (IsPullbackSquare.desc hpb (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂)
            ((pullback_isPullback.{u, u} β₁ β₂).1)) =
        FiberProduct.snd β₁ β₂
    exact IsPullbackSquare.desc_right hpb (FiberProduct.fst β₁ β₂) (FiberProduct.snd β₁ β₂)
      ((pullback_isPullback.{u, u} β₁ β₂).1)
  have hleft :
      (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp ψ =
        MonoidHom.id (FiberProduct.carrier β₁ β₂) := by
    apply FiberProduct.hom_ext
    · intro x
      calc
        FiberProduct.fst β₁ β₂ ((IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp ψ x)
            = α₁ (ψ x) := by
                rfl
        _ = FiberProduct.fst β₁ β₂ x := by
              exact congrArg (fun f : FiberProduct.carrier β₁ β₂ →* H₁ => f x) hψfst
    · intro x
      calc
        FiberProduct.snd β₁ β₂ ((IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp ψ x)
            = α₂ (ψ x) := by
                rfl
        _ = FiberProduct.snd β₁ β₂ x := by
              exact congrArg (fun f : FiberProduct.carrier β₁ β₂ →* H₂ => f x) hψsnd
  have hright_desc :
      ψ.comp (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb) =
        IsPullbackSquare.desc hpb α₁ α₂ hpb.1 := by
    apply IsPullbackSquare.desc_uniq hpb α₁ α₂ hpb.1
    constructor
    · ext g
      calc
        α₁ ((ψ.comp (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb)) g)
            = FiberProduct.fst β₁ β₂ (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb g) := by
                exact congrArg (fun f : FiberProduct.carrier β₁ β₂ →* H₁ =>
                  f (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb g)) hψfst
        _ = α₁ g := by
              rfl
    · ext g
      calc
        α₂ ((ψ.comp (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb)) g)
            = FiberProduct.snd β₁ β₂ (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb g) := by
                exact congrArg (fun f : FiberProduct.carrier β₁ β₂ →* H₂ =>
                  f (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb g)) hψsnd
        _ = α₂ g := by
              rfl
  have hself : IsPullbackSquare.desc hpb α₁ α₂ hpb.1 = MonoidHom.id G := by
    symm
    exact IsPullbackSquare.desc_uniq hpb α₁ α₂ hpb.1 (by simp only [MonoidHom.comp_id, and_self])
  have hright :
      ψ.comp (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb) = MonoidHom.id G := by
    exact hright_desc.trans hself
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hx : ψ (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb x) = x := by
      simpa using congrArg (fun f : G →* G => f x) hright
    have hy : ψ (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb y) = y := by
      simpa using congrArg (fun f : G →* G => f y) hright
    calc
      x = ψ (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb x) := hx.symm
      _ = ψ (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb y) := by simpa using congrArg ψ hxy
      _ = y := hy
  · intro x
    refine ⟨ψ x, ?_⟩
    simpa using congrArg (fun f : FiberProduct.carrier β₁ β₂ →* FiberProduct.carrier β₁ β₂ => f x) hleft

/-- Any abstract pullback square is canonically isomorphic to the concrete pullback. -/
noncomputable def IsPullbackSquare.concretePullbackEquiv
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂) :
    G ≃* FiberProduct.carrier β₁ β₂ :=
  MulEquiv.ofBijective
    (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb)
    (IsPullbackSquare.bijective_toConcretePullback α₁ α₂ β₁ β₂ hpb)

/-- The first coordinate of the pullback comparison equivalence is `α₁`. -/
@[simp] theorem IsPullbackSquare.concretePullbackEquiv_fst
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂) :
    (FiberProduct.fst β₁ β₂).comp (IsPullbackSquare.concretePullbackEquiv α₁ α₂ β₁ β₂ hpb).toMonoidHom = α₁ := by
  ext g
  rfl

/-- The second coordinate of the pullback comparison equivalence is `α₂`. -/
@[simp] theorem IsPullbackSquare.concretePullbackEquiv_snd
    (α₁ : G →* H₁) (α₂ : G →* H₂) (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂) :
    (FiberProduct.snd β₁ β₂).comp (IsPullbackSquare.concretePullbackEquiv α₁ α₂ β₁ β₂ hpb).toMonoidHom = α₂ := by
  ext g
  rfl

/-- A square is a pullback iff its canonical map to the concrete pullback is bijective. -/
theorem isPullbackSquare_iff_bijective_toConcretePullback
    {α₁ : G →* H₁} {α₂ : G →* H₂} {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    (hcomm : β₁.comp α₁ = β₂.comp α₂) :
    IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂ ↔
      Function.Bijective (FiberProduct.lift β₁ β₂ α₁ α₂ (fun g => by
        exact DFunLike.congr_fun hcomm g)) := by
  constructor
  · intro hpb
    simpa [IsPullbackSquare.toConcretePullback] using
      (IsPullbackSquare.bijective_toConcretePullback α₁ α₂ β₁ β₂ hpb)
  · intro hbij
    exact isPullbackSquare_of_bijective_toConcretePullback
      α₁ α₂ β₁ β₂
      (FiberProduct.lift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g))
      hbij
      (pullbackFst_pullbackLift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g))
      (pullbackSnd_pullbackLift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g))

/-- The canonical comparison map sends the chosen pullback descent map to the concrete
pullback lift. -/
@[simp 900] theorem IsPullbackSquare.toConcretePullback_comp_desc
    (α₁ : G →* H₁) (α₂ : G →* H₂)
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare α₁ α₂ β₁ β₂)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) =
      FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) := by
  apply FiberProduct.hom_ext
  · intro k
    have hleft :
        (FiberProduct.fst β₁ β₂).comp
            ((IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ)) = φ₁ := by
      calc
        (FiberProduct.fst β₁ β₂).comp
            ((IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ))
            = ((FiberProduct.fst β₁ β₂).comp
                (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb)).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) := by
                  rfl
        _ = α₁.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) := by
              rw [IsPullbackSquare.fst_toConcretePullback α₁ α₂ β₁ β₂ hpb]
        _ = φ₁ := IsPullbackSquare.desc_left hpb φ₁ φ₂ hφ
    have hright :
        (FiberProduct.fst β₁ β₂).comp
            (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) = φ₁ :=
      pullbackFst_pullbackLift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)
    exact congrArg (fun f : K →* H₁ => f k) (hleft.trans hright.symm)
  · intro k
    have hleft :
        (FiberProduct.snd β₁ β₂).comp
            ((IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ)) = φ₂ := by
      calc
        (FiberProduct.snd β₁ β₂).comp
            ((IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ))
            = ((FiberProduct.snd β₁ β₂).comp
                (IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb)).comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) := by
                  rfl
        _ = α₂.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hφ) := by
              rw [IsPullbackSquare.snd_toConcretePullback α₁ α₂ β₁ β₂ hpb]
        _ = φ₂ := IsPullbackSquare.desc_right hpb φ₁ φ₂ hφ
    have hright :
        (FiberProduct.snd β₁ β₂).comp
            (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) = φ₂ :=
      pullbackSnd_pullbackLift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)
    exact congrArg (fun f : K →* H₂ => f k) (hleft.trans hright.symm)

/-- For an abstract pullback square, surjectivity of the chosen descent map is equivalent to
surjectivity of the corresponding map into the concrete pullback. -/
theorem IsPullbackSquare.surjective_desc_iff_surjective_lift
    (α₁ : G →* H₁) (α₂ : G →* H₂)
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (IsPullbackSquare.desc hpb φ₁ φ₂ hcomp) ↔
      Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun a => DFunLike.congr_fun hcomp a)) := by
  let c : G →* FiberProduct.carrier β₁ β₂ := IsPullbackSquare.toConcretePullback α₁ α₂ β₁ β₂ hpb
  have hc : Function.Bijective c := IsPullbackSquare.bijective_toConcretePullback α₁ α₂ β₁ β₂ hpb
  have hcomm :
      c.comp (IsPullbackSquare.desc hpb φ₁ φ₂ hcomp) =
        FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hcomp a) := by
    simp only [toConcretePullback_comp_desc, c]
  constructor
  · intro hdesc z
    rcases hc.2 z with ⟨g, rfl⟩
    rcases hdesc g with ⟨a, rfl⟩
    exact ⟨a, (DFunLike.congr_fun hcomm a).symm⟩
  · intro hlift g
    rcases hlift (c g) with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply hc.1
    calc
      c (IsPullbackSquare.desc hpb φ₁ φ₂ hcomp a) =
          FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hcomp a) a := by
            exact DFunLike.congr_fun hcomm a
      _ = c g := ha

/-- Algebraic abstract-pullback form of the surjectivity criterion. -/
theorem IsPullbackSquare.surjective_desc_of_ker_eq
    (α₁ : G →* H₁) (α₂ : G →* H₂)
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hpb : IsPullbackSquare.{u, u} α₁ α₂ β₁ β₂)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker) :
    Function.Surjective (IsPullbackSquare.desc hpb φ₁ φ₂ hcomp) := by
  exact (IsPullbackSquare.surjective_desc_iff_surjective_lift
    α₁ α₂ β₁ β₂ hpb φ₁ φ₂ hcomp).2
      ((pullbackLift_surjective_iff_ker_eq β₁ β₂ φ₁ φ₂ hφ₁ hφ₂ hcomp).2 hker)

/-- Algebraic surjectivity criterion for the canonical map into the pullback. -/
theorem surjective_pullbackLift_of_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  exact (pullbackLift_surjective_iff_ker_eq β₁ β₂ φ₁ φ₂ hφ₁ hφ₂ hcomp).2 hker

/-- Reusable bijectivity package for the canonical pullback map, using injectivity of `φ₁`. -/
theorem bijective_pullbackLift_of_left_injective_of_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁surj : Function.Surjective φ₁) (hφ₂surj : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker)
    (hφ₁inj : Function.Injective φ₁) :
    Function.Bijective (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  refine ⟨?_, ?_⟩
  · exact pullbackLift_injective_of_left_injective β₁ β₂ φ₁ φ₂
      (fun a => DFunLike.congr_fun hcomp a) hφ₁inj
  · exact (pullbackLift_surjective_iff_ker_eq
      β₁ β₂ φ₁ φ₂ hφ₁surj hφ₂surj hcomp).2 hker

/-- Reusable bijectivity package for the canonical pullback map, using injectivity of `φ₂`. -/
theorem bijective_pullbackLift_of_right_injective_of_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁surj : Function.Surjective φ₁) (hφ₂surj : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker)
    (hφ₂inj : Function.Injective φ₂) :
    Function.Bijective (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  refine ⟨?_, ?_⟩
  · exact pullbackLift_injective_of_right_injective β₁ β₂ φ₁ φ₂
      (fun a => DFunLike.congr_fun hcomp a) hφ₂inj
  · exact (pullbackLift_surjective_iff_ker_eq
      β₁ β₂ φ₁ φ₂ hφ₁surj hφ₂surj hcomp).2 hker

end



end ProCGroups.Categorical
