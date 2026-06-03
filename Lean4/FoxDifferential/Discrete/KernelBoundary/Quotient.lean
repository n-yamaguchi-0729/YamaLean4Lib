import FoxDifferential.Discrete.KernelBoundary.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/KernelBoundary/Quotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Kernel-boundary quotient and augmentation exactness

The quotient of the relative differential module by the kernel-boundary image maps to the
identity differential module and to the augmentation ideal.  The result is the algebraic
head-exactness bridge used by Crowell exact sequences.

This file contains the quotient/exactness bridge for the discrete Crowell sequence and the
kernel-side group-homology infrastructure used to prove injectivity of the head map.
-/

namespace FoxDifferential

noncomputable section

open FoxDifferential

variable {H G : Type*} [Group H] [Group G]

/-- The quotient of `A_ψ` by the image of the head map. -/
abbrev HeadQuotientOfSurjective (ψ : G →* H) (hψ : Function.Surjective ψ) : Type _ :=
  DifferentialModule ψ ⧸ kernelAbelianizationBoundaryRangeOfSurjective ψ hψ

/-- The canonical map from `A_ψ` to the derived module of the identity on `H`. -/
def toIdentityDifferentialModule (ψ : G →* H) :
    DifferentialModule ψ →ₗ[GroupRing H] DifferentialModule (MonoidHom.id H) :=
  lift ψ (fun g => universalDifferential (MonoidHom.id H) (ψ g)) (by
    intro g₁ g₂
    simpa [map_mul] using universalDifferential_mul (MonoidHom.id H) (ψ g₁) (ψ g₂))

@[simp]
theorem toIdentityDifferentialModule_d (ψ : G →* H) (g : G) :
    toIdentityDifferentialModule ψ (universalDifferential ψ g) = universalDifferential (MonoidHom.id H) (ψ g) := by
  simpa [toIdentityDifferentialModule] using
    lift_d (A := DifferentialModule (MonoidHom.id H)) ψ
      (fun g => universalDifferential (MonoidHom.id H) (ψ g)) (by
        intro g₁ g₂
        simpa [map_mul] using universalDifferential_mul (MonoidHom.id H) (ψ g₁) (ψ g₂)) g

theorem toAugmentationIdeal_id_comp_toIdentityDifferentialModule
    (ψ : G →* H) :
    (toAugmentationIdeal (H := H) (MonoidHom.id H)).comp (toIdentityDifferentialModule ψ) =
      toAugmentationIdeal (H := H) ψ := by
  apply hom_ext ψ
  intro g
  simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, LinearMap.coe_comp, Function.comp_apply,
  toIdentityDifferentialModule_d, toAugmentationIdeal_d, augmentationBoundary, groupRingBoundary, MonoidHom.id_apply,
  MonoidAlgebra.of_apply]

@[simp]
theorem toIdentityDifferentialModule_kernelAbelianizationBoundaryLinearOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : KernelAbelianizationAdd ψ) :
    toIdentityDifferentialModule ψ
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) = 0 := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  rw [kernelAbelianizationBoundaryLinearOfSurjective_apply]
  change
    (fun y : Abelianization ψ.ker =>
      toIdentityDifferentialModule ψ (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul y)) = 0)
      (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change toIdentityDifferentialModule ψ
      (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of n))) = 0
  have hinner :
      toIdentityDifferentialModule ψ
          (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of n))) =
        toIdentityDifferentialModule ψ (universalDifferential ψ n.1) := by
    exact congrArg (toIdentityDifferentialModule ψ) (kernelAbelianizationBoundaryAdd_of ψ n)
  rw [hinner, toIdentityDifferentialModule_d, n.2, universalDifferential_one]

theorem kernelAbelianizationBoundaryRangeOfSurjective_le_ker_toIdentityDiffModule
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ ≤
      LinearMap.ker (toIdentityDifferentialModule ψ) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  simpa [LinearMap.mem_ker] using
    toIdentityDifferentialModule_kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x

/-- The quotient map `A_ψ / im(head) → A_id`. -/
def headQuotientToIdentityDifferentialModule
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    HeadQuotientOfSurjective ψ hψ →ₗ[GroupRing H] DifferentialModule (MonoidHom.id H) :=
  (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).liftQ
    (toIdentityDifferentialModule ψ)
    (kernelAbelianizationBoundaryRangeOfSurjective_le_ker_toIdentityDiffModule ψ hψ)

@[simp]
theorem headQuotientToIdentityDifferentialModule_mkQ
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : DifferentialModule ψ) :
    headQuotientToIdentityDifferentialModule ψ hψ
      ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ x) =
        toIdentityDifferentialModule ψ x := by
  rfl

/-- A section of `ψ`, viewed as a differential map into the head quotient. -/
def headQuotientSectionOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) :
    HeadQuotientOfSurjective ψ hψ :=
  (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ
    (universalDifferential ψ (Function.surjInv hψ h))

theorem headQuotientSectionOfSurjective_isDifferential
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    IsDifferentialMap (A := HeadQuotientOfSurjective ψ hψ) (MonoidHom.id H)
      (headQuotientSectionOfSurjective ψ hψ) := by
  intro h₁ h₂
  let s : H → G := Function.surjInv hψ
  let q : Submodule (GroupRing H) (DifferentialModule ψ) :=
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ
  have hs12 : ψ (s (h₁ * h₂)) = h₁ * h₂ := by
    simpa [s] using Function.surjInv_eq hψ (h₁ * h₂)
  let n : ψ.ker := ⟨s (h₁ * h₂) * (s h₁ * s h₂)⁻¹, by
    calc
      ψ (s (h₁ * h₂) * (s h₁ * s h₂)⁻¹)
          = ψ (s (h₁ * h₂)) * (ψ (s h₁ * s h₂))⁻¹ := by simp only [mul_inv_rev, map_mul, map_inv]
      _ = (h₁ * h₂) * (h₂⁻¹ * h₁⁻¹) := by
            rw [hs12]
            simp only [map_mul, Function.surjInv_eq hψ h₁, Function.surjInv_eq hψ h₂, mul_inv_rev, s]
      _ = 1 := by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]⟩
  have hn_zero : q.mkQ (universalDifferential ψ n.1) = 0 := by
    have hn_mem : universalDifferential ψ n.1 ∈ q := by
      letI := kernelAbelianizationModuleOfSurjective ψ hψ
      rw [← kernelAbelianizationBoundaryLinearOfSurjective_of (ψ := ψ) (hψ := hψ) n]
      exact LinearMap.mem_range_self _ _
    exact (Submodule.Quotient.mk_eq_zero (p := q) (x := universalDifferential ψ n.1)).2 hn_mem
  have hs :
      universalDifferential ψ (s (h₁ * h₂)) = universalDifferential ψ n.1 + universalDifferential ψ (s h₁ * s h₂) := by
    have hmul := universalDifferential_mul ψ n.1 (s h₁ * s h₂)
    have hψn : (MonoidAlgebra.of ℤ H (ψ n.1) : GroupRing H) = 1 := by
      rw [n.2, groupRing_of_one (H := H)]
    rw [hψn, one_smul] at hmul
    simpa [n, s, mul_assoc] using hmul
  have hq :
      q.mkQ (universalDifferential ψ (s (h₁ * h₂))) = q.mkQ (universalDifferential ψ (s h₁ * s h₂)) := by
    have hq' := congrArg q.mkQ hs
    simpa [map_add, hn_zero] using hq'
  calc
    headQuotientSectionOfSurjective ψ hψ (h₁ * h₂)
        = q.mkQ (universalDifferential ψ (s (h₁ * h₂))) := rfl
    _ = q.mkQ (universalDifferential ψ (s h₁ * s h₂)) := hq
    _ = q.mkQ (universalDifferential ψ (s h₁) + (MonoidAlgebra.of ℤ H (ψ (s h₁))) • universalDifferential ψ (s h₂)) := by
          rw [universalDifferential_mul]
    _ = headQuotientSectionOfSurjective ψ hψ h₁ +
          (MonoidAlgebra.of ℤ H h₁ : GroupRing H) •
            headQuotientSectionOfSurjective ψ hψ h₂ := by
          simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, Function.surjInv_eq hψ h₁,
  MonoidAlgebra.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
  headQuotientSectionOfSurjective, q, s]

/-- The inverse-direction map `A_id → A_ψ / im(head)` induced by a surjective section of `ψ`. -/
def fromIdentityDifferentialModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    DifferentialModule (MonoidHom.id H) →ₗ[GroupRing H] HeadQuotientOfSurjective ψ hψ :=
  lift (MonoidHom.id H) (headQuotientSectionOfSurjective ψ hψ)
    (headQuotientSectionOfSurjective_isDifferential ψ hψ)

@[simp]
theorem fromIdentityDifferentialModuleOfSurjective_d
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) :
    fromIdentityDifferentialModuleOfSurjective ψ hψ (universalDifferential (MonoidHom.id H) h) =
      headQuotientSectionOfSurjective ψ hψ h := by
  simpa [fromIdentityDifferentialModuleOfSurjective] using
    lift_d (A := HeadQuotientOfSurjective ψ hψ) (MonoidHom.id H)
      (headQuotientSectionOfSurjective ψ hψ)
      (headQuotientSectionOfSurjective_isDifferential ψ hψ) h

theorem headQuotientToIdentityDiffModule_fromIdentityDiffModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    (headQuotientToIdentityDifferentialModule ψ hψ).comp
      (fromIdentityDifferentialModuleOfSurjective ψ hψ) =
        LinearMap.id := by
  apply hom_ext (ψ := MonoidHom.id H)
  intro h
  rw [LinearMap.comp_apply, fromIdentityDifferentialModuleOfSurjective_d,
    headQuotientSectionOfSurjective, headQuotientToIdentityDifferentialModule_mkQ,
    toIdentityDifferentialModule_d]
  simp only [Function.surjInv_eq hψ h, relationSubmodule_eq_crossedDifferentialRelationSubmodule,
  LinearMap.id_coe, id_eq]

theorem fromIdentityDifferentialModuleOfSurjective_comp_toIdentityDifferentialModule
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    (fromIdentityDifferentialModuleOfSurjective ψ hψ).comp
      (toIdentityDifferentialModule ψ) =
        (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ := by
  apply hom_ext (ψ := ψ)
  intro g
  let s : H → G := Function.surjInv hψ
  let q : Submodule (GroupRing H) (DifferentialModule ψ) :=
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ
  let n : ψ.ker := ⟨g * (s (ψ g))⁻¹, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hψ (ψ g), mul_inv_cancel, s]⟩
  have hn_zero : q.mkQ (universalDifferential ψ n.1) = 0 := by
    have hn_mem : universalDifferential ψ n.1 ∈ q := by
      letI := kernelAbelianizationModuleOfSurjective ψ hψ
      rw [← kernelAbelianizationBoundaryLinearOfSurjective_of (ψ := ψ) (hψ := hψ) n]
      exact LinearMap.mem_range_self _ _
    exact (Submodule.Quotient.mk_eq_zero (p := q) (x := universalDifferential ψ n.1)).2 hn_mem
  have hgdecomp : universalDifferential ψ g = universalDifferential ψ n.1 + universalDifferential ψ (s (ψ g)) := by
    have hmul := universalDifferential_mul ψ n.1 (s (ψ g))
    have hψn : (MonoidAlgebra.of ℤ H (ψ n.1) : GroupRing H) = 1 := by
      rw [n.2, groupRing_of_one (H := H)]
    rw [hψn, one_smul] at hmul
    simpa [n, s, mul_assoc] using hmul
  have hq : q.mkQ (universalDifferential ψ g) = q.mkQ (universalDifferential ψ (s (ψ g))) := by
    have hq' := congrArg q.mkQ hgdecomp
    simpa [map_add, hn_zero] using hq'
  calc
    fromIdentityDifferentialModuleOfSurjective ψ hψ
        (toIdentityDifferentialModule ψ (universalDifferential ψ g))
        = q.mkQ (universalDifferential ψ (s (ψ g))) := by
            rw [toIdentityDifferentialModule_d, fromIdentityDifferentialModuleOfSurjective_d,
              headQuotientSectionOfSurjective]
    _ = q.mkQ (universalDifferential ψ g) := hq.symm

/-- The quotient `A_ψ / im(head)` is canonically identified with the derived module of `id_H`. -/
def headQuotientEquivIdentityDifferentialModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    HeadQuotientOfSurjective ψ hψ ≃ₗ[GroupRing H] DifferentialModule (MonoidHom.id H) where
  toLinearMap := headQuotientToIdentityDifferentialModule ψ hψ
  invFun := fromIdentityDifferentialModuleOfSurjective ψ hψ
  left_inv := by
    intro x
    have hcomp :
        (fromIdentityDifferentialModuleOfSurjective ψ hψ).comp
            (headQuotientToIdentityDifferentialModule ψ hψ) =
          LinearMap.id := by
      apply Submodule.linearMap_qext _
      simpa using
        fromIdentityDifferentialModuleOfSurjective_comp_toIdentityDifferentialModule ψ hψ
    exact LinearMap.congr_fun hcomp x
  right_inv := by
    intro x
    exact LinearMap.congr_fun
      (headQuotientToIdentityDiffModule_fromIdentityDiffModuleOfSurjective ψ hψ) x

/-- For a surjective `ψ`, the Crowell head quotient is the augmentation ideal. -/
def headQuotientEquivAugmentationIdealOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    HeadQuotientOfSurjective ψ hψ ≃ₗ[GroupRing H] augmentationIdeal H :=
  by
    classical
    exact
      (headQuotientEquivIdentityDifferentialModuleOfSurjective ψ hψ).trans
        (FoxDifferential.identityDifferentialModuleEquivAugmentationIdeal (H := H))

@[simp]
theorem headQuotientEquivAugmentationIdealOfSurjective_mkQ
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : DifferentialModule ψ) :
    headQuotientEquivAugmentationIdealOfSurjective ψ hψ
      ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ x) =
        toAugmentationIdeal (H := H) ψ x := by
  unfold headQuotientEquivAugmentationIdealOfSurjective
  rw [LinearEquiv.trans_apply]
  change (FoxDifferential.identityDifferentialModuleEquivAugmentationIdeal (H := H))
      (headQuotientToIdentityDifferentialModule ψ hψ
        ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ x)) = _
  rw [headQuotientToIdentityDifferentialModule_mkQ]
  have hid := congrArg
      (fun f : DifferentialModule (MonoidHom.id H) →ₗ[GroupRing H] augmentationIdeal H =>
        f (toIdentityDifferentialModule ψ x))
      (FoxDifferential.identityDifferentialModuleEquivAugmentationIdeal_toLinearMap (H := H))
  exact hid.trans <|
    LinearMap.congr_fun (toAugmentationIdeal_id_comp_toIdentityDifferentialModule (H := H) ψ) x

theorem kernelAbelianizationBoundaryRangeOfSurjective_eq_ker_toAugmentationIdeal
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ =
      LinearMap.ker (toAugmentationIdeal (H := H) ψ) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    change toAugmentationIdeal (H := H) ψ
        (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) = 0
    apply Subtype.ext
    exact toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective (H := H) ψ hψ x
  · intro y hy
    have hy0 : toAugmentationIdeal (H := H) ψ y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    have hq0 :
        headQuotientEquivAugmentationIdealOfSurjective ψ hψ
          ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ y) = 0 := by
      rw [headQuotientEquivAugmentationIdealOfSurjective_mkQ]
      exact hy0
    have hq : ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ y :
        HeadQuotientOfSurjective ψ hψ) = 0 := by
      exact (headQuotientEquivAugmentationIdealOfSurjective ψ hψ).injective
        (by simpa using hq0)
    exact (Submodule.Quotient.mk_eq_zero (p := kernelAbelianizationBoundaryRangeOfSurjective ψ hψ)
      (x := y)).1 hq

/-- Exactness at `A_ψ`, formulated against the augmentation ideal. -/
theorem exact_kernelAbelianizationBoundaryLinearOfSurjective_toAugmentationIdeal
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Function.Exact
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)
      (toAugmentationIdeal (H := H) ψ) := by
  intro y
  constructor
  · intro hy
    have hyker : y ∈ LinearMap.ker (toAugmentationIdeal (H := H) ψ) := by
      simpa [LinearMap.mem_ker] using hy
    rw [← kernelAbelianizationBoundaryRangeOfSurjective_eq_ker_toAugmentationIdeal
      (H := H) (ψ := ψ) hψ] at hyker
    exact hyker
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective (H := H) ψ hψ x

/-- Exactness at `A_ψ`, against the usual map `A_ψ → ℤ[H]`. -/
theorem exact_kernelAbelianizationBoundaryLinearOfSurjective_toGroupRing
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Function.Exact
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)
      (toGroupRing ψ) := by
  intro y
  constructor
  · intro hy
    have hy' : toAugmentationIdeal (H := H) ψ y = 0 := by
      apply Subtype.ext
      exact hy
    exact (exact_kernelAbelianizationBoundaryLinearOfSurjective_toAugmentationIdeal
      (H := H) ψ hψ y).1 hy'
  · rintro ⟨x, rfl⟩
    exact toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective (H := H) ψ hψ x
end

end FoxDifferential
