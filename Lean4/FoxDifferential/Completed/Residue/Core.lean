import FoxDifferential.Common.CrossedDifferentialModule
import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.CompletionMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Residue/Core.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Residue coefficient stages

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

/-- The residue group ring `(Z/nZ)[H]`. -/
abbrev ResidueGroupRing (n : ℕ) (H : Type*) : Type _ :=
  ModNCompletedGroupRing n H

section Basic

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The coefficient homomorphism `G -> (Z/nZ)[H]` induced by a group homomorphism
`ψ : G ->* H`. -/
def residueGroupRingScalar (n : ℕ) (ψ : G →* H) : G →* ResidueGroupRing n H :=
  (MonoidAlgebra.of (ModNCompletedCoeff n) H).comp ψ

/-- The residue coefficient homomorphism is `g ↦ [ψ g]`. -/
@[simp]
theorem residueGroupRingScalar_apply (n : ℕ) (ψ : G →* H) (g : G) :
    residueGroupRingScalar n ψ g =
      (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ g) : ResidueGroupRing n H) :=
  rfl

/-- The residue universal differential module attached to `ψ : G ->* H`. -/
abbrev ResidueDifferentialModule (n : ℕ) (ψ : G →* H) : Type _ :=
  CrossedDifferentialModule (residueGroupRingScalar n ψ)

/-- The universal residue crossed differential. -/
def residueUniversalDifferential (n : ℕ) (ψ : G →* H) (g : G) :
    ResidueDifferentialModule n ψ :=
  universalCrossedDifferential (residueGroupRingScalar n ψ) g

/-- The universal residue differential is a crossed differential. -/
theorem residueUniversalDifferential_isCrossedDifferential (n : ℕ) (ψ : G →* H) :
    IsCrossedDifferential
      (residueGroupRingScalar n ψ) (residueUniversalDifferential n ψ) := by
  exact universalCrossedDifferential_isCrossedDifferential (residueGroupRingScalar n ψ)

/-- The residue Fox boundary `g ↦ [ψ g] - 1`. -/
def residueGroupRingBoundary (n : ℕ) (ψ : G →* H) (g : G) : ResidueGroupRing n H :=
  MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ g) - 1

/-- The residue Fox boundary vanishes at the identity. -/
@[simp]
theorem residueGroupRingBoundary_one (n : ℕ) (ψ : G →* H) :
    residueGroupRingBoundary n ψ (1 : G) = 0 := by
  simp only [residueGroupRingBoundary, map_one, MonoidAlgebra.one_def, sub_self]

/-- The residue Fox boundary is a crossed differential. -/
theorem residueGroupRingBoundary_isCrossedDifferential (n : ℕ) (ψ : G →* H) :
    IsCrossedDifferential
      (residueGroupRingScalar n ψ) (residueGroupRingBoundary n ψ) := by
  intro g h
  simp only [residueGroupRingBoundary, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
  mul_one, sub_eq_add_neg, add_comm, residueGroupRingScalar_apply, smul_eq_mul, mul_add, mul_neg, add_assoc,
  add_neg_cancel_comm_assoc]

section UniversalProperty

variable (n : ℕ)
variable {A : Type*} [AddCommGroup A] [Module (ResidueGroupRing n H) A]

/-- The universal linear map induced by a residue crossed differential. -/
def residueDifferentialModuleLift
    (ψ : G →* H) (delta : G → A)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A :=
  crossedDifferentialModuleLift (A := A) (residueGroupRingScalar n ψ) delta hdelta

/-- The residue universal lift evaluates on the universal differential as the original crossed
differential. -/
@[simp]
theorem residueDifferentialModuleLift_universal
    (ψ : G →* H) (delta : G → A)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta) (g : G) :
    residueDifferentialModuleLift (A := A) n ψ delta hdelta
        (residueUniversalDifferential n ψ g) =
      delta g := by
  exact crossedDifferentialModuleLift_universal
    (A := A) (residueGroupRingScalar n ψ) delta hdelta g

/-- Linear maps out of the residue universal module are equal when they agree on universal
residue differentials. -/
@[ext]
theorem residueDifferentialModuleHom_ext
    (ψ : G →* H)
    {f h : ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A}
    (hfh : ∀ g, f (residueUniversalDifferential n ψ g) =
      h (residueUniversalDifferential n ψ g)) :
    f = h := by
  exact crossedDifferentialModuleHom_ext (A := A) (residueGroupRingScalar n ψ) hfh

/-- Existence and uniqueness of the linear map representing a residue crossed differential. -/
theorem existsUnique_residueDifferentialModuleLift
    (ψ : G →* H) (delta : G → A)
    (hdelta : IsCrossedDifferential (residueGroupRingScalar n ψ) delta) :
    ∃! f : ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A,
      ∀ g, f (residueUniversalDifferential n ψ g) = delta g := by
  exact existsUnique_crossedDifferentialModuleLift
    (A := A) (residueGroupRingScalar n ψ) delta hdelta

/-- Universal representation theorem for residue crossed differentials. -/
def residueCrossedDifferentialEquivLinearMap (ψ : G →* H) :
    {delta : G → A // IsCrossedDifferential (residueGroupRingScalar n ψ) delta} ≃
      (ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A) :=
  crossedDifferentialModuleEquivLinearMap (A := A) (residueGroupRingScalar n ψ)

/-- The universal residue Fox boundary map from the residue differential module to the residue
group ring. -/
def residueToGroupRing (ψ : G →* H) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] ResidueGroupRing n H :=
  residueDifferentialModuleLift (A := ResidueGroupRing n H) n ψ
    (residueGroupRingBoundary n ψ)
    (residueGroupRingBoundary_isCrossedDifferential n ψ)

/-- The universal residue Fox boundary sends `d g` to `[ψ g] - 1`. -/
@[simp]
theorem residueToGroupRing_universal (ψ : G →* H) (g : G) :
    residueToGroupRing n ψ (residueUniversalDifferential n ψ g) =
      residueGroupRingBoundary n ψ g := by
  exact residueDifferentialModuleLift_universal
    (A := ResidueGroupRing n H) n ψ
    (residueGroupRingBoundary n ψ)
    (residueGroupRingBoundary_isCrossedDifferential n ψ) g

/-- Existence and uniqueness of the universal residue Fox boundary map. -/
theorem existsUnique_residueToGroupRing (ψ : G →* H) :
    ∃! f : ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] ResidueGroupRing n H,
      ∀ g, f (residueUniversalDifferential n ψ g) =
        residueGroupRingBoundary n ψ g := by
  exact existsUnique_residueDifferentialModuleLift
    (A := ResidueGroupRing n H) n ψ
    (residueGroupRingBoundary n ψ)
    (residueGroupRingBoundary_isCrossedDifferential n ψ)

end UniversalProperty

end Basic

end

end FoxDifferential
