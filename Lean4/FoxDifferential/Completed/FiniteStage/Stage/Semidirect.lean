import FoxDifferential.Completed.FiniteStage.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Semidirect.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Finite-stage target quotient `F/N`. -/
abbrev finiteFoxStageTargetQuotient : Type u :=
  FreeGroup X ⧸ N

/-- Finite-stage target group algebra `(Z/nZ)[F/N]`. -/
abbrev finiteFoxStageTargetGroupAlgebra : Type u :=
  MonoidAlgebra (ModNCompletedCoeff n) (finiteFoxStageTargetQuotient (X := X) N)

/-- Finite-stage source group algebra `(Z/nZ)[F/[N,N]N^n]`. -/
abbrev finiteFoxStageSourceGroupAlgebra : Type u :=
  MonoidAlgebra (ModNCompletedCoeff n)
    (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)

/-- The finite-stage kernel `K_j` of
`(Z/nZ)[F/[N,N]N^n] → (Z/nZ)[F/N]`. -/
def finiteFoxStageGroupAlgebraMapKernelIdeal :
    Ideal (finiteFoxStageSourceGroupAlgebra (X := X) N n) :=
  RingHom.ker (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n)

omit [DecidableEq X] in
/-- Membership test for the finite-stage group-algebra map kernel ideal. -/
@[simp]
theorem mem_finiteFoxStageGroupAlgebraMapKernelIdeal
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {x : finiteFoxStageSourceGroupAlgebra (X := X) N n} :
    x ∈ finiteFoxStageGroupAlgebraMapKernelIdeal (X := X) N n ↔
      finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x = 0 := by
  rfl

/-- The finite-stage source augmentation ideal `I_j`. -/
def finiteFoxStageSourceAugmentationIdeal :
    Ideal (finiteFoxStageSourceGroupAlgebra (X := X) N n) :=
  RingHom.ker
    (finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
      (F := FreeGroup X) N n).toRingHom

omit [DecidableEq X] in
/-- Membership test for the finite-stage source augmentation ideal. -/
@[simp]
theorem mem_finiteFoxStageSourceAugmentationIdeal
    {N : Subgroup (FreeGroup X)} {n : ℕ}
    {x : finiteFoxStageSourceGroupAlgebra (X := X) N n} :
    x ∈ finiteFoxStageSourceAugmentationIdeal (X := X) N n ↔
      finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n x = 0 := by
  rfl

/-- The finite-stage product ideal `K_j I_j` governing the Fox kernel criterion. -/
def finiteFoxStageGroupAlgebraMapKernelMulAugmentationIdeal :
    Ideal (finiteFoxStageSourceGroupAlgebra (X := X) N n) :=
  finiteFoxStageGroupAlgebraMapKernelIdeal (X := X) N n *
    finiteFoxStageSourceAugmentationIdeal (X := X) N n

/-- Coordinate vectors for finite-stage Fox derivatives. -/
abbrev finiteFoxStageCoordinateVector : Type u :=
  X → finiteFoxStageTargetGroupAlgebra (X := X) N n

/-- Finite-stage Fox semidirect target `A^X ⋊ F/N`, whose left component stores the derivative
vector and whose right component stores the quotient word. -/
structure FiniteFoxStageSemidirect where
  left : finiteFoxStageCoordinateVector (X := X) N n
  right : finiteFoxStageTargetQuotient (X := X) N

namespace FiniteFoxStageSemidirect

omit [DecidableEq X] [N.Normal] in
/-- Extensionality for finite-stage semidirect elements. -/
@[ext]
theorem ext
    {a b : FiniteFoxStageSemidirect (X := X) N n}
    (hleft : a.left = b.left) (hright : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

/-- Identity element of the finite-stage Fox semidirect product. -/
instance instOneFiniteFoxStageSemidirect : One (FiniteFoxStageSemidirect (X := X) N n) where
  one := ⟨0, 1⟩

/-- Multiplication in the finite-stage Fox semidirect product. -/
instance instMulFiniteFoxStageSemidirect : Mul (FiniteFoxStageSemidirect (X := X) N n) where
  mul a b :=
    ⟨a.left +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) a.right) • b.left,
      a.right * b.right⟩

/-- Inversion in the finite-stage Fox semidirect product. -/
instance instInvFiniteFoxStageSemidirect : Inv (FiniteFoxStageSemidirect (X := X) N n) where
  inv a :=
    ⟨-((MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) a.right⁻¹) • a.left),
      a.right⁻¹⟩

omit [DecidableEq X] in
/-- The left component of the finite-stage semidirect identity is zero. -/
@[simp]
theorem one_left :
    (1 : FiniteFoxStageSemidirect (X := X) N n).left = 0 := rfl

omit [DecidableEq X] in
/-- The right component of the finite-stage semidirect identity is the group identity. -/
@[simp]
theorem one_right :
    (1 : FiniteFoxStageSemidirect (X := X) N n).right = 1 := rfl

omit [DecidableEq X] in
/-- Left-component formula for multiplication in the finite-stage semidirect product. -/
@[simp]
theorem mul_left
    (a b : FiniteFoxStageSemidirect (X := X) N n) :
    (a * b).left =
      a.left +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) a.right) • b.left := rfl

omit [DecidableEq X] in
/-- Right-component formula for multiplication in the finite-stage semidirect product. -/
@[simp]
theorem mul_right
    (a b : FiniteFoxStageSemidirect (X := X) N n) :
    (a * b).right = a.right * b.right := rfl

omit [DecidableEq X] in
/-- Left-component formula for inversion in the finite-stage semidirect product. -/
@[simp]
theorem inv_left
    (a : FiniteFoxStageSemidirect (X := X) N n) :
    a⁻¹.left =
      -((MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) a.right⁻¹) • a.left) := rfl

omit [DecidableEq X] in
/-- Right-component formula for inversion in the finite-stage semidirect product. -/
@[simp]
theorem inv_right
    (a : FiniteFoxStageSemidirect (X := X) N n) :
    a⁻¹.right = a.right⁻¹ := rfl

/-- Group structure on the finite-stage Fox semidirect product. -/
instance instGroupFiniteFoxStageSemidirect : Group (FiniteFoxStageSemidirect (X := X) N n) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    apply ext
    · funext i
      simp only [mul_left, MonoidAlgebra.of_apply, mul_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc,
  smul_add, smul_smul, MonoidAlgebra.single_mul_single, mul_one]
    · simp only [mul_right, mul_assoc]
  one_mul a := by
    apply ext
    · funext i
      simp only [mul_left, one_left, one_right, Pi.smul_apply, zero_add]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) 1 :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.one_def]
      rw [hone, one_smul]
    · simp only [mul_right, one_right, one_mul]
  mul_one a := by
    apply ext
    · funext i
      simp only [mul_left, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, one_left,
  smul_zero, Pi.add_apply, Pi.zero_apply, add_zero]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel a := by
    apply ext
    · funext i
      simp only [mul_left, inv_left, MonoidAlgebra.of_apply, inv_right, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
  smul_eq_mul, neg_add_cancel, one_left, Pi.zero_apply]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

end FiniteFoxStageSemidirect


end

end FoxDifferential
