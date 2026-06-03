import FoxDifferential.Completed.FiniteStage.BoundaryCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/BoundaryCycleHom.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage boundary-cycle homomorphism

This file turns the finite-stage relation-cycle image into an actual additive map.  On the
kernel of
`F / ([N,N] N^n) -> F/N`, the descended crossed Fox differential is additive because the
coefficient of every kernel element is `1`.  The remaining finite-stage exactness problem can
therefore be stated as surjectivity of this map onto `ker ∂`, rather than as an unstructured set
inclusion.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The kernel of the finite source-to-target quotient `F/[N,N]N^n -> F/N`. -/
abbrev finiteFoxStageSourceKernel : Type u :=
  (finiteFoxCommutatorPowerQuotientMapToNormalQuotient
    (F := FreeGroup X) N n).ker

/-- The descended finite-stage Fox derivative, restricted to the source quotient kernel, is an
additive homomorphism. -/
def finiteFoxStageSourceKernelDerivativeAddHom :
    Additive (finiteFoxStageSourceKernel (X := X) N n) →+
      finiteFoxStageCoordinateVector (X := X) N n where
  toFun q :=
    finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1
  map_zero' := by
    change finiteFoxStageQuotientDerivativeVector (X := X) N n
      (1 : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0
    simp only [finiteFoxStageQuotientDerivativeVector_one]
  map_add' := by
    intro q r
    change finiteFoxStageQuotientDerivativeVector (X := X) N n
        ((Additive.toMul q).1 * (Additive.toMul r).1) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1 +
        finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul r).1
    rw [finiteFoxStageQuotientDerivativeVector_mul]
    have hqcoeff :
        finiteFoxStageQuotientCoefficient (X := X) N n (Additive.toMul q).1 = 1 :=
      finiteFoxStageQuotientCoefficient_eq_one_of_kernel (X := X) N n
        (Additive.toMul q).2
    rw [hqcoeff]
    simp only [one_smul]

@[simp]
theorem finiteFoxStageSourceKernelDerivativeAddHom_of
    (q : finiteFoxStageSourceKernel (X := X) N n) :
    finiteFoxStageSourceKernelDerivativeAddHom (X := X) N n (Additive.ofMul q) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q.1 :=
  rfl

/-- The range of the additive source-kernel derivative map is exactly the source-kernel derivative
additive subgroup already used in the finite-stage density target. -/
theorem finiteFoxStageSourceKernelDerivativeAddHom_range_eq :
    AddMonoidHom.range (finiteFoxStageSourceKernelDerivativeAddHom (X := X) N n) =
      finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨q, rfl⟩
    refine ⟨(Additive.toMul q).1, (Additive.toMul q).2, rfl⟩
  · intro hv
    rcases hv with ⟨q, hq, rfl⟩
    exact ⟨Additive.ofMul
      (⟨q, hq⟩ : finiteFoxStageSourceKernel (X := X) N n), rfl⟩

/-- The source-kernel derivative map, with codomain restricted to finite Fox boundary cycles. -/
def finiteFoxStageSourceKernelDerivativeToBoundaryCycles [Fintype X] :
    Additive (finiteFoxStageSourceKernel (X := X) N n) →+
      finiteFoxStageBoundaryCycleSubmodule (X := X) N n where
  toFun q :=
    ⟨finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1,
      finiteFoxStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule (X := X) N n
        ⟨(Additive.toMul q).1, (Additive.toMul q).2, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    change finiteFoxStageQuotientDerivativeVector (X := X) N n
      (1 : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0
    simp only [finiteFoxStageQuotientDerivativeVector_one]
  map_add' := by
    intro q r
    apply Subtype.ext
    change finiteFoxStageQuotientDerivativeVector (X := X) N n
        ((Additive.toMul q).1 * (Additive.toMul r).1) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1 +
        finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul r).1
    rw [finiteFoxStageQuotientDerivativeVector_mul]
    have hqcoeff :
        finiteFoxStageQuotientCoefficient (X := X) N n (Additive.toMul q).1 = 1 :=
      finiteFoxStageQuotientCoefficient_eq_one_of_kernel (X := X) N n
        (Additive.toMul q).2
    rw [hqcoeff]
    simp only [one_smul]

@[simp]
theorem finiteFoxStageSourceKernelDerivativeToBoundaryCycles_val
    [Fintype X] (q : finiteFoxStageSourceKernel (X := X) N n) :
    (finiteFoxStageSourceKernelDerivativeToBoundaryCycles (X := X) N n
      (Additive.ofMul q) : finiteFoxStageCoordinateVector (X := X) N n) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q.1 :=
  rfl

/-- The finite-stage coverage statement is precisely surjectivity of the source-kernel derivative
map onto the boundary-cycle subgroup. -/
theorem finiteFoxStageBoundaryCyclesCovered_iff_surj_derivativeToBoundaryCycles
    [Fintype X] :
    finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n ↔
      Function.Surjective
        (finiteFoxStageSourceKernelDerivativeToBoundaryCycles (X := X) N n) := by
  constructor
  · intro hcover y
    rcases hcover y.2 with ⟨q, hq, hqy⟩
    refine ⟨Additive.ofMul
      (⟨q, hq⟩ : finiteFoxStageSourceKernel (X := X) N n), ?_⟩
    apply Subtype.ext
    simpa using hqy
  · intro hsurj v hv
    rcases hsurj ⟨v, hv⟩ with ⟨q, hq⟩
    refine ⟨(Additive.toMul q).1, (Additive.toMul q).2, ?_⟩
    exact congrArg Subtype.val hq

/-- If the restricted source-kernel derivative map is surjective, then the source-kernel image is
all of the finite boundary-cycle subgroup. -/
theorem finiteFoxStageSourceKernelDerivativeSet_eq_boundaryCycleSubmodule_of_surjective
    [Fintype X]
    (hsurj : Function.Surjective
      (finiteFoxStageSourceKernelDerivativeToBoundaryCycles (X := X) N n)) :
    finiteFoxStageSourceKernelDerivativeSet (X := X) N n =
      (finiteFoxStageBoundaryCycleSubmodule (X := X) N n :
        Set (finiteFoxStageCoordinateVector (X := X) N n)) := by
  exact
    (finiteFoxStageSourceKernelDerivativeSet_eq_boundaryCycleSubmodule_iff
      (X := X) N n).2
      ((finiteFoxStageBoundaryCyclesCovered_iff_surj_derivativeToBoundaryCycles
        (X := X) N n).2 hsurj)

end

end FoxDifferential
