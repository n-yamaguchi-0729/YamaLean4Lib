import FoxDifferential.Completed.FiniteStage.RelationModule

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/RelationAction.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Conjugation action on finite-stage relation derivatives

The finite-stage relation group `ker (F/[N,N]N^n -> F/N)` is acted on by the source quotient.
This file records the Fox-calculus calculation that the relation boundary is equivariant with
respect to conjugation and the `Z/nZ[F/N]` basis action.  This is the algebraic input needed to
upgrade relation-word derivatives from an additive subgroup to the module image used in the
finite Blanchfield--Lyndon exactness step.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Conjugating a finite-stage relation by an arbitrary source-quotient element gives another
finite-stage relation. -/
def finiteFoxStageRelationConjBySource
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageRelationGroup (X := X) N n :=
  ⟨s * q.1 * s⁻¹, by
    change finiteFoxCommutatorPowerQuotientMapToNormalQuotient
      (F := FreeGroup X) N n (s * q.1 * s⁻¹) = 1
    rw [map_mul, map_mul, map_inv, q.2]
    simp only [mul_one, mul_inv_cancel]⟩

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageRelationConjBySource_val
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    (finiteFoxStageRelationConjBySource (X := X) N n s q).1 = s * q.1 * s⁻¹ :=
  rfl

/-- Relation-boundary equivariance for conjugation by a source-quotient element. -/
theorem finiteFoxStageRelationBoundary_conjBySource
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n
        (Additive.ofMul (finiteFoxStageRelationConjBySource (X := X) N n s q)) =
      finiteFoxStageQuotientCoefficient (X := X) N n s •
        finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [finiteFoxStageRelationBoundaryAddMonoidHom_of,
    finiteFoxStageRelationBoundaryAddMonoidHom_of,
    finiteFoxStageRelationConjBySource_val]
  have hconj :=
    IsCrossedDifferential.conj
      (finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n)
      s q.1
  have hcoeff :
      finiteFoxStageQuotientCoefficient (X := X) N n (s * q.1 * s⁻¹) = 1 := by
    have htarget :
        finiteFoxCommutatorPowerQuotientMapToNormalQuotient
            (F := FreeGroup X) N n (s * q.1 * s⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, q.2]
      simp only [mul_one, mul_inv_cancel]
    rw [finiteFoxStageQuotientCoefficient_apply, htarget]
    rfl
  calc
    finiteFoxStageQuotientDerivativeVector (X := X) N n (s * q.1 * s⁻¹) =
        finiteFoxStageQuotientDerivativeVector (X := X) N n s +
          finiteFoxStageQuotientCoefficient (X := X) N n s •
            finiteFoxStageQuotientDerivativeVector (X := X) N n q.1 -
          finiteFoxStageQuotientCoefficient (X := X) N n (s * q.1 * s⁻¹) •
            finiteFoxStageQuotientDerivativeVector (X := X) N n s := hconj
    _ = finiteFoxStageQuotientCoefficient (X := X) N n s •
          finiteFoxStageQuotientDerivativeVector (X := X) N n q.1 := by
          rw [hcoeff, one_smul]
          abel

/-- A chosen source-quotient lift of an element of `F/N`. -/
def finiteFoxStageTargetQuotientLiftToSource
    (h : finiteFoxStageTargetQuotient (X := X) N) :
    FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n :=
  Classical.choose
    (finiteFoxCommutatorPowerQuotientMapToNormalQuotient_surjective
      (F := FreeGroup X) N n h)

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageTargetQuotientLiftToSource_spec
    (h : finiteFoxStageTargetQuotient (X := X) N) :
    finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n
      (finiteFoxStageTargetQuotientLiftToSource (X := X) N n h) = h :=
  Classical.choose_spec
    (finiteFoxCommutatorPowerQuotientMapToNormalQuotient_surjective
      (F := FreeGroup X) N n h)

omit [DecidableEq X] in
/-- The coefficient of a chosen source lift is the corresponding group-ring basis element. -/
@[simp]
theorem finiteFoxStageQuotientCoefficient_targetLift
    (h : finiteFoxStageTargetQuotient (X := X) N) :
    finiteFoxStageQuotientCoefficient (X := X) N n
        (finiteFoxStageTargetQuotientLiftToSource (X := X) N n h) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) h := by
  rw [finiteFoxStageQuotientCoefficient_apply,
    finiteFoxStageTargetQuotientLiftToSource_spec]

/-- Basis-element equivariance of the relation boundary over `Z/nZ[F/N]`. -/
theorem finiteFoxStageRelationBoundary_of_basis_smul
    (h : finiteFoxStageTargetQuotient (X := X) N)
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n
        (Additive.ofMul
          (finiteFoxStageRelationConjBySource (X := X) N n
            (finiteFoxStageTargetQuotientLiftToSource (X := X) N n h) q)) =
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) h) •
        finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [finiteFoxStageRelationBoundary_conjBySource,
    finiteFoxStageQuotientCoefficient_targetLift]

/-- The relation-boundary image is stable under multiplication by target group basis elements. -/
theorem finiteFoxStageRelationBoundaryRange_basis_smul_mem
    (h : finiteFoxStageTargetQuotient (X := X) N)
    {v : finiteFoxStageCoordinateVector (X := X) N n}
    (hv : v ∈ finiteFoxStageRelationBoundaryRange (X := X) N n) :
    (MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) h) • v ∈
      finiteFoxStageRelationBoundaryRange (X := X) N n := by
  rw [mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n] at hv
  rcases hv with ⟨q, hq⟩
  let qmul : finiteFoxStageRelationGroup (X := X) N n := Additive.toMul q
  rw [mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n]
  refine ⟨Additive.ofMul
    (finiteFoxStageRelationConjBySource (X := X) N n
      (finiteFoxStageTargetQuotientLiftToSource (X := X) N n h) qmul), ?_⟩
  calc
    finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n
        (Additive.ofMul
          (finiteFoxStageRelationConjBySource (X := X) N n
            (finiteFoxStageTargetQuotientLiftToSource (X := X) N n h) qmul)) =
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) h) •
          finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n
            (Additive.ofMul qmul) := by
          exact finiteFoxStageRelationBoundary_of_basis_smul (X := X) N n h qmul
    _ = (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) h) • v := by
          have hqmul :
              finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n
                (Additive.ofMul qmul) = v := by
            simpa [qmul] using hq
          rw [hqmul]

end

end FoxDifferential
