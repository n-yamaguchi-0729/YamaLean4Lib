import FoxDifferential.Completed.FiniteStage.BoundaryCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/RelationModule.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage relation module for the Crowell density step

This file packages the finite quotient
`ker (F/[N,N]N^n -> F/N)` as the relation object whose Fox derivative maps into the
finite-stage coordinate module.  It is the finite-level head map in the Blanchfield--Lyndon
complex over `Z/nZ[F/N]`.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite-stage relation group
`ker (F/[N,N]N^n -> F/N)`.  Its elements are exactly finite-stage kernel relations. -/
abbrev finiteFoxStageRelationGroup : Type u :=
  (finiteFoxCommutatorPowerQuotientMapToNormalQuotient
    (F := FreeGroup X) N n).ker

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageRelationGroup_target_eq_one
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxCommutatorPowerQuotientMapToNormalQuotient
      (F := FreeGroup X) N n q.1 = 1 :=
  q.2

omit [DecidableEq X] in
@[simp]
theorem finiteFoxStageQuotientCoefficient_relation_eq_one
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageQuotientCoefficient (X := X) N n q.1 = 1 :=
  finiteFoxStageQuotientCoefficient_eq_one_of_kernel (X := X) N n q.2

/-- The finite-stage relation boundary, written additively:
`N/[N,N]N^n -> (Z/nZ[F/N])^X`. -/
def finiteFoxStageRelationBoundaryAddMonoidHom :
    Additive (finiteFoxStageRelationGroup (X := X) N n) →+
      finiteFoxStageCoordinateVector (X := X) N n :=
  IsCrossedDifferential.restrictTrivialSubgroupAddMonoidHom
    (finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n)
    ((finiteFoxCommutatorPowerQuotientMapToNormalQuotient
      (F := FreeGroup X) N n).ker)
    (fun q => finiteFoxStageQuotientCoefficient_relation_eq_one (X := X) N n q)

@[simp]
theorem finiteFoxStageRelationBoundaryAddMonoidHom_of
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q.1 :=
  rfl

/-- The relation-boundary image, as an additive subgroup of the finite coordinate module. -/
def finiteFoxStageRelationBoundaryRange :
    AddSubgroup (finiteFoxStageCoordinateVector (X := X) N n) :=
  finiteFoxStageSourceKernelDerivativeAddSubgroup (X := X) N n

@[simp]
theorem finiteFoxStageRelationBoundaryRange_coe :
    ((finiteFoxStageRelationBoundaryRange (X := X) N n :
        AddSubgroup (finiteFoxStageCoordinateVector (X := X) N n)) :
          Set (finiteFoxStageCoordinateVector (X := X) N n)) =
      finiteFoxStageSourceKernelDerivativeSet (X := X) N n :=
  rfl

/-- Membership in the relation-boundary image is the existence of a relation whose Fox derivative
is the given vector. -/
theorem mem_finiteFoxStageRelationBoundaryRange_iff
    {v : finiteFoxStageCoordinateVector (X := X) N n} :
    v ∈ finiteFoxStageRelationBoundaryRange (X := X) N n ↔
      ∃ q : Additive (finiteFoxStageRelationGroup (X := X) N n),
        finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n q = v := by
  constructor
  · intro hv
    rcases hv with ⟨q, hq, hv⟩
    let qrel : finiteFoxStageRelationGroup (X := X) N n := ⟨q, hq⟩
    refine ⟨Additive.ofMul qrel, ?_⟩
    simpa [qrel] using hv
  · rintro ⟨q, hq⟩
    let qrel : finiteFoxStageRelationGroup (X := X) N n := Additive.toMul q
    refine ⟨qrel.1, qrel.2, ?_⟩
    simpa [qrel] using hq

/-- The finite-stage relation boundary lands in finite Fox boundary cycles. -/
theorem finiteFoxStageFoxBoundary_relationBoundary_eq_zero
    [Fintype X] (q : Additive (finiteFoxStageRelationGroup (X := X) N n)) :
    finiteFoxStageFoxBoundary (X := X) N n
      (finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n q) = 0 := by
  change
    finiteFoxStageFoxBoundary (X := X) N n
      (finiteFoxStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1) = 0
  rw [finiteFoxStageFoxBoundary_quotientDerivativeVector]
  rw [finiteFoxStageQuotientCoefficient_eq_one_of_kernel
    (X := X) N n (Additive.toMul q).2]
  simp only [sub_self]

/-- The relation-boundary range is contained in `ker ∂`. -/
theorem finiteFoxStageRelationBoundary_range_le_boundaryCycleSubmodule
    [Fintype X] :
    finiteFoxStageRelationBoundaryRange (X := X) N n ≤
      (finiteFoxStageBoundaryCycleSubmodule (X := X) N n).toAddSubgroup := by
  intro v hv
  rw [mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n] at hv
  rcases hv with ⟨q, rfl⟩
  exact finiteFoxStageFoxBoundary_relationBoundary_eq_zero (X := X) N n q

/-- Finite-stage exactness at the coordinate module, stated as a named proposition. -/
def finiteFoxStageRelationBoundaryExact [Fintype X] : Prop :=
  Function.Exact
    (finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n)
    (finiteFoxStageFoxBoundary (X := X) N n)

/-- Finite-stage exactness is equivalent to the coverage statement formulated in
`BoundaryCycles.lean`. -/
theorem finiteFoxStageRelationBoundaryExact_iff_boundaryCyclesCoveredBySourceKernel
    [Fintype X] :
    finiteFoxStageRelationBoundaryExact (X := X) N n ↔
      finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro hexact v hv
    have hvzero : finiteFoxStageFoxBoundary (X := X) N n v = 0 := hv
    rcases (hexact v).1 hvzero with ⟨q, hq⟩
    change v ∈ finiteFoxStageRelationBoundaryRange (X := X) N n
    rw [mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n]
    exact ⟨q, hq⟩
  · intro hcovered v
    constructor
    · intro hvzero
      have hvcycle : v ∈ finiteFoxStageBoundaryCycleSubmodule (X := X) N n := hvzero
      have hvsource : v ∈ finiteFoxStageSourceKernelDerivativeSet (X := X) N n :=
        hcovered hvcycle
      have hvsourceRange : v ∈ finiteFoxStageRelationBoundaryRange (X := X) N n := by
        change v ∈ finiteFoxStageSourceKernelDerivativeSet (X := X) N n
        exact hvsource
      rw [mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n] at hvsourceRange
      exact hvsourceRange
    · rintro ⟨q, hq⟩
      rw [← hq]
      exact finiteFoxStageFoxBoundary_relationBoundary_eq_zero (X := X) N n q

/-- Coverage of finite boundary cycles gives finite-stage exactness in the usual function-level
form. -/
theorem finiteFoxStageRelationBoundaryExact_of_boundaryCyclesCoveredBySourceKernel
    [Fintype X]
    (hcovered : finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n) :
    finiteFoxStageRelationBoundaryExact (X := X) N n :=
  (finiteFoxStageRelationBoundaryExact_iff_boundaryCyclesCoveredBySourceKernel
    (X := X) N n).2 hcovered

/-- Function-level finite-stage exactness gives the set-level coverage used by the density step. -/
theorem finiteFoxStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryExact
    [Fintype X]
    (hexact : finiteFoxStageRelationBoundaryExact (X := X) N n) :
    finiteFoxStageBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  (finiteFoxStageRelationBoundaryExact_iff_boundaryCyclesCoveredBySourceKernel
    (X := X) N n).1 hexact

end

end FoxDifferential
