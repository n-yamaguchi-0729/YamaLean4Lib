import FoxDifferential.Completed.FiniteStage.SourceDerivativeVector

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/RelationIdealPrimitive.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Primitives for the finite-stage relation augmentation ideal

A source relation augmentation element should be read as an actual source Fox boundary.  This file
packages the primitive statement: an element `x` of the source group algebra is primitive if
`x = ∂_src p` for a source-coordinate vector `p` whose target projection is already in the
relation-boundary submodule.  The basic generators `q - 1` have such primitives by the source
Fox fundamental formula.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- An element of the source finite group algebra has a relation-compatible source Fox primitive
if it is the source boundary of a vector whose target projection lies in the finite
relation-boundary submodule. -/
def finiteFoxStageSourceBoundaryPrimitive [Fintype X]
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N n) : Prop :=
  ∃ p : finiteFoxStageSourceCoordinateVector (X := X) N n,
    finiteFoxStageSourceFoxBoundary (X := X) N n p = x ∧
      finiteFoxStageCoordinateSourceToTarget (X := X) N n p ∈
        finiteFoxStageRelationBoundarySubmodule (X := X) N n

/-- The zero source-boundary primitive. -/
theorem finiteFoxStageSourceBoundaryPrimitive_zero [Fintype X] :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n 0 := by
  refine ⟨0, ?_, ?_⟩
  · simp only [finiteFoxStageSourceFoxBoundary_apply, Pi.zero_apply, QuotientGroup.mk'_apply,
  MonoidAlgebra.of_apply, zero_mul, Finset.sum_const_zero]
  · exact (finiteFoxStageRelationBoundarySubmodule (X := X) N n).zero_mem

/-- Source-boundary primitives are closed under addition. -/
theorem finiteFoxStageSourceBoundaryPrimitive_add [Fintype X]
    {x y : finiteFoxStageSourceGroupAlgebra (X := X) N n}
    (hx : finiteFoxStageSourceBoundaryPrimitive (X := X) N n x)
    (hy : finiteFoxStageSourceBoundaryPrimitive (X := X) N n y) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n (x + y) := by
  rcases hx with ⟨px, hpx, hpxrel⟩
  rcases hy with ⟨py, hpy, hpyrel⟩
  refine ⟨px + py, ?_, ?_⟩
  · rw [map_add, hpx, hpy]
  · rw [map_add]
    exact (finiteFoxStageRelationBoundarySubmodule (X := X) N n).add_mem hpxrel hpyrel

/-- Source-boundary primitives are closed under negation. -/
theorem finiteFoxStageSourceBoundaryPrimitive_neg [Fintype X]
    {x : finiteFoxStageSourceGroupAlgebra (X := X) N n}
    (hx : finiteFoxStageSourceBoundaryPrimitive (X := X) N n x) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n (-x) := by
  rcases hx with ⟨p, hp, hprel⟩
  refine ⟨-p, ?_, ?_⟩
  · rw [map_neg, hp]
  · rw [map_neg]
    exact (finiteFoxStageRelationBoundarySubmodule (X := X) N n).neg_mem hprel

/-- Source-boundary primitives are closed under subtraction. -/
theorem finiteFoxStageSourceBoundaryPrimitive_sub [Fintype X]
    {x y : finiteFoxStageSourceGroupAlgebra (X := X) N n}
    (hx : finiteFoxStageSourceBoundaryPrimitive (X := X) N n x)
    (hy : finiteFoxStageSourceBoundaryPrimitive (X := X) N n y) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n (x - y) := by
  simpa [sub_eq_add_neg] using
    finiteFoxStageSourceBoundaryPrimitive_add (X := X) N n hx
      (finiteFoxStageSourceBoundaryPrimitive_neg (X := X) N n hy)

/-- Source-boundary primitives are closed under left multiplication by source coefficients. -/
theorem finiteFoxStageSourceBoundaryPrimitive_smul [Fintype X]
    (a : finiteFoxStageSourceGroupAlgebra (X := X) N n)
    {x : finiteFoxStageSourceGroupAlgebra (X := X) N n}
    (hx : finiteFoxStageSourceBoundaryPrimitive (X := X) N n x) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n (a • x) := by
  rcases hx with ⟨p, hp, hprel⟩
  refine ⟨a • p, ?_, ?_⟩
  · rw [map_smul, hp]
  · rw [finiteFoxStageCoordinateSourceToTarget_smul_source]
    exact (finiteFoxStageRelationBoundarySubmodule (X := X) N n).smul_mem
      (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a) hprel

/-- Source-boundary primitives form a left submodule of the source group algebra. -/
def finiteFoxStageSourceBoundaryPrimitiveSubmodule [Fintype X] :
    Submodule (finiteFoxStageSourceGroupAlgebra (X := X) N n)
      (finiteFoxStageSourceGroupAlgebra (X := X) N n) where
  carrier := {x | finiteFoxStageSourceBoundaryPrimitive (X := X) N n x}
  zero_mem' := finiteFoxStageSourceBoundaryPrimitive_zero (X := X) N n
  add_mem' := by
    intro x y hx hy
    exact finiteFoxStageSourceBoundaryPrimitive_add (X := X) N n hx hy
  smul_mem' := by
    intro a x hx
    exact finiteFoxStageSourceBoundaryPrimitive_smul (X := X) N n a hx

@[simp]
theorem finiteFoxStageSourceBoundaryPrimitiveSubmodule_coe [Fintype X] :
    ((finiteFoxStageSourceBoundaryPrimitiveSubmodule (X := X) N n :
      Submodule (finiteFoxStageSourceGroupAlgebra (X := X) N n)
        (finiteFoxStageSourceGroupAlgebra (X := X) N n)) :
        Set (finiteFoxStageSourceGroupAlgebra (X := X) N n)) =
      {x | finiteFoxStageSourceBoundaryPrimitive (X := X) N n x} :=
  rfl

/-- The source primitive attached to a finite relation `q`. -/
def finiteFoxStageRelationAugmentationPrimitiveVector
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageSourceCoordinateVector (X := X) N n :=
  finiteFoxStageSourceDerivativeVector (X := X) N n q.1

/-- The source boundary of the primitive vector for `q` is the augmentation generator `q - 1`. -/
theorem finiteFoxStageSourceFoxBoundary_relationAugmentationPrimitiveVector
    [Fintype X]
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageSourceFoxBoundary (X := X) N n
        (finiteFoxStageRelationAugmentationPrimitiveVector (X := X) N n q) =
      finiteFoxStageRelationAugmentationGenerator (X := X) N n q := by
  rw [finiteFoxStageRelationAugmentationPrimitiveVector,
    finiteFoxStageSourceFoxBoundary_sourceDerivativeVector,
    finiteFoxStageRelationAugmentationGenerator]

/-- The target projection of the primitive vector for `q` is the finite relation boundary of `q`. -/
theorem finiteFoxStageCoordinateSourceToTarget_relationAugmentationPrimitiveVector
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageCoordinateSourceToTarget (X := X) N n
        (finiteFoxStageRelationAugmentationPrimitiveVector (X := X) N n q) =
      finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [finiteFoxStageRelationAugmentationPrimitiveVector,
    finiteFoxStageCoordinateSourceToTarget_sourceDerivativeVector,
    finiteFoxStageRelationBoundaryAddMonoidHom_of]

/-- Relation augmentation generators have relation-compatible source Fox primitives. -/
theorem finiteFoxStageSourceBoundaryPrimitive_relationAugmentationGenerator
    [Fintype X]
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n
      (finiteFoxStageRelationAugmentationGenerator (X := X) N n q) := by
  refine ⟨finiteFoxStageRelationAugmentationPrimitiveVector (X := X) N n q, ?_, ?_⟩
  · exact finiteFoxStageSourceFoxBoundary_relationAugmentationPrimitiveVector
      (X := X) N n q
  · rw [finiteFoxStageCoordinateSourceToTarget_relationAugmentationPrimitiveVector]
    exact finiteFoxStageRelationBoundaryRange_subset_relationBoundarySubmodule
      (X := X) N n
      ((mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n).2
        ⟨Additive.ofMul q, rfl⟩)


/-- Left multiplication of a relation augmentation generator by a source quotient basis element has
an explicit relation-compatible source primitive. -/
theorem finiteFoxStageSourceBoundaryPrimitive_sourceBasis_mul_relationAugmentationGenerator
    [Fintype X]
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : finiteFoxStageRelationGroup (X := X) N n) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n
      (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) s *
        finiteFoxStageRelationAugmentationGenerator (X := X) N n q) := by
  simpa [Algebra.smul_def] using
    finiteFoxStageSourceBoundaryPrimitive_smul (X := X) N n
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) s)
      (finiteFoxStageSourceBoundaryPrimitive_relationAugmentationGenerator (X := X) N n q)

/-- Source primitive for the right basis multiple `(q - 1)s`.  The primitive is
`D_src(qs) - D_src(s)`. -/
def finiteFoxStageRelationAugmentationRightBasisPrimitiveVector
    (q : finiteFoxStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceCoordinateVector (X := X) N n :=
  finiteFoxStageSourceDerivativeVector (X := X) N n (q.1 * s) -
    finiteFoxStageSourceDerivativeVector (X := X) N n s

/-- The source boundary of `D_src(qs) - D_src(s)` is `(q - 1)s`. -/
theorem finiteFoxStageSourceFoxBoundary_relationAugmentationRightBasisPrimitiveVector
    [Fintype X]
    (q : finiteFoxStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceFoxBoundary (X := X) N n
        (finiteFoxStageRelationAugmentationRightBasisPrimitiveVector (X := X) N n q s) =
      finiteFoxStageRelationAugmentationGenerator (X := X) N n q *
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) s := by
  rw [finiteFoxStageRelationAugmentationRightBasisPrimitiveVector, map_sub,
    finiteFoxStageSourceFoxBoundary_sourceDerivativeVector,
    finiteFoxStageSourceFoxBoundary_sourceDerivativeVector,
    finiteFoxStageRelationAugmentationGenerator]
  simp only [MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm,
  add_left_comm, add_assoc, add_neg_cancel, add_zero, add_mul, MonoidAlgebra.single_mul_single, mul_one, neg_mul,
  one_mul]

/-- The target projection of `D_src(qs) - D_src(s)` is the relation boundary of `q`. -/
theorem finiteFoxStageCoordinateSourceToTarget_relationAugmentationRightBasisPrimitiveVector
    (q : finiteFoxStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageCoordinateSourceToTarget (X := X) N n
        (finiteFoxStageRelationAugmentationRightBasisPrimitiveVector (X := X) N n q s) =
      finiteFoxStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [finiteFoxStageRelationAugmentationRightBasisPrimitiveVector, map_sub,
    finiteFoxStageCoordinateSourceToTarget_sourceDerivativeVector,
    finiteFoxStageCoordinateSourceToTarget_sourceDerivativeVector,
    finiteFoxStageRelationBoundaryAddMonoidHom_of,
    finiteFoxStageQuotientDerivativeVector_mul,
    finiteFoxStageQuotientCoefficient_relation_eq_one]
  simp only [one_smul, add_sub_cancel_right]

/-- Right multiplication of a relation augmentation generator by a source quotient basis element
has an explicit relation-compatible source primitive. -/
theorem finiteFoxStageSourceBoundaryPrimitive_relationAugmentationGenerator_mul_sourceBasis
    [Fintype X]
    (q : finiteFoxStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n
      (finiteFoxStageRelationAugmentationGenerator (X := X) N n q *
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) s) := by
  refine ⟨finiteFoxStageRelationAugmentationRightBasisPrimitiveVector (X := X) N n q s, ?_, ?_⟩
  · exact finiteFoxStageSourceFoxBoundary_relationAugmentationRightBasisPrimitiveVector
      (X := X) N n q s
  · rw [finiteFoxStageCoordinateSourceToTarget_relationAugmentationRightBasisPrimitiveVector]
    exact finiteFoxStageRelationBoundaryRange_subset_relationBoundarySubmodule
      (X := X) N n
      ((mem_finiteFoxStageRelationBoundaryRange_iff (X := X) N n).2
        ⟨Additive.ofMul q, rfl⟩)

/-- The left source-submodule generated by the relation augmentation generators. -/
def finiteFoxStageRelationAugmentationLeftSubmodule [Fintype X] :
    Submodule (finiteFoxStageSourceGroupAlgebra (X := X) N n)
      (finiteFoxStageSourceGroupAlgebra (X := X) N n) :=
  Submodule.span (finiteFoxStageSourceGroupAlgebra (X := X) N n)
    (Set.range (finiteFoxStageRelationAugmentationGenerator (X := X) N n))

/-- The left relation-augmentation submodule is contained in the primitive submodule. -/
theorem finiteFoxStageRelationAugmentationLeftSubmodule_le_primitiveSubmodule
    [Fintype X] :
    finiteFoxStageRelationAugmentationLeftSubmodule (X := X) N n ≤
      finiteFoxStageSourceBoundaryPrimitiveSubmodule (X := X) N n := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨q, rfl⟩
  exact finiteFoxStageSourceBoundaryPrimitive_relationAugmentationGenerator
    (X := X) N n q

/-- Membership in the left relation-augmentation submodule gives a relation-compatible source
primitive. -/
theorem finiteFoxStageSourceBoundaryPrimitive_of_mem_relationAugmentationLeftSubmodule
    [Fintype X]
    {x : finiteFoxStageSourceGroupAlgebra (X := X) N n}
    (hx : x ∈ finiteFoxStageRelationAugmentationLeftSubmodule (X := X) N n) :
    finiteFoxStageSourceBoundaryPrimitive (X := X) N n x :=
  finiteFoxStageRelationAugmentationLeftSubmodule_le_primitiveSubmodule (X := X) N n hx

end

end FoxDifferential
