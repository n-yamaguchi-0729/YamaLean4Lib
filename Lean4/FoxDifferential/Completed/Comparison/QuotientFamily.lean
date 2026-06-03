import FoxDifferential.Completed.Comparison.DiscreteCompletion

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Comparison/QuotientFamily.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete-completed comparison

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

universe u

section FiniteStageQuotientBundle

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal]

/-- A bundled finite-stage quotient family for source-stage comparison theorems.

The point is to carry the topology and topological-group structure on the quotient target once,
instead of repeating these hypotheses at every comparison theorem. -/
structure ZCFiniteStageQuotientBundle where
  targetTopology : TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)
  targetIsTopologicalGroup :
    @IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)
      targetTopology inferInstance

namespace ZCFiniteStageQuotientBundle

variable {N}
variable (C : ProCGroups.FiniteGroupClass.{u})

/-- The target quotient carried by a finite-stage quotient bundle. -/
abbrev Target (_B : ZCFiniteStageQuotientBundle N) : Type u :=
  finiteFoxStageTargetQuotient (X := X) N

/-- The completed pro-`C` stage indices for the bundled target quotient. -/
abbrev Index (B : ZCFiniteStageQuotientBundle N) : Type u :=
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  ZCCompletedGroupAlgebraIndex C (Target (N := N) B)

/-- The completed group algebra of the bundled target quotient. -/
abbrev CompletedGroupAlgebra (B : ZCFiniteStageQuotientBundle N) : Type u :=
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  ZCCompletedGroupAlgebra C (Target (N := N) B)

/-- Scalar projection theorem, using the bundled quotient-family hypotheses. -/
theorem scalarStage_apply
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    zcCompletedGroupAlgebraScalarStage C N j w =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageCoefficient (X := X) N j.1.modulus w)) := by
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcCompletedGroupAlgebraScalarStage_apply (C := C) (X := X) N j w

/-- Completed derivative projection theorem, using the bundled quotient-family hypotheses. -/
theorem derivative_finiteStageProjection
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (i : X) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) := by
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivative_finiteStageProjection (C := C) (X := X) N j i w

/-- Completed derivative-vector projection theorem, using the bundled quotient-family
hypotheses. -/
theorem derivativeVector_finiteStageProjection
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    (fun i : X =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) =
      fun i : X =>
        letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
        modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (finiteFoxStageDerivative (X := X) N j.1.modulus i w) := by
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivativeVector_finiteStageProjection (C := C) (X := X) N j w

/-- Discrete-reduction derivative projection theorem, using the bundled quotient-family
hypotheses. -/
theorem derivative_finiteStageProjection_discreteReduction
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (i : X) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageGroupRingReduction (X := X) N j.1.modulus
          (FoxCalculus.relativeFreeGroupFoxDerivative
            (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i))) := by
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivative_finiteStageProjection_discreteReduction
    (C := C) (X := X) N i w j

/-- Discrete-reduction derivative-vector projection theorem, using the bundled quotient-family
hypotheses. -/
theorem derivativeVector_finiteStageProjection_discreteReduction
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    (fun i : X =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) =
      fun i : X =>
        letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
        modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (finiteFoxStageGroupRingReduction (X := X) N j.1.modulus
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i)) := by
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivativeVector_finiteStageProjection_discreteReduction
    (C := C) (X := X) N w j

end ZCFiniteStageQuotientBundle

end FiniteStageQuotientBundle

end

end FoxDifferential
