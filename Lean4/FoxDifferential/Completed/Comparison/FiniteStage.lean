import FoxDifferential.Completed.DifferentialModule.Identity
import FoxDifferential.Completed.FiniteStage.MagnusQuotient
import FoxDifferential.Completed.ProCIntegerCoefficients.Naturality

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Comparison/FiniteStage.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete-completed comparison

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u

section FiniteStageCompletedComparison

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal]
variable [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
variable [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]

abbrev zcFiniteStageTarget (X : Type u) [DecidableEq X]
    (N : Subgroup (FreeGroup X)) [N.Normal] :=
  finiteFoxStageTargetQuotient (X := X) N

/-- The coefficient homomorphism obtained by projecting the completed `Z_C[[F/N]]`
coefficient homomorphism to one finite pro-`C` stage. -/
def zcCompletedGroupAlgebraScalarStage
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    FreeGroup X →* ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j where
  toFun w :=
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
      (zcCompletedGroupAlgebraScalar C (QuotientGroup.mk' N) w)
  map_one' := by
    simp only [zcCompletedGroupAlgebraScalar, map_one, zcCompletedGroupAlgebraProjection_one]
  map_mul' u v := by
    simp only [zcCompletedGroupAlgebraScalar, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
  map_mul, zcCompletedGroupAlgebraProjection_mul, zcCompletedGroupAlgebraProjection_groupLike,
  MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]

/-- Projecting the completed coefficient homomorphism agrees with the finite-stage quotient map
applied to the ordinary finite Fox coefficient homomorphism at the same modulus. -/
@[simp]
theorem zcCompletedGroupAlgebraScalarStage_apply
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N))
    (w : FreeGroup X) :
    zcCompletedGroupAlgebraScalarStage C N j w =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageCoefficient (X := X) N j.1.modulus w)) := by
  letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  rw [finiteFoxStageCoefficient_apply, modNCompletedGroupAlgebraStageMapInClass_of]
  rfl

/-- The projected completed Fox derivative vector is a crossed differential at one finite
pro-`C` stage. -/
theorem zcFreeGroupFoxDerivativeVector_stage_isCrossedDifferential
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    IsCrossedDifferential
      (zcCompletedGroupAlgebraScalarStage C N j)
      (fun w : FreeGroup X =>
        fun i : X =>
          zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
            (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) := by
  intro u v
  funext i
  have h :=
    congrArg
      (zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j)
      (congrFun
        (zcFreeGroupFoxDerivativeVector_mul C (QuotientGroup.mk' N) u v) i)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zcCompletedGroupAlgebraScalarStage,
    zcCompletedGroupAlgebraProjection_add, zcCompletedGroupAlgebraProjection_mul] using h

/-- The finite-stage Fox derivative vector, pushed to one pro-`C` quotient stage of the target,
is a crossed differential with the projected completed coefficient homomorphism. -/
theorem finiteFoxStageDerivativeVector_zcStageMap_isCrossedDifferential
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    IsCrossedDifferential
      (zcCompletedGroupAlgebraScalarStage C N j)
      (fun w : FreeGroup X =>
        fun i : X =>
          letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
          modNCompletedGroupAlgebraStageMapInClass j.1.modulus
            (zcFiniteStageTarget X N) C j.2
            (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) := by
  intro u v
  funext i
  letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  have h :=
    congrArg
      (modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2)
      (finiteFoxStageDerivative_mul (X := X) N j.1.modulus i u v)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, finiteFoxStageDerivative,
    zcCompletedGroupAlgebraScalarStage_apply, zcFiniteStageTarget, map_add, map_mul] using h

/-- Projecting the completed derivative vector to a finite pro-`C` stage recovers the finite
Fox derivative vector, mapped to that stage. -/
theorem zcFreeGroupFoxDerivativeVector_finiteStageProjection
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N))
    (w : FreeGroup X) :
    (fun i : X =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) =
      fun i : X =>
        letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
        modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (finiteFoxStageDerivative (X := X) N j.1.modulus i w) := by
  letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  let projected : FreeGroup X →
      X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j :=
    fun w i =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)
  let staged : FreeGroup X →
      X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j :=
    fun w i =>
      modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageDerivative (X := X) N j.1.modulus i w)
  have hprojected :
      projected =
        freeCrossedDifferentialWithCoeff
          (A := X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)
          (zcCompletedGroupAlgebraScalarStage C N j)
          (fun x : X =>
            Pi.single x
              (1 : ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)) := by
    refine freeCrossedDifferentialWithCoeff_unique
      (A := X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)
      (zcCompletedGroupAlgebraScalarStage C N j)
      (fun x : X =>
        Pi.single x
          (1 : ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j))
      projected ?_ ?_
    · simpa [projected] using
        zcFreeGroupFoxDerivativeVector_stage_isCrossedDifferential C N j
    · intro x
      funext i
      by_cases hi : i = x
      · subst i
        simp only [zcFreeGroupFoxDerivativeVector_of, Pi.single_eq_same, zcCompletedGroupAlgebraProjection_one,
  projected]
      · simp only [zcFreeGroupFoxDerivativeVector_of, Pi.single_eq_of_ne hi, zcCompletedGroupAlgebraProjection_zero,
  projected]
  have hstaged :
      staged =
        freeCrossedDifferentialWithCoeff
          (A := X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)
          (zcCompletedGroupAlgebraScalarStage C N j)
          (fun x : X =>
            Pi.single x
              (1 : ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)) := by
    refine freeCrossedDifferentialWithCoeff_unique
      (A := X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)
      (zcCompletedGroupAlgebraScalarStage C N j)
      (fun x : X =>
        Pi.single x
          (1 : ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j))
      staged ?_ ?_
    · simpa [staged] using
        finiteFoxStageDerivativeVector_zcStageMap_isCrossedDifferential C N j
    · intro x
      funext i
      have h :=
        congrFun (finiteFoxStageDerivativeVector_of (X := X) N j.1.modulus x) i
      change
        (modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2)
          (finiteFoxStageDerivativeVector (X := X) N j.1.modulus
            (FreeGroup.of x) i) =
        ((Pi.single x
          (1 : ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j)) :
            X → ZCCompletedGroupAlgebraStage C (zcFiniteStageTarget X N) j) i
      rw [h]
      by_cases hi : i = x
      · subst i
        simp only [Pi.single_eq_same, map_one]
      · simp only [Pi.single_eq_of_ne hi, map_zero]
  exact congrFun (hprojected.trans hstaged.symm) w

/-- Component form of `zcFreeGroupFoxDerivativeVector_finiteStageProjection`. -/
@[simp]
theorem zcFreeGroupFoxDerivative_finiteStageProjection
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N))
    (i : X) (w : FreeGroup X) :
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) := by
  have h := congrFun
    (zcFreeGroupFoxDerivativeVector_finiteStageProjection C N j w) i
  simpa [zcFreeGroupFoxDerivative] using h

/-- If the universal completed differential of a word is zero, then every finite `Z_C` stage
projection of its finite Fox derivative vanishes. -/
theorem finiteFoxStageDerivative_zcStageMap_eq_zero_of_zcUniversalDifferential_eq_zero
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N))
    (i : X) {w : FreeGroup X}
    (hw : zcUniversalDifferential C (QuotientGroup.mk' N) w = 0) :
    (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
     modNCompletedGroupAlgebraStageMapInClass j.1.modulus
      (zcFiniteStageTarget X N) C j.2
      (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) = 0 := by
  letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  have hcompleted :
      zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w = 0 :=
    zcFreeGroupFoxDerivative_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := C) (QuotientGroup.mk' N) i hw
  have hprojection :
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
          (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) = 0 := by
    simpa using
      congrArg
        (zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j)
        hcompleted
  exact
    (zcFreeGroupFoxDerivative_finiteStageProjection C N j i w).symm.trans hprojection

/-- Vector form of
`finiteFoxStageDerivative_zcStageMap_eq_zero_of_zcUniversalDifferential_eq_zero`. -/
theorem finiteFoxStageDerivativeVector_zcStageMap_eq_zero_of_zcUnivDiff_eq_zero
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N))
    {w : FreeGroup X}
    (hw : zcUniversalDifferential C (QuotientGroup.mk' N) w = 0) :
    (fun i : X =>
      letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
      modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) = 0 := by
  funext i
  exact
    finiteFoxStageDerivative_zcStageMap_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := C) (X := X) N j i hw

/-- At the identity quotient stage, a zero universal completed differential forces the finite Fox
derivative itself to vanish modulo every allowed pro-`C` coefficient modulus. -/
theorem finiteFoxStageDerivative_eq_zero_of_zcUniversalDifferential_eq_zero
    [DiscreteTopology (zcFiniteStageTarget X N)]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hCtarget : C.pred (zcFiniteStageTarget X N))
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    (i : X) {w : FreeGroup X}
    (hw : zcUniversalDifferential C (QuotientGroup.mk' N) w = 0) :
    finiteFoxStageDerivative (X := X) N j.modulus i w = 0 := by
  letI : Fact (0 < j.modulus) := ⟨j.positive⟩
  let U : CompletedGroupAlgebraIndexInClass (zcFiniteStageTarget X N) C :=
    identityCompletedGroupAlgebraIndexInClassOfMem C (zcFiniteStageTarget X N) hIso hCtarget
  have hstage :
      modNCompletedGroupAlgebraStageMapInClass j.modulus
          (zcFiniteStageTarget X N) C U
          (finiteFoxStageDerivative (X := X) N j.modulus i w) = 0 := by
    simpa [U] using
      finiteFoxStageDerivative_zcStageMap_eq_zero_of_zcUniversalDifferential_eq_zero
        (C := C) (X := X) N (j, U) i hw
  exact
    (modNCompletedGAStageMapInClass_identityCompletedGAIndexInClassOfMem_inj
      j.modulus C (zcFiniteStageTarget X N) hIso hCtarget) hstage

/-- Vector form of
`finiteFoxStageDerivative_eq_zero_of_zcUniversalDifferential_eq_zero`. -/
theorem finiteFoxStageDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
    [DiscreteTopology (zcFiniteStageTarget X N)]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hCtarget : C.pred (zcFiniteStageTarget X N))
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    {w : FreeGroup X}
    (hw : zcUniversalDifferential C (QuotientGroup.mk' N) w = 0) :
    finiteFoxStageDerivativeVector (X := X) N j.modulus w = 0 := by
  funext i
  exact
    finiteFoxStageDerivative_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := C) (X := X) N hIso hCtarget j i hw

/-- At the identity quotient stage, a zero completed component derivative forces the finite Fox
derivative itself to vanish modulo the corresponding pro-`C` coefficient modulus. -/
theorem finiteFoxStageDerivative_eq_zero_of_zcFreeGroupFoxDerivative_eq_zero
    [DiscreteTopology (zcFiniteStageTarget X N)]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hCtarget : C.pred (zcFiniteStageTarget X N))
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    (i : X) {w : FreeGroup X}
    (hw : zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w = 0) :
    finiteFoxStageDerivative (X := X) N j.modulus i w = 0 := by
  letI : Fact (0 < j.modulus) := ⟨j.positive⟩
  let U : CompletedGroupAlgebraIndexInClass (zcFiniteStageTarget X N) C :=
    identityCompletedGroupAlgebraIndexInClassOfMem C (zcFiniteStageTarget X N) hIso hCtarget
  have hstage :
      modNCompletedGroupAlgebraStageMapInClass j.modulus
          (zcFiniteStageTarget X N) C U
          (finiteFoxStageDerivative (X := X) N j.modulus i w) = 0 := by
    have hprojection :
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) (j, U)
            (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) = 0 := by
      simpa using
        congrArg
          (zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) (j, U))
          hw
    exact
      (zcFreeGroupFoxDerivative_finiteStageProjection C N (j, U) i w).symm.trans
        hprojection
  exact
    (modNCompletedGAStageMapInClass_identityCompletedGAIndexInClassOfMem_inj
      j.modulus C (zcFiniteStageTarget X N) hIso hCtarget) hstage

/-- Vector form of
`finiteFoxStageDerivative_eq_zero_of_zcFreeGroupFoxDerivative_eq_zero`. -/
theorem finiteFoxStageDerivativeVector_eq_zero_of_zcFreeGroupFoxDerivativeVector_eq_zero
    [DiscreteTopology (zcFiniteStageTarget X N)]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hCtarget : C.pred (zcFiniteStageTarget X N))
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    {w : FreeGroup X}
    (hw : zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w = 0) :
    finiteFoxStageDerivativeVector (X := X) N j.modulus w = 0 := by
  funext i
  have hcoord :
      zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w = 0 := by
    simpa [zcFreeGroupFoxDerivative] using congrFun hw i
  exact
    finiteFoxStageDerivative_eq_zero_of_zcFreeGroupFoxDerivative_eq_zero
      (C := C) (X := X) N hIso hCtarget j i hcoord

/-- At the identity quotient stage, it is enough for the completed derivative vector to vanish
after projection to the selected finite coefficient stage. -/
theorem finiteFoxStageDerivativeVector_eq_zero_of_zcFreeFoxDerivVec_identityProj_eq_zero
    [DiscreteTopology (zcFiniteStageTarget X N)]
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hCtarget : C.pred (zcFiniteStageTarget X N))
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    {w : FreeGroup X}
    (hw :
      (fun i : X =>
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N)
          (j, identityCompletedGroupAlgebraIndexInClassOfMem
            C (zcFiniteStageTarget X N) hIso hCtarget)
          (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) = 0) :
    finiteFoxStageDerivativeVector (X := X) N j.modulus w = 0 := by
  funext i
  letI : Fact (0 < j.modulus) := ⟨j.positive⟩
  let U : CompletedGroupAlgebraIndexInClass (zcFiniteStageTarget X N) C :=
    identityCompletedGroupAlgebraIndexInClassOfMem C (zcFiniteStageTarget X N) hIso hCtarget
  have hstage :
      modNCompletedGroupAlgebraStageMapInClass j.modulus
          (zcFiniteStageTarget X N) C U
          (finiteFoxStageDerivative (X := X) N j.modulus i w) = 0 := by
    have hcoord := congrFun hw i
    simpa [U] using
      (zcFreeGroupFoxDerivative_finiteStageProjection C N (j, U) i w).symm.trans hcoord
  exact
    (modNCompletedGAStageMapInClass_identityCompletedGAIndexInClassOfMem_inj
      j.modulus C (zcFiniteStageTarget X N) hIso hCtarget) hstage

/-- A completed component derivative is determined by all of its finite pro-`C` stage
projections. -/
theorem zcFreeGroupFoxDerivative_unique_finiteStageProjection
    (i : X)
    (delta : FreeGroup X → ZCCompletedGroupAlgebra C (zcFiniteStageTarget X N))
    (hprojection : ∀ w
      (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w) =
        (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
         modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (finiteFoxStageDerivative (X := X) N j.1.modulus i w))) :
    delta = zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i := by
  funext w
  apply Subtype.ext
  funext j
  change zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w) =
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
      (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w)
  rw [hprojection w j, zcFreeGroupFoxDerivative_finiteStageProjection C N j i w]

/-- Existence and uniqueness of the completed component derivative characterized by all finite
pro-`C` stage projection formulas. -/
theorem existsUnique_zcFreeGroupFoxDerivative_finiteStageProjection
    (i : X) :
    ∃! delta : FreeGroup X → ZCCompletedGroupAlgebra C (zcFiniteStageTarget X N),
      ∀ w (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w) =
          (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
           modNCompletedGroupAlgebraStageMapInClass j.1.modulus
            (zcFiniteStageTarget X N) C j.2
            (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) := by
  refine ⟨zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i, ?_, ?_⟩
  · intro w j
    exact zcFreeGroupFoxDerivative_finiteStageProjection C N j i w
  · intro delta hprojection
    exact zcFreeGroupFoxDerivative_unique_finiteStageProjection C N i delta hprojection

/-- The completed derivative vector is determined by all finite pro-`C` stage projection
formulas. -/
theorem zcFreeGroupFoxDerivativeVector_unique_finiteStageProjection
    (delta : FreeGroup X →
      ZCFreeFoxCoordinates C (X := X) (H := zcFiniteStageTarget X N))
    (hprojection : ∀ w
      (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
      (fun i : X =>
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
          (delta w i)) =
        fun i : X =>
          letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
          modNCompletedGroupAlgebraStageMapInClass j.1.modulus
            (zcFiniteStageTarget X N) C j.2
            (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) :
    delta = zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) := by
  funext w i
  apply Subtype.ext
  funext j
  change zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w i) =
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
      (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)
  have hcoord := congrFun (hprojection w j) i
  rw [hcoord]
  exact (by
    simpa [zcFreeGroupFoxDerivative] using
      (zcFreeGroupFoxDerivative_finiteStageProjection C N j i w).symm)

/-- Existence and uniqueness of the completed derivative vector characterized by all finite
pro-`C` stage projection formulas. -/
theorem existsUnique_zcFreeGroupFoxDerivativeVector_finiteStageProjection :
    ∃! delta : FreeGroup X →
      ZCFreeFoxCoordinates C (X := X) (H := zcFiniteStageTarget X N),
      ∀ w (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
        (fun i : X =>
          zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
            (delta w i)) =
          fun i : X =>
            letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
            modNCompletedGroupAlgebraStageMapInClass j.1.modulus
              (zcFiniteStageTarget X N) C j.2
              (finiteFoxStageDerivative (X := X) N j.1.modulus i w) := by
  refine ⟨zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N), ?_, ?_⟩
  · intro w j
    exact zcFreeGroupFoxDerivativeVector_finiteStageProjection C N j w
  · intro delta hprojection
    exact zcFreeGroupFoxDerivativeVector_unique_finiteStageProjection
      C N delta hprojection

section FundamentalFormula

variable [Fintype X]

/-- The completed Fox-Euler formula for the quotient map `F -> F/N`. -/
theorem zcFreeGroupFoxDerivative_fundamental_formula_quotientMap
    (w : FreeGroup X) :
    zcCompletedGroupAlgebraBoundary C (QuotientGroup.mk' N) w =
      ∑ i : X,
        zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w *
          (zcGroupLike C (zcFiniteStageTarget X N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  exact zcFreeGroupFoxDerivative_fundamental_formula C (QuotientGroup.mk' N) w

/-- Projection of the completed Fox-Euler formula to one finite pro-`C` target stage. -/
theorem zcFreeGroupFoxDerivative_fundamental_formula_finiteStageProjection
    (w : FreeGroup X)
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcCompletedGroupAlgebraBoundary C (QuotientGroup.mk' N) w) =
      ∑ i : X,
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
          (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) *
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
          (zcGroupLike C (zcFiniteStageTarget X N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have h := congrArg
    (zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j)
    (zcFreeGroupFoxDerivative_fundamental_formula_quotientMap C N w)
  rw [zcCompletedGroupAlgebraProjection_sum] at h
  simpa using h

/-- Projection of the completed Fox-Euler formula with derivative coordinates rewritten as
finite Fox derivatives at the selected pro-`C` coefficient modulus. -/
theorem zcFreeGroupFoxDerivative_fundamental_formula_finiteStageProjection_stageMap
    (w : FreeGroup X)
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcCompletedGroupAlgebraBoundary C (QuotientGroup.mk' N) w) =
      ∑ i : X,
        (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
         modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (finiteFoxStageDerivative (X := X) N j.1.modulus i w)) *
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
          (zcGroupLike C (zcFiniteStageTarget X N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rw [zcFreeGroupFoxDerivative_fundamental_formula_finiteStageProjection C N w j]
  apply Finset.sum_congr rfl
  intro i _
  rw [zcFreeGroupFoxDerivative_finiteStageProjection C N j i w]

end FundamentalFormula

end FiniteStageCompletedComparison

section FiniteTargetStageZero

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X : Type u} [DecidableEq X]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [DiscreteTopology H]

include hC

/-- Surjective-target form of finite-stage zero from completed universal zero.

The quotient-map theorem is applied after transporting the target along
`FreeGroup X / ker ψ ≃* H`; this avoids redoing the quotient identification at Crowell use sites. -/
theorem finiteFoxStageDerivativeVector_eq_zero_of_zcUnivDiff_eq_zero_of_surj
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hCH : C.pred H)
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    {w : FreeGroup X}
    (hw : zcUniversalDifferential C ψ w = 0) :
    finiteFoxStageDerivativeVector (X := X) ψ.ker j.modulus w = 0 := by
  let N : Subgroup (FreeGroup X) := ψ.ker
  let Q : Type u := finiteFoxStageTargetQuotient (X := X) N
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  letI : IsTopologicalGroup Q := inferInstance
  let e : Q ≃* H := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let q : FreeGroup X →* Q := QuotientGroup.mk' N
  have hQ : C.pred Q :=
    ProCGroups.FiniteGroupClass.IsomClosed.of_mulEquiv hIso e.symm hCH
  have he_apply (g : FreeGroup X) : e (q g) = ψ g := by
    change QuotientGroup.quotientKerEquivOfSurjective ψ hψ
        (QuotientGroup.mk' ψ.ker g) = ψ g
    rfl
  let eSymm : H →ₜ* Q :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  have hcompSymm : eSymm.toMonoidHom.comp ψ = q := by
    apply MonoidHom.ext
    intro g
    apply e.injective
    change e (e.symm (ψ g)) = e (q g)
    simpa using (he_apply g).symm
  have hq :
      zcUniversalDifferential C q w = 0 := by
    have htarget :
        zcUniversalDifferential C (eSymm.toMonoidHom.comp ψ) w = 0 :=
      zcUniversalDifferential_eq_zero_of_target C hC ψ eSymm hw
    rwa [hcompSymm] at htarget
  exact
    finiteFoxStageDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := C) (X := X) N hIso hQ j hq

/-- Finite-quotient commutator conclusion from completed universal zero, assuming only the
finite-stage Magnus reverse inclusion at the pro-`C` coefficient moduli that kill the finite
kernel.

The coefficient modulus is not an extra hypothesis: under formation plus hereditary hypotheses,
`ProCIntegerIndex.exists_index_kills_finite_group_of_mem` chooses an allowed modulus that kills
`ker β`, and this is the only finite-stage Magnus input used below. -/
theorem mem_commutator_ker_of_zcUnivDiff_eq_zero_of_finite_magnus_surj
    [Fintype X]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hCH : C.pred H)
    {Q : Type u} [Group Q]
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (hCker : C.pred β.ker)
    (hmag :
      ∀ j : ProCGroups.Completion.ProCIntegerIndex C,
        (∀ k : β.ker, k ^ j.modulus = 1) →
          ∀ w : FreeGroup X,
            w ∈ (β.comp α).ker →
            residueUniversalDifferential j.modulus
                (QuotientGroup.mk' (β.comp α).ker) w = 0 →
              w ∈ finiteFoxCommutatorPowerSubgroup
                (F := FreeGroup X) (β.comp α).ker j.modulus)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hzero : zcUniversalDifferential C (β.comp α) w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  letI : Finite β.ker := hForm.finiteOnly hCker
  rcases ProCGroups.Completion.ProCIntegerIndex.exists_index_kills_finite_group_of_mem
      (C := C) hForm hC hCker with ⟨j, hpow⟩
  have hψ : Function.Surjective (β.comp α) := by
    intro h
    rcases hβ h with ⟨q, rfl⟩
    rcases hα q with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hder :
      finiteFoxStageDerivativeVector (X := X) (β.comp α).ker j.modulus w = 0 :=
    finiteFoxStageDerivativeVector_eq_zero_of_zcUnivDiff_eq_zero_of_surj
      (C := C) (X := X) hC hForm.isomClosed hCH
      (β.comp α) hψ j hzero
  have hres :
      residueUniversalDifferential j.modulus
          (QuotientGroup.mk' (β.comp α).ker) w = 0 :=
    (finiteFoxStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
      (X := X) (β.comp α).ker j.modulus w).1 hder
  exact
    mem_commutator_ker_of_residueUniversalDifferential_eq_zero_of_kernel_le
      (X := X) α β j.modulus hpow (hmag j hpow) hwker hres

end FiniteTargetStageZero

end

end FoxDifferential
