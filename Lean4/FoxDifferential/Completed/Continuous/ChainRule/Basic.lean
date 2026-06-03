import FoxDifferential.Completed.Continuous.Free.Rules

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/ChainRule/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous crossed differentials

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

section AllFiniteChainRule

variable {X Y F F' H : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [DecidableEq Y] [TopologicalSpace Y] [DiscreteTopology Y]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The target generator map pulled back along a continuous homomorphism of free pro-`C` sources. -/
def allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) : X → H :=
  fun x =>
    freeProCZCCompletedFoxRightHom
      (ProC := ProCGroups.ProC.allFiniteProC) hκ
      (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ)
      (η (ι x))

/-- The completed Fox-Jacobian family of a continuous homomorphism between free pro-`C` sources. -/
def allFiniteProC_freeProCZCCompletedFoxJacobian
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) :
    X → ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) :=
  fun x =>
    freeProCZCCompletedFoxDerivativeVector
      (ProC := ProCGroups.ProC.allFiniteProC) hκ
      (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ)
      (η (ι x))

/-- The completed Fox-Jacobian family as a finite linear map on completed coordinate vectors. -/
def allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) :
    ZCFreeFoxCoordinates
        ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) →ₗ[
          ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) :=
  foxJacobianLinearMap
    (allFiniteProC_freeProCZCCompletedFoxJacobian (X := X) (F := F) hκ η φ ι)

/-- The completed Fox-Jacobian packaged as a matrix. -/
def allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) :
    Matrix X Y (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) :=
  foxJacobianMatrix
    (allFiniteProC_freeProCZCCompletedFoxJacobian (X := X) (F := F) hκ η φ ι)

/-- A finite-stage projection of the completed Fox-Jacobian matrix. -/
def allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) :
    Matrix X Y (ZCCompletedGroupAlgebraStage ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j) :=
  fun x y =>
    zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j
      (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (F := F) hκ η φ ι x y)

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- Matrix evaluation is componentwise the completed Fox-Jacobian family. -/
@[simp]
theorem allFiniteProC_freeProCZCCompletedFoxJacobianMatrix_apply
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (x : X) (y : Y) :
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (F := F) hκ η φ ι x y =
      allFiniteProC_freeProCZCCompletedFoxJacobian
        (X := X) (F := F) hκ η φ ι x y :=
  rfl

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- Evaluation of the finite-stage completed Fox-Jacobian matrix. -/
@[simp]
theorem allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage_apply
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) (x : X) (y : Y) :
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage
        (X := X) (F := F) hκ η φ ι j x y =
      zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j
        (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η φ ι x y) :=
  rfl

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- Evaluation formula for the completed Fox-Jacobian linear map. -/
@[simp]
theorem allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_apply
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (v : ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H)) (y : Y) :
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η φ ι v y =
      ∑ x : X,
        v x * allFiniteProC_freeProCZCCompletedFoxJacobian
          (X := X) (F := F) hκ η φ ι x y :=
  rfl

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- The completed Fox-Jacobian linear map is row-vector multiplication by its matrix. -/
theorem allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (v : ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H)) :
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η φ ι v =
      Matrix.vecMul v
        (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η φ ι) := by
  exact foxJacobianLinearMap_eq_vecMul
    (allFiniteProC_freeProCZCCompletedFoxJacobian (X := X) (F := F) hκ η φ ι) v

omit [Fintype X] in
/-- The canonical right homomorphism for the pulled-back generator map is the composite of the
target right homomorphism with the source homomorphism. -/
theorem allFiniteProC_freeProCZCCompletedFoxRightHom_comp
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) :
    freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) hι
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
        (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hκ η φ ι)
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
          (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η φ ι)) =
      (freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ)).comp η := by
  let htargetX : ProCGroups.ProC.allFiniteProC
      (G := ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H) :=
    allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H
  let htargetY : ProCGroups.ProC.allFiniteProC
      (G := ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) :=
    allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H
  let hφY : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProCGroups.ProC.allFiniteProC) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ
  let φX : X → H :=
    allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hκ η φ ι
  let hφX : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProCGroups.ProC.allFiniteProC) φX) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H φX
  have hHtarget : ProCGroups.ProC.allFiniteProC (G := H) :=
    (ProCGroups.ProC.allFiniteProCGroup_of_profinite
      (G := H)
      (by
        exact
          (⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ :
            ProCGroups.IsProfiniteGroup H))).isProC
  apply hι.hom_ext hHtarget
  · exact continuous_freeProCZCCompletedFoxRightHom
      (ProC := ProCGroups.ProC.allFiniteProC) X H hι htargetX φX hφX
  · exact (continuous_freeProCZCCompletedFoxRightHom
      (ProC := ProCGroups.ProC.allFiniteProC) Y H hκ htargetY φ hφY).comp hη_continuous
  · intro x
    simp only [freeProCZCCompletedFoxRightHom_apply, freeProCZCCompletedFoxSemidirectLift_generator,
  freeProCZCCompletedFoxSemidirectGenerator_right, allFiniteProC_freeProCZCCompletedFoxPullbackGenerator,
  MonoidHom.coe_comp, Function.comp_apply]

/-- Completed pro-`C` Fox chain rule, vector form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ) (η g) =
      allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η φ ι
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProCGroups.ProC.allFiniteProC) hι
          (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
          (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
            (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η φ ι)) g) := by
  let htargetX : ProCGroups.ProC.allFiniteProC
      (G := ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H) :=
    allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H
  let htargetY : ProCGroups.ProC.allFiniteProC
      (G := ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) :=
    allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H
  let hφY : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProCGroups.ProC.allFiniteProC) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ
  let ρY : F' →* H :=
    freeProCZCCompletedFoxRightHom (ProC := ProCGroups.ProC.allFiniteProC)
      hκ htargetY φ hφY
  let DY : F' → ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) :=
    freeProCZCCompletedFoxDerivativeVector (ProC := ProCGroups.ProC.allFiniteProC)
      hκ htargetY φ hφY
  let φX : X → H :=
    allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hκ η φ ι
  let hφX : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProCGroups.ProC.allFiniteProC) φX) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H φX
  let ρX : F →* H :=
    freeProCZCCompletedFoxRightHom (ProC := ProCGroups.ProC.allFiniteProC)
      hι htargetX φX hφX
  let DX : F → ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) :=
    freeProCZCCompletedFoxDerivativeVector (ProC := ProCGroups.ProC.allFiniteProC)
      hι htargetX φX hφX
  let jac : X → ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) :=
    allFiniteProC_freeProCZCCompletedFoxJacobian
      (X := X) (F := F) hκ η φ ι
  let L :
      ZCFreeFoxCoordinates
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) →ₗ[
            ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) :=
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
      (X := X) (F := F) hκ η φ ι
  let beta : F → ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) := fun g => DY (η g)
  let gamma : F → ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := Y) (H := H) := fun g => L (DX g)
  have hρX : ρX = ρY.comp η := by
    simpa [ρX, ρY, φX, htargetX, htargetY, hφX, hφY] using
      allFiniteProC_freeProCZCCompletedFoxRightHom_comp
        (X := X) (Y := Y) (F := F) (F' := F') (H := H) hι hκ η hη_continuous φ
  have hbeta_cross : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProCGroups.ProC.allFiniteProC.finiteQuotientClass ρX) beta := by
    intro a b
    have hDY := freeProCZCCompletedFoxDerivativeVector_isCrossedDifferential
      (ProC := ProCGroups.ProC.allFiniteProC) hκ htargetY φ hφY (η a) (η b)
    simpa [beta, DY, hρX, MonoidHom.comp_apply] using hDY
  have hgamma_cross : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProCGroups.ProC.allFiniteProC.finiteQuotientClass ρX) gamma := by
    exact IsCrossedDifferential.map_linear
      (freeProCZCCompletedFoxDerivativeVector_isCrossedDifferential
        (ProC := ProCGroups.ProC.allFiniteProC) hι htargetX φX hφX) L
  have hbeta_continuous : Continuous beta := by
    exact (continuous_freeProCZCCompletedFoxDerivativeVector
      (ProC := ProCGroups.ProC.allFiniteProC) Y H hκ htargetY φ hφY).comp hη_continuous
  have hgamma_continuous : Continuous gamma := by
    refine continuous_pi fun y => ?_
    change Continuous (fun g : F => ∑ x : X, DX g x * jac x y)
    exact continuous_finset_sum _ fun x _ =>
      ((continuous_apply x).comp
        (continuous_freeProCZCCompletedFoxDerivativeVector
          (ProC := ProCGroups.ProC.allFiniteProC) X H hι htargetX φX hφX)).mul
        continuous_const
  have hgen : ∀ x : X, beta (ι x) = gamma (ι x) := by
    intro x
    have hsingle :
        L ((Pi.single x (1 : ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H)) :
          ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H)) = jac x := by
      simp only [allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap, foxJacobianLinearMap_single, L, jac]
    simpa [beta, gamma, DX, jac] using hsingle.symm
  let f : F →* ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX beta hbeta_cross
  let h : F →* ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX gamma hgamma_cross
  have hf_continuous : Continuous f :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX beta hbeta_cross hbeta_continuous
      (continuous_freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) X H hι htargetX φX hφX)
  have hh_continuous : Continuous h :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX gamma hgamma_cross hgamma_continuous
      (continuous_freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) X H hι htargetX φX hφX)
  have hfg : ∀ x : X, f (ι x) = h (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hgen x
    · rfl
  have hfh : f = h := hι.hom_ext htargetY hf_continuous hh_continuous hfg
  have hleft := congrArg (fun q : F →* ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H => (q g).left) hfh
  simpa [f, h, beta, gamma, L, DY, DX, jac, htargetX, htargetY, hφY, hφX, ρY, ρX, φX,
    allFiniteProC_freeProCZCCompletedFoxPullbackGenerator,
    allFiniteProC_freeProCZCCompletedFoxJacobian,
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap] using hleft

/-- Completed pro-`C` Fox chain rule, component form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_apply
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) (g : F) (y : Y) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ) (η g) y =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
                (X := X) (F := F) hκ η φ ι)) g x *
          allFiniteProC_freeProCZCCompletedFoxJacobian
            (X := X) (F := F) hκ η φ ι x y := by
  have h := congrFun
    (allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
      (X := X) (Y := Y) (F := F) (F' := F') (H := H)
      hι hκ η hη_continuous φ g) y
  simpa using h

/-- Completed pro-`C` Fox chain rule, matrix form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_matrix
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H φ) (η g) =
      Matrix.vecMul
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProCGroups.ProC.allFiniteProC) hι
          (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
          (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
            (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η φ ι)) g)
        (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η φ ι) := by
  rw [allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η hη_continuous φ g]
  exact allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul
    (X := X) (F := F) hκ η φ ι
    (freeProCZCCompletedFoxDerivativeVector
      (ProC := ProCGroups.ProC.allFiniteProC) hι
      (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
      (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
        (X := X) (F := F) hκ η φ ι)
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
        (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hκ η φ ι)) g)

omit [Fintype X] in
/-- Continuous-homomorphism form of the right-homomorphism chain rule. -/
theorem allFiniteProC_freeProCZCCompletedFoxRightHom_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →ₜ* F') (φ : Y → H) :
    freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) hι
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
        (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hκ η.toMonoidHom φ ι)
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) X H
          (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η.toMonoidHom φ ι)) =
      (freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Y H φ)).comp η.toMonoidHom := by
  exact allFiniteProC_freeProCZCCompletedFoxRightHom_comp
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ

/-- Continuous-homomorphism form of the completed pro-`C` Fox chain rule, vector form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →ₜ* F') (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Y H φ) (η g) =
      allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η.toMonoidHom φ ι
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProCGroups.ProC.allFiniteProC) hι
          (allFiniteProC_zcCompletedFoxSemidirect
            ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
          (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η.toMonoidHom φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProCGroups.ProC.allFiniteProC) X H
            (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η.toMonoidHom φ ι)) g) := by
  exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ g

/-- Continuous-homomorphism form of the completed pro-`C` Fox chain rule, component form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_apply_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →ₜ* F') (φ : Y → H) (g : F) (y : Y) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Y H φ) (η g) y =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect
              ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η.toMonoidHom φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
              (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
                (X := X) (F := F) hκ η.toMonoidHom φ ι)) g x *
          allFiniteProC_freeProCZCCompletedFoxJacobian
            (X := X) (F := F) hκ η.toMonoidHom φ ι x y := by
  exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_apply
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ g y

/-- Continuous-homomorphism form of the completed pro-`C` Fox chain rule, matrix form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_matrix_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (η : F →ₜ* F') (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hκ
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Y H φ) (η g) =
      Matrix.vecMul
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProCGroups.ProC.allFiniteProC) hι
          (allFiniteProC_zcCompletedFoxSemidirect
            ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
          (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η.toMonoidHom φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProCGroups.ProC.allFiniteProC) X H
            (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η.toMonoidHom φ ι)) g)
        (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η.toMonoidHom φ ι) := by
  exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_matrix
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ g

end AllFiniteChainRule

end

end FoxDifferential
