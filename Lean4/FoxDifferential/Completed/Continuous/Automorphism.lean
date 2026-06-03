import FoxDifferential.Completed.Continuous.ChainRule.Iterated

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Automorphism.lean
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

section AllFiniteAutomorphismJacobian

variable {X F H : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The named inverse linear map for the completed Fox-Jacobian of a continuous automorphism. -/
def allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (φ : X → H) :
    ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) :=
  allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
    (X := X) (Y := X) (F := F) (F' := F) hι e.symm.toMonoidHom
    (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι)
    ι

/-- The named inverse matrix for the completed Fox-Jacobian of a continuous automorphism. -/
def allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (φ : X → H) :
    Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) :=
  allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
    (X := X) (Y := X) (F := F) (F' := F) hι e.symm.toMonoidHom
    (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι)
    ι

/-- A finite-stage projection of the named inverse matrix for a completed Fox-Jacobian of a
continuous automorphism. -/
def allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (φ : X → H)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) :
    Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j) :=
  fun x y =>
    zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j
      (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
        (X := X) (F := F) (H := H) hι e φ x y)

omit [Fintype X] in
/-- Evaluation of the finite-stage inverse matrix for a completed Fox-Jacobian of a continuous
automorphism. -/
@[simp]
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage_apply
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (φ : X → H)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) (x y : X) :
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
        (X := X) (F := F) (H := H) hι e φ j x y =
      zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j
        (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
          (X := X) (F := F) (H := H) hι e φ x y) :=
  rfl

/-- The named inverse linear map is row-vector multiplication by the named inverse matrix. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (φ : X → H)
    (v : ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H)) :
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
        (X := X) (F := F) (H := H) hι e φ v =
      Matrix.vecMul v
        (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
          (X := X) (F := F) (H := H) hι e φ) := by
  exact allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul
    (X := X) (F := F) hι e.symm.toMonoidHom
    (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι)
    ι v

omit [Fintype X] in
/-- Pulling the target generator map first along an automorphism and then along its inverse
recovers the original generator map. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphism_pullback_symm
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H) :
    allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
        (X := X) (F := F) hι e.symm.toMonoidHom
        (allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hι e.toMonoidHom φ ι)
        ι =
      φ := by
  let htarget : ProCGroups.ProC.allFiniteProC
      (G := ZCCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H) :=
    allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H
  let hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProCGroups.ProC.allFiniteProC) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H φ
  let φe : X → H :=
    allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι
  let hφe : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProCGroups.ProC.allFiniteProC) φe) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H φe
  have hρ := allFiniteProC_freeProCZCCompletedFoxRightHom_comp
    (X := X) (Y := X) (F := F) (F' := F) (H := H)
    hι hι e.toMonoidHom he_continuous φ
  funext x
  change freeProCZCCompletedFoxRightHom
      (ProC := ProCGroups.ProC.allFiniteProC) hι htarget φe hφe
      (e.symm (ι x)) = φ x
  have happ := congrFun (congrArg DFunLike.coe hρ) (e.symm (ι x))
  calc
    freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) hι htarget φe hφe
        (e.symm (ι x)) =
        ((freeProCZCCompletedFoxRightHom
          (ProC := ProCGroups.ProC.allFiniteProC) hι htarget φ hφ).comp
          e.toMonoidHom) (e.symm (ι x)) := by
          simpa [φe, htarget, hφ, hφe] using happ
    _ = freeProCZCCompletedFoxRightHom
        (ProC := ProCGroups.ProC.allFiniteProC) hι htarget φ hφ (ι x) := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
  MulEquiv.apply_symm_apply, freeProCZCCompletedFoxRightHom_apply, freeProCZCCompletedFoxSemidirectLift_generator,
  freeProCZCCompletedFoxSemidirectGenerator_right]
    _ = φ x := by
          simp only [freeProCZCCompletedFoxRightHom_apply, freeProCZCCompletedFoxSemidirectLift_generator,
  freeProCZCCompletedFoxSemidirectGenerator_right]

/-- The completed Fox-Jacobian linear map of a continuous automorphism composed with its named
inverse is the identity. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_comp_inverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H) :
    (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι).comp
      (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
        (X := X) (F := F) (H := H) hι e φ) =
      LinearMap.id := by
  apply linearMap_ext_pi_single
  intro x
  have hchain := allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := X) (F := F) (F' := F) (H := H)
    hι hι e.toMonoidHom he_continuous φ (e.symm (ι x))
  simpa [LinearMap.comp_apply,
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse,
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap,
    allFiniteProC_freeProCZCCompletedFoxJacobian] using hchain.symm

/-- The named inverse for the completed Fox-Jacobian linear map of a continuous automorphism
composed with the Jacobian is the identity. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_inverse_comp
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) :
    (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
        (X := X) (F := F) (H := H) hι e φ).comp
      (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι) =
      LinearMap.id := by
  apply linearMap_ext_pi_single
  intro x
  let φe : X → H :=
    allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι
  have hpull :
      allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hι e.symm.toMonoidHom φe ι =
        φ := by
    simpa [φe] using
      allFiniteProC_freeProCZCCompletedFoxAutomorphism_pullback_symm
        (X := X) (F := F) (H := H) hι e he_continuous φ
  have hchain := allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := X) (F := F) (F' := F) (H := H)
    hι hι e.symm.toMonoidHom he_symm_continuous φe (e (ι x))
  rw [hpull] at hchain
  simpa [LinearMap.comp_apply,
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse,
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap,
    allFiniteProC_freeProCZCCompletedFoxJacobian, φe] using hchain.symm

/-- The named inverse matrix is a left inverse for the completed Fox-Jacobian matrix of a
continuous automorphism. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse_mul
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H) :
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
        (X := X) (F := F) (H := H) hι e φ *
      allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι =
      (1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H)) := by
  rw [Matrix.ext_iff_vecMul]
  intro v
  have hlin :=
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_comp_inverse
      (X := X) (F := F) (H := H) hι e he_continuous φ
  have happ := congrFun (congrArg DFunLike.coe hlin) v
  simpa [LinearMap.comp_apply,
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul,
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul,
    Matrix.vecMul_vecMul, Matrix.vecMul_one] using happ

/-- The named inverse matrix is a right inverse for the completed Fox-Jacobian matrix of a
continuous automorphism. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrix_mul_inverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) :
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι *
      allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
        (X := X) (F := F) (H := H) hι e φ =
      (1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H)) := by
  rw [Matrix.ext_iff_vecMul]
  intro v
  have hlin :=
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_inverse_comp
      (X := X) (F := F) (H := H) hι e he_continuous he_symm_continuous φ
  have happ := congrFun (congrArg DFunLike.coe hlin) v
  simpa [LinearMap.comp_apply,
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul,
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul,
    Matrix.vecMul_vecMul, Matrix.vecMul_one] using happ

/-- The finite-stage inverse matrix is a left inverse for the finite-stage completed Fox-Jacobian
matrix of a continuous automorphism. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixStageInverse_mul
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) :
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
        (X := X) (F := F) (H := H) hι e φ j *
      allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι j =
      (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j)) := by
  apply Matrix.ext
  intro x y
  have h := congrArg
    (fun M : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) =>
      zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j (M x y))
    (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse_mul
      (X := X) (F := F) (H := H) hι e he_continuous φ)
  have hone :
      zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j
          ((1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H)) x y) =
        (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j)) x y := by
    by_cases hxy : x = y
    · subst y
      simp only [zcCompletedGroupAlgebraProjection, Matrix.one_apply_eq, zcCompletedGroupAlgebraProjection_one]
    · simp only [zcCompletedGroupAlgebraProjection, ne_eq, hxy, not_false_eq_true, Matrix.one_apply_ne,
  zcCompletedGroupAlgebraProjection_zero]
  simp only [Matrix.mul_apply] at h
  rw [zcCompletedGroupAlgebraProjection_sum] at h
  rw [hone] at h
  simp only [zcCompletedGroupAlgebraProjection, MulEquiv.toMonoidHom_eq_coe,
  allFiniteProC_freeProCZCCompletedFoxJacobianMatrix_apply, zcCompletedGroupAlgebraProjection_mul] at h
  simpa [Matrix.mul_apply,
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage,
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage] using h

/-- The finite-stage inverse matrix is a right inverse for the finite-stage completed Fox-Jacobian
matrix of a continuous automorphism. -/
theorem allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixStage_mul_inverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) (j : ZCCompletedGroupAlgebraIndex ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) :
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι j *
      allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
        (X := X) (F := F) (H := H) hι e φ j =
      (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j)) := by
  apply Matrix.ext
  intro x y
  have h := congrArg
    (fun M : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H) =>
      zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j (M x y))
    (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrix_mul_inverse
      (X := X) (F := F) (H := H) hι e he_continuous he_symm_continuous φ)
  have hone :
      zcCompletedGroupAlgebraProjection ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j
          ((1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H)) x y) =
        (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.ProC.allFiniteProC.finiteQuotientClass H j)) x y := by
    by_cases hxy : x = y
    · subst y
      simp only [zcCompletedGroupAlgebraProjection, Matrix.one_apply_eq, zcCompletedGroupAlgebraProjection_one]
    · simp only [zcCompletedGroupAlgebraProjection, ne_eq, hxy, not_false_eq_true, Matrix.one_apply_ne,
  zcCompletedGroupAlgebraProjection_zero]
  simp only [Matrix.mul_apply] at h
  rw [zcCompletedGroupAlgebraProjection_sum] at h
  rw [hone] at h
  simp only [zcCompletedGroupAlgebraProjection, MulEquiv.toMonoidHom_eq_coe,
  allFiniteProC_freeProCZCCompletedFoxJacobianMatrix_apply, zcCompletedGroupAlgebraProjection_mul] at h
  simpa [Matrix.mul_apply,
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrixStage,
    allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage] using h

/-- The completed Fox-Jacobian of a continuous automorphism as a linear equivalence. -/
def allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearEquiv
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) :
    ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) ≃ₗ[ZCCompletedGroupAlgebra ProCGroups.ProC.allFiniteProC.finiteQuotientClass H]
      ZCFreeFoxCoordinates ProCGroups.ProC.allFiniteProC.finiteQuotientClass (X := X) (H := H) := by
  refine LinearEquiv.ofLinear
    (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
      (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι)
    (allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
      (X := X) (F := F) (H := H) hι e φ)
    ?_ ?_
  · exact allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_comp_inverse
      (X := X) (F := F) (H := H) hι e he_continuous φ
  · exact allFiniteProC_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_inverse_comp
      (X := X) (F := F) (H := H) hι e he_continuous he_symm_continuous φ

end AllFiniteAutomorphismJacobian

end

end FoxDifferential
