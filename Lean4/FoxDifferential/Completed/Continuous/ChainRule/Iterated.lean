import FoxDifferential.Completed.Continuous.ChainRule.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/ChainRule/Iterated.lean
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

universe u

section AllFiniteIteratedChainRule

variable {X Y Z F F' F'' H : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [Fintype Y] [DecidableEq Y] [TopologicalSpace Y] [DiscreteTopology Y]
variable [DecidableEq Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [Group F''] [TopologicalSpace F''] [IsTopologicalGroup F'']
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The pulled-back target generator on the middle free source in a two-step source chain. -/
abbrev allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
    {mu : Z → F''}
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (θ : F' →* F'') (φ : Z → H) (κ : Y → F') : Y → H :=
  allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
    (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ

/-- The pulled-back target generator on the first free source in a two-step source chain. -/
abbrev allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
    {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →* F') (θ : F' →* F'') (φ : Z → H) (ι : X → F) : X → H :=
  allFiniteProC_freeProCZCCompletedFoxPullbackGenerator
    (X := X) (Y := Y) (F := F) (F' := F') hκ η
    (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
      (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
    ι

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- Completed Fox-Jacobian functoriality for two composable continuous free pro-`C` source maps,
as a composition of finite linear maps. -/
theorem allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_comp_comp
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →* F') (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) :
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := Z) (F := F) (F' := F'') hmu (θ.comp η) φ ι =
      (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ).comp
        (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι) := by
  classical
  apply linearMap_ext_pi_single
  intro x
  have hchain := allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
    (X := Y) (Y := Z) (F := F') (F' := F'') (H := H)
    hκ hmu θ hθ_continuous φ (η (ι x))
  simpa [LinearMap.comp_apply,
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap,
    allFiniteProC_freeProCZCCompletedFoxJacobian,
    allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator] using hchain

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- Completed Fox-Jacobian functoriality for two composable continuous free pro-`C` source maps,
as a matrix product. -/
theorem allFiniteProC_freeProCZCCompletedFoxJacobianMatrix_comp_comp
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →* F') (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) :
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := Z) (F := F) (F' := F'') hmu (θ.comp η) φ ι =
      allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι *
        allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ := by
  apply Matrix.ext
  intro x z
  have h := congrFun
    (allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
      (X := Y) (Y := Z) (F := F') (F' := F'') (H := H)
      hκ hmu θ hθ_continuous φ (η (ι x))) z
  simpa [Matrix.mul_apply,
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrix,
    allFiniteProC_freeProCZCCompletedFoxJacobian,
    allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator] using h

/-- Three-term completed pro-`C` Fox chain rule, vector form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →* F') (hη_continuous : Continuous η)
    (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) =
      allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ
        (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι
          (freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η θ φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)) g)) := by
  calc
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) =
      allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProCGroups.ProC.allFiniteProC) hκ
          (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Y H)
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Y H
            (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)) (η g)) := by
        exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
          (X := Y) (Y := Z) (F := F') (F' := F'') (H := H)
          hκ hmu θ hθ_continuous φ (η g)
    _ =
      allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ
        (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι
          (freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η θ φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)) g)) := by
        exact congrArg
          (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
            (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ)
          (allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp
            (X := X) (Y := Y) (F := F) (F' := F') (H := H)
            hι hκ η hη_continuous
            (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ) g)

/-- Three-term completed pro-`C` Fox chain rule, matrix form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →* F') (hη_continuous : Continuous η)
    (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) =
      Matrix.vecMul
        (Matrix.vecMul
          (freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η θ φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)) g)
          (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
            (X := X) (Y := Y) (F := F) (F' := F') hκ η
            (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
            ι))
        (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ) := by
  rw [allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η hη_continuous θ hθ_continuous φ g]
  rw [allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul]
  rw [allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul]

/-- Three-term completed pro-`C` Fox chain rule, component form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_apply
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →* F') (hη_continuous : Continuous η)
    (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) (g : F) (z : Z) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) z =
      ∑ y : Y,
        (∑ x : X,
          freeProCZCCompletedFoxDerivativeVector
              (ProC := ProCGroups.ProC.allFiniteProC) hι
              (allFiniteProC_zcCompletedFoxSemidirect ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)
              (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProCGroups.ProC.allFiniteProC) X H
                (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                  (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                  hκ hmu η θ φ ι)) g x *
            allFiniteProC_freeProCZCCompletedFoxJacobian
              (X := X) (Y := Y) (F := F) (F' := F') hκ η
              (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
                (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
              ι x y) *
          allFiniteProC_freeProCZCCompletedFoxJacobian
            (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ y z := by
  have h := congrFun
      (allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix
        (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
      hι hκ hmu η hη_continuous θ hθ_continuous φ g) z
  simpa [Matrix.vecMul, dotProduct,
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrix] using h

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X] [IsTopologicalGroup F] in
/-- Continuous-homomorphism form of completed Fox-Jacobian functoriality, as a composition of
finite linear maps. -/
theorem allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_comp_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) :
    allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := Z) (F := F) (F' := F'') hmu
        (θ.toMonoidHom.comp η.toMonoidHom) φ ι =
      (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ).comp
        (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
          ι) := by
  exact allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hκ hmu η.toMonoidHom θ.toMonoidHom θ.continuous_toFun φ

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [IsTopologicalGroup F] in
/-- Continuous-homomorphism form of completed Fox-Jacobian functoriality, as a matrix product. -/
theorem allFiniteProC_freeProCZCCompletedFoxJacobianMatrix_comp_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) :
    allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := Z) (F := F) (F' := F'') hmu
        (θ.toMonoidHom.comp η.toMonoidHom) φ ι =
      allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
          ι *
        allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ := by
  exact allFiniteProC_freeProCZCCompletedFoxJacobianMatrix_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hκ hmu η.toMonoidHom θ.toMonoidHom θ.continuous_toFun φ

/-- Continuous-homomorphism form of the three-term completed pro-`C` Fox chain rule. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) =
      allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ
        (allFiniteProC_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
          (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
          ι
          (freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect
              ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
              (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)) g)) := by
  exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η.toMonoidHom η.continuous_toFun θ.toMonoidHom θ.continuous_toFun φ g

/-- Continuous-homomorphism form of the three-term completed pro-`C` Fox chain rule, matrix
form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) =
      Matrix.vecMul
        (Matrix.vecMul
          (freeProCZCCompletedFoxDerivativeVector
            (ProC := ProCGroups.ProC.allFiniteProC) hι
            (allFiniteProC_zcCompletedFoxSemidirect
              ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
            (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
              (ProC := ProCGroups.ProC.allFiniteProC) X H
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)) g)
          (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
            (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
            (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
            ι))
        (allFiniteProC_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ) := by
  exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η.toMonoidHom η.continuous_toFun θ.toMonoidHom θ.continuous_toFun φ g

/-- Continuous-homomorphism form of the three-term completed pro-`C` Fox chain rule, component
form. -/
theorem allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_apply_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.allFiniteProC) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) (g : F) (z : Z) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProCGroups.ProC.allFiniteProC) hmu
        (allFiniteProC_zcCompletedFoxSemidirect
          ProCGroups.ProC.allFiniteProC.finiteQuotientClass Z H) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProCGroups.ProC.allFiniteProC) Z H φ) (θ (η g)) z =
      ∑ y : Y,
        (∑ x : X,
          freeProCZCCompletedFoxDerivativeVector
              (ProC := ProCGroups.ProC.allFiniteProC) hι
              (allFiniteProC_zcCompletedFoxSemidirect
                ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
              (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)
              (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
                (ProC := ProCGroups.ProC.allFiniteProC) X H
                (allFiniteProC_freeProCZCCompletedFoxFirstPullbackGenerator
                  (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                  hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)) g x *
            allFiniteProC_freeProCZCCompletedFoxJacobian
              (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
              (allFiniteProC_freeProCZCCompletedFoxMiddlePullbackGenerator
                (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
              ι x y) *
          allFiniteProC_freeProCZCCompletedFoxJacobian
            (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ y z := by
  exact allFiniteProC_freeProCZCCompletedFoxDerivativeVector_comp_comp_apply
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η.toMonoidHom η.continuous_toFun θ.toMonoidHom θ.continuous_toFun φ g z

end AllFiniteIteratedChainRule

end

end FoxDifferential
