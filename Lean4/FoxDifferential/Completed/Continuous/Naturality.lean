import FoxDifferential.Completed.Continuous.Free.Rules

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Naturality.lean
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

open ProCGroups.Completion
open ProCGroups.InverseSystems
open ProCGroups.ProC
open scoped BigOperators

universe u v

section ContinuousTargetMaps

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {H K : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The completed group-algebra map induced by a continuous target homomorphism is continuous. -/
theorem continuous_zcCompletedGroupAlgebraMap (η : H →ₜ* K) :
    Continuous (zcCompletedGroupAlgebraMap C hC η) := by
  refine Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C K)
    (continuous_pi fun i => ?_) (fun x => (zcCompletedGroupAlgebraMap C hC η x).2)
  let sourceIndex : ZCCompletedGroupAlgebraIndex C H :=
    (i.1, completedGroupAlgebraComapIndexInClass
      (G := H) (H := K) C hC η i.2)
  letI : TopologicalSpace (ZCCompletedGroupAlgebraStage C H sourceIndex) := ⊥
  letI : DiscreteTopology (ZCCompletedGroupAlgebraStage C H sourceIndex) := ⟨rfl⟩
  have hstage : Continuous (zcCompletedGroupAlgebraMapStage C hC η i) :=
    continuous_of_discreteTopology
  exact hstage.comp ((continuous_apply sourceIndex).comp continuous_subtype_val)

/-- A surjective target homomorphism induces a surjective completed group-algebra map. -/
theorem zcCompletedGroupAlgebraMap_surjective_of_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (η : H →ₜ* K) (hη : Function.Surjective η) :
    Function.Surjective (zcCompletedGroupAlgebraMap C hC η) := by
  let S := zcCompletedGroupAlgebraSystem C K
  let ψ : ∀ i : ZCCompletedGroupAlgebraIndex C K,
      ZCCompletedGroupAlgebra C H → S.X i :=
    fun i x => zcCompletedGroupAlgebraProjection C K i
      (zcCompletedGroupAlgebraMap C hC η x)
  have hψcont : ∀ i, Continuous (ψ i) := by
    intro i
    exact (continuous_apply i).comp
      (continuous_subtype_val.comp (continuous_zcCompletedGroupAlgebraMap C hC η))
  have hψcompat : S.CompatibleMaps ψ := by
    intro i j hij
    funext x
    change zcCompletedGroupAlgebraTransition C K hij
        (zcCompletedGroupAlgebraProjection C K j
          (zcCompletedGroupAlgebraMap C hC η x)) =
      zcCompletedGroupAlgebraProjection C K i
        (zcCompletedGroupAlgebraMap C hC η x)
    exact (zcCompletedGroupAlgebraMap C hC η x).2 i j hij
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i y
    rcases zcCompletedGroupAlgebraMapStage_surjective_of_surjective
        C hC η hη i y with ⟨y₀, hy₀⟩
    rcases zcCompletedGroupAlgebraProjection_surjective C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC η i.2) y₀ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    dsimp [ψ]
    rw [hx, hy₀]
  letI : Nonempty (ZCCompletedGroupAlgebraIndex C K) :=
    ⟨(ProCIntegerIndex.terminal (C := C) inferInstance, zcCompletedGroupAlgebraTopIndex C K)⟩
  have hdir : Directed (· ≤ ·)
      (id : ZCCompletedGroupAlgebraIndex C K → ZCCompletedGroupAlgebraIndex C K) := by
    intro i j
    rcases ProCIntegerIndex.directed_of_formation hForm i.1 j.1 with
      ⟨n, hin, hjn⟩
    rcases directed_openNormalSubgroupInClass
        (C := C) (G := K) hForm i.2 j.2 with
      ⟨U, hiU, hjU⟩
    exact ⟨(n, U), ⟨hin, hiU⟩, ⟨hjn, hjU⟩⟩
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C K, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  have hlift : Function.Surjective (S.inverseLimitLift ψ hψcompat) :=
    S.surjective_inverseLimitLift ψ hψcont hψcompat hψsurj hdir
  intro y
  rcases hlift y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : S.inverseLimit => S.projection i z) hx
  simpa [S, ψ] using hi

/-- A surjective completed group-algebra map is a quotient map. -/
theorem isQuotientMap_zcCompletedGroupAlgebraMap_of_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (η : H →ₜ* K) (hη : Function.Surjective η) :
    Topology.IsQuotientMap (zcCompletedGroupAlgebraMap C hC η) :=
  IsQuotientMap.of_surjective_continuous
    (zcCompletedGroupAlgebraMap_surjective_of_surjective C hC hForm η hη)
    (continuous_zcCompletedGroupAlgebraMap C hC η)

/-- A surjective completed group-algebra map is an open quotient map as an additive-group
homomorphism. -/
theorem isOpenQuotientMap_zcCompletedGroupAlgebraMap_of_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (η : H →ₜ* K) (hη : Function.Surjective η) :
    IsOpenQuotientMap (zcCompletedGroupAlgebraMap C hC η) :=
  AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
    (isQuotientMap_zcCompletedGroupAlgebraMap_of_surjective C hC hForm η hη)

variable {X : Type v}

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The coordinatewise target map on completed Fox-coordinate vectors is continuous. -/
theorem continuous_zcFreeFoxCoordinatesMap (η : H →ₜ* K) :
    Continuous (zcFreeFoxCoordinatesMap (X := X) C hC η) := by
  refine continuous_pi fun x => ?_
  exact (continuous_zcCompletedGroupAlgebraMap C hC η).comp (continuous_apply x)

end ContinuousTargetMaps

section SourceBoundaryNaturality

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X H K : Type u} [Fintype X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Source-shaped completed Fox boundary maps are natural in the target group. -/
theorem freeProCZCCompletedFoxBoundary_mapTarget
    (η : H →ₜ* K) (φ : X → H)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcCompletedGroupAlgebraMap C hC η (freeProCZCCompletedFoxBoundary C φ v) =
      freeProCZCCompletedFoxBoundary C (fun x : X => η (φ x))
        (zcFreeFoxCoordinatesMap (X := X) C hC η v) := by
  simp only [freeProCZCCompletedFoxBoundary_apply, map_sum, map_mul, map_sub,
    zcCompletedGroupAlgebraMap_groupLike, map_one, zcFreeFoxCoordinatesMap]

end SourceBoundaryNaturality

section SemidirectTargetMap

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X H K : Type u} [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Target functoriality for completed Fox semidirect products. -/
def zcCompletedFoxSemidirectMapTarget (η : H →ₜ* K) :
    ZCCompletedFoxSemidirect C X H →* ZCCompletedFoxSemidirect C X K where
  toFun a :=
    { left := zcFreeFoxCoordinatesMap (X := X) C hC η a.left
      right := η a.right }
  map_one' := by
    ext x
    · simp only [ZCCompletedFoxSemidirect.one_left, zcFreeFoxCoordinatesMap_apply,
        Pi.zero_apply, map_zero, zcCompletedGroupAlgebraProjection_zero, Finsupp.coe_zero]
    · simp only [ZCCompletedFoxSemidirect.one_right, map_one]
  map_mul' a b := by
    ext x
    · simp only [ZCCompletedFoxSemidirect.mul_left, zcFreeFoxCoordinatesMap_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        zcCompletedGroupAlgebraMap_groupLike, zcCompletedGroupAlgebraProjection_add,
        zcCompletedGroupAlgebraProjection_map, zcCompletedGroupAlgebraProjection_mul,
        zcCompletedGroupAlgebraProjection_groupLike, MonoidAlgebra.of_apply,
        MonoidAlgebra.coe_add, MonoidAlgebra.single_mul_apply, one_mul]
    · simp only [ZCCompletedFoxSemidirect.mul_right, map_mul]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- Left component of the target map on completed Fox semidirect products. -/
@[simp]
theorem zcCompletedFoxSemidirectMapTarget_left
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTarget (X := X) C hC η a).left =
      zcFreeFoxCoordinatesMap (X := X) C hC η a.left :=
  rfl

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- Right component of the target map on completed Fox semidirect products. -/
@[simp]
theorem zcCompletedFoxSemidirectMapTarget_right
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTarget (X := X) C hC η a).right = η a.right :=
  rfl

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The target map on completed Fox semidirect products is continuous. -/
theorem continuous_zcCompletedFoxSemidirectMapTarget
    (η : H →ₜ* K) :
    Continuous (zcCompletedFoxSemidirectMapTarget (X := X) C hC η) := by
  rw [continuous_induced_rng]
  refine (continuous_zcFreeFoxCoordinatesMap (X := X) C hC η).comp
      (continuous_zcCompletedFoxSemidirect_left C X H) |>.prodMk ?_
  exact η.continuous_toFun.comp (continuous_zcCompletedFoxSemidirect_right C X H)

/-- Target functoriality for completed Fox semidirect products as a continuous homomorphism. -/
def zcCompletedFoxSemidirectMapTargetHom (η : H →ₜ* K) :
    ZCCompletedFoxSemidirect C X H →ₜ* ZCCompletedFoxSemidirect C X K where
  toMonoidHom := zcCompletedFoxSemidirectMapTarget (X := X) C hC η
  continuous_toFun := continuous_zcCompletedFoxSemidirectMapTarget (X := X) C hC η

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The continuous target map has the expected underlying homomorphism. -/
@[simp]
theorem zcCompletedFoxSemidirectMapTargetHom_toMonoidHom
    (η : H →ₜ* K) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η).toMonoidHom =
      zcCompletedFoxSemidirectMapTarget (X := X) C hC η :=
  rfl

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- Left component of the continuous target map on completed Fox semidirect products. -/
@[simp]
theorem zcCompletedFoxSemidirectMapTargetHom_left
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η a).left =
      zcFreeFoxCoordinatesMap (X := X) C hC η a.left :=
  rfl

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- Right component of the continuous target map on completed Fox semidirect products. -/
@[simp]
theorem zcCompletedFoxSemidirectMapTargetHom_right
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η a).right = η a.right :=
  rfl

end SemidirectTargetMap

section SourceNaturality

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
variable (hC : ProCGroups.FiniteGroupClass.Hereditary ProC.finiteQuotientClass)
include hC
variable {X F H K : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] [Fintype X] in
/-- Target naturality of the canonical completed Fox semidirect lift. -/
theorem freeProCZCCompletedFoxSemidirectLift_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetH :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetK :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) :
    zcCompletedFoxSemidirectMapTarget (X := X) ProC.finiteQuotientClass hC η
        (freeProCZCCompletedFoxSemidirectLift
          (ProC := ProC) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ) g) =
      freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProC) X K (fun x : X => η (φ x))) g := by
  let hφH : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X H φ
  let φK : X → K := fun x => η (φ x)
  let hφK : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φK) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (ProC := ProC) X K φK
  let f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K :=
    (zcCompletedFoxSemidirectMapTarget (X := X) ProC.finiteQuotientClass hC η).comp
      (freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htargetH φ hφH)
  let h : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K :=
    freeProCZCCompletedFoxSemidirectLift
      (ProC := ProC) hι htargetK φK hφK
  have hf_continuous : Continuous f :=
    (continuous_zcCompletedFoxSemidirectMapTarget
      (X := X) ProC.finiteQuotientClass hC η).comp
      (continuous_freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htargetH φ hφH)
  have hh_continuous : Continuous h :=
    continuous_freeProCZCCompletedFoxSemidirectLift
      (ProC := ProC) hι htargetK φK hφK
  have hfg : ∀ x : X, f (ι x) = h (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · funext y
      by_cases hxy : x = y
      · subst y
        simp only [MonoidHom.coe_comp, Function.comp_apply, freeProCZCCompletedFoxSemidirectLift_generator,
  zcCompletedFoxSemidirectMapTarget_left, zcFreeFoxCoordinatesMap, freeProCZCCompletedFoxSemidirectGenerator_left,
  Pi.single_eq_same, map_one, f, h, φK]
      · simp only [MonoidHom.coe_comp, Function.comp_apply, freeProCZCCompletedFoxSemidirectLift_generator,
  zcCompletedFoxSemidirectMapTarget_left, zcFreeFoxCoordinatesMap, freeProCZCCompletedFoxSemidirectGenerator_left,
  ne_eq, hxy, not_false_eq_true, Pi.single_eq_of_ne', map_zero, f, h, φK]
    · simp only [MonoidHom.coe_comp, Function.comp_apply, freeProCZCCompletedFoxSemidirectLift_generator,
  zcCompletedFoxSemidirectMapTarget_right, freeProCZCCompletedFoxSemidirectGenerator_right, f, h, φK]
  have hfh : f = h := hι.hom_ext htargetK hf_continuous hh_continuous hfg
  exact congrFun (congrArg DFunLike.coe hfh) g

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] [Fintype X] in
/-- Continuous-hom form of target naturality for the canonical completed Fox semidirect lift. -/
theorem freeProCZCCompletedFoxSemidirectLiftHom_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetH :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetK :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K))
    (η : H →ₜ* K) (φ : X → H) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) ProC.finiteQuotientClass hC η).comp
        (freeProCZCCompletedFoxSemidirectLiftHom
          (ProC := ProC) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ)) =
      freeProCZCCompletedFoxSemidirectLiftHom
        (ProC := ProC) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProC) X K (fun x : X => η (φ x))) := by
  apply ContinuousMonoidHom.ext
  intro g
  exact freeProCZCCompletedFoxSemidirectLift_mapTarget
    (ProC := ProC) (X := X) (F := F) (H := H) (K := K)
    hC hι htargetH htargetK η φ g

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] [Fintype X] in
/-- Target naturality of the right homomorphism of the canonical completed Fox lift. -/
theorem freeProCZCCompletedFoxRightHom_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetH :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetK :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K))
    (η : H →ₜ* K) (φ : X → H) :
    freeProCZCCompletedFoxRightHom
        (ProC := ProC) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProC) X K (fun x : X => η (φ x))) =
      η.toMonoidHom.comp
        (freeProCZCCompletedFoxRightHom
          (ProC := ProC) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ)) := by
  ext g
  have h := congrArg ZCCompletedFoxSemidirect.right
    (freeProCZCCompletedFoxSemidirectLift_mapTarget
      (ProC := ProC) (X := X) (F := F) (H := H) (K := K)
      hC hι htargetH htargetK η φ g)
  simpa [freeProCZCCompletedFoxRightHom_apply, MonoidHom.comp_apply] using h.symm

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] [Fintype X] in
/-- Target naturality of the derivative vector of the canonical completed Fox lift. -/
theorem freeProCZCCompletedFoxDerivativeVector_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetH :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetK :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProC) X K (fun x : X => η (φ x))) g =
      zcFreeFoxCoordinatesMap (X := X) ProC.finiteQuotientClass hC η
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ) g) := by
  have h := congrArg ZCCompletedFoxSemidirect.left
    (freeProCZCCompletedFoxSemidirectLift_mapTarget
      (ProC := ProC) (X := X) (F := F) (H := H) (K := K)
      hC hι htargetH htargetK η φ g)
  simpa [freeProCZCCompletedFoxDerivativeVector] using h.symm

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] [Fintype X] in
/-- Component form of target naturality for the canonical completed Fox derivative. -/
theorem freeProCZCCompletedFoxDerivativeVector_mapTarget_apply
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetH :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetK :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) (x : X) :
    freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
          (ProC := ProC) X K (fun x : X => η (φ x))) g x =
      zcCompletedGroupAlgebraMap ProC.finiteQuotientClass hC η
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X H φ) g x) := by
  have h := congrFun
    (freeProCZCCompletedFoxDerivativeVector_mapTarget
      (ProC := ProC) (X := X) (F := F) (H := H) (K := K)
      hC hι htargetH htargetK η φ g) x
  simpa [zcFreeFoxCoordinatesMap] using h

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Target naturality for the source-shaped boundary applied to the canonical completed Fox
derivative vector. -/
theorem freeProCZCCompletedFoxBoundary_mapTarget_of_derivativeVector
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htargetH :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (htargetK :
      ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) :
    zcCompletedGroupAlgebraMap ProC.finiteQuotientClass hC η
        (freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass φ
          (freeProCZCCompletedFoxDerivativeVector
            (ProC := ProC) hι htargetH φ
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
              (ProC := ProC) X H φ) g)) =
      freeProCZCCompletedFoxBoundary ProC.finiteQuotientClass (fun x : X => η (φ x))
        (freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι htargetK (fun x : X => η (φ x))
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
            (ProC := ProC) X K (fun x : X => η (φ x))) g) := by
  rw [freeProCZCCompletedFoxBoundary_mapTarget]
  rw [← freeProCZCCompletedFoxDerivativeVector_mapTarget
    (ProC := ProC) (X := X) (F := F) (H := H) (K := K)
    hC hι htargetH htargetK η φ g]

end SourceNaturality

end

end FoxDifferential
