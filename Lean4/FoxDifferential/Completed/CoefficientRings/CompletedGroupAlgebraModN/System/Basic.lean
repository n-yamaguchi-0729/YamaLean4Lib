import CompletedGroupAlgebra.Basic.AllFinite.Index
import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Augmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/System/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed coefficient algebras

Coefficient algebras, residue stages, and completed group-algebra maps are kept as the scalar layer for completed Fox calculus.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] in
abbrev ModNCompletedGroupAlgebraStage (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) : Type _ :=
  ModNCompletedGroupRing n (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)

instance instFiniteModNCompletedGroupAlgebraStage (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    Finite (ModNCompletedGroupAlgebraStage n G U) := by
  classical
  letI : Finite (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) := (OrderDual.ofDual U).2
  letI : Fintype (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) := Fintype.ofFinite _
  letI : DecidableEq (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) := Classical.decEq _
  letI : NeZero n := ⟨Nat.ne_of_gt (show 0 < n from Fact.out)⟩
  letI : Fintype (ModNCompletedCoeff n) := Fintype.ofEquiv (Fin n) (ZMod.finEquiv n)
  letI : Finite (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U → ModNCompletedCoeff n) := by
    letI : Fintype (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U → ModNCompletedCoeff n) := inferInstance
    exact Finite.of_fintype _
  let f :
      ModNCompletedGroupAlgebraStage n G U →
        _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U → ModNCompletedCoeff n := fun x q => x q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

omit [Fact (0 < n)] in
/-- The transition map between residue-coefficient stages. -/
def modNCompletedGroupAlgebraTransition
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    ModNCompletedGroupAlgebraStage n G V →+* ModNCompletedGroupAlgebraStage n G U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraTransition_of. -/
@[simp]
theorem modNCompletedGroupAlgebraTransition_of
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (g : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V) :
    modNCompletedGroupAlgebraTransition n G hUV (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single ((OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  simp only [modNCompletedGroupAlgebraTransition, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [Fact (0 < n)] in
/-- Identity case for modNCompletedGroupAlgebraTransition_id. -/
@[simp]
theorem modNCompletedGroupAlgebraTransition_id (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    modNCompletedGroupAlgebraTransition n G (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [modNCompletedGroupAlgebraTransition, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := ModNCompletedCoeff n) (M := _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)

omit [Fact (0 < n)] in
/-- Composition lemma modNCompletedGroupAlgebraTransition_comp. -/
@[simp]
theorem modNCompletedGroupAlgebraTransition_comp
    {U V W : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (hVW : V ≤ W) :
    (modNCompletedGroupAlgebraTransition n G hUV).comp
        (modNCompletedGroupAlgebraTransition n G hVW) =
      modNCompletedGroupAlgebraTransition n G (hUV.trans hVW) := by
  rw [modNCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraTransition,
    modNCompletedGroupAlgebraTransition, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1
  exact OpenNormalSubgroupInClass.map_comp
    (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
    (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
    hUV hVW

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraTransition_single_apply. -/
theorem modNCompletedGroupAlgebraTransition_single_apply
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V)
    (a : ModNCompletedCoeff n) :
    modNCompletedGroupAlgebraTransition n G hUV (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) a := by
  simp only [modNCompletedGroupAlgebraTransition, MonoidAlgebra.single, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  rfl

omit [Fact (0 < n)] in
/-- Surjectivity lemma modNCompletedGroupAlgebraTransition_surjective. -/
theorem modNCompletedGroupAlgebraTransition_surjective
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    Function.Surjective (modNCompletedGroupAlgebraTransition n G hUV) := by
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases OpenNormalSubgroupInClass.map_surjective
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV q with
        ⟨q', hq'⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single q' a : ModNCompletedGroupAlgebraStage n G V) + y, ?_⟩
      rw [map_add, modNCompletedGroupAlgebraTransition_single_apply, hy, hq']

omit [Fact (0 < n)] in
/-- The quotient map `(ZMod n)[G] → (ZMod n)[G/U]`. -/
def modNCompletedGroupAlgebraStageMap (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupRing n G →+* ModNCompletedGroupAlgebraStage n G U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraStageMap_of. -/
@[simp]
theorem modNCompletedGroupAlgebraStageMap_of
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (g : G) :
    modNCompletedGroupAlgebraStageMap n G U (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 := by
  classical
  simp only [modNCompletedGroupAlgebraStageMap, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [Fact (0 < n)] in
/-- Compatibility lemma modNCompletedGroupAlgebraStageMap_compatible. -/
@[simp]
theorem modNCompletedGroupAlgebraStageMap_compatible
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraTransition n G hUV).comp
        (modNCompletedGroupAlgebraStageMap n G V) =
      modNCompletedGroupAlgebraStageMap n G U := by
  rw [modNCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageMap,
    modNCompletedGroupAlgebraStageMap, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

omit [Fact (0 < n)] in
/-- The inverse system `U ↦ (ZMod n)[G/U]`. -/
def modNCompletedGroupAlgebraSystem :
    InverseSystem (I := _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) where
  X := ModNCompletedGroupAlgebraStage n G
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => modNCompletedGroupAlgebraTransition n G hUV
  continuous_map := by
    intro U V hUV
    letI : TopologicalSpace (ModNCompletedGroupAlgebraStage n G U) := ⊥
    letI : TopologicalSpace (ModNCompletedGroupAlgebraStage n G V) := ⊥
    letI : DiscreteTopology (ModNCompletedGroupAlgebraStage n G V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe (modNCompletedGroupAlgebraTransition_id (n := n) (G := G) U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransition_comp (n := n) (G := G) hUV hVW)) x

omit [Fact (0 < n)] in
/-- The inverse-limit object of the residue-coefficient stage tower. -/
abbrev ModNCompletedGroupAlgebra :=
  (modNCompletedGroupAlgebraSystem n G).inverseLimit

omit [Fact (0 < n)] in
/-- The projection from the residue-coefficient inverse limit to one finite stage. -/
abbrev modNCompletedGroupAlgebraProjection (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebra n G → ModNCompletedGroupAlgebraStage n G U :=
  (modNCompletedGroupAlgebraSystem n G).projection U


end

end FoxDifferential
