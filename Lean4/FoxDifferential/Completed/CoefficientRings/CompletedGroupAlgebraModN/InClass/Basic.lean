import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebra
import Mathlib.Data.ZMod.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/InClass/Basic.lean
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
/-- The coefficient ring `Z/nZ` used in one residue-coefficient stage. -/
abbrev ModNCompletedCoeff : Type := ZMod n

omit [Fact (0 < n)] in
/-- The group ring `(ZMod n)[H]` used in the residue-coefficient tower. -/
abbrev ModNCompletedGroupRing (H : Type*) : Type _ :=
  MonoidAlgebra (ModNCompletedCoeff n) H

omit [Fact (0 < n)] in
/-- The residue-coefficient stage over a class-restricted finite quotient `G/U`. -/
abbrev ModNCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) : Type _ :=
  ModNCompletedGroupRing n (CompletedGroupAlgebraQuotientInClass G C U)

/-- 法 n 係数で定めた 有限群クラスを固定した 標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem finite_modNCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hFinite : ∀ {Q : Type u} [Group Q], C Q → Finite Q)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Finite (ModNCompletedGroupAlgebraStageInClass n G C U) := by
  classical
  letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    hFinite (OrderDual.ofDual U).2
  letI : Fintype (CompletedGroupAlgebraQuotientInClass G C U) := Fintype.ofFinite _
  letI : DecidableEq (CompletedGroupAlgebraQuotientInClass G C U) := Classical.decEq _
  letI : NeZero n := ⟨Nat.ne_of_gt (show 0 < n from Fact.out)⟩
  letI : Fintype (ModNCompletedCoeff n) := Fintype.ofEquiv (Fin n) (ZMod.finEquiv n)
  letI :
      Finite (CompletedGroupAlgebraQuotientInClass G C U → ModNCompletedCoeff n) := by
    letI :
        Fintype (CompletedGroupAlgebraQuotientInClass G C U → ModNCompletedCoeff n) :=
      inferInstance
    exact Finite.of_fintype _
  let f :
      ModNCompletedGroupAlgebraStageInClass n G C U →
        CompletedGroupAlgebraQuotientInClass G C U → ModNCompletedCoeff n := fun x q => x q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

omit [Fact (0 < n)] in
/-- The transition map between class-restricted residue-coefficient stages. -/
def modNCompletedGroupAlgebraTransitionInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    ModNCompletedGroupAlgebraStageInClass n G C V →+*
      ModNCompletedGroupAlgebraStageInClass n G C U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraTransitionInClass_of. -/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_of
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (g : CompletedGroupAlgebraQuotientInClass G C V) :
    modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  simp only [modNCompletedGroupAlgebraTransitionInClass, MonoidAlgebra.of, MonoidAlgebra.single,
  MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した 遷移写像が群環の単項基底元を有限商段階の対応する単項基底元へ送ることを述べる。 -/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_single
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotientInClass G C V)
    (a : ModNCompletedCoeff n) :
    modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) a := by
  classical
  simp only [modNCompletedGroupAlgebraTransitionInClass, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  rfl

omit [Fact (0 < n)] in
/-- Identity case for modNCompletedGroupAlgebraTransitionInClass_id. -/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_id
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    modNCompletedGroupAlgebraTransitionInClass n G C (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [modNCompletedGroupAlgebraTransitionInClass, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := ModNCompletedCoeff n) (M := CompletedGroupAlgebraQuotientInClass G C U)

omit [Fact (0 < n)] in
/-- Composition lemma modNCompletedGroupAlgebraTransitionInClass_comp. -/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    (modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
        (modNCompletedGroupAlgebraTransitionInClass n G C hVW) =
      modNCompletedGroupAlgebraTransitionInClass n G C (hUV.trans hVW) := by
  rw [modNCompletedGroupAlgebraTransitionInClass, modNCompletedGroupAlgebraTransitionInClass,
    modNCompletedGroupAlgebraTransitionInClass, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1
  exact OpenNormalSubgroupInClass.map_comp
    (C := C) (G := G)
    (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
    hUV hVW

omit [Fact (0 < n)] in
/-- The class-restricted inverse system `U ↦ (ZMod n)[G/U]`. -/
def modNCompletedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := CompletedGroupAlgebraIndexInClass G C) where
  X := ModNCompletedGroupAlgebraStageInClass n G C
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => modNCompletedGroupAlgebraTransitionInClass n G C hUV
  continuous_map := by
    intro U V hUV
    letI : TopologicalSpace (ModNCompletedGroupAlgebraStageInClass n G C U) := ⊥
    letI : TopologicalSpace (ModNCompletedGroupAlgebraStageInClass n G C V) := ⊥
    letI : DiscreteTopology (ModNCompletedGroupAlgebraStageInClass n G C V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransitionInClass_id n G C U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransitionInClass_comp n G C hUV hVW)) x

omit [Fact (0 < n)] in
/-- Surjectivity lemma modNCompletedGroupAlgebraTransitionInClass_surjective. -/
theorem modNCompletedGroupAlgebraTransitionInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    Function.Surjective (modNCompletedGroupAlgebraTransitionInClass n G C hUV) := by
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases OpenNormalSubgroupInClass.map_surjective
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV q with
        ⟨q', hq'⟩
      rcases ih with ⟨y, hy⟩
      refine
        ⟨(MonoidAlgebra.single q' a : ModNCompletedGroupAlgebraStageInClass n G C V) + y,
          ?_⟩
      rw [map_add, modNCompletedGroupAlgebraTransitionInClass_single, hy, hq']

omit [Fact (0 < n)] in
/-- The quotient map `(ZMod n)[G] -> (ZMod n)[G/U]` for a class-restricted stage. -/
def modNCompletedGroupAlgebraStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    ModNCompletedGroupRing n G →+* ModNCompletedGroupAlgebraStageInClass n G C U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (openNormalSubgroupInClassProj (C := C) (G := G) U)

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraStageMapInClass_of. -/
@[simp]
theorem modNCompletedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (g : G) :
    modNCompletedGroupAlgebraStageMapInClass n G C U
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  classical
  simp only [modNCompletedGroupAlgebraStageMapInClass, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [Fact (0 < n)] in
/-- Compatibility lemma modNCompletedGroupAlgebraStageMapInClass_compatible. -/
@[simp]
theorem modNCompletedGroupAlgebraStageMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
        (modNCompletedGroupAlgebraStageMapInClass n G C V) =
      modNCompletedGroupAlgebraStageMapInClass n G C U := by
  rw [modNCompletedGroupAlgebraTransitionInClass, modNCompletedGroupAlgebraStageMapInClass,
    modNCompletedGroupAlgebraStageMapInClass, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

omit [Fact (0 < n)] in
/-- Compatibility for a class-restricted residue-coefficient completed group algebra family. -/
def ModNCompletedGroupAlgebraCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      ModNCompletedGroupAlgebraStageInClass n G C U) : Prop :=
  (modNCompletedGroupAlgebraSystemInClass n G C).Compatible x

omit [Fact (0 < n)] in
/-- The class-restricted residue-coefficient completed group algebra as an inverse-limit subtype. -/
abbrev ModNCompletedGroupAlgebraInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      ModNCompletedGroupAlgebraStageInClass n G C U //
    ModNCompletedGroupAlgebraCompatibleInClass n G C x}

omit [Fact (0 < n)] in
/-- Projection from the class-restricted residue-coefficient completed group algebra to a stage. -/
def modNCompletedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    ModNCompletedGroupAlgebraInClass n G C →
      ModNCompletedGroupAlgebraStageInClass n G C U :=
  (modNCompletedGroupAlgebraSystemInClass n G C).projection U
end

end FoxDifferential
