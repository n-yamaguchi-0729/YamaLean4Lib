import CompletedGroupAlgebra.Basic.InClass.Index

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/InClass/Stage.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Class-Indexed Completed Group Algebras

Finite-class-indexed inverse systems and inverse limits for completed group algebras.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R]

section InClass

/-- The finite-stage group algebra `R[G/U]` for a `C`-indexed quotient. -/
abbrev CompletedGroupAlgebraStageInClass (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndexInClass G C) :
    Type (max u v) :=
  MonoidAlgebra R (CompletedGroupAlgebraQuotientInClass G C U)

/-- Change coefficients on one `C`-indexed completed-group-algebra stage. -/
def completedGroupAlgebraStageCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraStageInClass C R G U →+*
      CompletedGroupAlgebraStageInClass C S G U :=
  MonoidAlgebra.mapRangeRingHom (CompletedGroupAlgebraQuotientInClass G C U) f

@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) (r : R) :
    completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (f r) := by
  exact MonoidAlgebra.mapRangeRingHom_single f q r

@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_comp
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) (T : Type*) [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U) =
      completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U := by
  exact (MonoidAlgebra.mapRangeRingHom_comp
    (M := CompletedGroupAlgebraQuotientInClass G C U) g f).symm

/-- A finite coefficient ring gives finite `C`-indexed completed-group-algebra stages. -/
theorem finite_completedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    [Finite R] (U : CompletedGroupAlgebraIndexInClass G C) :
    Finite (CompletedGroupAlgebraStageInClass C R G U) := by
  classical
  letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C hC U
  letI : Fintype (CompletedGroupAlgebraQuotientInClass G C U) := Fintype.ofFinite _
  letI : Fintype R := Fintype.ofFinite R
  letI : DecidableEq (CompletedGroupAlgebraQuotientInClass G C U) := Classical.decEq _
  letI : Finite (CompletedGroupAlgebraQuotientInClass G C U → R) := by
    letI : Fintype (CompletedGroupAlgebraQuotientInClass G C U → R) := inferInstance
    exact Finite.of_fintype _
  let f :
      CompletedGroupAlgebraStageInClass C R G U →
        CompletedGroupAlgebraQuotientInClass G C U → R := fun x q => x q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

instance instRingCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    Ring (CompletedGroupAlgebraStageInClass C R G U) := by
  dsimp [CompletedGroupAlgebraStageInClass, CompletedGroupAlgebraQuotientInClass]
  infer_instance

/-- The transition map `R[G/V] -> R[G/U]` in the `C`-indexed completed-group-algebra tower. -/
def completedGroupAlgebraTransitionInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    CompletedGroupAlgebraStageInClass C R G V →+*
      CompletedGroupAlgebraStageInClass C R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/-- The transition map sends group-like basis elements by quotient projection. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (g : CompletedGroupAlgebraQuotientInClass G C V) :
    completedGroupAlgebraTransitionInClass C R G hUV (MonoidAlgebra.of R _ g) =
      MonoidAlgebra.single ((OpenNormalSubgroupInClass.map
        (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  simp only [completedGroupAlgebraTransitionInClass, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

/-- The transition map sends singleton coefficients by quotient projection. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_single
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotientInClass G C V) (r : R) :
    completedGroupAlgebraTransitionInClass C R G hUV (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r := by
  classical
  simp only [completedGroupAlgebraTransitionInClass, MonoidAlgebra.single, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  rfl

/-- The identity transition map in the `C`-indexed tower is the identity ring homomorphism. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_id
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    completedGroupAlgebraTransitionInClass C R G (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [completedGroupAlgebraTransitionInClass, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := R) (M := CompletedGroupAlgebraQuotientInClass G C U)

/-- Transition maps in the `C`-indexed tower compose as expected. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_comp
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraTransitionInClass C R G hVW) =
      completedGroupAlgebraTransitionInClass C R G (hUV.trans hVW) := by
  rw [completedGroupAlgebraTransitionInClass, completedGroupAlgebraTransitionInClass,
    completedGroupAlgebraTransitionInClass, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1
  exact OpenNormalSubgroupInClass.map_comp
    (C := C) (G := G)
    (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
    hUV hVW

/-- `C`-indexed stage transitions commute with coefficient change. -/
@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S] (f : R →+* S)
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U).comp
        (completedGroupAlgebraTransitionInClass C R G hUV) =
      (completedGroupAlgebraTransitionInClass C S G hUV).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V) := by
  exact MonoidAlgebra.mapRangeRingHom_comp_mapDomainRingHom
    (f := f)
    (g := OpenNormalSubgroupInClass.map
      (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/-- Two coefficient changes and two `C`-indexed group-quotient transitions compose as the
combined change and combined transition. -/
@[simp 900]
theorem completedGroupAlgebraStageCoeffMapInClass_transition_comp
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) (T : Type*) [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T)
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    ((completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraTransitionInClass C S G hUV)).comp
        ((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V).comp
          (completedGroupAlgebraTransitionInClass C R G hVW)) =
      (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U).comp
        (completedGroupAlgebraTransitionInClass C R G (hUV.trans hVW)) := by
  calc
    ((completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraTransitionInClass C S G hUV)).comp
        ((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V).comp
          (completedGroupAlgebraTransitionInClass C R G hVW))
      =
    (completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
      (((completedGroupAlgebraTransitionInClass C S G hUV).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V)).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
      (((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U).comp
        (completedGroupAlgebraTransitionInClass C R G hUV)).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          rw [← completedGroupAlgebraStageCoeffMapInClass_compatible
            (R := R) (G := G) C S f hUV]
    _ =
    ((completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)).comp
      ((completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U).comp
      ((completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          rw [completedGroupAlgebraStageCoeffMapInClass_comp]
    _ =
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U).comp
      (completedGroupAlgebraTransitionInClass C R G (hUV.trans hVW)) := by
        rw [completedGroupAlgebraTransitionInClass_comp]

/-- Transition maps commute with scalar multiplication by coefficients. -/
theorem completedGroupAlgebraTransitionInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (r : R) (x : CompletedGroupAlgebraStageInClass C R G V) :
    completedGroupAlgebraTransitionInClass C R G hUV (r • x) =
      r • completedGroupAlgebraTransitionInClass C R G hUV x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp only [completedGroupAlgebraTransitionInClass, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

/-- Transition maps commute with the coefficient algebra maps. -/
theorem completedGroupAlgebraTransitionInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (r : R) :
    completedGroupAlgebraTransitionInClass C R G hUV
        (algebraMap R (CompletedGroupAlgebraStageInClass C R G V) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r := by
  simp only [completedGroupAlgebraTransitionInClass, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

variable [TopologicalSpace R] [IsTopologicalRing R]

end InClass

end

end CompletedGroupAlgebra
