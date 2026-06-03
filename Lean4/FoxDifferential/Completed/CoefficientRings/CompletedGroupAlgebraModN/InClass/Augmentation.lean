import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.StageCoeffMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/InClass/Augmentation.lean
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

/-- The augmentation on one class-restricted residue-coefficient finite stage. -/
def modNCompletedGroupAlgebraStageAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    ModNCompletedGroupAlgebraStageInClass n G C U →+* ModNCompletedCoeff n :=
  MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
    (CompletedGroupAlgebraQuotientInClass G C U)
    (1 : CompletedGroupAlgebraQuotientInClass G C U →* ModNCompletedCoeff n)

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraStageAugmentationInClass_of. -/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) :
    modNCompletedGroupAlgebraStageAugmentationInClass n G C U
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) = 1 := by
  classical
  simp only [modNCompletedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.of, MonoidAlgebra.single,
  MonoidHom.coe_mk, OneHom.coe_mk, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul,
  mul_one]

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限群クラスを固定した augmentation または augmentation ideal への標準写像が群環の単項基底元を有限商段階の対応する単項基底元へ送ることを述べる。 -/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_single
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) (a : ModNCompletedCoeff n) :
    modNCompletedGroupAlgebraStageAugmentationInClass n G C U
        (MonoidAlgebra.single q a) = a := by
  classical
  simp only [modNCompletedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.single, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

omit [Fact (0 < n)] in
/-- Compatibility lemma modNCompletedGroupAlgebraStageAugmentationInClass_compatible. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraTransitionInClass n G C hUV) =
      modNCompletedGroupAlgebraStageAugmentationInClass n G C V := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
          (modNCompletedGroupAlgebraTransitionInClass n G C hUV)) x =
        modNCompletedGroupAlgebraStageAugmentationInClass n G C V x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraTransitionInClass_of]
    simp only [modNCompletedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.single, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one, MonoidAlgebra.of, MonoidHom.coe_mk,
  OneHom.coe_mk]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
            (modNCompletedGroupAlgebraTransitionInClass n G C hUV))
            (algebraMap (ModNCompletedCoeff n)
              (ModNCompletedGroupAlgebraStageInClass n G C V) a) =
          (modNCompletedGroupAlgebraStageAugmentationInClass n G C V)
            (algebraMap (ModNCompletedCoeff n)
              (ModNCompletedGroupAlgebraStageInClass n G C V) a) := by
      simp only [modNCompletedGroupAlgebraStageAugmentationInClass, modNCompletedGroupAlgebraTransitionInClass,
  MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one, RingHom.coe_coe,
  MonoidAlgebra.lift_single, smul_eq_mul, mul_one]
    rw [hcoeff]

omit [Fact (0 < n)] in
/-- Composition lemma modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageMap. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageMap
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraStageMapInClass n G C U) =
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
        (1 : G →* ModNCompletedCoeff n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
          (modNCompletedGroupAlgebraStageMapInClass n G C U)) x =
        (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
          (1 : G →* ModNCompletedCoeff n)) x)
    x ?_ ?_ ?_
  · intro g
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraStageMapInClass_of]
    simp only [modNCompletedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.single, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one, MonoidAlgebra.of, MonoidHom.coe_mk,
  OneHom.coe_mk]
  · intro x y hx hy
    simp only [hx, hy, map_add]
  · intro a x hx
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
            (modNCompletedGroupAlgebraStageMapInClass n G C U))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) = a := by
      simp only [modNCompletedGroupAlgebraStageAugmentationInClass, modNCompletedGroupAlgebraStageMapInClass,
  MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one, RingHom.coe_coe,
  MonoidAlgebra.lift_single, smul_eq_mul, mul_one]
    have hcoeff' :
        ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
            (modNCompletedGroupAlgebraStageMapInClass n G C U))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
            (1 : G →* ModNCompletedCoeff n))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) := by
      rw [hcoeff]
      simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]
    rw [Algebra.smul_def]
    calc
      ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
          (modNCompletedGroupAlgebraStageMapInClass n G C U))
          ((algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) * x)
        =
          ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
              (modNCompletedGroupAlgebraStageMapInClass n G C U))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
              (modNCompletedGroupAlgebraStageMapInClass n G C U)) x := by
            rw [RingHom.map_mul]
      _ =
          ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
              (modNCompletedGroupAlgebraStageMapInClass n G C U))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n)) x := by
            rw [hx]
      _ =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n)) x := by
            rw [hcoeff']
      _ =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
            (1 : G →* ModNCompletedCoeff n))
            ((algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) * x) := by
            exact
              (map_mul
                (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
                  (1 : G →* ModNCompletedCoeff n))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) x).symm

omit [Fact (0 < n)] in
/-- Stage augmentations commute with coefficient reduction on class-restricted finite quotient
stages. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMap
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    {m : ℕ} [Fact (0 < m)] (hnm : n ∣ m) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm) =
      (modNCompletedCoeffMap (n := n) (m := m) hnm).comp
        (modNCompletedGroupAlgebraStageAugmentationInClass m G C U) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C U hnm)) x =
        ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
          (modNCompletedGroupAlgebraStageAugmentationInClass m G C U)) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply,
      modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageAugmentationInClass_of,
      modNCompletedGroupAlgebraStageAugmentationInClass_of]
    exact (map_one (modNCompletedCoeffMap (n := n) (m := m) hnm)).symm
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro a x hx
    letI : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
      ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
            (modNCompletedGroupAlgebraStageCoeffMapInClass
              (n := n) (m := m) (G := G) C U hnm))
            (algebraMap (ModNCompletedCoeff m)
              (ModNCompletedGroupAlgebraStageInClass m G C U) a) =
          ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
            (modNCompletedGroupAlgebraStageAugmentationInClass m G C U))
            (algebraMap (ModNCompletedCoeff m)
              (ModNCompletedGroupAlgebraStageInClass m G C U) a) := by
      have hleft :
          ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
              (modNCompletedGroupAlgebraStageCoeffMapInClass
                (n := n) (m := m) (G := G) C U hnm))
              (algebraMap (ModNCompletedCoeff m)
                (ModNCompletedGroupAlgebraStageInClass m G C U) a) =
            algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a := by
        simp only [modNCompletedGroupAlgebraStageAugmentationInClass, modNCompletedGroupAlgebraStageCoeffMapInClass,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, RingHom.comp_apply, RingHom.coe_coe, MonoidAlgebra.lift_single,
  MonoidAlgebra.of_apply, Algebra.smul_def, MonoidAlgebra.single_mul_single, mul_one,
  MonoidHom.one_apply]
      have hright :
          ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
              (modNCompletedGroupAlgebraStageAugmentationInClass m G C U))
              (algebraMap (ModNCompletedCoeff m)
                (ModNCompletedGroupAlgebraStageInClass m G C U) a) =
            algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a := by
        simp only [modNCompletedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.coe_algebraMap,
  Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq, RingHom.comp_apply, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]
        rfl
      exact hleft.trans hright.symm
    rw [hcoeff]

end

end FoxDifferential
