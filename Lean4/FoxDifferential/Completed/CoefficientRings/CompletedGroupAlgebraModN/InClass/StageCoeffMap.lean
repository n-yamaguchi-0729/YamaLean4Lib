import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.CoeffMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/InClass/StageCoeffMap.lean
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


variable {n m k : ℕ}
variable [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The coefficient reduction map on one class-restricted finite quotient stage `G/U`. -/
abbrev modNCompletedGroupAlgebraStageCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣ m) :
    ModNCompletedGroupAlgebraStageInClass m G C U →+*
      ModNCompletedGroupAlgebraStageInClass n G C U :=
  modNCompletedGroupRingCoeffMap (n := n) (m := m)
    (CompletedGroupAlgebraQuotientInClass G C U) hnm

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Evaluation formula for modNCompletedGroupAlgebraStageCoeffMapInClass_of. -/
@[simp]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣ m)
    (q : CompletedGroupAlgebraQuotientInClass G C U) :
    modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff n) _ q := by
  simpa [modNCompletedGroupAlgebraStageCoeffMapInClass] using
    modNCompletedGroupRingCoeffMap_of (n := n) (m := m)
      (H := CompletedGroupAlgebraQuotientInClass G C U) hnm q

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Evaluation formula for modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply. -/
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣ m)
    (q : CompletedGroupAlgebraQuotientInClass G C U)
    (a : ModNCompletedCoeff m) :
    modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a) := by
  letI : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
  have hcoeff :
      algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a =
        modNCompletedCoeffMap (n := n) (m := m) hnm a := by
    rfl
  ext x
  simp only [modNCompletedGroupAlgebraStageCoeffMapInClass, modNCompletedGroupRingCoeffMap,
  AlgHom.toRingHom_eq_coe, MonoidAlgebra.single, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply,
  Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Function.comp_apply, hcoeff, MonoidAlgebra.single_mul_single,
  one_mul, mul_one]

omit [Fact (0 < n)] in
/-- Identity case for modNCompletedGroupAlgebraStageCoeffMapInClass_rfl. -/
@[simp]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_rfl
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := n) (G := G) C U dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := n) (G := G) C U dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rw [modNCompletedGroupAlgebraStageCoeffMapInClass_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [modNCompletedGroupAlgebraStageCoeffMapInClass, modNCompletedGroupRingCoeffMap,
  AlgHom.toRingHom_eq_coe, map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)] in
/-- Composition lemma modNCompletedGroupAlgebraStageCoeffMapInClass_comp. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (hnm : n ∣ m) (hmk : m ∣ k) :
    (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := m) (m := k) (G := G) C U hmk) =
      modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := k) (G := G) C U (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C U hnm).comp
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := m) (m := k) (G := G) C U hmk)) x =
        modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := k) (G := G) C U (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageCoeffMapInClass_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [modNCompletedGroupAlgebraStageCoeffMapInClass, modNCompletedGroupRingCoeffMap,
  AlgHom.toRingHom_eq_coe, map_intCast, RingHom.coe_coe]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Compatibility lemma modNCompletedGroupAlgebraStageCoeffMapInClass_compatible. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hnm : n ∣ m) :
    (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm).comp
        (modNCompletedGroupAlgebraTransitionInClass m G C hUV) =
      (modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C V hnm) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C U hnm).comp
          (modNCompletedGroupAlgebraTransitionInClass m G C hUV)) x =
        ((modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C V hnm)) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply,
      modNCompletedGroupAlgebraTransitionInClass_of]
    change modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) _
          ((OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q)) =
      (modNCompletedGroupAlgebraTransitionInClass n G C hUV)
        ((modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C V hnm)
          (MonoidAlgebra.of (ModNCompletedCoeff m) _ q))
    rw [modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraTransitionInClass_of]
    rfl
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageCoeffMapInClass
              (n := n) (m := m) (G := G) C U hnm).comp
            (modNCompletedGroupAlgebraTransitionInClass m G C hUV))
            (algebraMap (ModNCompletedCoeff m)
              (ModNCompletedGroupAlgebraStageInClass m G C V) a) =
          ((modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
            (modNCompletedGroupAlgebraStageCoeffMapInClass
              (n := n) (m := m) (G := G) C V hnm))
            (algebraMap (ModNCompletedCoeff m)
              (ModNCompletedGroupAlgebraStageInClass m G C V) a) := by
      simpa [Algebra.smul_def] using
        (show
          ((modNCompletedGroupAlgebraStageCoeffMapInClass
                (n := n) (m := m) (G := G) C U hnm).comp
              (modNCompletedGroupAlgebraTransitionInClass m G C hUV))
              (algebraMap (ModNCompletedCoeff m)
                (ModNCompletedGroupAlgebraStageInClass m G C V) a) =
            ((modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
              (modNCompletedGroupAlgebraStageCoeffMapInClass
                (n := n) (m := m) (G := G) C V hnm))
              (algebraMap (ModNCompletedCoeff m)
                (ModNCompletedGroupAlgebraStageInClass m G C V) a) by
          simp only [modNCompletedGroupAlgebraStageCoeffMapInClass, modNCompletedGroupRingCoeffMap,
            AlgHom.toRingHom_eq_coe, modNCompletedGroupAlgebraTransitionInClass,
            MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
            Function.comp_apply, id_eq, RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
            MonoidAlgebra.one_def, Finsupp.mapDomain_single, map_one, RingHom.coe_coe,
            MonoidAlgebra.lift_single, MonoidAlgebra.smul_single])
    rw [hcoeff]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Surjectivity lemma modNCompletedGroupAlgebraStageCoeffMapInClass_surjective. -/
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣ m) :
    Function.Surjective
      (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm) := by
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases ZMod.castHom_surjective hnm a with ⟨a', ha'⟩
      have ha'' : modNCompletedCoeffMap (n := n) (m := m) hnm a' = a := by
        simpa [modNCompletedCoeffMap] using ha'
      rcases ih with ⟨y, hy⟩
      refine
        ⟨(MonoidAlgebra.single q a' : ModNCompletedGroupAlgebraStageInClass m G C U) + y,
          ?_⟩
      rw [map_add, modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply, hy, ha'']



end

end FoxDifferential
