import FoxDifferential.Completed.FreeProC.BifilteredCoefficientStageProjection
import FoxDifferential.Completed.ProCIntegerCoefficients.Core

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/ProCIntegerStageCoeffProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite Fox stage maps from actual `Z_C[[H]]` projections

This file constructs the coefficient map

`Z_C[[H]] -> (Z/nZ)[F/N]`

from a finite stage of the completed group algebra `Z_C[[H]]`, a finite quotient map from that
stage quotient to the finite Fox target quotient `F/N`, and coefficient reduction.  The resulting
maps feed the coefficient-level bifiltered density API.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v

section OneStageToFiniteFox

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (N : Subgroup (FreeGroup X)) [N.Normal]
variable (n : ℕ) [Fact (0 < n)]
variable (i : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H)

/-- A finite stage of `Z_C[[H]]` maps to a finite Fox target group algebra once its coefficient
modulus dominates `n` and its finite quotient maps to `F/N`. -/
def zcCompletedGroupAlgebraStageToFiniteFoxStage
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N) :
    ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H i →+*
      finiteFoxStageTargetGroupAlgebra (X := X) N n := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  letI : Algebra (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := i.1.modulus) hmod
  letI : Algebra (ModNCompletedCoeff i.1.modulus)
      (finiteFoxStageTargetGroupAlgebra (X := X) N n) := inferInstance
  exact
    (MonoidAlgebra.lift (ModNCompletedCoeff i.1.modulus)
      (finiteFoxStageTargetGroupAlgebra (X := X) N n)
      (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2)
      ((MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N)).comp qmap)).toRingHom

omit [DecidableEq X] [Fact (0 < n)] in
/-- Evaluation on a completed group-algebra stage basis element. -/
@[simp]
theorem zcCompletedGroupAlgebraStageToFiniteFoxStage_of
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2) :
    zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) N n i hmod qmap
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) (qmap q) := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  simp only [zcCompletedGroupAlgebraStageToFiniteFoxStage, AlgHom.toRingHom_eq_coe, MonoidAlgebra.of_apply,
  RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply, MonoidAlgebra.smul_single,
  one_smul]

omit [DecidableEq X] [Fact (0 < n)] in
/-- Evaluation on a single coefficient at a stage quotient element. -/
theorem zcCompletedGroupAlgebraStageToFiniteFoxStage_single
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2)
    (a : ModNCompletedCoeff i.1.modulus) :
    zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) N n i hmod qmap
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (qmap q)
        (modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod a) := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  letI : Algebra (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := i.1.modulus) hmod
  have hcoeff :
      algebraMap (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) a =
        modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod a := by
    rfl
  rw [zcCompletedGroupAlgebraStageToFiniteFoxStage]
  ext q'
  simp only [AlgHom.toRingHom_eq_coe, MonoidAlgebra.single, RingHom.coe_coe, MonoidAlgebra.lift_single,
  MonoidHom.coe_comp, Function.comp_apply, MonoidAlgebra.of_apply, Algebra.smul_def, MonoidAlgebra.coe_algebraMap,
  hcoeff, MonoidAlgebra.single_mul_single, one_mul, mul_one]

omit [DecidableEq X] in
/-- If no coefficient reduction is taken and the target quotient comparison is injective, then the
finite-stage map from the completed group-algebra stage to the finite Fox target group algebra is
injective. -/
theorem zcCompletedGroupAlgebraStageToFiniteFoxStage_self_injective
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (hqmap : Function.Injective qmap) :
    Function.Injective
      (zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) N i.1.modulus i dvd_rfl qmap) := by
  classical
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  have hstage :
      zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H) N i.1.modulus i dvd_rfl qmap =
        MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff i.1.modulus) qmap := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      rw [zcCompletedGroupAlgebraStageToFiniteFoxStage_single]
      simp only [map_one, modNCompletedCoeffMap_rfl, RingHom.id_apply, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
    · intro q
      rw [← MonoidAlgebra.of_apply,
        zcCompletedGroupAlgebraStageToFiniteFoxStage_of]
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rw [hstage]
  intro x y hxy
  exact (MonoidAlgebra.mapDomain_injective
    (R := ModNCompletedCoeff i.1.modulus) hqmap) (by
      simpa [MonoidAlgebra.mapDomainRingHom_apply] using hxy)

/-- The resulting completed-to-finite coefficient map. -/
def zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N) :
    ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
      finiteFoxStageTargetGroupAlgebra (X := X) N n :=
  (zcCompletedGroupAlgebraStageToFiniteFoxStage
    (ProC := ProC) (X := X) (H := H) N n i hmod qmap).comp
    (zcCompletedGroupAlgebraProjectionRingHom ProC.finiteQuotientClass H i)

omit [DecidableEq X] [Fact (0 < n)] in
@[simp]
theorem zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_apply
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) :
    zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
        (ProC := ProC) (X := X) (H := H) N n i hmod qmap a =
      zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) N n i hmod qmap
        (zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass H i a) :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] in
/-- Group-like formula for the completed-to-finite coefficient map. -/
theorem zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_groupLike
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (h : H) :
    zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
        (ProC := ProC) (X := X) (H := H) N n i hmod qmap
        (zcGroupLike ProC.finiteQuotientClass H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N)
        (qmap (QuotientGroup.mk h)) := by
  rw [zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_apply,
    zcCompletedGroupAlgebraProjection_groupLike,
    zcCompletedGroupAlgebraStageToFiniteFoxStage_of]

omit [DecidableEq X] [Fact (0 < n)] in
/-- Group-like formula rewritten through a named finite right quotient map. -/
theorem zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_groupLike_eq_stageRight
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (stageRight : H →* finiteFoxStageTargetQuotient (X := X) N)
    (hqmap : ∀ h : H, qmap (QuotientGroup.mk h) = stageRight h)
    (h : H) :
    zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
        (ProC := ProC) (X := X) (H := H) N n i hmod qmap
        (zcGroupLike ProC.finiteQuotientClass H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N) (stageRight h) := by
  rw [zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_groupLike]
  rw [hqmap h]

end OneStageToFiniteFox

section SingleCoefficientTransitions

variable {X : Type u} [DecidableEq X]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)

omit [DecidableEq X] [Fact (0 < n)] in
/-- Target quotient maps send a single group-algebra coefficient to the mapped basis element. -/
theorem finiteFoxStageTargetGroupAlgebraMap_single_apply
    (q : finiteFoxStageTargetQuotient (X := X) N)
    (a : ModNCompletedCoeff n) :
    finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (finiteFoxStageTargetQuotientMap (X := X) hNM q) a := by
  rw [finiteFoxStageTargetGroupAlgebraMap]
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- The bifiltered target transition on a single group-algebra coefficient. -/
theorem finiteFoxStageBifilteredTargetGroupAlgebraMap_single_apply
    (q : finiteFoxStageTargetQuotient (X := X) N)
    (a : ModNCompletedCoeff m) :
    finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (finiteFoxStageTargetQuotientMap (X := X) hNM q)
        (modNCompletedCoeffMap (n := n) (m := m) hnm a) := by
  rw [finiteFoxStageBifilteredTargetGroupAlgebraMap_apply,
    finiteFoxStageTargetGroupAlgebraCoeffMap_single_apply,
    finiteFoxStageTargetGroupAlgebraMap_single_apply]

end SingleCoefficientTransitions

section Transition

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)
variable {i j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H}
variable (hij : i ≤ j)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- Stage-to-finite maps commute with completed-group-algebra transitions when the coefficient
reductions and quotient maps commute. -/
theorem zcCompletedGroupAlgebraStageToFiniteFoxStage_transition
    (hmod_i : n ∣ i.1.modulus)
    (hmod_j : m ∣ j.1.modulus)
    (hcoeff : ∀ a : ModNCompletedCoeff j.1.modulus,
      modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod_i
          (modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1 a) =
        modNCompletedCoeffMap (n := n) (m := m) hnm
          (modNCompletedCoeffMap (n := m) (m := j.1.modulus) hmod_j a))
    (qmap_i : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) M)
    (qmap_j : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (hqmap : ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2,
      qmap_i
          ((OpenNormalSubgroupInClass.map
            (C := ProC.finiteQuotientClass) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) =
        finiteFoxStageTargetQuotientMap (X := X) hNM (qmap_j q))
    (x : ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j) :
    finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j x) =
      zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i
        (zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij x) := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  refine MonoidAlgebra.induction_on
    (p := fun x : ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j =>
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
          (zcCompletedGroupAlgebraStageToFiniteFoxStage
            (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j x) =
        zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i
          (zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij x))
    x ?_ ?_ ?_
  · intro q
    calc
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
          (zcCompletedGroupAlgebraStageToFiniteFoxStage
            (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j
            (MonoidAlgebra.of (ModNCompletedCoeff j.1.modulus)
              (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2) q)) =
        finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (finiteFoxStageTargetQuotient (X := X) N) (qmap_j q)) := by
          rw [zcCompletedGroupAlgebraStageToFiniteFoxStage_of]
      _ = MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) M)
          (finiteFoxStageTargetQuotientMap (X := X) hNM (qmap_j q)) := by
          rw [finiteFoxStageBifilteredTargetGroupAlgebraMap_apply,
            finiteFoxStageTargetGroupAlgebraCoeffMap_of_quotient,
            finiteFoxStageTargetGroupAlgebraMap_of_quotient]
      _ = MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) M)
          (qmap_i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)) := by
          rw [← hqmap q]
      _ = zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i
          (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2)
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)) := by
          rw [zcCompletedGroupAlgebraStageToFiniteFoxStage_of]
      _ = zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i
          (zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij
            (MonoidAlgebra.of (ModNCompletedCoeff j.1.modulus)
              (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2) q)) := by
          rw [zcCompletedGroupAlgebraTransition_of]
          rfl
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy]
    exact (map_add
      (zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i)
      ((zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij) x)
      ((zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij) y)).symm
  · intro a x hx
    have hscalar :
        finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
            (zcCompletedGroupAlgebraStageToFiniteFoxStage
              (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j
              (algebraMap (ModNCompletedCoeff j.1.modulus)
                (ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j) a)) =
          zcCompletedGroupAlgebraStageToFiniteFoxStage
            (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i
            (zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij
              (algebraMap (ModNCompletedCoeff j.1.modulus)
                (ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass H j) a)) := by
      change
        finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
            (zcCompletedGroupAlgebraStageToFiniteFoxStage
              (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j
              (MonoidAlgebra.single
                (1 : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2)
                a)) =
          zcCompletedGroupAlgebraStageToFiniteFoxStage
            (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i
            (zcCompletedGroupAlgebraTransition ProC.finiteQuotientClass H hij
              (MonoidAlgebra.single
                (1 : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2)
                a))
      rw [zcCompletedGroupAlgebraStageToFiniteFoxStage_single,
        finiteFoxStageBifilteredTargetGroupAlgebraMap_single_apply,
        zcCompletedGroupAlgebraTransition_single,
        zcCompletedGroupAlgebraStageToFiniteFoxStage_single]
      rw [← hqmap 1]
      rw [hcoeff a]
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_mul, RingHom.map_mul, hx]
    rw [hscalar]

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- The completed coefficient maps built from stage projections are compatible on completed
points once the underlying finite-stage maps commute with transitions. -/
theorem zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_transition
    (hmod_i : n ∣ i.1.modulus)
    (hmod_j : m ∣ j.1.modulus)
    (hcoeff : ∀ a : ModNCompletedCoeff j.1.modulus,
      modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod_i
          (modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1 a) =
        modNCompletedCoeffMap (n := n) (m := m) hnm
          (modNCompletedCoeffMap (n := m) (m := j.1.modulus) hmod_j a))
    (qmap_i : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.2 →*
      finiteFoxStageTargetQuotient (X := X) M)
    (qmap_j : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2 →*
      finiteFoxStageTargetQuotient (X := X) N)
    (hqmap : ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2,
      qmap_i
          ((OpenNormalSubgroupInClass.map
            (C := ProC.finiteQuotientClass) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) =
        finiteFoxStageTargetQuotientMap (X := X) hNM (qmap_j q))
    (a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) :
    finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
          (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j a) =
      zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
        (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i a := by
    rw [zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_apply,
      zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_apply]
    change finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (zcCompletedGroupAlgebraStageToFiniteFoxStage
          (ProC := ProC) (X := X) (H := H) N m j hmod_j qmap_j (a.1 j)) =
      zcCompletedGroupAlgebraStageToFiniteFoxStage
        (ProC := ProC) (X := X) (H := H) M n i hmod_i qmap_i (a.1 i)
    rw [← a.2 i j hij]
    exact zcCompletedGroupAlgebraStageToFiniteFoxStage_transition
      (ProC := ProC) (X := X) (H := H) hNM hnm hij hmod_i hmod_j hcoeff
      qmap_i qmap_j hqmap
      (a.1 j)

end Transition

end

end FoxDifferential
