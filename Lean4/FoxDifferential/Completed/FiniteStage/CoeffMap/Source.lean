import FoxDifferential.Completed.FiniteStage.CoeffMap.Target

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/CoeffMap/Source.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]
/-- Coefficient-reduction map on a fixed finite Fox source quotient. -/
def finiteFoxStageSameSourceGroupAlgebraCoeffMap
    (N : Subgroup (FreeGroup X)) (k : ℕ) (hnm : n₀ ∣ m₀) :
    MonoidAlgebra (ModNCompletedCoeff m₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k) →+*
      MonoidAlgebra (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k) :=
  modNCompletedGroupRingCoeffMap
    (n := n₀) (m := m₀)
    (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k) hnm

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of fixed-source coefficient reduction on a quotient basis element. -/
@[simp]
theorem finiteFoxStageSameSourceGroupAlgebraCoeffMap_of
    (N : Subgroup (FreeGroup X)) (k : ℕ) (hnm : n₀ ∣ m₀)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k) :
    finiteFoxStageSameSourceGroupAlgebraCoeffMap (X := X) N k hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k) q := by
  simpa [finiteFoxStageSameSourceGroupAlgebraCoeffMap] using
    (modNCompletedGroupRingCoeffMap_of
      (n := n₀) (m := m₀)
      (H := FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k)
      hnm q)

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Source quotient transition `F/[N,N]N^m → F/[N,N]N^n` induced by `n ∣ m`. -/
def finiteFoxStagePowerSourceQuotientMap
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) :
    FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀ →*
      FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀ :=
  QuotientGroup.map _ _ (MonoidHom.id (FreeGroup X))
    (finiteFoxCommutatorPowerSubgroup_dvd (X := X) N hnm)

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of the source quotient transition on a representative. -/
@[simp]
theorem finiteFoxStagePowerSourceQuotientMap_mk
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    finiteFoxStagePowerSourceQuotientMap (X := X) N hnm
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w) =
      QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w := by
  rfl

/-- Combined source transition on finite Fox source group algebras: quotient transition plus
coefficient reduction. -/
def finiteFoxStagePowerSourceGroupAlgebraMap
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) :
    MonoidAlgebra (ModNCompletedCoeff m₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) →+*
      MonoidAlgebra (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) :=
  (finiteFoxStageSameSourceGroupAlgebraCoeffMap (X := X) N n₀ hnm).comp
    (MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff m₀)
      (finiteFoxStagePowerSourceQuotientMap (X := X) N hnm))

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of the finite Fox source group-algebra transition on a represented word. -/
@[simp 900]
theorem finiteFoxStagePowerSourceGroupAlgebraMap_of
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w) := by
  rw [finiteFoxStagePowerSourceGroupAlgebraMap, RingHom.comp_apply]
  have hmap :
      MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff m₀)
          (finiteFoxStagePowerSourceQuotientMap (X := X) N hnm)
          (MonoidAlgebra.of (ModNCompletedCoeff m₀)
            (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)
            (QuotientGroup.mk'
              (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w)) =
        MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w) := by
    simp only [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.of, MonoidAlgebra.single, QuotientGroup.mk'_apply,
  MonoidHom.coe_mk, OneHom.coe_mk, RingHom.coe_mk, Finsupp.mapDomain_single]
    simpa using congrArg
      (fun q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀ =>
        Finsupp.single q (1 : ModNCompletedCoeff m₀))
      (finiteFoxStagePowerSourceQuotientMap_mk (X := X) N hnm w)
  rw [hmap, finiteFoxStageSameSourceGroupAlgebraCoeffMap_of]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- On a single source-stage basis coefficient, the finite source transition sends the group
coordinate by the quotient map and reduces the coefficient. -/
@[simp]
theorem finiteFoxStagePowerSourceGroupAlgebraMap_single_apply
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)
    (a : ModNCompletedCoeff m₀) :
    finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (finiteFoxStagePowerSourceQuotientMap (X := X) N hnm q)
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
  letI : Algebra (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) :=
    ZMod.algebra' (R := ModNCompletedCoeff n₀) (m := n₀) (n := m₀) hnm
  have hcoeff :
      algebraMap (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) a =
        modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a := by
    rfl
  rw [finiteFoxStagePowerSourceGroupAlgebraMap, RingHom.comp_apply]
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  ext r
  simp only [finiteFoxStageSameSourceGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap,
  AlgHom.toRingHom_eq_coe, MonoidAlgebra.single, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply,
  Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Function.comp_apply, hcoeff, MonoidAlgebra.single_mul_single,
  one_mul, mul_one]

omit [DecidableEq X] [Fact (0 < n₀)] in
/-- The finite Fox source group-algebra transition along `dvd_rfl` is the identity map. -/
@[simp 900]
theorem finiteFoxStagePowerSourceGroupAlgebraMap_rfl
    (N : Subgroup (FreeGroup X)) :
    finiteFoxStagePowerSourceGroupAlgebraMap (X := X) (n₀ := n₀) (m₀ := n₀) N
        dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxStagePowerSourceGroupAlgebraMap (X := X) (n₀ := n₀) (m₀ := n₀) N
          dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) q with ⟨w, rfl⟩
    rw [finiteFoxStagePowerSourceGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [finiteFoxStagePowerSourceGroupAlgebraMap, finiteFoxStageSameSourceGroupAlgebraCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.mapDomainRingHom,
  finiteFoxStagePowerSourceQuotientMap, QuotientGroup.map_id, MonoidHom.coe_id, map_intCast]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Finite Fox source group-algebra transitions compose along divisibility. -/
@[simp 900]
theorem finiteFoxStagePowerSourceGroupAlgebraMap_comp
    {k₀ : ℕ}
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) (hmk : m₀ ∣ k₀) :
    (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm).comp
        (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hmk) =
      finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm).comp
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hmk)) x =
        finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N k₀) q with ⟨w, rfl⟩
    rw [RingHom.comp_apply, finiteFoxStagePowerSourceGroupAlgebraMap_of,
      finiteFoxStagePowerSourceGroupAlgebraMap_of, finiteFoxStagePowerSourceGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [finiteFoxStagePowerSourceGroupAlgebraMap, finiteFoxStageSameSourceGroupAlgebraCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.mapDomainRingHom,
  finiteFoxStagePowerSourceQuotientMap, map_intCast, RingHom.coe_comp, RingHom.coe_coe, RingHom.coe_mk,
  MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- The natural finite-stage map
`(Z/mZ)[F/[N,N]N^m] -> (Z/mZ)[F/N]` commutes with coefficient/source
reduction to a divisor `n ∣ m`. -/
theorem finiteFoxStageGroupAlgebraMap_powerSourceGroupAlgebraMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (x : finiteFoxStageSourceGroupAlgebra (X := X) N m₀) :
    finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀ x) =
      finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀
        (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm
          (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀ x) =
        finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) q with ⟨w, rfl⟩
    rw [finiteFoxCommutatorPowerGroupAlgebraMap_of,
      finiteFoxStageTargetGroupAlgebraCoeffMap_of,
      finiteFoxStagePowerSourceGroupAlgebraMap_of,
      finiteFoxCommutatorPowerGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def]
    change
      ((finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
          (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀))
          (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x) =
        ((finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀).comp
          (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm))
          (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x)
    rw [RingHom.map_mul, RingHom.map_mul]
    have hx' :
        ((finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
            (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀)) x =
          ((finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀).comp
            (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm)) x := by
      simpa [RingHom.comp_apply] using hx
    rw [hx']
    have hcoeff :
        ((finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
            (finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀))
            (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) =
          ((finiteFoxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀).comp
            (finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N hnm))
            (algebraMap (ModNCompletedCoeff m₀)
              (finiteFoxStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) := by
      simp only [finiteFoxStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
  finiteFoxCommutatorPowerGroupAlgebraMap, MonoidAlgebra.mapDomainRingHom, map_intCast,
  finiteFoxStagePowerSourceGroupAlgebraMap, finiteFoxStageSameSourceGroupAlgebraCoeffMap,
  finiteFoxStagePowerSourceQuotientMap]
    rw [hcoeff]




end

end FoxDifferential
