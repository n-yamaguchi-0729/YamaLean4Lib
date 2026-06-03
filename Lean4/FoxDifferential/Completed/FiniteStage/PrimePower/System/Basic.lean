import FoxDifferential.Completed.FiniteStage.CoeffMap.BoundaryCycles

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Basic.lean
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


omit [Fact (0 < ℓ)] in
/-- Source group algebra at the `ℓ^a` finite Fox stage. -/
abbrev finiteFoxStagePrimePowerSourceGroupAlgebra
    (N : Subgroup (FreeGroup X)) (a : ℕ) : Type u :=
  MonoidAlgebra (ModNCompletedCoeff (ℓ ^ a))
    (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))

omit [Fact (0 < ℓ)] in
/-- Target group algebra at the `ℓ^a` finite Fox stage. -/
abbrev finiteFoxStagePrimePowerTargetGroupAlgebra
    (N : Subgroup (FreeGroup X)) (a : ℕ) : Type u :=
  finiteFoxStageTargetGroupAlgebra (X := X) N (ℓ ^ a)

omit [Fact (0 < ℓ)] in
/-- Free-group group algebra with coefficients modulo `ℓ^a`. -/
abbrev finiteFoxStagePrimePowerFreeGroupAlgebra (a : ℕ) : Type u :=
  MonoidAlgebra (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X)

omit [Fact (0 < ℓ)] in
/-- Coefficient reduction on free-group group algebras between prime-power stages. -/
def finiteFoxStagePrimePowerFreeGroupAlgebraTransition
    {a b : ℕ} (hab : a ≤ b) :
    finiteFoxStagePrimePowerFreeGroupAlgebra (ℓ := ℓ) (X := X) b →+*
      finiteFoxStagePrimePowerFreeGroupAlgebra (ℓ := ℓ) (X := X) a :=
  modNCompletedGroupRingCoeffMap (n := ℓ ^ a) (m := ℓ ^ b)
    (FreeGroup X) (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Coefficient reduction sends a group-like free-group element to the same group-like element at
the lower prime-power stage. -/
@[simp]
theorem finiteFoxStagePrimePowerFreeGroupAlgebraTransition_of
    {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    finiteFoxStagePrimePowerFreeGroupAlgebraTransition (ℓ := ℓ) (X := X) hab
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b)) (FreeGroup X) w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X) w := by
  exact modNCompletedGroupRingCoeffMap_of (n := ℓ ^ a) (m := ℓ ^ b)
    (H := FreeGroup X) (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [Fact (0 < ℓ)] in
/-- Projection from the free-group group algebra to the finite Fox source quotient at a
prime-power stage. -/
def finiteFoxStagePrimePowerSourceProjection
    (N : Subgroup (FreeGroup X)) (a : ℕ) :
    finiteFoxStagePrimePowerFreeGroupAlgebra (ℓ := ℓ) (X := X) a →+*
      finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff (ℓ ^ a))
    (QuotientGroup.mk'
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation of the source projection on a group-like free-group algebra element. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceProjection_of
    (N : Subgroup (FreeGroup X)) (a : ℕ) (w : FreeGroup X) :
    finiteFoxStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X) w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) := by
  simp only [finiteFoxStagePrimePowerSourceProjection, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, QuotientGroup.coe_mk', Finsupp.mapDomain_single,
  QuotientGroup.mk'_apply]

omit [Fact (0 < ℓ)] in
/-- Transition map for the finite Fox source quotient group algebras along prime-power stages. -/
def finiteFoxStagePrimePowerSourceTransition
    (N : Subgroup (FreeGroup X)) {a b : ℕ} (hab : a ≤ b) :
    finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b →+*
      finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a :=
  finiteFoxStagePowerSourceGroupAlgebraMap (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation of a source transition map on a group-like quotient element. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceTransition_of
    (N : Subgroup (FreeGroup X)) {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
          (FreeGroup X ⧸
            finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b))
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b)) w)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) := by
  exact finiteFoxStagePowerSourceGroupAlgebraMap_of (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- The source transition map from a stage to itself is the identity. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceTransition_id
    (N : Subgroup (FreeGroup X)) (a : ℕ) :
    finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N
        (le_rfl : a ≤ a) =
      RingHom.id _ := by
  simp only [finiteFoxStagePrimePowerSourceTransition, finiteFoxStagePowerSourceGroupAlgebraMap_rfl]

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Source transition maps compose along the order on prime-power stages. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceTransition_comp
    (N : Subgroup (FreeGroup X)) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab).comp
        (finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hbc) =
      finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N (hab.trans hbc) := by
  simp only [finiteFoxStagePrimePowerSourceTransition, finiteFoxStagePowerSourceGroupAlgebraMap_comp]

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Source projection commutes with coefficient reduction and the source transition map. -/
theorem finiteFoxStagePrimePowerSourceProjection_transition
    (N : Subgroup (FreeGroup X)) {a b : ℕ} (hab : a ≤ b) :
    (finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab).comp
        (finiteFoxStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N b) =
      (finiteFoxStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a).comp
        (finiteFoxStagePrimePowerFreeGroupAlgebraTransition (ℓ := ℓ) (X := X) hab) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab).comp
          (finiteFoxStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N b)) x =
        ((finiteFoxStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a).comp
          (finiteFoxStagePrimePowerFreeGroupAlgebraTransition (ℓ := ℓ) (X := X) hab)) x)
    x ?_ ?_ ?_
  · intro w
    rw [RingHom.comp_apply, RingHom.comp_apply,
      finiteFoxStagePrimePowerSourceProjection_of,
      finiteFoxStagePrimePowerSourceTransition_of,
      finiteFoxStagePrimePowerFreeGroupAlgebraTransition_of,
      finiteFoxStagePrimePowerSourceProjection_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro r x hx
    rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [finiteFoxStagePrimePowerSourceTransition, finiteFoxStagePowerSourceGroupAlgebraMap,
  finiteFoxStageSameSourceGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
  finiteFoxStagePrimePowerSourceProjection, map_intCast, finiteFoxStagePrimePowerFreeGroupAlgebraTransition,
  RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MonoidAlgebra.mapDomainRingHom_apply, QuotientGroup.coe_mk']

omit [Fact (0 < ℓ)] in
/-- Transition map for the finite Fox target group algebras along prime-power stages. -/
def finiteFoxStagePrimePowerTargetTransition
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) :
    finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b →+*
      finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a :=
  finiteFoxStageTargetGroupAlgebraCoeffMap (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation of a target transition map on a group-like target quotient element. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetTransition_of
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
          (finiteFoxStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (finiteFoxStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w) := by
  exact finiteFoxStageTargetGroupAlgebraCoeffMap_of (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- The target transition map from a stage to itself is the identity. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetTransition_id
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N
        (le_rfl : a ≤ a) =
      RingHom.id _ := by
  simp only [finiteFoxStagePrimePowerTargetTransition, finiteFoxStageTargetGroupAlgebraCoeffMap_rfl]

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Target transition maps compose along the order on prime-power stages. -/
@[simp]
theorem finiteFoxStagePrimePowerTargetTransition_comp
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab).comp
        (finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hbc) =
      finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N (hab.trans hbc) := by
  simp only [finiteFoxStagePrimePowerTargetTransition, finiteFoxStageTargetGroupAlgebraCoeffMap_comp]

/-- The inverse system of finite Fox source quotient group algebras over prime-power stages. -/
def finiteFoxStagePrimePowerSourceSystem
    (N : Subgroup (FreeGroup X)) :
    InverseSystem (I := ℕ) where
  X := finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N
  topologicalSpace := fun _ => ⊥
  map := fun {a b} hab => finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
  continuous_map := by
    intro a b hab
    letI : TopologicalSpace
        (finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a) := ⊥
    letI : TopologicalSpace
        (finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⊥
    letI : DiscreteTopology
        (finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro a
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (finiteFoxStagePrimePowerSourceTransition_id (ℓ := ℓ) (X := X) N a)) x
  map_comp := by
    intro a b c hab hbc
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (finiteFoxStagePrimePowerSourceTransition_comp
          (ℓ := ℓ) (X := X) N hab hbc)) x

/-- The inverse system of finite Fox target group algebras over prime-power stages. -/
def finiteFoxStagePrimePowerTargetSystem
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    InverseSystem (I := ℕ) where
  X := finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N
  topologicalSpace := fun _ => ⊥
  map := fun {a b} hab => finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
  continuous_map := by
    intro a b hab
    letI : TopologicalSpace
        (finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a) := ⊥
    letI : TopologicalSpace
        (finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⊥
    letI : DiscreteTopology
        (finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro a
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (finiteFoxStagePrimePowerTargetTransition_id (ℓ := ℓ) (X := X) N a)) x
  map_comp := by
    intro a b c hab hbc
    funext x
    exact congrFun
      (congrArg DFunLike.coe
      (finiteFoxStagePrimePowerTargetTransition_comp
          (ℓ := ℓ) (X := X) N hab hbc)) x



end

end FoxDifferential
