import FoxDifferential.Completed.FiniteStage.PrimePower.System.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Semidirect.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Prime-power inverse system of finite Fox semidirect stages

The completed density argument eventually needs honest finite quotients of
`Z_C[[H]]^X ⋊ H`.  For a fixed finite-stage normal subgroup `N`, this file constructs the
coefficient-direction inverse system

`((Z/ℓ^a)[F/N]^X ⋊ F/N)_a`

and proves that its transition maps preserve the two finite objects used in the density proof:
boundary-cycle points and kernel-word points.
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

instance finiteFoxStagePrimePowerFactPos (a : ℕ) : Fact (0 < ℓ ^ a) :=
  ⟨primePower_pos ℓ a⟩

/-- Coefficient reduction between prime-power finite Fox semidirect stages. -/
def finiteFoxStagePrimePowerSemidirectTransition
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) :
    FiniteFoxStageSemidirect (X := X) N (ℓ ^ b) →*
      FiniteFoxStageSemidirect (X := X) N (ℓ ^ a) := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  exact finiteFoxStageSemidirectCoeffMap (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [Fact (0 < ℓ)] [DecidableEq X] in
@[simp]
theorem finiteFoxStagePrimePowerSemidirectTransition_left
    [Fact (0 < ℓ)]
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b)
    (y : FiniteFoxStageSemidirect (X := X) N (ℓ ^ b)) :
    (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab y).left =
      fun i : X =>
        finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab (y.left i) := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  rfl

omit [Fact (0 < ℓ)] [DecidableEq X] in
@[simp]
theorem finiteFoxStagePrimePowerSemidirectTransition_right
    [Fact (0 < ℓ)]
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b)
    (y : FiniteFoxStageSemidirect (X := X) N (ℓ ^ b)) :
    (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab y).right =
      y.right := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  rfl

omit [Fact (0 < ℓ)] [DecidableEq X] in
/-- The prime-power semidirect transition from a stage to itself is the identity. -/
@[simp]
theorem finiteFoxStagePrimePowerSemidirectTransition_id
    [Fact (0 < ℓ)]
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    finiteFoxStagePrimePowerSemidirectTransition
        (ℓ := ℓ) (X := X) N (le_rfl : a ≤ a) =
      MonoidHom.id (FiniteFoxStageSemidirect (X := X) N (ℓ ^ a)) := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  change finiteFoxStageSemidirectCoeffMap
      (X := X) (n₀ := ℓ ^ a) (m₀ := ℓ ^ a) N dvd_rfl =
    MonoidHom.id (FiniteFoxStageSemidirect (X := X) N (ℓ ^ a))
  exact finiteFoxStageSemidirectCoeffMap_rfl (X := X) N

omit [DecidableEq X] in
/-- Prime-power semidirect transitions compose along the stage order. -/
@[simp]
theorem finiteFoxStagePrimePowerSemidirectTransition_comp
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp
        (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hbc) =
      finiteFoxStagePrimePowerSemidirectTransition
        (ℓ := ℓ) (X := X) N (hab.trans hbc) := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  haveI : Fact (0 < ℓ ^ c) := ⟨primePower_pos ℓ c⟩
  change (finiteFoxStageSemidirectCoeffMap (X := X) N
        (primePow_dvd_primePow (ℓ := ℓ) hab)).comp
      (finiteFoxStageSemidirectCoeffMap (X := X) N
        (primePow_dvd_primePow (ℓ := ℓ) hbc)) =
    finiteFoxStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) (hab.trans hbc))
  simp only [finiteFoxStageSemidirectCoeffMap_comp]

/-- The inverse system of finite Fox semidirect stages over prime-power coefficients. -/
def finiteFoxStagePrimePowerSemidirectSystem
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    InverseSystem (I := ℕ) where
  X := fun a => FiniteFoxStageSemidirect (X := X) N (ℓ ^ a)
  topologicalSpace := fun _ => ⊥
  map := fun {a b} hab =>
    finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
  continuous_map := by
    intro a b hab
    letI : TopologicalSpace (FiniteFoxStageSemidirect (X := X) N (ℓ ^ a)) := ⊥
    letI : TopologicalSpace (FiniteFoxStageSemidirect (X := X) N (ℓ ^ b)) := ⊥
    letI : DiscreteTopology (FiniteFoxStageSemidirect (X := X) N (ℓ ^ b)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro a
    funext y
    exact congrArg (fun f : FiniteFoxStageSemidirect (X := X) N (ℓ ^ a) →*
        FiniteFoxStageSemidirect (X := X) N (ℓ ^ a) => f y)
      (finiteFoxStagePrimePowerSemidirectTransition_id (ℓ := ℓ) (X := X) N a)
  map_comp := by
    intro a b c hab hbc
    funext y
    exact congrArg (fun f : FiniteFoxStageSemidirect (X := X) N (ℓ ^ c) →*
        FiniteFoxStageSemidirect (X := X) N (ℓ ^ a) => f y)
      (finiteFoxStagePrimePowerSemidirectTransition_comp
        (ℓ := ℓ) (X := X) N hab hbc)

instance instGroupFiniteFoxStagePrimePowerSemidirectSystemX
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    Group ((finiteFoxStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N).X a) := by
  dsimp [finiteFoxStagePrimePowerSemidirectSystem]
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  infer_instance

instance instIsGroupSystemFiniteFoxStagePrimePowerSemidirectSystem
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    IsGroupSystem (finiteFoxStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N) where
  map_one := by
    intro a b hab
    exact map_one (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab)
  map_mul := by
    intro a b hab x y
    exact map_mul (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab) x y
  map_inv := by
    intro a b hab x
    exact map_inv (finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab) x

omit [Fact (0 < ℓ)] in
/-- Prime-power semidirect transitions carry finite lifts to finite lifts. -/
theorem finiteFoxStagePrimePowerSemidirectTransition_lift
    [Fact (0 < ℓ)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
        (finiteFoxStageLift (X := X) N (ℓ ^ b) w) =
      finiteFoxStageLift (X := X) N (ℓ ^ a) w := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  change finiteFoxStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) hab)
        (finiteFoxStageLift (X := X) N (ℓ ^ b) w) =
    finiteFoxStageLift (X := X) N (ℓ ^ a) w
  exact finiteFoxStageSemidirectCoeffMap_lift (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [Fact (0 < ℓ)] in
/-- Prime-power semidirect transitions carry kernel-word points to kernel-word points. -/
theorem finiteFoxStagePrimePowerSemidirectTransition_kernelWordPoint
    [Fact (0 < ℓ)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
        (finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ b) w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  change finiteFoxStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) hab)
        (finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ b) w) =
    finiteFoxStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w
  exact finiteFoxStageSemidirectCoeffMap_kernelWordPoint (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [Fact (0 < ℓ)] [DecidableEq X] in
/-- Prime-power semidirect transitions preserve finite boundary-cycle points. -/
theorem finiteFoxStagePrimePowerSemidirectTransition_mem_boundaryCycleSet
    [Fact (0 < ℓ)]
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b)
    {y : FiniteFoxStageSemidirect (X := X) N (ℓ ^ b)}
    (hy : y ∈ finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ b)) :
    finiteFoxStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab y ∈
      finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  change finiteFoxStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) hab) y ∈
    finiteFoxStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a)
  exact finiteFoxStageSemidirectCoeffMap_mem_boundaryCycleSet (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) hy

end

end FoxDifferential
