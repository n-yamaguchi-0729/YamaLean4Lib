import FoxDifferential.Completed.FiniteStage.Bifiltered.System

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Bifiltered/InverseSystem.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bifiltered inverse systems of finite Fox semidirect stages

The completed density argument should eventually range over a cofinal family in which both the
finite relation quotient and the coefficient modulus vary.  The finite-stage files already provide
single transition maps

`(Z/m)[F/N]^X ⋊ F/N -> (Z/n)[F/M]^X ⋊ F/M`

for `N ≤ M` and `n ∣ m`.  This file upgrades those transitions to an honest inverse system for an
arbitrary preorder-indexed family of normal subgroups and moduli.  It also exposes the stagewise
boundary-cycle subset and the compatible inverse-limit point attached to a single relation word.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

section BifilteredFamilySystem

variable {X : Type u} [DecidableEq X]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]

/-- Transition in a bifiltered family of finite Fox semidirect stages.

For `i ≤ j`, the `j`-stage is finer: its normal subgroup is contained in the `i`-stage normal
subgroup and its coefficient modulus is divisible by the `i`-stage modulus. -/
def finiteFoxStageBifilteredSemidirectFamilyTransition
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j : J} (hij : i ≤ j) :
    FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j) →*
      FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i) :=
  finiteFoxStageBifilteredSemidirectMap (X := X) (hN hij) (hn hij)

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
@[simp]
theorem finiteFoxStageBifilteredSemidirectFamilyTransition_left
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j : J} (hij : i ≤ j)
    (y : FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j)) :
    (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij y).left =
      finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij) y.left :=
  rfl

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
@[simp]
theorem finiteFoxStageBifilteredSemidirectFamilyTransition_right
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j : J} (hij : i ≤ j)
    (y : FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j)) :
    (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij y).right =
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) y.right :=
  rfl

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)] in
/-- The bifiltered family transition along reflexivity is the identity. -/
@[simp]
theorem finiteFoxStageBifilteredSemidirectFamilyTransition_rfl
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (i : J) :
    finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn (le_rfl : i ≤ i) =
      MonoidHom.id (FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i)) := by
  have hNid : hN (le_rfl : i ≤ i) = (le_rfl : Nstage i ≤ Nstage i) :=
    Subsingleton.elim _ _
  have hnid : hn (le_rfl : i ≤ i) = (dvd_rfl : nstage i ∣ nstage i) :=
    Subsingleton.elim _ _
  change finiteFoxStageBifilteredSemidirectMap
      (X := X) (hN (le_rfl : i ≤ i)) (hn (le_rfl : i ≤ i)) =
    MonoidHom.id (FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i))
  simp only [finiteFoxStageBifilteredSemidirectMap_rfl]

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)] in
/-- Bifiltered family transitions compose. -/
@[simp 900]
theorem finiteFoxStageBifilteredSemidirectFamilyTransition_comp
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) :
    (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hjk) =
    finiteFoxStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn (hij.trans hjk) := by
  have hNcomp : le_trans (hN hjk) (hN hij) = hN (hij.trans hjk) :=
    Subsingleton.elim _ _
  have hncomp : dvd_trans (hn hij) (hn hjk) = hn (hij.trans hjk) :=
    Subsingleton.elim _ _
  change
    (finiteFoxStageBifilteredSemidirectMap (X := X) (hN hij) (hn hij)).comp
      (finiteFoxStageBifilteredSemidirectMap (X := X) (hN hjk) (hn hjk)) =
    finiteFoxStageBifilteredSemidirectMap (X := X) (hN (hij.trans hjk))
      (hn (hij.trans hjk))
  rw [finiteFoxStageBifilteredSemidirectMap_comp
    (X := X) (N₀ := Nstage k) (N₁ := Nstage j) (N₂ := Nstage i)
    (n₀ := nstage i) (n₁ := nstage j) (n₂ := nstage k)
    (hN hjk) (hN hij) (hn hij) (hn hjk)]

/-- The inverse system of a bifiltered family of finite Fox semidirect stages. -/
def finiteFoxStageBifilteredSemidirectSystem
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) :
    InverseSystem (I := J) where
  X := fun j => FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    finiteFoxStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij
  continuous_map := by
    intro i j hij
    letI : TopologicalSpace (FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i)) := ⊥
    letI : TopologicalSpace (FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j)) := ⊥
    letI : DiscreteTopology (FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext y
    exact congrArg (fun f : FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i) →*
        FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i) => f y)
      (finiteFoxStageBifilteredSemidirectFamilyTransition_rfl
        (X := X) Nstage nstage hN hn i)
  map_comp := by
    intro i j k hij hjk
    funext y
    exact congrArg (fun f : FiniteFoxStageSemidirect (X := X) (Nstage k) (nstage k) →*
        FiniteFoxStageSemidirect (X := X) (Nstage i) (nstage i) => f y)
      (finiteFoxStageBifilteredSemidirectFamilyTransition_comp
        (X := X) Nstage nstage hN hn hij hjk)

instance instGroupFiniteFoxStageBifilteredSemidirectSystemX
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) (j : J) :
    Group ((finiteFoxStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn).X j) := by
  dsimp [finiteFoxStageBifilteredSemidirectSystem]
  infer_instance

instance instIsGroupSystemFiniteFoxStageBifilteredSemidirectSystem
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) :
    IsGroupSystem (finiteFoxStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn) where
  map_one := by
    intro i j hij
    exact map_one (finiteFoxStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij)
  map_mul := by
    intro i j hij x y
    exact map_mul (finiteFoxStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij) x y
  map_inv := by
    intro i j hij x
    exact map_inv (finiteFoxStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij) x

/-- The inverse limit of a bifiltered finite Fox semidirect system. -/
abbrev FiniteFoxStageBifilteredSemidirectLimit
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) : Type _ :=
  (finiteFoxStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn).inverseLimit

/-- Projection from the bifiltered inverse limit to a finite Fox semidirect stage. -/
def finiteFoxStageBifilteredSemidirectLimitProjection
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (j : J) :
    FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn →
      FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j) :=
  (finiteFoxStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn).projection j

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)] in
@[simp]
theorem finiteFoxStageBifilteredSemidirectLimitProjection_apply
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (j : J)
    (y : FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn) :
    finiteFoxStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j y = y.1 j :=
  rfl

/-- Boundary-cycle membership in the bifiltered inverse limit is stagewise boundary-cycle
membership. -/
def finiteFoxStageBifilteredSemidirectLimitBoundaryCycleSet
    [Fintype X]
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) :
    Set (FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn) :=
  {y | ∀ j : J,
    finiteFoxStageBifilteredSemidirectLimitProjection
      (X := X) Nstage nstage hN hn j y ∈
        finiteFoxStageSemidirectBoundaryCycleSet (X := X) (Nstage j) (nstage j)}

/-- A relation word gives a compatible point in the bifiltered finite Fox semidirect limit. -/
def finiteFoxStageBifilteredSemidirectKernelWordPointLimit
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (w : FreeGroup X) :
    FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  ⟨fun j => finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w, by
    intro i j hij
    exact finiteFoxStageBifilteredSemidirectMap_kernelWordPoint
      (X := X) (hN hij) (hn hij) w⟩

omit [∀ j, Fact (0 < nstage j)] in
@[simp]
theorem finiteFoxStageBifilteredSemidirectKernelWordPointLimit_projection
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (j : J) (w : FreeGroup X) :
    finiteFoxStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (finiteFoxStageBifilteredSemidirectKernelWordPointLimit
          (X := X) Nstage nstage hN hn w) =
      finiteFoxStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w :=
  rfl

end BifilteredFamilySystem

end

end FoxDifferential
