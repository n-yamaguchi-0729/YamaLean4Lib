import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Index

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Completion/Source/LimitMap.lean
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

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The additive map from the completed source group algebra to the prime-power finite-stage
source inverse limit. -/
def primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N where
  toFun z :=
    ⟨fun a =>
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) z,
      by
        intro a b hab
        change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (b, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b) z) =
          primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) z
        exact z.2
          (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
          (b, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
          ⟨hab,
            finiteFoxStagePrimePowerSourceCompletedIndex_mono
              (ℓ := ℓ) (X := X) N hfinite hab⟩⟩
  map_zero' := by
    apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        (0 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 0
    exact primePowerCompletedGroupAlgebraProjection_zero (ℓ := ℓ) (G := FreeGroup X) _
  map_add' x y := by
    apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        (x + y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) x +
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) y
    exact primePowerCompletedGroupAlgebraProjection_add (ℓ := ℓ) (G := FreeGroup X) _ x y

omit [DecidableEq X] in
/-- The completed-source-to-finite-stage-limit map preserves one. -/
@[simp]
theorem primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite
        (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 1 := by
  apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 1
  exact primePowerCompletedGroupAlgebraProjection_one (ℓ := ℓ) (G := FreeGroup X) _

omit [DecidableEq X] in
/-- The completed-source-to-finite-stage-limit map preserves multiplication. -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_mul
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (x y : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) :
    primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite (x * y) =
      primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
          (ℓ := ℓ) (X := X) N hfinite x *
        primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
          (ℓ := ℓ) (X := X) N hfinite y := by
  apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (x * y) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) x *
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) y
  exact primePowerCompletedGroupAlgebraProjection_mul (ℓ := ℓ) (G := FreeGroup X) _ x y

omit [DecidableEq X] in
/-- Projection formula for the completed-source-to-finite-stage-limit map. -/
@[simp]
theorem primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    (finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
          (ℓ := ℓ) (X := X) N hfinite z) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) z := rfl

omit [DecidableEq X] in
/-- The restriction from the genuine completed group algebra to the completed-free-derivative
source subsystem is surjective.

This stays inside completed group algebras and inverse limits: each source stage is one of the
finite completed group-algebra stages, and the stage projections are already surjective. -/
theorem primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_surjective
    [Fact (0 < ℓ)]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite) := by
  classical
  let T := finiteFoxStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N
  let S := primePowerCompletedGroupAlgebraSystem ℓ (FreeGroup X)
  let ψ : ∀ a : ℕ,
      PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) → T.X a :=
    fun a z =>
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        z
  have hψcont : ∀ a : ℕ, Continuous (ψ a) := by
    intro a
    simpa [ψ, S] using
      (S.continuous_projection
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a))
  have hψcompat : T.CompatibleMaps ψ := by
    intro a b hab
    funext z
    change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (b, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
          z) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        z
    exact z.2
      (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (b, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
      ⟨hab,
        finiteFoxStagePrimePowerSourceCompletedIndex_mono
          (ℓ := ℓ) (X := X) N hfinite hab⟩
  have hψsurj : ∀ a : ℕ, Function.Surjective (ψ a) := by
    intro a
    simpa [ψ] using
      (primePowerCompletedGroupAlgebraProjection_surjective
        (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a))
  letI : ∀ a : ℕ, TopologicalSpace (T.X a) := fun a => T.topologicalSpace a
  letI : ∀ a : ℕ, DiscreteTopology (T.X a) := fun _ => ⟨rfl⟩
  letI : ∀ a : ℕ, T2Space (T.X a) := fun _ => inferInstance
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), DiscreteTopology (S.X i) :=
    fun _ => ⟨rfl⟩
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), CompactSpace (S.X i) :=
    fun i => by
      letI : Finite (S.X i) := by
        dsimp [S, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      letI : Fintype (S.X i) := Fintype.ofFinite _
      infer_instance
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), T2Space (S.X i) :=
    fun _ => inferInstance
  letI : CompactSpace (PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) :=
    inferInstance
  letI : T2Space (PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) :=
    S.t2Space_inverseLimit
  have hdirNat : Directed (· ≤ ·) (id : ℕ → ℕ) := by
    intro a b
    exact ⟨max a b, le_max_left _ _, le_max_right _ _⟩
  have hlift : Function.Surjective (T.inverseLimitLift ψ hψcompat) :=
    T.surjective_inverseLimitLift ψ hψcont hψcompat hψsurj hdirNat
  intro y
  rcases hlift y with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  have hcomponent := congrArg (T.projection a) hz
  simpa [ψ, primePowerCompletedGroupAlgebraToFiniteFoxStagePrimePowerSourceLimit_projection]
    using hcomponent

omit [DecidableEq X] in
/-- Compatibility between source-stage augmentation and completed-group-algebra augmentation after
projecting to a finite Fox source stage. -/
@[simp]
theorem finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation_projection_eq_completed
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    finiteFoxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N (ℓ ^ a)
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite a) z) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
          N hfinite a)
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := FreeGroup X) z) := by
  rw [primePowerCompletedCoeffProjection_augmentation]
  rfl



end

end FoxDifferential
