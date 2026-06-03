import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Augmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/AugmentationIdealPrimePower/Stage.lean
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

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The augmentation ideal on one prime-power finite stage. -/
def primePowerCompletedGroupAlgebraStageAugmentationIdeal
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Ideal (PrimePowerCompletedGroupAlgebraStage ℓ G i) := by
  letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
  exact RingHom.ker (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2)

instance instFinitePrimePowerCompletedGroupAlgebraStageAugmentationIdeal
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Finite ↥(primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) := by
  classical
  letI : Finite (PrimePowerCompletedGroupAlgebraStage ℓ G i) :=
    instFinitePrimePowerCompletedGroupAlgebraStage (ℓ := ℓ) (G := G) i
  refine Finite.of_injective Subtype.val ?_
  intro x y hxy
  exact Subtype.ext hxy

/-- The kernel of the canonical prime-power augmentation. -/
def primePowerCompletedGroupAlgebraAugmentationKernel :
    Set (PrimePowerCompletedGroupAlgebra ℓ G) :=
  {x | primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
    (Zero.zero : PrimePowerCompletedCoeff ℓ G)}

/-- The kernel of the canonical prime-power augmentation, viewed as a subtype. -/
abbrev PrimePowerCompletedGroupAlgebraAugmentationKernel :=
  {x : PrimePowerCompletedGroupAlgebra ℓ G //
    x ∈ primePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G)}

omit [Fact (0 < ℓ)] in
variable {ℓ G} in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が所属条件を対応する augmentation または射影の消滅条件として特徴づけることを述べる。 -/
@[simp]
theorem mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
    {i : PrimePowerCompletedGroupAlgebraIndex G}
    {x : PrimePowerCompletedGroupAlgebraStage ℓ G i} :
    x ∈ primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i ↔
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2 x = 0 := by
  rw [primePowerCompletedGroupAlgebraStageAugmentationIdeal, RingHom.mem_ker]

variable {ℓ G} in
omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が所属条件を対応する augmentation または射影の消滅条件として特徴づけることを述べる。 -/
@[simp]
theorem mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff
    {x : PrimePowerCompletedGroupAlgebra ℓ G} :
    x ∈ primePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) ↔
      primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
        (Zero.zero : PrimePowerCompletedCoeff ℓ G) := by
  rfl

variable {ℓ G} in
omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall
    {x : PrimePowerCompletedGroupAlgebra ℓ G} :
    x ∈ primePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) ↔
      ∀ i : PrimePowerCompletedGroupAlgebraIndex G,
        modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x) = 0 := by
  constructor
  · intro hx i
    have hx0 :
        primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
          (Zero.zero : PrimePowerCompletedCoeff ℓ G) :=
      (mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff
        (ℓ := ℓ) (G := G) (x := x)).1 hx
    have hi := congrArg
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i) hx0
    simpa [primePowerCompletedCoeffProjection_augmentation]
      using hi
  · intro hx
    rw [mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff]
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    simpa [primePowerCompletedCoeffProjection_augmentation] using hx i

/-- The transition maps on the prime-power finite-stage augmentation ideals. -/
def primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j →
      primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i := by
  intro x
  refine ⟨primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij x.1, ?_⟩
  rw [mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff]
  letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
  letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (primePowerCompletedGroupAlgebraStageAugmentation_comp_transition
        (ℓ := ℓ) (G := G) hij))
    x.1
  rw [RingHom.comp_apply] at hcomp
  have hx0 :
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ j.1) G j.2 x.1 = 0 :=
    (mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
      (ℓ := ℓ) (G := G) (i := j) (x := x.1)).1 x.2
  simpa [hx0] using hcomp

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 遷移写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_val
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
    ((primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
        (ℓ := ℓ) (G := G) hij x :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
      PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij x.1 := rfl

/-- The inverse system of prime-power finite-stage augmentation ideals. -/
def primePowerCompletedGroupAlgebraAugmentationIdealSystem :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndex G) where
  X := fun i => ↥(primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
      (ℓ := ℓ) (G := G) hij
  continuous_map := by
    intro i j hij
    letI : TopologicalSpace
        (primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) := ⊥
    letI : TopologicalSpace
        (primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) := ⊥
    letI : DiscreteTopology
        (primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransition_id (ℓ := ℓ) (G := G) i)) x.1
  map_comp := by
    intro i j k hij hjk
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransition_comp (ℓ := ℓ) (G := G) hij hjk))
      x.1

/-- The inverse-limit object of the prime-power augmentation-ideal system. -/
abbrev PrimePowerCompletedGroupAlgebraAugmentationIdeal :=
  (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).inverseLimit

/-- The projection from the prime-power augmentation-ideal inverse limit to one stage. -/
abbrev primePowerCompletedGroupAlgebraAugmentationIdealProjection
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →
      primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i :=
  (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).projection i

end

end FoxDifferential
