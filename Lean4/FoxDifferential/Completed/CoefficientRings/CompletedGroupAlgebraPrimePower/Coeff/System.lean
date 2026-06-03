import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.Projection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Coeff/System.lean
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

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coefficient inverse system `i = (a, U) ↦ ZMod (ℓ^a)`. -/
def primePowerCompletedCoeffSystem :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndex G) where
  X := fun i => ZMod (ℓ ^ i.1)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    modNCompletedCoeffMap (n := ℓ ^ i.1) (m := ℓ ^ j.1)
      (primePow_dvd_primePow (ℓ := ℓ) hij.1)
  continuous_map := by
    intro i j hij
    letI : TopologicalSpace (ZMod (ℓ ^ i.1)) := ⊥
    letI : TopologicalSpace (ZMod (ℓ ^ j.1)) := ⊥
    letI : DiscreteTopology (ZMod (ℓ ^ j.1)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_rfl (n := ℓ ^ i.1))) x
  map_comp := by
    intro i j k hij hjk
    funext x
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    letI : Fact (0 < ℓ ^ k.1) := ⟨primePower_pos ℓ k.1⟩
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_comp
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (k := ℓ ^ k.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) x

/-- The inverse-limit object of the coefficient tower indexed by prime powers and quotients. -/
abbrev PrimePowerCompletedCoeff :=
  (primePowerCompletedCoeffSystem ℓ G).inverseLimit

/-- The projection from the prime-power coefficient limit to one finite stage. -/
abbrev primePowerCompletedCoeffProjection (i : PrimePowerCompletedGroupAlgebraIndex G) :
    PrimePowerCompletedCoeff ℓ G →
      ModNCompletedCoeff (ℓ ^ i.1) :=
  (primePowerCompletedCoeffSystem ℓ G).projection i

end

end FoxDifferential
