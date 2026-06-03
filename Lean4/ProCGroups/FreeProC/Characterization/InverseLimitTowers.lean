import ProCGroups.FreeProC.Characterization.EmbeddingProblems

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Characterization/InverseLimitTowers.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

namespace ProCGroups.FreeProC.Characterization

open ProCGroups.FreeProC
open ProCGroups.InverseSystems
open Set
open scoped Topology

universe u

/-- A countable surjective inverse system of free pro-`C` groups.

This record stores the transition maps for all `m ≤ n`, together with the identity and
composition laws. Its limit is the canonical subtype inverse limit supplied by
`InverseSystems.InverseSystem`. -/
structure CountableSurjectiveFreeProCSystem
    (ProC : ProCGroups.ProC.ProCGroupPredicate) where
  stage : ℕ → FreeProCGroupOnConvergingSetData (ProC := ProC)
  transition :
    ∀ {m n : ℕ}, m ≤ n → (stage n).carrier →* (stage m).carrier
  continuous_transition :
    ∀ {m n : ℕ} (hmn : m ≤ n), Continuous (transition hmn)
  transition_id :
    ∀ n : ℕ, transition (le_rfl : n ≤ n) = MonoidHom.id (stage n).carrier
  transition_comp :
    ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n),
      (transition hlm).comp (transition hmn) = transition (hlm.trans hmn)
  surjective_transition :
    ∀ {m n : ℕ} (hmn : m ≤ n), Function.Surjective (transition hmn)

namespace CountableSurjectiveFreeProCSystem

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}

/-- The adjacent bonding map in the countable system. -/
def bonding (T : CountableSurjectiveFreeProCSystem ProC) (n : ℕ) :
    (T.stage (n + 1)).carrier →* (T.stage n).carrier :=
  T.transition (Nat.le_succ n)

theorem continuous_bonding (T : CountableSurjectiveFreeProCSystem ProC) (n : ℕ) :
    Continuous (T.bonding n) :=
  T.continuous_transition (Nat.le_succ n)

theorem surjective_bonding (T : CountableSurjectiveFreeProCSystem ProC) (n : ℕ) :
    Function.Surjective (T.bonding n) :=
  T.surjective_transition (Nat.le_succ n)

/-- The underlying inverse system associated to the countable tower data. -/
def inverseSystem (T : CountableSurjectiveFreeProCSystem ProC) :
    InverseSystem (I := ℕ) where
  X := fun n => (T.stage n).carrier
  topologicalSpace := fun n => inferInstance
  map := fun {_m _n} hmn => T.transition hmn
  continuous_map := fun {_m _n} hmn => T.continuous_transition hmn
  map_id := by
    intro n
    funext x
    simpa using congrArg (fun f : (T.stage n).carrier →* (T.stage n).carrier => f x)
      (T.transition_id n)
  map_comp := by
    intro l m n hlm hmn
    funext x
    simpa [Function.comp, MonoidHom.comp_apply] using
      congrArg (fun f : (T.stage n).carrier →* (T.stage l).carrier => f x)
        (T.transition_comp hlm hmn)

instance instGroupInverseSystemStage (T : CountableSurjectiveFreeProCSystem ProC)
    (n : ℕ) : Group (T.inverseSystem.X n) := by
  change Group (T.stage n).carrier
  infer_instance

instance instIsTopologicalGroupInverseSystemStage (T : CountableSurjectiveFreeProCSystem ProC)
    (n : ℕ) : IsTopologicalGroup (T.inverseSystem.X n) := by
  change IsTopologicalGroup (T.stage n).carrier
  infer_instance

/-- The associated inverse system is group-valued. -/
def isGroupSystem (T : CountableSurjectiveFreeProCSystem ProC) :
    IsGroupSystem T.inverseSystem where
  map_one := by
    intro m n hmn
    exact (T.transition hmn).map_one
  map_mul := by
    intro m n hmn x y
    exact (T.transition hmn).map_mul x y
  map_inv := by
    intro m n hmn x
    exact (T.transition hmn).map_inv x

/-- The canonical inverse-limit carrier of a countable surjective free pro-`C` system. -/
abbrev limitCarrier (T : CountableSurjectiveFreeProCSystem ProC) : Type u :=
  T.inverseSystem.inverseLimit

instance instGroupLimitCarrier (T : CountableSurjectiveFreeProCSystem ProC) :
    Group T.limitCarrier := by
  letI : IsGroupSystem T.inverseSystem := T.isGroupSystem
  infer_instance

instance instTopologicalSpaceLimitCarrier (T : CountableSurjectiveFreeProCSystem ProC) :
    TopologicalSpace T.limitCarrier := by
  infer_instance

instance instIsTopologicalGroupLimitCarrier (T : CountableSurjectiveFreeProCSystem ProC) :
    IsTopologicalGroup T.limitCarrier := by
  letI : IsGroupSystem T.inverseSystem := T.isGroupSystem
  infer_instance

/-- The canonical projection homomorphism from the inverse limit to a stage. -/
def projection (T : CountableSurjectiveFreeProCSystem ProC) (n : ℕ) :
    T.limitCarrier →* (T.stage n).carrier := by
  letI : IsGroupSystem T.inverseSystem := T.isGroupSystem
  exact projectionHom (S := T.inverseSystem) n

theorem continuous_projection (T : CountableSurjectiveFreeProCSystem ProC) (n : ℕ) :
    Continuous (T.projection n) := by
  simpa [projection, projectionHom] using T.inverseSystem.continuous_projection n

theorem compatible (T : CountableSurjectiveFreeProCSystem ProC) (n : ℕ)
    (x : T.limitCarrier) :
    T.bonding n (T.projection (n + 1) x) = T.projection n x := by
  simpa [bonding, projection, inverseSystem] using
    T.inverseSystem.projection_compatible x n (n + 1) (Nat.le_succ n)

/-- The canonical projection family satisfies the inverse-limit universal property. -/
theorem isInverseLimit_projection (T : CountableSurjectiveFreeProCSystem ProC) :
    T.inverseSystem.IsInverseLimit (fun n => T.projection n) := by
  letI : IsGroupSystem T.inverseSystem := T.isGroupSystem
  simpa [projection] using T.inverseSystem.isInverseLimit_projection

end CountableSurjectiveFreeProCSystem

/-- External freeness input for countable surjective inverse systems.

The inverse-system data now determines the limit object itself; this criterion only records the
additional mathematical input needed to identify that canonical limit as a free pro-`C` group. -/
structure CountableSurjectiveSystemFreenessCriterion
    {ProC : ProCGroups.ProC.ProCGroupPredicate}
    (T : CountableSurjectiveFreeProCSystem ProC) : Prop where
  free_limit_of_countable_generating_family :
    Nonempty (ConvergingGeneratingMap ℕ T.limitCarrier) →
      ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
        Nonempty (Fdata.carrier ≃ₜ* T.limitCarrier)

namespace CountableSurjectiveSystemFreenessCriterion

/-- Apply the freeness criterion to the canonical inverse limit of a countable system. -/
theorem apply
    {ProC : ProCGroups.ProC.ProCGroupPredicate}
    (T : CountableSurjectiveFreeProCSystem ProC)
    (hcrit : CountableSurjectiveSystemFreenessCriterion T)
    (hcount : Nonempty (ConvergingGeneratingMap ℕ T.limitCarrier)) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData (ProC := ProC),
      Nonempty (Fdata.carrier ≃ₜ* T.limitCarrier) :=
  hcrit.free_limit_of_countable_generating_family hcount

end CountableSurjectiveSystemFreenessCriterion

end ProCGroups.FreeProC.Characterization
