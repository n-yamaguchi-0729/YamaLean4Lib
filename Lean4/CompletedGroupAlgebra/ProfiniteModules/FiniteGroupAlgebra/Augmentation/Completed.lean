import CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Augmentation.Abstract

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/ProfiniteModules/FiniteGroupAlgebra/Augmentation/Completed.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Augmentation packages for completed group algebra models

This module transports finite-stage augmentation packages to completed group-algebra models and their augmentation ideals.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v w z

/-- The coefficient map `R → RG` attached to a dense map from the abstract group
algebra. -/
noncomputable def completedGroupAlgebraCoefficientMap
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [Group G] [Ring RG]
    (dense : RingHom (MonoidAlgebra R G) RG) : RingHom R RG :=
  dense.comp (algebraMap R (MonoidAlgebra R G))

/-- The completed coefficient map is the dense map applied to coefficient scalars. -/
@[simp]
theorem completedGroupAlgebraCoefficientMap_apply
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [Group G] [Ring RG]
    (dense : RingHom (MonoidAlgebra R G) RG) (r : R) :
    completedGroupAlgebraCoefficientMap R G RG dense r =
      dense (algebraMap R (MonoidAlgebra R G) r) :=
  rfl

/-- A completed group algebra model has a continuous augmentation when its dense abstract
group-algebra map admits a continuous extension of the abstract augmentation. -/
def hasCompletedGroupAlgebraAugmentation
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    (dense : RingHom (MonoidAlgebra R G) RG) : Prop :=
  Exists fun ε : RingHom RG R =>
    And (ε.comp dense = groupAlgebraAugmentation R G) (Continuous ε)

/-- The continuous augmentation extracted from completed group algebra augmentation data. -/
noncomputable def completedGroupAlgebraAugmentation
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) : RingHom RG R :=
  Classical.choose haug

/-- The completed augmentation extends the abstract augmentation along the dense map. -/
theorem completedGroupAlgebraAugmentation_comp_dense
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    (completedGroupAlgebraAugmentation R G RG haug).comp dense =
      groupAlgebraAugmentation R G :=
  (Classical.choose_spec haug).1

/-- The augmentation extracted from the completed augmentation package is continuous. -/
theorem continuous_completedGroupAlgebraAugmentation
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    Continuous (completedGroupAlgebraAugmentation R G RG haug) :=
  (Classical.choose_spec haug).2

/-- The coefficient map is a section of the completed augmentation. -/
theorem completedGroupAlgebraAugmentation_comp_coefficientMap
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    (completedGroupAlgebraAugmentation R G RG haug).comp
        (completedGroupAlgebraCoefficientMap R G RG dense) = RingHom.id R := by
  ext r
  have h := congrArg
    (fun f : RingHom (MonoidAlgebra R G) R => f (algebraMap R (MonoidAlgebra R G) r))
    (completedGroupAlgebraAugmentation_comp_dense R G RG haug)
  simpa [completedGroupAlgebraCoefficientMap] using h

/-- The augmentation ideal of a completed group algebra model with augmentation data. -/
noncomputable def completedGroupAlgebraAugmentationIdeal
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) : Ideal RG :=
  RingHom.ker (completedGroupAlgebraAugmentation R G RG haug)

/-- Membership in the completed augmentation ideal is the vanishing of the completed
augmentation. -/
@[simp]
theorem mem_completedGroupAlgebraAugmentationIdeal_iff
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) (x : RG) :
    x ∈ completedGroupAlgebraAugmentationIdeal R G RG haug ↔
      completedGroupAlgebraAugmentation R G RG haug x = 0 :=
  Iff.rfl

/-- The completed augmentation is split by the completed coefficient map. -/
theorem completedGroupAlgebraAugmentation_surjective
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    Function.Surjective (completedGroupAlgebraAugmentation R G RG haug) := by
  intro r
  refine ⟨completedGroupAlgebraCoefficientMap R G RG dense r, ?_⟩
  have h := congrArg (fun f : RingHom R R => f r)
    (completedGroupAlgebraAugmentation_comp_coefficientMap R G RG haug)
  simpa using h

/-- The inclusion of the completed augmentation ideal into the completed group algebra model is
injective. -/
theorem completedGroupAlgebraAugmentationIdeal_subtype_injective
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    Function.Injective
      (fun x : completedGroupAlgebraAugmentationIdeal R G RG haug => (x : RG)) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The completed augmentation ideal is exactly the kernel of the completed augmentation. -/
theorem exact_completedGroupAlgebraAugmentationIdeal_subtype
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    Function.Exact
      (fun x : completedGroupAlgebraAugmentationIdeal R G RG haug => (x : RG))
      (completedGroupAlgebraAugmentation R G RG haug) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/-- Any completed group algebra model with augmentation data has a short exact augmentation
sequence `0 → I_G → [[R G]] → R → 0`. -/
theorem completedGroupAlgebraAugmentation_shortExact
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) :
    Function.Injective
        (fun x : completedGroupAlgebraAugmentationIdeal R G RG haug => (x : RG)) ∧
      Function.Exact
        (fun x : completedGroupAlgebraAugmentationIdeal R G RG haug => (x : RG))
        (completedGroupAlgebraAugmentation R G RG haug) ∧
      Function.Surjective (completedGroupAlgebraAugmentation R G RG haug) := by
  exact ⟨completedGroupAlgebraAugmentationIdeal_subtype_injective R G RG haug,
    exact_completedGroupAlgebraAugmentationIdeal_subtype R G RG haug,
    completedGroupAlgebraAugmentation_surjective R G RG haug⟩

/-- In the finite-group case, the finite group algebra has the expected completed augmentation
data. -/
theorem finiteGroupAlgebra_hasCompletedGroupAlgebraAugmentation
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [Finite G] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    hasCompletedGroupAlgebraAugmentation R G (MonoidAlgebra R G)
      (RingHom.id (MonoidAlgebra R G)) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  refine Exists.intro (groupAlgebraAugmentation R G) ?_
  exact And.intro (RingHom.comp_id (groupAlgebraAugmentation R G))
    (finiteGroupAlgebra_augmentation_continuous R G)

end CompletedGroupAlgebra
