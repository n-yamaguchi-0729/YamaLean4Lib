import ProCGroups.InverseSystems.FiniteStageFactorization

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/ProfiniteModules/Basic/Definitions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Basic predicates for profinite modules
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- A compact Hausdorff totally disconnected topological ring. -/
def IsProfiniteRing (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] : Prop :=
  IsTopologicalRing Λ ∧ CompactSpace Λ ∧ T2Space Λ ∧ TotallyDisconnectedSpace Λ

namespace IsProfiniteRing

variable {Λ : Type u} [Ring Λ] [TopologicalSpace Λ]

/-- The topological-ring component of a profinite ring. -/
theorem isTopologicalRing (hΛ : IsProfiniteRing Λ) : IsTopologicalRing Λ :=
  hΛ.1

/-- The compactness component of a profinite ring. -/
theorem compactSpace (hΛ : IsProfiniteRing Λ) : CompactSpace Λ :=
  hΛ.2.1

/-- The Hausdorff component of a profinite ring. -/
theorem t2Space (hΛ : IsProfiniteRing Λ) : T2Space Λ :=
  hΛ.2.2.1

/-- The `T1` component of a profinite ring. -/
theorem t1Space (hΛ : IsProfiniteRing Λ) : T1Space Λ := by
  letI : T2Space Λ := hΛ.t2Space
  infer_instance

/-- The totally disconnected component of a profinite ring. -/
theorem totallyDisconnectedSpace (hΛ : IsProfiniteRing Λ) : TotallyDisconnectedSpace Λ :=
  hΛ.2.2.2

/-- The underlying topological space of a profinite ring is profinite. -/
theorem isProfiniteSpace (hΛ : IsProfiniteRing Λ) :
    ProCGroups.InverseSystems.IsProfiniteSpace Λ :=
  ⟨hΛ.compactSpace, hΛ.t2Space, hΛ.totallyDisconnectedSpace⟩

end IsProfiniteRing

/-- A topological module over a topological ring. -/
def IsTopologicalModuleOver (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M] : Prop :=
  IsTopologicalRing Λ ∧ IsTopologicalAddGroup M ∧ ContinuousSMul Λ M

/-- A profinite module over a profinite ring.

This predicate is intentionally a `Prop`, not a typeclass. The bundled public object for data
APIs is `ProfiniteModule`; theorem statements may keep taking explicit
`hM : IsProfiniteModule Λ M` hypotheses. -/
def IsProfiniteModule (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M] : Prop :=
  IsProfiniteRing Λ ∧ IsTopologicalAddGroup M ∧ ContinuousSMul Λ M ∧
    CompactSpace M ∧ T2Space M ∧ TotallyDisconnectedSpace M

/-- The universal property of the free profinite module on a profinite space.

This is a minimal public interface used by the completed group algebra universal property. The
larger construction libraries live outside the public completed-group-algebra root. -/
def IsFreeProfiniteModuleOn (Λ : Type u) (X : Type v) (M : Type w)
    [Ring Λ] [TopologicalSpace Λ] [TopologicalSpace X] [AddCommGroup M] [TopologicalSpace M]
    [Module Λ M] (ι : X -> M) : Prop :=
  IsProfiniteRing Λ ∧ IsProfiniteModule Λ M ∧ Continuous ι ∧
    closure (Submodule.span Λ (Set.range ι) : Set M) = Set.univ ∧
      ∀ (N : Type w) [AddCommGroup N] [TopologicalSpace N] [Module Λ N],
        IsProfiniteModule Λ N →
          ∀ f : X -> N, Continuous f →
            ∃! F : M →L[Λ] N, ∀ x : X, F (ι x) = f x

/-- Pointed version of `IsFreeProfiniteModuleOn`, with the base point mapped to zero. -/
def IsFreeProfiniteModuleOnPointed (Λ : Type u) (X : Type v) (M : Type w)
    [Ring Λ] [TopologicalSpace Λ] [TopologicalSpace X] [AddCommGroup M] [TopologicalSpace M]
    [Module Λ M] (base : X) (ι : X -> M) : Prop :=
  IsProfiniteRing Λ ∧ IsProfiniteModule Λ M ∧ Continuous ι ∧ ι base = 0 ∧
    closure (Submodule.span Λ (Set.range ι) : Set M) = Set.univ ∧
      ∀ (N : Type w) [AddCommGroup N] [TopologicalSpace N] [Module Λ N],
        IsProfiniteModule Λ N →
          ∀ f : X -> N, Continuous f → f base = 0 →
            ∃! F : M →L[Λ] N, ∀ x : X, F (ι x) = f x

/-- Bundled profinite modules over a fixed profinite ring.

Use this when a public data structure should carry a profinite module as an object rather than
separate carrier, instances, and `IsProfiniteModule` proof fields. -/
structure ProfiniteModule (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [module : Module Λ carrier]
  isProfinite : IsProfiniteModule Λ carrier

attribute [instance] ProfiniteModule.addCommGroup
attribute [instance] ProfiniteModule.topologicalSpace
attribute [instance] ProfiniteModule.module

namespace IsProfiniteModule

variable {Λ : Type u} {M : Type v} [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M]

/-- The profinite-ring component of a profinite module. -/
theorem isProfiniteRing (hM : IsProfiniteModule Λ M) : IsProfiniteRing Λ :=
  hM.1

/-- The additive topological-group component of a profinite module. -/
theorem isTopologicalAddGroup (hM : IsProfiniteModule Λ M) : IsTopologicalAddGroup M :=
  hM.2.1

/-- The continuous scalar-action component of a profinite module. -/
theorem continuousSMul (hM : IsProfiniteModule Λ M) : ContinuousSMul Λ M :=
  hM.2.2.1

/-- The compactness component of a profinite module. -/
theorem compactSpace (hM : IsProfiniteModule Λ M) : CompactSpace M :=
  hM.2.2.2.1

/-- The Hausdorff component of a profinite module. -/
theorem t2Space (hM : IsProfiniteModule Λ M) : T2Space M :=
  hM.2.2.2.2.1

/-- The `T1` component of a profinite module. -/
theorem t1Space (hM : IsProfiniteModule Λ M) : T1Space M := by
  letI : T2Space M := hM.t2Space
  infer_instance

/-- The totally disconnected component of a profinite module. -/
theorem totallyDisconnectedSpace (hM : IsProfiniteModule Λ M) :
    TotallyDisconnectedSpace M :=
  hM.2.2.2.2.2

/-- A profinite module is a topological module over its scalar ring. -/
theorem isTopologicalModuleOver (hM : IsProfiniteModule Λ M) :
    IsTopologicalModuleOver Λ M :=
  ⟨hM.isProfiniteRing.isTopologicalRing, hM.isTopologicalAddGroup, hM.continuousSMul⟩

/-- The underlying topological space of a profinite module is profinite. -/
theorem isProfiniteSpace (hM : IsProfiniteModule Λ M) :
    ProCGroups.InverseSystems.IsProfiniteSpace M :=
  ⟨hM.compactSpace, hM.t2Space, hM.totallyDisconnectedSpace⟩

end IsProfiniteModule

/-- A discrete topological module. -/
def IsDiscreteModule (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M] : Prop :=
  IsTopologicalModuleOver Λ M ∧ DiscreteTopology M

/-- A submodule whose underlying set is finite. -/
def IsFiniteSubmodule {Λ : Type u} {M : Type v} [Ring Λ] [AddCommGroup M] [Module Λ M]
    (N : Submodule Λ M) : Prop :=
  (N : Set M).Finite

/-- Every element lies in a finite submodule. -/
def IsUnionOfFiniteSubmodules (Λ : Type u) (M : Type v) [Ring Λ] [AddCommGroup M]
    [Module Λ M] : Prop :=
  ∀ m : M, ∃ N : Submodule Λ M, IsFiniteSubmodule N ∧ m ∈ N

/-- Finite-index submodules form a neighborhood basis at zero. -/
def HasFiniteIndexSubmoduleBasis (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M]
    [AddCommGroup M] [Module Λ M] : Prop :=
  ∀ U ∈ 𝓝 (0 : M), ∃ N : Submodule Λ M,
    IsOpen (N : Set M) ∧ (N : Set M) ⊆ U ∧ Nonempty (Fintype (M ⧸ N))

/-- A profinite module is represented by its finite quotient modules. -/
def IsInverseLimitOfFiniteQuotientModules (Λ : Type u) (M : Type v) [Ring Λ]
    [TopologicalSpace M] [AddCommGroup M] [Module Λ M] : Prop :=
  HasFiniteIndexSubmoduleBasis Λ M ∧
    ∀ U ∈ 𝓝 (0 : M), ∃ N : Submodule Λ M,
      IsOpen (N : Set M) ∧ (N : Set M) ⊆ U ∧ Nonempty (Fintype (M ⧸ N))

/-- Lemma 5.1.1(b), predicate form: in this development the inverse-limit formulation is recorded
by a finite-index open-submodule basis at zero. -/
theorem inverseLimitOfFiniteQuotientModules_iff_finiteIndexSubmoduleBasis
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M] [AddCommGroup M]
    [Module Λ M] :
    IsInverseLimitOfFiniteQuotientModules Λ M ↔ HasFiniteIndexSubmoduleBasis Λ M := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h⟩

end CompletedGroupAlgebra
