import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.DiscreteQuotient
import ProCGroups.InverseSystems.CofinalityAndDensity

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/InverseSystems/ProfiniteSpace.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Inverse systems and inverse limits

Defines inverse systems of topological groups and proves lift, projection, exactness, quotient, stagewise isomorphism, and finite-stage factorization results.
-/

open scoped Topology

namespace ProCGroups.InverseSystems

universe u v w

/-- A compact Hausdorff totally disconnected space has a basis of
clopen sets. -/
theorem isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected {X : Type w}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  isTopologicalBasis_isClopen

/-- Every open neighborhood in a profinite space contains a clopen neighborhood of the point. -/
theorem exists_clopen_subset_of_mem_open {X : Type w} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  compact_exists_isClopen_in_isOpen hU hx

/-- A profinite space, in the unbundled form matching Mathlib's `Profinite.of` constructor. -/
abbrev IsProfiniteSpace (X : Type w) [TopologicalSpace X] : Prop :=
  CompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X

namespace IsProfiniteSpace

variable {X : Type w} [TopologicalSpace X]

/-- The compactness component of a profinite space. -/
theorem compactSpace (hX : IsProfiniteSpace X) : CompactSpace X :=
  hX.1

/-- The Hausdorff component of a profinite space. -/
theorem t2Space (hX : IsProfiniteSpace X) : T2Space X :=
  hX.2.1

/-- The `T1` component of a profinite space. -/
theorem t1Space (hX : IsProfiniteSpace X) : T1Space X := by
  letI : T2Space X := hX.t2Space
  infer_instance

/-- The totally disconnected component of a profinite space. -/
theorem totallyDisconnectedSpace (hX : IsProfiniteSpace X) : TotallyDisconnectedSpace X :=
  hX.2.2

/-- Bundle an unbundled profinite space as Mathlib's `Profinite`. -/
noncomputable def toProfinite (hX : IsProfiniteSpace X) : Profinite.{w} := by
  letI : CompactSpace X := hX.compactSpace
  letI : T2Space X := hX.t2Space
  letI : TotallyDisconnectedSpace X := hX.totallyDisconnectedSpace
  exact Profinite.of X

/-- The profinite-space wrapper has the same underlying type as the original space. -/
@[simp] theorem coe_toProfinite (hX : IsProfiniteSpace X) :
    (hX.toProfinite : Type w) = X := by
  letI : CompactSpace X := hX.compactSpace
  letI : T2Space X := hX.t2Space
  letI : TotallyDisconnectedSpace X := hX.totallyDisconnectedSpace
  rfl

/-- Every Mathlib bundled profinite space is profinite in the unbundled sense. -/
theorem of_profinite (X : Profinite.{w}) : IsProfiniteSpace X :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end IsProfiniteSpace

/-- The inverse system of all discrete quotients of `X`. -/
def discreteQuotientSystem (X : Type w) [TopologicalSpace X] :
    InverseSystem (I := OrderDual (DiscreteQuotient X)) where
  X := fun Q => Quotient (show DiscreteQuotient X from Q).toSetoid
  topologicalSpace := fun _ => inferInstance
  map := fun {Q R} h => DiscreteQuotient.ofLE h
  continuous_map := fun {Q R} _ => continuous_of_discreteTopology
  map_id := fun Q => by
    funext x
    exact DiscreteQuotient.ofLE_refl_apply (A := (Q : DiscreteQuotient X)) x
  map_comp := fun {Q R T} hQR hRT => by
    funext x
    exact congrFun (DiscreteQuotient.ofLE_comp_ofLE hRT hQR) x

private theorem compatibleMaps_discreteQuotientProj (X : Type w) [TopologicalSpace X] :
    (discreteQuotientSystem X).CompatibleMaps
      (fun Q : OrderDual (DiscreteQuotient X) => (Q : DiscreteQuotient X).proj) := by
  intro Q R h
  funext x
  exact DiscreteQuotient.ofLE_proj h x

/-- A compact Hausdorff totally disconnected space is profinite. -/
noncomputable def homeomorph_inverseLimit_discreteQuotientSystem (X : Type w)
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    X ≃ₜ (discreteQuotientSystem X).inverseLimit := by
  let S := discreteQuotientSystem X
  letI : ∀ Q : OrderDual (DiscreteQuotient X), CompactSpace (S.X Q) := fun Q => by
    change CompactSpace (Quotient (show DiscreteQuotient X from Q).toSetoid)
    let _ : Fintype (Quotient (show DiscreteQuotient X from Q).toSetoid) := by
      have : Finite (show DiscreteQuotient X from Q) := inferInstance
      exact Fintype.ofFinite _
    infer_instance
  letI : ∀ Q : OrderDual (DiscreteQuotient X), T2Space (S.X Q) := fun Q => by
    change T2Space (Quotient (show DiscreteQuotient X from Q).toSetoid)
    infer_instance
  letI : ∀ Q : OrderDual (DiscreteQuotient X), TotallyDisconnectedSpace (S.X Q) := fun Q => by
    change TotallyDisconnectedSpace (Quotient (show DiscreteQuotient X from Q).toSetoid)
    infer_instance
  letI : CompactSpace S.inverseLimit := inferInstance
  letI : T2Space S.inverseLimit := S.t2Space_inverseLimit
  letI : TotallyDisconnectedSpace S.inverseLimit := S.totallyDisconnectedSpace_inverseLimit
  let f : X → S.inverseLimit :=
    S.inverseLimitLift (fun Q : OrderDual (DiscreteQuotient X) => (Q : DiscreteQuotient X).proj)
      (compatibleMaps_discreteQuotientProj X)
  have hf_continuous : Continuous f :=
    S.continuous_inverseLimitLift (fun Q : OrderDual (DiscreteQuotient X) => (Q : DiscreteQuotient X).proj)
      (fun Q => (Q : DiscreteQuotient X).proj_continuous) (compatibleMaps_discreteQuotientProj X)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact DiscreteQuotient.eq_of_forall_proj_eq fun Q => by
      have hQ := congrArg (fun z => S.projection (show OrderDual (DiscreteQuotient X) from Q) z) hxy
      simpa [f] using hQ
  have hf_surj : Function.Surjective f := by
    intro y
    let qs : (Q : DiscreteQuotient X) → Q := fun Q => S.projection (show OrderDual (DiscreteQuotient X) from Q) y
    have hqs :
        ∀ (A B : DiscreteQuotient X) (h : A ≤ B), DiscreteQuotient.ofLE h (qs A) = qs B := by
      intro A B h
      simpa [qs] using
        S.projection_compatible y (show OrderDual (DiscreteQuotient X) from B)
          (show OrderDual (DiscreteQuotient X) from A) h
    rcases DiscreteQuotient.exists_of_compat qs hqs with ⟨x, hx⟩
    refine ⟨x, S.ext ?_⟩
    intro Q
    simpa [f] using hx Q
  let fHom : Profinite.of X ⟶ Profinite.of S.inverseLimit := CompHausLike.ofHom _ ⟨f, hf_continuous⟩
  exact CompHausLike.homeoOfIso (CompHausLike.isoOfBijective fHom ⟨hf_inj, hf_surj⟩)

@[simp] theorem discreteQuotientSystem_projection_homeomorph (X : Type w)
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (Q : OrderDual (DiscreteQuotient X)) (x : X) :
    (discreteQuotientSystem X).projection Q
        (homeomorph_inverseLimit_discreteQuotientSystem X x) =
      (show DiscreteQuotient X from Q).proj x := by
  let S := discreteQuotientSystem X
  change (S.inverseLimitLift (fun Q : OrderDual (DiscreteQuotient X) =>
      (show DiscreteQuotient X from Q).proj)
      (compatibleMaps_discreteQuotientProj X) x).1 Q =
    (show DiscreteQuotient X from Q).proj x
  rfl

/-- A compact Hausdorff totally disconnected space is a profinite space. -/
theorem isProfiniteSpace_of_compact_t2_totallyDisconnected (X : Type w) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    IsProfiniteSpace X :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A profinite space is compact, Hausdorff, and totally disconnected. -/
theorem compact_t2_totallyDisconnected_of_isProfiniteSpace (X : Type w) [TopologicalSpace X]
    (hX : IsProfiniteSpace X) :
    CompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X :=
  hX

/-- A Hausdorff space with a clopen basis is totally disconnected. -/
theorem totallyDisconnectedSpace_of_t2_basis_clopen (X : Type w) [TopologicalSpace X] [T2Space X]
    (hX : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}) :
    TotallyDisconnectedSpace X := by
  let _ : TotallySeparatedSpace X := totallySeparatedSpace_of_t0_of_basis_clopen hX
  infer_instance

/-- The inverse-limit definition of a profinite space is equivalent to the usual compact Hausdorff
totally disconnected characterization. -/
theorem isProfiniteSpace_iff_compact_t2_totallyDisconnected {X : Type w} [TopologicalSpace X] :
    IsProfiniteSpace X ↔ CompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X :=
  Iff.rfl

/-- A compact Hausdorff space is profinite exactly when the clopen sets form a basis. -/
theorem isProfiniteSpace_iff_compact_t2_basis_clopen {X : Type w} [TopologicalSpace X] :
    IsProfiniteSpace X ↔
      CompactSpace X ∧ T2Space X ∧ TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} := by
  constructor
  · intro hX
    rcases compact_t2_totallyDisconnected_of_isProfiniteSpace X hX with ⟨hcompact, hT2, htot⟩
    let _ : CompactSpace X := hcompact
    let _ : T2Space X := hT2
    let _ : TotallyDisconnectedSpace X := htot
    exact ⟨hcompact, hT2, isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected⟩
  · rintro ⟨hcompact, hT2, hbasis⟩
    let _ : CompactSpace X := hcompact
    let _ : T2Space X := hT2
    let _ : TotallyDisconnectedSpace X := totallyDisconnectedSpace_of_t2_basis_clopen X hbasis
    exact isProfiniteSpace_of_compact_t2_totallyDisconnected X

end ProCGroups.InverseSystems
