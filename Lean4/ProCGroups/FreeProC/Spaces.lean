import ProCGroups.FreeProC.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Spaces.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u v

section GeneralTopologicalSpaces

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}

private theorem isProfiniteSpace_of_isProfiniteGroup
    {G : Type u} [Group G] [TopologicalSpace G] (hG : IsProfiniteGroup G) :
    InverseSystems.IsProfiniteSpace G :=
  (InverseSystems.isProfiniteSpace_iff_compact_t2_totallyDisconnected (X := G)).2
    ⟨hG.2.1, hG.2.2.1, hG.2.2.2⟩

/-- A closed equivalence relation with finite Hausdorff quotient, viewed as one of the finite
pointed quotients used to build the profinite reflection of a pointed space. -/
structure PointedFiniteClosedEquivalenceRelation
    (X : Type u) [TopologicalSpace X] (_x0 : X) where
  toSetoid : Setoid X
  closed_rel : IsClosed {p : X × X | toSetoid.r p.1 p.2}
  finite_quotient : Finite (Quotient toSetoid)
  t2_quotient : T2Space (Quotient toSetoid)

attribute [instance] PointedFiniteClosedEquivalenceRelation.t2_quotient

/-- The cardinal `ρ(X)` of clopen subsets of a space. -/
noncomputable def clopenCardinal
    (X : Type u) [TopologicalSpace X] : Cardinal :=
  Cardinal.mk {U : Set X // IsClopen U}

/-- A bundled profinite reflection of a pointed topological space. This packages the inverse-limit
space `X̌`, its basepoint, and the natural map `τ : X → X̌`. -/
structure PointedProfiniteReflectionData
    (X : Type u) [TopologicalSpace X] (x0 : X) where
  carrier : Type u
  instTopologicalSpace : TopologicalSpace carrier
  point : carrier
  τ : X → carrier
  continuous_τ : Continuous τ
  map_base : τ x0 = point
  denseRange_τ : DenseRange τ
  isProfinite : InverseSystems.IsProfiniteSpace carrier
  existsUnique_factor :
    ∀ {Y : Type u} [TopologicalSpace Y],
      InverseSystems.IsProfiniteSpace Y →
      ∀ (y0 : Y) (f : X → Y), Continuous f → f x0 = y0 →
        ∃! ftilde : carrier → Y,
          Continuous ftilde ∧ ftilde point = y0 ∧ ∀ x, ftilde (τ x) = f x
  cardinal_quotients_eq_clopen :
    Cardinal.mk (PointedFiniteClosedEquivalenceRelation X x0) =
      clopenCardinal carrier

attribute [instance] PointedProfiniteReflectionData.instTopologicalSpace

/-- After factoring through the profinite reflection, the same free pro-`C` group is free on the
pointed profinite space `(X̌, ∗)`.

This formulation includes the bridge saying that `ProC`-targets are profinite spaces. -/
theorem pointedFreeProCGroupOn_profiniteReflection
    {X : Type u} [TopologicalSpace X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (Xhat : PointedProfiniteReflectionData X x0)
    (hProfinite :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC (G := G) → InverseSystems.IsProfiniteSpace G)
    (hι : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι) :
    ∃ ιtilde : Xhat.carrier → F,
      Continuous ιtilde ∧
        ιtilde Xhat.point = 1 ∧
        (∀ x, ιtilde (Xhat.τ x) = ι x) ∧
        IsPointedFreeProCGroupOn (ProC := ProC) Xhat.carrier Xhat.point F ιtilde := by
  let hfactor :=
    Xhat.existsUnique_factor (hProfinite hι.isProC) 1 ι hι.continuous_ι hι.map_base
  let ιtilde : Xhat.carrier → F := Classical.choose (ExistsUnique.exists hfactor)
  have hιtilde : Continuous ιtilde ∧ ιtilde Xhat.point = 1 ∧
      ∀ x, ιtilde (Xhat.τ x) = ι x :=
    Classical.choose_spec (ExistsUnique.exists hfactor)
  refine ⟨ιtilde, hιtilde.1, hιtilde.2.1, hιtilde.2.2, ?_⟩
  refine ⟨hι.isProC, hιtilde.1, hιtilde.2.1, ?_, ?_⟩
  · have hsubset : Set.range ι ⊆ Set.range ιtilde := by
      rintro z ⟨x, rfl⟩
      exact ⟨Xhat.τ x, hιtilde.2.2 x⟩
    have hsub :
        Subgroup.closure (Set.range ι) ≤
          Subgroup.closure (Set.range ιtilde) :=
      Subgroup.closure_mono hsubset
    have hsub' :
        (Subgroup.closure (Set.range ι)).topologicalClosure ≤
          (Subgroup.closure (Set.range ιtilde)).topologicalClosure := by
      exact Subgroup.topologicalClosure_minimal _ (hsub.trans (Subgroup.le_topologicalClosure _))
        (Subgroup.isClosed_topologicalClosure _)
    rw [hι.generates_range] at hsub'
    exact top_unique hsub'
  intro G _ _ _ hG φ hφ hφ0 hgen
  let ψ : X → G := φ ∘ Xhat.τ
  have hψ : Continuous ψ := hφ.comp Xhat.continuous_τ
  have hψ0 : ψ x0 = 1 := by
    simpa [ψ, Function.comp, Xhat.map_base] using hφ0
  have hgenψ : Generation.TopologicallyGenerates (G := G) (Set.range ψ) := by
    have hclosureRange : closure (Set.range ψ) = closure (Set.range φ) := by
      have hsubset : Set.range ψ ⊆ Set.range φ := by
        rintro z ⟨x, rfl⟩
        exact ⟨Xhat.τ x, rfl⟩
      apply le_antisymm
      · exact closure_mono hsubset
      · have hdense : Dense (Set.range Xhat.τ) := Xhat.denseRange_τ
        have hrange : Set.range φ ⊆ closure (Set.range ψ) := by
          simpa [Set.range_comp, Function.comp, ψ] using
            (Continuous.range_subset_closure_image_dense (f := φ) hφ hdense)
        exact closure_minimal hrange isClosed_closure
    have hgenClosure :
        Generation.TopologicallyGenerates (G := G) (closure (Set.range ψ)) := by
      rw [hclosureRange]
      exact (Generation.topologicallyGenerates_closure_iff (G := G) (X := Set.range φ)).1 hgen
    exact (Generation.topologicallyGenerates_closure_iff (G := G) (X := Set.range ψ)).2 hgenClosure
  rcases hι.existsUnique_lift hG ψ hψ hψ0 hgenψ with ⟨f, hf, huniq⟩
  refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
  · have hGprofinite : InverseSystems.IsProfiniteSpace G := hProfinite hG
    let hGctd :=
      (InverseSystems.isProfiniteSpace_iff_compact_t2_totallyDisconnected (X := G)).1 hGprofinite
    letI : CompactSpace G := hGctd.1
    letI : T2Space G := hGctd.2.1
    have hEq :
        (fun y => f (ιtilde y)) = φ := by
      apply DenseRange.equalizer (f := Xhat.τ) Xhat.denseRange_τ
      · exact hf.1.comp hιtilde.1
      · exact hφ
      · funext x
        simpa [Function.comp, ψ, hιtilde.2.2 x] using hf.2 x
    intro y
    exact congrFun hEq y
  · intro g hg
    apply huniq g
    refine ⟨hg.1, ?_⟩
    intro x
    simpa [ψ, Function.comp, hιtilde.2.2 x] using
      hg.2 (Xhat.τ x)

end GeneralTopologicalSpaces

end ProCGroups.FreeProC
