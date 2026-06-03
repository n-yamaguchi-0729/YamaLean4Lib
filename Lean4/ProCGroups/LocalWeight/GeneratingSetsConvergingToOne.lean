import ProCGroups.LocalWeight.LocalWeightTheorems

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/LocalWeight/GeneratingSetsConvergingToOne.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Local weight and quotient ranks

Studies local weight, metrizability, quotient size bounds, and cardinal invariants of profinite groups.
-/

open Set
open TopologicalSpace
open Order
open scoped Cardinal
open scoped Topology Pointwise

namespace ProCGroups.LocalWeight

universe u

open ProCGroups.Generation ProCGroups.ProC ProCGroups.FiniteGeneration


/-- A generating set converging to `1` is countable exactly when the profinite group admits a
countable descending open-normal chain at the identity. -/
theorem cardinal_le_aleph0_iff_hasCountableDescendingOpenNormalChainAtOne
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Set G) :
    IsProfiniteGroup G →
      GeneratesAndConvergesToOne (G := G) X →
        (Cardinal.mk X ≤ ℵ₀ ↔
          ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G) := by
  intro hG hX
  constructor
  · intro hXcount
    by_cases hXinfinite : Set.Infinite X
    · have hlocal : localWeight G ≤ ℵ₀ := by
        simpa [cardinalEqLocalWeight_of_generatesAndConvergesToOne_infinite
          (G := G) X hG hX hXinfinite] using hXcount
      exact hasCountableDescendingOpenNormalChainAtOne_of_localWeight_le_aleph0
        (G := G) hG hlocal
    · letI : Finite X := Set.not_infinite.mp hXinfinite
      have hXfinite : X.Finite := Set.toFinite X
      let s : Finset G := hXfinite.toFinset
      have hsgen : TopologicallyFinitelyGenerated G := by
        refine ⟨s, ?_⟩
        simpa [s] using hX.1
      letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
      letI : T2Space G := IsProfiniteGroup.t2Space hG
      letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
      exact hasCountableDescendingOpenNormalChainAtOne_of_topologicallyFinitelyGenerated
        (G := G) hsgen
  · intro hchain
    rcases hchain with ⟨U, _hUanti, hUbasis⟩
    have hBasis : IsNeighborhoodBasisAt (X := G) (1 : G)
        (Set.range fun n : ℕ => (((U n : Subgroup G) : Set G))) := by
      constructor
      · intro V hV
        rcases hV with ⟨n, rfl⟩
        exact ⟨openNormalSubgroup_isOpen (G := G) (U n), (U n).one_mem'⟩
      · intro V hVopen h1V
        rcases hUbasis V hVopen h1V with ⟨n, hnV⟩
        exact ⟨((U n : Subgroup G) : Set G), ⟨n, rfl⟩, hnV⟩
    have hlocal : localWeight G ≤ ℵ₀ := by
      calc
        localWeight G ≤
            familyCardinal (X := G) (Set.range fun n : ℕ => (((U n : Subgroup G) : Set G))) := by
          simpa [localWeight] using
            localWeightAt_le_familyCardinal_of_basis (X := G) (x := (1 : G)) hBasis
        _ ≤ ℵ₀ := by
          unfold familyCardinal
          exact Cardinal.mk_le_aleph0_iff.mpr
            (Set.countable_range (fun n : ℕ => (((U n : Subgroup G) : Set G))))
    by_cases hXinfinite : Set.Infinite X
    · calc
        Cardinal.mk X = localWeight G :=
          cardinalEqLocalWeight_of_generatesAndConvergesToOne_infinite
            (G := G) X hG hX hXinfinite
        _ ≤ ℵ₀ := hlocal
    · letI : Finite X := Set.not_infinite.mp hXinfinite
      exact ((Cardinal.lt_aleph0_iff_finite (α := X)).2 inferInstance).le

/-- A profinite group is metrizable exactly when it admits a countable generating set converging
to `1`. -/
theorem nonempty_metrizableSpace_iff_exists_countable_generatingSetConvergingToOne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    IsProfiniteGroup G →
      (Nonempty (MetrizableSpace G) ↔
        ∃ X : Set G, GeneratesAndConvergesToOne (G := G) X ∧ Countable X) := by
  intro hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  constructor
  · intro hmetr
    rcases exists_generatorsConvergingToOne (G := G) hG with ⟨X, hX⟩
    refine ⟨X, hX, ?_⟩
    have hchain : ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
      exact (metrizable_iff_hasCountableDescendingOpenNormalChainAtOne
        (G := G) hG).1 hmetr
    have hXcount : Cardinal.mk X ≤ ℵ₀ := by
      exact
        ((cardinal_le_aleph0_iff_hasCountableDescendingOpenNormalChainAtOne
            (G := G) X)
          hG hX).2 hchain
    exact Cardinal.mk_le_aleph0_iff.mp hXcount
  · rintro ⟨X, hX, hXcount⟩
    have hchain : ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
      exact
        ((cardinal_le_aleph0_iff_hasCountableDescendingOpenNormalChainAtOne
            (G := G) X)
          hG hX).1
          (Cardinal.mk_le_aleph0_iff.mpr hXcount)
    exact (metrizable_iff_hasCountableDescendingOpenNormalChainAtOne
      (G := G) hG).2 hchain

end LocalWeight
