import ProCGroups.LocalWeight.ClosedNormalDataAndTransfiniteSeries

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/LocalWeight/LocalWeightTheorems.lean
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

open ProCGroups.ProC ProCGroups.Generation
open ProCGroups.FiniteGeneration


/-- 6.2(a). Closed generating subsets compute the local weight.
-/
theorem localWeight_eq_rho_of_closedGeneratingSet
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Set G) (hG : IsProfiniteGroup G) (hXclosed : IsClosed X)
    (hXgen : TopologicallyGenerates (G := G) X) (hXinfinite : Set.Infinite X) :
    localWeight G = rho ↥X := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  have hGinf : Infinite G := by
    classical
    by_contra hfin
    letI : Finite G := not_infinite_iff_finite.mp hfin
    exact hXinfinite (Set.toFinite X)
  letI : Infinite G := hGinf
  have hle : localWeight G ≤ rho ↥X :=
    localWeight_le_rho_of_closedGeneratingSet
      (G := G) X hG hXclosed hXgen hXinfinite
  have hrho_le : rho ↥X ≤ localWeight G := by
    have hBasis : TopologicalSpace.IsTopologicalBasis { U : Set G | IsClopen U } :=
      ProCGroups.InverseSystems.isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected
    calc
      rho ↥X ≤ rho G :=
        rho_subtype_le_rho_of_closed (X := G) (A := X) hXclosed
      _ = weight G := (weight_eq_rho_of_clopenBasis (X := G) hBasis).symm
      _ = localWeight G :=
        (localWeight_eq_weight_of_infinite_profiniteGroup (G := G) hG).symm
  exact le_antisymm hle hrho_le

/-- 6.2(b). Infinite generating sets converging to `1` have cardinality `w₀(G)`.
-/
theorem cardinalEqLocalWeight_of_generatesAndConvergesToOne_infinite
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Set G) (hG : IsProfiniteGroup G)
    (hX : GeneratesAndConvergesToOne (G := G) X) (hXinfinite : Set.Infinite X) :
    Cardinal.mk X = localWeight G := by
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  have hclosure : closure X = X ∪ ({1} : Set G) := by
    exact (closure_generatorsConvergingToOne (G := G) hG hX.2).2 hXinfinite
  have hClosureInf : Set.Infinite (closure X) := by
    by_contra hfin
    exact hXinfinite ((Set.not_infinite.mp hfin).subset subset_closure)
  have hClosureGen : TopologicallyGenerates (G := G) (closure X) := by
    exact (topologicallyGenerates_closure_iff (G := G) (X := X)).1 hX.1
  have hClosureClosed : IsClosed (closure X) := isClosed_closure
  calc
    Cardinal.mk X = rho ↥(closure X) := by
      symm
      exact rho_closure_eq_cardinal_of_generatesAndConvergesToOne_infinite
        (G := G) X hG hX hXinfinite hclosure
    _ = localWeight G := by
      simpa using
        (localWeight_eq_rho_of_closedGeneratingSet
          (G := G) (closure X) hG hClosureClosed hClosureGen hClosureInf).symm




/-- 6.3. Infinite generator rank equals local weight.
-/
theorem topologicalRank_eq_localWeight_of_infinite
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) (hdinf : Cardinal.aleph0 ≤ topologicalRank G) :
    topologicalRank G = localWeight G := by
  classical
  obtain ⟨X, hX, hXle⟩ :=
    hasGeneratingSetConvergingToOneOfCardinalLE_of_d_le
      (G := G) hG (κ := topologicalRank G) le_rfl
  let C : Set Cardinal := {κ : Cardinal |
    ∃ Y : Set G, GeneratesAndConvergesToOne (G := G) Y ∧ Cardinal.mk Y = κ}
  have hd_le : topologicalRank G ≤ Cardinal.mk X := by
    have hXmem : Cardinal.mk X ∈ C := by
      exact ⟨X, hX, rfl⟩
    simpa [topologicalRank, C] using (csInf_le' hXmem)
  have hXcard : Cardinal.mk X = topologicalRank G := le_antisymm hXle hd_le
  have hXinfinite : Set.Infinite X := by
    refine setInfinite_of_cardinal_ge_aleph0 (X := X) ?_
    calc
      Cardinal.aleph0 ≤ topologicalRank G := hdinf
      _ = Cardinal.mk X := hXcard.symm
  calc
    topologicalRank G = Cardinal.mk X := hXcard.symm
    _ = localWeight G :=
      cardinalEqLocalWeight_of_generatesAndConvergesToOne_infinite
        (G := G) X hG hX hXinfinite


end LocalWeight
