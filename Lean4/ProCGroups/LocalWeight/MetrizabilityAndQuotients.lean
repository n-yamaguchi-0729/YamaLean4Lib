import ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import ProCGroups.Generation.QuotientGeneratorConvergingPairs
import ProCGroups.LocalWeight.CardinalInvariantsAndLocalWeight
import ProCGroups.LocalWeight.SubgroupChains
import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/LocalWeight/MetrizabilityAndQuotients.lean
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


/-!
# Metrizability And Quotients

## Main declarations
- `quotientLocalWeight`
- `quotientLocalWeight_eq_localWeight`
- `FiniteGroupClass.allFinite_normalSubgroupClosed`
- `setInfinite_of_cardinal_ge_aleph0`
- `17` more local declarations

## Notes
- Status: Complete
-/
section QuotientLocalWeightStatements

section QuotientLocalWeight

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- 6. Quotient local weight at the identity coset.
-/
noncomputable def quotientLocalWeight (H : Subgroup G) : Cardinal :=
  localWeightAt (X := G ⧸ H) ((QuotientGroup.mk : G → G ⧸ H) 1)

@[simp] theorem quotientLocalWeight_eq_localWeight (H : Subgroup G) [H.Normal] :
    quotientLocalWeight (G := G) H = localWeight (G ⧸ H) :=
  rfl

/-- Enlarging the denominator subgroup does not increase quotient local weight. -/
theorem quotientLocalWeight_mono_of_le
    [IsTopologicalGroup G] {H K : Subgroup G} [H.Normal] [K.Normal] (hHK : H ≤ K) :
    quotientLocalWeight (G := G) K ≤ quotientLocalWeight (G := G) H := by
  let f : G ⧸ H → G ⧸ K := QuotientGroup.map H K (MonoidHom.id G) hHK
  have hfcont : Continuous f := by
    have hcomp : Continuous (f ∘ ((↑) : G → G ⧸ H)) := by
      simpa [f, Function.comp] using
        (QuotientGroup.continuous_mk : Continuous ((↑) : G → G ⧸ K))
    exact (QuotientGroup.isOpenQuotientMap_mk (N := H)).continuous_comp_iff.mp hcomp
  have hfopen : IsOpenMap f := by
    intro U hUopen
    have hpreOpen : IsOpen (((↑) : G → G ⧸ H) ⁻¹' U) := by
      exact hUopen.preimage QuotientGroup.continuous_mk
    have himage :
        f '' U = ((↑) : G → G ⧸ K) '' (((↑) : G → G ⧸ H) ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases Quotient.exists_rep x with ⟨g, rfl⟩
        exact ⟨g, hx, by simp only [QuotientGroup.map_mk, MonoidHom.id_apply, f]⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨((↑) : G → G ⧸ H) g, hg, by simp only [QuotientGroup.map_mk, MonoidHom.id_apply, f]⟩
    rw [himage]
    exact QuotientGroup.isOpenMap_coe _ hpreOpen
  simpa [quotientLocalWeight, f] using
    localWeightAt_image_le_of_continuous_open
      (X := G ⧸ H) (Y := G ⧸ K) (f := f) hfcont hfopen

end QuotientLocalWeight

/-- Open subgroups have the same local weight as the ambient topological group. -/
theorem localWeight_openSubgroup_eq
    (G : Type u) [Group G] [TopologicalSpace G]
    (H : OpenSubgroup G) :
    localWeight ↥(H : Subgroup G) = localWeight G := by
  have hle : localWeight ↥(H : Subgroup G) ≤ localWeight G := by
    rcases exists_neighborhoodBasisAt_cardinal_le_of_localWeightAt_le
        (X := G) (x := (1 : G)) (κ := localWeight G) le_rfl with
      ⟨B, hBbasis, hBcard⟩
    let ι : Type u := {U : Set G // U ∈ B}
    let C : Set (Set ↥(H : Subgroup G)) :=
      Set.range fun i : ι => ((↑) : ↥(H : Subgroup G) → G) ⁻¹' i.1
    have hCbasis :
        IsNeighborhoodBasisAt (X := ↥(H : Subgroup G)) (1 : ↥(H : Subgroup G)) C := by
      constructor
      · intro V hV
        rcases hV with ⟨i, rfl⟩
        constructor
        · exact (hBbasis.1 i.1 i.2).1.preimage continuous_subtype_val
        · simpa using (hBbasis.1 i.1 i.2).2
      · intro V hVopen hVone
        rcases isOpen_induced_iff.mp hVopen with ⟨O, hOopen, hOeq⟩
        have hOone : (1 : G) ∈ O := by
          have : (1 : ↥(H : Subgroup G)) ∈ ((↑) : ↥(H : Subgroup G) → G) ⁻¹' O := by
            simpa [hOeq] using hVone
          simpa using this
        have hOHopen : IsOpen (O ∩ (H : Set G)) := hOopen.inter H.isOpen'
        have hOHone : (1 : G) ∈ O ∩ (H : Set G) := by
          exact ⟨hOone, H.one_mem⟩
        rcases hBbasis.2 (O ∩ (H : Set G)) hOHopen hOHone with ⟨U, hUrange, hUsub⟩
        refine ⟨((↑) : ↥(H : Subgroup G) → G) ⁻¹' U, ?_, ?_⟩
        · exact ⟨⟨U, hUrange⟩, rfl⟩
        · intro x hx
          have hx' : (x : G) ∈ O ∩ (H : Set G) := hUsub hx
          rw [← hOeq]
          exact hx'.1
    have hCcard :
        familyCardinal (X := ↥(H : Subgroup G)) C ≤ localWeight G := by
      calc
        familyCardinal (X := ↥(H : Subgroup G)) C ≤ Cardinal.mk ι := by
          unfold familyCardinal C
          exact Cardinal.mk_range_le
        _ = familyCardinal (X := G) B := by rfl
        _ ≤ localWeight G := hBcard
    simpa [localWeight] using
      (localWeightAt_le_familyCardinal_of_basis
        (X := ↥(H : Subgroup G)) (x := (1 : ↥(H : Subgroup G))) hCbasis).trans hCcard
  have hge : localWeight G ≤ localWeight ↥(H : Subgroup G) := by
    simpa [localWeight] using
      (localWeightAt_image_le_of_continuous_open
        (X := ↥(H : Subgroup G)) (Y := G)
        (f := ((↑) : ↥(H : Subgroup G) → G)) (x := (1 : ↥(H : Subgroup G)))
        continuous_subtype_val H.isOpen'.isOpenMap_subtype_val)
  exact le_antisymm hle hge




end QuotientLocalWeightStatements

section FiniteGroupClassHelpers

theorem FiniteGroupClass.allFinite_normalSubgroupClosed :
    FiniteGroupClass.NormalSubgroupClosed FiniteGroupClass.allFinite := by
  intro G _ N _ hfin
  letI : Finite G := by
    simpa [FiniteGroupClass.allFinite] using hfin
  letI : Finite N := Finite.of_injective (fun n : N => (n : G)) (by
    intro n₁ n₂ h
    exact Subtype.ext (show (n₁ : G) = n₂ from h))
  simpa [FiniteGroupClass.allFinite]

theorem setInfinite_of_cardinal_ge_aleph0
    {α : Type u} (X : Set α) (hX : ℵ₀ ≤ Cardinal.mk X) : Set.Infinite X := by
  classical
  by_contra hXfin
  letI : Finite X := Set.not_infinite.mp hXfin
  have hlt : Cardinal.mk X < ℵ₀ :=
    (Cardinal.lt_aleph0_iff_finite (α := X)).2 inferInstance
  exact not_lt_of_ge hX hlt

/-- A profinite group with `w₀(G) ≤ ℵ₀` admits a countable descending open-normal basis at `1`.
-/
theorem hasCountableDescendingOpenNormalChainAtOne_of_localWeight_le_aleph0
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) (hcount : localWeight G ≤ ℵ₀) :
    ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
  classical
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
      (G := G) hG with ⟨ι, W, hWbasis, hWcard⟩
  have hιcount : Countable ι := Cardinal.mk_le_aleph0_iff.mp (hWcard.trans hcount)
  have hιne : Nonempty ι := by
    rcases hWbasis.2 Set.univ isOpen_univ (by simp only [mem_univ]) with ⟨U, hUrange, _hUsub⟩
    rcases hUrange with ⟨i, rfl⟩
    exact ⟨i⟩
  letI : Countable ι := hιcount
  letI : Nonempty ι := hιne
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  let V : ℕ → OpenNormalSubgroup G := fun n => W (e n)
  let U : ℕ → OpenNormalSubgroup G :=
    Nat.rec (V 0) (fun n Un => Un ⊓ V (n + 1))
  let USub : ℕ → Subgroup G := fun n => (U n).toOpenSubgroup.toSubgroup
  have hstep : ∀ n, U (n + 1) ≤ U n := by
    intro n
    simp only [inf_le_left, U]
  have hUanti' : Antitone U := antitone_nat_of_succ_le hstep
  have hUanti : Antitone USub := by
    intro m n hmn x hx
    exact hUanti' hmn hx
  have hUV : ∀ n, U n ≤ V n := by
    intro n
    cases n with
    | zero =>
        exact le_rfl
    | succ n =>
        simp only [inf_le_right, U]
  refine ⟨U, hUanti, ?_⟩
  intro O hOopen h1O
  rcases hWbasis.2 O hOopen h1O with ⟨S, hSrange, hSO⟩
  rcases hSrange with ⟨i, rfl⟩
  rcases he i with ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  intro x hx
  exact hSO (hUV n hx)

section CharacteristicHelpers

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem IsTopologicallyCharacteristic.normal {H : Subgroup G}
    (hH : IsTopologicallyCharacteristic G H) : H.Normal := by
  classical
  refine ⟨?_⟩
  intro x hx g
  let conj : G ≃ₜ* G :=
    ContinuousMulEquiv.mk'
      ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹))
      (by
        intro y z
        simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight, mul_assoc,
  inv_mul_cancel_left])
  have hmem : conj x ∈ H ↔ x ∈ H := by
    exact IsTopologicallyCharacteristic.apply_mem_iff (G := G) (H := H) hH conj (g := x)
  simpa [conj] using hmem.2 hx

end CharacteristicHelpers



/--
Helper criterion: metrizability is equivalent to a countable descending open-normal basis at `1`.
-/
theorem metrizable_iff_hasCountableDescendingOpenNormalChainAtOne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) :
    Nonempty (MetrizableSpace G) ↔ ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
  constructor
  · intro hmetr
    letI : MetrizableSpace G := hmetr.some
    letI : FirstCountableTopology G := inferInstance
    letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
    letI : T2Space G := IsProfiniteGroup.t2Space hG
    letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
    obtain ⟨u, hu, _⟩ := IsTopologicalGroup.exists_antitone_basis_nhds_one (G := G)
    have hV :
        ∀ n, ∃ V : Set G, V ⊆ u n ∧ IsOpen V ∧ (1 : G) ∈ V := by
      intro n
      rcases mem_nhds_iff.mp (hu.mem n) with ⟨V, hVu, hVopen, h1V⟩
      exact ⟨V, hVu, hVopen, h1V⟩
    choose V hVu hVopen h1V using hV
    have hN :
        ∀ n, ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ V n := by
      intro n
      rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) (hVopen n) (h1V n) with
        ⟨N, hNV⟩
      exact ⟨N, hNV⟩
    choose N hNV using hN
    let U : ℕ → OpenNormalSubgroup G :=
      Nat.rec (N 0) (fun n Un => Un ⊓ N (n + 1))
    have hstep : ∀ n, U (n + 1) ≤ U n := by
      intro n
      change U n ⊓ N (n + 1) ≤ U n
      exact inf_le_left
    have hUanti' : Antitone U := antitone_nat_of_succ_le hstep
    have hUanti : Antitone (fun n => (U n).toSubgroup) := by
      intro m n hmn
      exact hUanti' hmn
    have hUN : ∀ n, U n ≤ N n := by
      intro n
      cases n with
      | zero =>
          simp only [Nat.rec_zero, le_refl, U]
      | succ n =>
          change U n ⊓ N (n + 1) ≤ N (n + 1)
          exact inf_le_right
    refine ⟨U, hUanti, ?_⟩
    intro O hOopen h1O
    have hOnhds : O ∈ 𝓝 (1 : G) := IsOpen.mem_nhds hOopen h1O
    rcases hu.mem_iff.1 hOnhds with ⟨n, hnuO⟩
    refine ⟨n, ?_⟩
    intro x hx
    have hxN : x ∈ (N n : Subgroup G) := hUN n hx
    have hxV : x ∈ V n := hNV n hxN
    exact hnuO (hVu n hxV)
  · intro hchain
    letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
    letI : T2Space G := IsProfiniteGroup.t2Space hG
    rcases hchain with ⟨U, _hUanti, hUbasis⟩
    have hnhds :
        (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True)
          (fun n : ℕ => (((U n : Subgroup G) : Set G))) := by
      refine ⟨fun s => ?_⟩
      constructor
      · intro hs
        rcases mem_nhds_iff.mp hs with ⟨V, hVs, hVopen, h1V⟩
        rcases hUbasis V hVopen h1V with ⟨n, hnV⟩
        exact ⟨n, trivial, hnV.trans hVs⟩
      · rintro ⟨n, -, hns⟩
        exact Filter.mem_of_superset
          (IsOpen.mem_nhds (openNormalSubgroup_isOpen (G := G) (U n)) (U n).one_mem') hns
    letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    haveI : (𝓝 (1 : G)).IsCountablyGenerated :=
      Filter.HasCountableBasis.isCountablyGenerated ⟨hnhds, Set.to_countable _⟩
    haveI : IsUniformGroup G := IsUniformGroup.of_compactSpace
    haveI : (uniformity G).IsCountablyGenerated :=
      IsUniformGroup.uniformity_countably_generated (α := G)
    exact ⟨UniformSpace.metrizableSpace (X := G)⟩

/-- Any explicit cardinal bound on `topologicalRank G` yields a generating set converging to `1` of the same
size. This is the direct bridge from the Section 2.5 generator invariant to the Section 2.6
cardinality language. -/
theorem hasGeneratingSetConvergingToOneOfCardinalLE_of_d_le
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) {κ : Cardinal} (hd : topologicalRank G ≤ κ) :
    ∃ X : Set G, GeneratesAndConvergesToOne (G := G) X ∧ Cardinal.mk X ≤ κ := by
  classical
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  let C : Set Cardinal := {κ' : Cardinal |
    ∃ X : Set G, GeneratesAndConvergesToOne (G := G) X ∧ Cardinal.mk X = κ'}
  have hCne : C.Nonempty := by
    rcases exists_generatorsConvergingToOne (G := G) hG with ⟨X, hX⟩
    exact ⟨Cardinal.mk X, X, hX, rfl⟩
  have hdmem : topologicalRank G ∈ C := by
    simpa [topologicalRank, C] using (csInf_mem hCne)
  rcases hdmem with ⟨X, hX, hXcard⟩
  refine ⟨X, hX, ?_⟩
  calc
    Cardinal.mk X = topologicalRank G := hXcard
    _ ≤ κ := hd

/-- Topologically finitely generated profinite groups have a countable descending open-normal
basis at `1`. -/
theorem hasCountableDescendingOpenNormalChainAtOne_of_topologicallyFinitelyGenerated
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hgen : TopologicallyFinitelyGenerated G) :
    ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
  rcases exists_characteristicOpenBasis_of_topologicallyFinitelyGenerated (G := G) hgen with
    ⟨V, _hV0, hVanti, hVopen, hVchar, hVbasis⟩
  refine ⟨
    (fun n =>
      { toOpenSubgroup := ⟨V n, hVopen n⟩
        isNormal' := ProCGroups.LocalWeight.IsTopologicallyCharacteristic.normal
          (G := G) (H := V n) (hH := hVchar n) }),
    ?_,
    ?_⟩
  · intro m n hmn x hx
    exact hVanti hmn hx
  · intro W hW h1W
    exact hVbasis W (IsOpen.mem_nhds hW h1W)

end FiniteGroupClassHelpers


end LocalWeight
