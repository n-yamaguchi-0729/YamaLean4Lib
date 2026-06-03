import ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import ProCGroups.ProC.GroupPredicates.Abelian

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FiniteStepSolvableQuotients/Commutators/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-step solvable quotients

Develops topological derived series, maximal solvable quotients of bounded derived length, commutator closure formulas, and abelian-action consequences.
-/

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

universe u

/-- The topological closure of the abstract commutator subgroup. -/
abbrev topologicalCommutator
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : Subgroup G :=
  (commutator G).topologicalClosure

@[simp] theorem topologicalCommutator_eq_closedCommutator_top_top
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    topologicalCommutator G = closedCommutator (⊤ : Subgroup G) ⊤ := by
  simp only [topologicalCommutator, commutator, closedCommutator]

@[simp] theorem topDerivedTop_one_eq_topologicalCommutator
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    topDerivedTop G 1 = topologicalCommutator G := by
  simp only [topDerivedTop, closedDerivedSeries, closedCommutator, topologicalCommutator, commutator]

/-- The first closed derived subgroup of the whole group is the closed commutator subgroup. -/
theorem closedDerivedSeries_top_one_eq_closedCommutator
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    closedDerivedSeries (G := G) (⊤ : Subgroup G) 1 =
      Subgroup.closedCommutator G := by
  calc
    closedDerivedSeries (G := G) (⊤ : Subgroup G) 1 = topDerivedTop G 1 := rfl
    _ = topologicalCommutator G := topDerivedTop_one_eq_topologicalCommutator G
    _ = Subgroup.closedCommutator G := rfl

@[simp] theorem topologicalCommutator_eq_commutator_of_isClosed
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hclosed : IsClosed ((commutator G : Subgroup G) : Set G)) :
    topologicalCommutator G = commutator G := by
  ext x
  change x ∈ closure ((commutator G : Set G)) ↔ x ∈ (commutator G : Set G)
  rw [closure_eq_iff_isClosed.mpr hclosed]

/-- In a compact Hausdorff topological group, the set of individual commutators is closed. -/
theorem isClosed_commutatorSet
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] :
    IsClosed (commutatorSet G : Set G) := by
  let f : G × G → G := fun p => ⁅p.1, p.2⁆
  have hf : Continuous f := by
    have hfst : Continuous fun p : G × G => p.1 := continuous_fst
    have hsnd : Continuous fun p : G × G => p.2 := continuous_snd
    simpa [f, commutatorElement_def, mul_assoc] using
      (((hfst.mul hsnd).mul hfst.inv).mul hsnd.inv)
  have himage : f '' (Set.univ : Set (G × G)) = commutatorSet G := by
    ext z
    constructor
    · rintro ⟨p, -, rfl⟩
      exact commutator_mem_commutatorSet (g₁ := p.1) (g₂ := p.2)
    · intro hz
      rcases mem_commutatorSet_iff.mp hz with ⟨x, y, rfl⟩
      exact ⟨(x, y), by simp only [Set.mem_univ], rfl⟩
  simpa [himage] using (isCompact_univ.image hf).isClosed

theorem commutator_subset_topologicalCommutator
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    commutator G ≤ topologicalCommutator G :=
  Subgroup.le_topologicalClosure _

@[simp] theorem topologicalCommutator_eq_bot_of_commGroup
    (G : Type u) [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T1Space G] :
    topologicalCommutator G = ⊥ := by
  have hcomm : commutator G = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, CommGroup.center_eq_top]
  rw [topologicalCommutator, hcomm]
  ext x
  change x ∈ closure ({(1 : G)} : Set G) ↔ x ∈ (⊥ : Subgroup G)
  rw [closure_singleton]
  simp only [Set.mem_singleton_iff, Subgroup.mem_bot]

/-- A commutative topological group has trivial positive closed derived stages. -/
theorem topDerivedTop_eq_bot_of_commGroup
    {G : Type u} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T1Space G]
    {m : ℕ} (hm : 1 ≤ m) :
    topDerivedTop G m = ⊥ := by
  have h1 : topDerivedTop G 1 = (⊥ : Subgroup G) := by
    rw [topDerivedTop_one_eq_topologicalCommutator]
    exact topologicalCommutator_eq_bot_of_commGroup G
  have hle : topDerivedTop G m ≤ topDerivedTop G 1 :=
    (topDerivedTop_antitone (G := G)) hm
  have hlebot : topDerivedTop G m ≤ (⊥ : Subgroup G) := by
    rw [← h1]
    exact hle
  exact le_antisymm hlebot bot_le

/-- A procyclic group has trivial positive closed derived stages. -/
theorem topDerivedTop_eq_bot_of_procyclic
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hG : ProCGroups.ProC.IsProcyclicGroup G) {m : ℕ} (hm : 1 ≤ m) :
    topDerivedTop G m = ⊥ := by
  letI : T2Space G := hG.t2Space
  have hcomm : ∀ a b : G, a * b = b * a :=
    ProCGroups.ProC.IsProabelianGroup.isAbelian (G := G)
      (ProCGroups.ProC.IsProcyclicGroup.isProabelianGroup (G := G) hG)
  let base : Group G := inferInstance
  letI : CommGroup G := { base with mul_comm := hcomm }
  exact topDerivedTop_eq_bot_of_commGroup hm

/-- Images of a topologically cyclic source in a discrete quotient of a maximal solvable quotient
are algebraic powers of the image of the chosen generator. -/
theorem maxSolvQuot_leftFactor_image_mem_zpowers
    {Ω A B : Type u}
    [TopologicalSpace Ω] [Group Ω] [IsTopologicalGroup Ω]
    [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
    [TopologicalSpace B] [Group B] [IsTopologicalGroup B] [DiscreteTopology B]
    {m : ℕ}
    (q : MaxSolvQuot Ω m →* B) (hq : Continuous q)
    (ιC : A →ₜ* Ω) {x a : A}
    (hxgen : ProCGroups.Generation.TopologicallyGenerates (G := A) ({x} : Set A)) :
    q (continuousToMaxSolvQuot Ω m (ιC a)) ∈
      Subgroup.zpowers (q (continuousToMaxSolvQuot Ω m (ιC x))) := by
  let f : A →* B := (q.comp (continuousToMaxSolvQuot Ω m : Ω →* MaxSolvQuot Ω m)).comp ιC
  have hf : Continuous f := by
    exact hq.comp ((continuousToMaxSolvQuot Ω m).continuous_toFun.comp ιC.continuous_toFun)
  simpa [f] using
    ProCGroups.Generation.monoidHom_map_mem_zpowers_of_topologicallyGenerates_singleton
      (A := A) f hf hxgen (a := a)

/-- `g` can be written as a product of at most `n` commutators. -/
def IsProductOfCommutatorsLE
    {G : Type u} [Group G] (n : ℕ) (g : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ n ∧ (l.map fun p => ⁅p.1, p.2⁆).prod = g

theorem isProductOfCommutatorsLE_one
    {G : Type u} [Group G] (n : ℕ) :
    IsProductOfCommutatorsLE n (1 : G) := by
  refine ⟨[], Nat.zero_le _, ?_⟩
  simp only [List.map_nil, List.prod_nil]

theorem isProductOfCommutatorsLE_commutatorElement
    {G : Type u} [Group G] (x y : G) :
    IsProductOfCommutatorsLE 1 ⁅x, y⁆ := by
  refine ⟨[(x, y)], by simp only [List.length_cons, List.length_nil, zero_add, le_refl], ?_⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem IsProductOfCommutatorsLE.mul
    {G : Type u} [Group G]
    {m n : ℕ} {g h : G}
    (hg : IsProductOfCommutatorsLE m g)
    (hh : IsProductOfCommutatorsLE n h) :
    IsProductOfCommutatorsLE (m + n) (g * h) := by
  rcases hg with ⟨lg, hlg, rfl⟩
  rcases hh with ⟨lh, hlh, rfl⟩
  refine ⟨lg ++ lh, by simpa using Nat.add_le_add hlg hlh, ?_⟩
  simp only [List.map_append, List.prod_append]

/-- A product of at most `m` commutators is also a product of at most any larger bound `n`. -/
theorem IsProductOfCommutatorsLE.mono
    {G : Type u} [Group G]
    {m n : ℕ} {g : G}
    (hg : IsProductOfCommutatorsLE m g)
    (hmn : m ≤ n) :
    IsProductOfCommutatorsLE n g := by
  rcases hg with ⟨l, hl, hprod⟩
  exact ⟨l, le_trans hl hmn, hprod⟩

theorem mem_commutator_of_isProductOfCommutatorsLE
    {G : Type u} [Group G]
    {n : ℕ} {g : G}
    (hg : IsProductOfCommutatorsLE n g) :
    g ∈ commutator G := by
  rcases hg with ⟨l, -, rfl⟩
  induction l with
  | nil =>
      simp only [commutator, List.map_nil, List.prod_nil, one_mem]
  | cons a t ih =>
      have ha : ⁅a.1, a.2⁆ ∈ commutator G := by
        rw [commutator_eq_closure]
        exact Subgroup.subset_closure (commutator_mem_commutatorSet (g₁ := a.1) (g₂ := a.2))
      exact Subgroup.mul_mem _ ha ih

end ProCGroups.FiniteStepSolvableQuotients
