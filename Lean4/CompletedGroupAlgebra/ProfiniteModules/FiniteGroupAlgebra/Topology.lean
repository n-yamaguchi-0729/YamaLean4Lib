import CompletedGroupAlgebra.ProfiniteModules.Basic.OpenIdeals
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/ProfiniteModules/FiniteGroupAlgebra/Topology.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite group algebra topology and free-module structure

This module equips finite group algebras with the finite product topology and records the coordinate continuity used for continuous-linear extension arguments.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v w z

/-- A completed-group-algebra model consists of a profinite coefficient ring, a profinite group,
a profinite topological ring carrier, and a dense algebraic group-algebra map from a chosen
topology on `R[G]`. -/
structure IsCompletedGroupAlgebraModel (R : Type u) (G : Type v) (RG : Type w)
    [CommRing R] [TopologicalSpace R] [Group G] [TopologicalSpace G] [Ring RG]
    [TopologicalSpace RG] : Prop where
  (coefficient_isProfiniteRing : IsProfiniteRing R)
  (group_isProfiniteGroup : IsProfiniteGroup G)
  (carrier_isProfiniteRing : IsProfiniteRing RG)
  (dense_algebraicMap :
    ∃ τ : TopologicalSpace (MonoidAlgebra R G),
      letI := τ
      ∃ dense : MonoidAlgebra R G →+* RG, DenseRange dense ∧ Continuous dense)

/-- The product topology on the group algebra of a finite group, transported through
`R[G] = G →₀ R ≃ G → R`. This is the finite stage used in the construction of the completed
group algebra. -/
noncomputable def finiteGroupAlgebraTopology
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R] :
    TopologicalSpace (MonoidAlgebra R G) :=
  TopologicalSpace.induced (Finsupp.equivFunOnFinite : MonoidAlgebra R G ≃ (G → R))
    inferInstance

/-- The finite group algebra with its transported product topology is homeomorphic to `G → R`. -/
noncomputable def finiteGroupAlgebraHomeomorph
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G ≃ₜ (G → R) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) := Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : MonoidAlgebra R G → G → R) :=
    Topology.IsInducing.induced e
  exact e.toHomeomorphOfIsInducing he

/-- The finite-stage group algebra is the finite product of copies of the coefficient ring as a
topological `R`-module. -/
noncomputable def finiteGroupAlgebraContinuousLinearEquivPi
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G ≃L[R] (G → R) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) := Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : MonoidAlgebra R G → G → R) :=
    Topology.IsInducing.induced e
  exact ContinuousLinearEquiv.mk
    (Finsupp.linearEquivFunOnFinite R R G)
    (by
      change Continuous (e : MonoidAlgebra R G → G → R)
      exact he.continuous)
    (by
      change Continuous ((e.toHomeomorphOfIsInducing he).symm : (G → R) → MonoidAlgebra R G)
      exact (e.toHomeomorphOfIsInducing he).symm.continuous)

@[simp]
theorem finiteGroupAlgebraContinuousLinearEquivPi_apply
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    (x : MonoidAlgebra R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    finiteGroupAlgebraContinuousLinearEquivPi R G x = Finsupp.equivFunOnFinite x :=
  rfl

/-- Coordinate evaluation on a finite group algebra is continuous for the transported product
topology. -/
theorem finiteGroupAlgebra_coordinate_continuous
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ∀ g : G, Continuous fun x : MonoidAlgebra R G => x g := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) := Finsupp.equivFunOnFinite
  intro g
  simpa [e] using
    (continuous_apply g).comp (continuous_induced_dom : Continuous (e : MonoidAlgebra R G → G → R))

/-- Addition is continuous for the finite-stage group algebra topology. -/
theorem finiteGroupAlgebra_continuousAdd
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousAdd (MonoidAlgebra R G) := by
  classical
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) := Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun p : A × A => (p.1 + p.2) g
  simpa using ((hcoord g).comp continuous_fst).add ((hcoord g).comp continuous_snd)

/-- Negation is continuous for the finite-stage group algebra topology. -/
theorem finiteGroupAlgebra_continuousNeg
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousNeg (MonoidAlgebra R G) := by
  classical
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) := Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun x : A => (-x) g
  simpa using (hcoord g).neg

/-- Multiplication is continuous for the finite-stage group algebra topology. The coordinate
formula is the finite convolution sum over pairs `(g₁,g₂)` with `g₁*g₂ = g`. -/
theorem finiteGroupAlgebra_continuousMul
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousMul (MonoidAlgebra R G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) := Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun p : A × A => (p.1 * p.2) g
  rw [show (fun p : A × A => (p.1 * p.2) g) =
      (fun p : A × A => ∑ q ∈ (Finset.univ.filter (fun q : G × G => q.1 * q.2 = g)),
        p.1 q.1 * p.2 q.2) from ?_]
  · apply continuous_finset_sum
    intro q _hq
    exact ((hcoord q.1).comp continuous_fst).mul ((hcoord q.2).comp continuous_snd)
  · funext p
    exact MonoidAlgebra.mul_apply_antidiagonal p.1 p.2 g
      (Finset.univ.filter (fun q : G × G => q.1 * q.2 = g)) (by intro q; simp only [Finset.mem_filter, Finset.mem_univ, true_and])

/-- Scalar multiplication by the coefficient ring is continuous on the finite-stage group
algebra topology. -/
theorem finiteGroupAlgebra_continuousSMul
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousSMul R (MonoidAlgebra R G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) := Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ContinuousSMul.mk ?_
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun p : R × A => p.1 * p.2 g
  exact continuous_fst.mul ((hcoord g).comp continuous_snd)

/-- The finite-stage group algebra topology makes `R[G]` a topological ring. -/
theorem finiteGroupAlgebra_isTopologicalRing
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    IsTopologicalRing (MonoidAlgebra R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  letI : ContinuousAdd (MonoidAlgebra R G) := finiteGroupAlgebra_continuousAdd R G
  letI : ContinuousMul (MonoidAlgebra R G) := finiteGroupAlgebra_continuousMul R G
  letI : ContinuousNeg (MonoidAlgebra R G) := finiteGroupAlgebra_continuousNeg R G
  letI : IsTopologicalSemiring (MonoidAlgebra R G) := IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

/-- The finite-stage group algebra of a profinite coefficient ring over a finite group is
profinite. -/
theorem finiteGroupAlgebra_isProfiniteRing
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    (hR : IsProfiniteRing R) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    IsProfiniteRing (MonoidAlgebra R G) := by
  letI : IsTopologicalRing R := hR.1
  letI : CompactSpace R := hR.2.1
  letI : T2Space R := hR.2.2.1
  letI : TotallyDisconnectedSpace R := hR.2.2.2
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e := finiteGroupAlgebraHomeomorph R G
  letI : IsTopologicalRing (MonoidAlgebra R G) := finiteGroupAlgebra_isTopologicalRing R G
  letI : CompactSpace (MonoidAlgebra R G) := Homeomorph.compactSpace e.symm
  letI : T2Space (MonoidAlgebra R G) := Homeomorph.t2Space e.symm
  letI : TotallyDisconnectedSpace (MonoidAlgebra R G) :=
    Homeomorph.totallyDisconnectedSpace e.symm
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The finite-stage group algebra of a profinite coefficient ring over a finite group is a
profinite module over the coefficient ring. -/
theorem finiteGroupAlgebra_isProfiniteModule
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    (hR : IsProfiniteRing R) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    IsProfiniteModule R (MonoidAlgebra R G) := by
  letI : IsTopologicalRing R := hR.1
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  letI : IsTopologicalRing (MonoidAlgebra R G) := finiteGroupAlgebra_isTopologicalRing R G
  letI : IsTopologicalAddGroup (MonoidAlgebra R G) := inferInstance
  letI : ContinuousSMul R (MonoidAlgebra R G) := finiteGroupAlgebra_continuousSMul R G
  have hA : IsProfiniteRing (MonoidAlgebra R G) := finiteGroupAlgebra_isProfiniteRing R G hR
  exact ⟨hR, inferInstance, inferInstance, hA.2.1, hA.2.2.1, hA.2.2.2⟩

private noncomputable def finiteGroupAlgebraPiLift
    (R : Type u) (G : Type v) (N : Type w)
    [Ring R] [TopologicalSpace R] [Fintype G]
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N] [ContinuousSMul R N]
    (f : G -> N) : (G -> R) →L[R] N where
  toLinearMap :=
    { toFun := fun m => ∑ x : G, m x • f x
      map_add' := by
        intro m n
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro lam m
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]}
  cont := by
    apply continuous_finset_sum
    intro x _hx
    exact (continuous_apply x).smul continuous_const

private theorem finiteGroupAlgebraPiLift_apply_basis
    (R : Type u) (G : Type v) (N : Type w)
    [Ring R] [TopologicalSpace R] [Fintype G] [DecidableEq G]
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N] [ContinuousSMul R N]
    (f : G -> N) (g : G) :
    finiteGroupAlgebraPiLift R G N f (Pi.single g (1 : R)) = f g := by
  simp only [finiteGroupAlgebraPiLift, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
  Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The continuous linear map out of a finite group algebra determined by the values on group
elements. -/
noncomputable def finiteGroupAlgebraLift
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Group G] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : G → N) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G →L[R] N := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  letI : TopologicalSpace (G →₀ R) := finiteGroupAlgebraTopology R G
  exact
    { toLinearMap :=
        (finiteGroupAlgebraPiLift R G N f).toLinearMap.comp
          (Finsupp.linearEquivFunOnFinite R R G).toLinearMap
      cont :=
        by
          have hcont :
              Continuous
                ((Finsupp.linearEquivFunOnFinite R R G) :
                  MonoidAlgebra R G → G → R) := by
            let e := finiteGroupAlgebraHomeomorph R G
            change Continuous ((e : MonoidAlgebra R G ≃ₜ (G → R)) :
              MonoidAlgebra R G → G → R)
            exact e.continuous
          exact (finiteGroupAlgebraPiLift R G N f).continuous.comp hcont }

/-- The finite group-algebra lift sends the group-like basis vector at `g` to `f g`. -/
@[simp]
theorem finiteGroupAlgebraLift_apply_of
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Group G] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : G → N) (g : G) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    finiteGroupAlgebraLift R G N f (MonoidAlgebra.of R G g) = f g := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  change finiteGroupAlgebraPiLift R G N f
      ((Finsupp.linearEquivFunOnFinite R R G) (Finsupp.single g (1 : R))) =
    f g
  rw [Finsupp.linearEquivFunOnFinite_single]
  exact finiteGroupAlgebraPiLift_apply_basis R G N f g

/-- Finite-stage group algebras are the free profinite modules on the underlying finite
discrete group. -/
theorem finiteGroupAlgebra_freeProfiniteModuleOn
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [Finite G] [DiscreteTopology G] (hR : IsProfiniteRing R) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    IsFreeProfiniteModuleOn R G (MonoidAlgebra R G) (MonoidAlgebra.of R G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  have hM : IsProfiniteModule R (MonoidAlgebra R G) :=
    finiteGroupAlgebra_isProfiniteModule R G hR
  refine ⟨hR, hM, continuous_of_discreteTopology, ?_, ?_⟩
  · rw [Set.eq_univ_iff_forall]
    intro m
    apply subset_closure
    change m ∈ Submodule.span R (Set.range (MonoidAlgebra.of R G))
    have hm : m = ∑ g : G, (m g) • MonoidAlgebra.of R G g := by
      have hm_single : m = ∑ g : G, MonoidAlgebra.single g (m g) := by
        have hsum : m.sum MonoidAlgebra.single = m := MonoidAlgebra.sum_single m
        have hfin :
            m.sum MonoidAlgebra.single = ∑ g : G, MonoidAlgebra.single g (m g) :=
          Finsupp.sum_fintype m (fun g r => MonoidAlgebra.single g r) (by intro g; simp only [Finsupp.single_zero])
        exact hsum.symm.trans hfin
      simpa [MonoidAlgebra.of] using hm_single
    rw [hm]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ (m g)
      (Submodule.subset_span ⟨g, rfl⟩)
  · intro N _addN _topN _modN hN f _hf
    letI : IsTopologicalAddGroup N := hN.2.1
    letI : ContinuousAdd N := inferInstance
    letI : ContinuousSMul R N := hN.2.2.1
    let F : MonoidAlgebra R G →L[R] N := finiteGroupAlgebraLift R G N f
    refine ⟨F, ?_, ?_⟩
    · intro g
      exact finiteGroupAlgebraLift_apply_of R G N f g
    · intro H hH
      ext m
      let s : MonoidAlgebra R G := ∑ g : G, (m g) • MonoidAlgebra.of R G g
      have hm : m = s := by
        have hm_single : m = ∑ g : G, MonoidAlgebra.single g (m g) := by
          have hsum : m.sum MonoidAlgebra.single = m := MonoidAlgebra.sum_single m
          have hfin :
              m.sum MonoidAlgebra.single = ∑ g : G, MonoidAlgebra.single g (m g) :=
            Finsupp.sum_fintype m (fun g r => MonoidAlgebra.single g r) (by intro g; simp only [Finsupp.single_zero])
          exact hsum.symm.trans hfin
        simpa [s, MonoidAlgebra.of] using hm_single
      rw [hm]
      calc
        H s = ∑ g : G, (m g) • H (MonoidAlgebra.of R G g) := by
          change H (∑ g : G, (m g) • MonoidAlgebra.of R G g) =
            ∑ g : G, (m g) • H (MonoidAlgebra.of R G g)
          simp only [map_sum, map_smul]
        _ = ∑ g : G, (m g) • f g := by
          apply Finset.sum_congr rfl
          intro g _hg
          rw [hH]
        _ = F s := by
          symm
          calc
            F s = ∑ g : G, (m g) • F (MonoidAlgebra.of R G g) := by
              change F (∑ g : G, (m g) • MonoidAlgebra.of R G g) =
                ∑ g : G, (m g) • F (MonoidAlgebra.of R G g)
              simp only [map_sum, map_smul]
            _ = ∑ g : G, (m g) • f g := by
              apply Finset.sum_congr rfl
              intro g _hg
              have hFg : F (MonoidAlgebra.of R G g) = f g := by
                simpa [F] using finiteGroupAlgebraLift_apply_of R G N f g
              rw [hFg]

end CompletedGroupAlgebra
