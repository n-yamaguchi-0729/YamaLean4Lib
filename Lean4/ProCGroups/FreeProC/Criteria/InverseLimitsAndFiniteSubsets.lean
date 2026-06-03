import ProCGroups.FreeProC.Basic
import ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Criteria/InverseLimitsAndFiniteSubsets.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite
quotient characterizations, and standard comparison isomorphisms.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u v

section InverseLimitsAndFiniteSubsets

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {I : Type u} [Preorder I]

/-- A bundled inverse system of topological groups. -/
structure TopologicalGroupInverseSystemData where
  toInverseSystem : ProCGroups.InverseSystems.InverseSystem (I := I)
  group : ∀ i, Group (toInverseSystem.X i)
  isGroupSystem : ProCGroups.InverseSystems.IsGroupSystem toInverseSystem
  isTopologicalGroup : ∀ i, IsTopologicalGroup (toInverseSystem.X i)
  inverseLimit_isTopologicalGroup :
    letI : ∀ i, Group (toInverseSystem.X i) := group
    letI : ProCGroups.InverseSystems.IsGroupSystem toInverseSystem := isGroupSystem
    letI : ∀ i, IsTopologicalGroup (toInverseSystem.X i) := isTopologicalGroup
    IsTopologicalGroup toInverseSystem.inverseLimit

attribute [instance] TopologicalGroupInverseSystemData.group
attribute [instance] TopologicalGroupInverseSystemData.isGroupSystem
attribute [instance] TopologicalGroupInverseSystemData.isTopologicalGroup

instance instInverseLimitIsTopologicalGroupTopologicalGroupInverseSystemData
    (S : TopologicalGroupInverseSystemData (I := I)) :
    IsTopologicalGroup S.toInverseSystem.inverseLimit := by
  simpa using S.inverseLimit_isTopologicalGroup

/-- A pointed inverse system of profinite spaces. -/
structure PointedProfiniteInverseSystem where
  I : Type u
  instPreorder : Preorder I
  system : ProCGroups.InverseSystems.InverseSystem.{u, u} (I := I)
  point : ∀ i, system.X i
  map_point : ∀ {i j : I} (hij : i ≤ j), system.map hij (point j) = point i
  profinite_stage : ∀ i, ProCGroups.InverseSystems.IsProfiniteSpace (system.X i)

attribute [instance] PointedProfiniteInverseSystem.instPreorder

namespace PointedProfiniteInverseSystem

/-- The compatible basepoint in the inverse limit of a pointed profinite system. -/
def limitPoint (S : PointedProfiniteInverseSystem) : S.system.inverseLimit :=
  ⟨fun i => S.point i, fun _i _j hij => S.map_point hij⟩

end PointedProfiniteInverseSystem

/-- A presentation of a pointed profinite space as an inverse limit of pointed profinite spaces. -/
structure PointedProfinitePresentation
    (X : Type u) [TopologicalSpace X] (x0 : X) where
  inverseSystem : PointedProfiniteInverseSystem
  homeomorph : X ≃ₜ inverseSystem.system.inverseLimit
  map_base : homeomorph x0 = inverseSystem.limitPoint

/-- The type of finite subsets of `X`, encoded without any decidable-equality assumption. -/
abbrev FiniteSubset (X : Type u) := {Y : Set X // Y.Finite}

/-- A continuous homomorphism from a profinite group onto a profinite target is surjective once
its range contains a topological generating family of the target. -/
theorem surjective_of_rangeContainsGeneratingSet
    {α : Type u}
    {G : Type u} [Group G] [TopologicalSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hGprof : IsProfiniteGroup G)
    (hHprof : IsProfiniteGroup H)
    {ι : α → H}
    (hgen : Generation.TopologicallyGenerates (G := H) (Set.range ι))
    {σ : G →* H} (hσ : Continuous σ)
    (hsub : Set.range ι ⊆ (σ.range : Set H)) :
    Function.Surjective σ := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hGprof
  letI : T2Space H := IsProfiniteGroup.t2Space hHprof
  have hσgen : Generation.TopologicallyGenerates (G := H) ((σ.range : Set H)) :=
    Generation.topologicallyGenerates_mono (G := H) hgen hsub
  have hσclosed : IsClosed ((σ.range : Set H)) := by
    simpa using (isCompact_range hσ).isClosed
  have hσclosure_le : (σ.range : Subgroup H).topologicalClosure ≤ σ.range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
  have hσclosure_top : (σ.range : Subgroup H).topologicalClosure = ⊤ := by
    have htop :
        (Subgroup.closure (σ.range : Set H)).topologicalClosure = (⊤ : Subgroup H) := by
      simpa [Generation.TopologicallyGenerates] using hσgen
    have hclosure_eq : (σ.range : Subgroup H) = Subgroup.closure (σ.range : Set H) := by
      simpa using (Subgroup.closure_eq (σ.range)).symm
    rw [hclosure_eq]
    exact htop
  have hσrange_top : σ.range = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z ∈ ((σ.range : Subgroup H).topologicalClosure : Set H) := by
      rw [hσclosure_top]
      simp only [Subgroup.coe_top, mem_univ]
    exact hσclosure_le hz'
  intro z
  have hz : z ∈ (σ.range : Set H) := by
    simp only [hσrange_top, Subgroup.coe_top, mem_univ]
  simpa using hz

/-- The kernel in a split exact sequence is the smallest closed normal subgroup containing
a specified set. -/
def IsSmallestClosedNormalSubgroupContaining
    {G : Type u} [Group G] [TopologicalSpace G]
    (A : Set G) (N : Subgroup G) : Prop :=
  N.Normal ∧
    IsClosed ((N : Set G)) ∧
    A ⊆ (N : Set G) ∧
    ∀ M : Subgroup G, M.Normal → IsClosed ((M : Set G)) → A ⊆ (M : Set G) → N ≤ M

/-- Pointed free pro-`C` groups on pointed profinite spaces preserve inverse-limit
presentations by transporting the pointed free structure across the presenting homeomorphism. -/
theorem pointedFreeProCGroup_preserves_inverseLimits
    {X : Type u} [TopologicalSpace X] {x0 : X}
    (P : PointedProfinitePresentation X x0)
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι) :
    ∃ ιlim : P.inverseSystem.system.inverseLimit → F,
      Continuous ιlim ∧
        ιlim P.inverseSystem.limitPoint = 1 ∧
        (∀ x, ιlim (P.homeomorph x) = ι x) ∧
        IsPointedFreeProCGroupOn (ProC := ProC)
          P.inverseSystem.system.inverseLimit P.inverseSystem.limitPoint F ιlim := by
  let ιlim : P.inverseSystem.system.inverseLimit → F := ι ∘ P.homeomorph.symm
  have hιlim : Continuous ιlim :=
    hι.continuous_ι.comp P.homeomorph.symm.continuous_toFun
  have hsymm_base : P.homeomorph.symm P.inverseSystem.limitPoint = x0 := by
    simpa [P.map_base] using P.homeomorph.left_inv x0
  refine ⟨ιlim, hιlim, ?_, ?_, ?_⟩
  · simpa [ιlim, hsymm_base] using hι.map_base
  · intro x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply, ιlim]
  · refine ⟨hι.isProC, hιlim, ?_, ?_, ?_⟩
    · simpa [ιlim, hsymm_base] using hι.map_base
    · have hsub : Set.range ι ⊆ Set.range ιlim := by
        rintro z ⟨x, rfl⟩
        exact ⟨P.homeomorph x, by simp only [Function.comp_apply, Homeomorph.symm_apply_apply, ιlim]⟩
      exact Generation.topologicallyGenerates_mono (G := F) hι.generates_range hsub
    · intro G _ _ _ hG φ hφ hφ0 hgen
      let ψ : X → G := φ ∘ P.homeomorph
      have hψ : Continuous ψ := hφ.comp P.homeomorph.continuous_toFun
      have hψ0 : ψ x0 = 1 := by
        simpa [ψ, Function.comp, P.map_base] using hφ0
      have hψgen : Generation.TopologicallyGenerates (G := G) (Set.range ψ) := by
        have hrange : Set.range ψ = Set.range φ := by
          ext z
          constructor
          · rintro ⟨x, rfl⟩
            exact ⟨P.homeomorph x, rfl⟩
          · rintro ⟨y, rfl⟩
            exact ⟨P.homeomorph.symm y, by simp only [Function.comp_apply, Homeomorph.apply_symm_apply, ψ]⟩
        simpa [hrange] using hgen
      rcases hι.existsUnique_lift hG ψ hψ hψ0 hψgen with ⟨f, hf, huniq⟩
      refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
      · intro y
        rcases P.homeomorph.surjective y with ⟨x, rfl⟩
        simpa [ιlim, ψ, Function.comp] using hf.2 x
      · intro g hg
        apply huniq g
        refine ⟨hg.1, ?_⟩
        intro x
        simpa [ψ, ιlim, Function.comp] using hg.2 (P.homeomorph x)

/-- Every pointed profinite space has a finite inverse-limit presentation. -/
theorem exists_pointedProfinitePresentation_of_isProfiniteSpace
    {X : Type u} [TopologicalSpace X] (hX : ProCGroups.InverseSystems.IsProfiniteSpace X)
    (x0 : X) :
    ∃ P : PointedProfinitePresentation.{u, u} X x0,
      ∀ i : P.inverseSystem.I, Finite (P.inverseSystem.system.X i) := by
  letI : CompactSpace X := hX.1
  letI : T2Space X := hX.2.1
  letI : TotallyDisconnectedSpace X := hX.2.2
  let S := ProCGroups.InverseSystems.discreteQuotientSystem X
  let Psys : PointedProfiniteInverseSystem := {
    I := OrderDual (DiscreteQuotient X)
    instPreorder := inferInstance
    system := S
    point := fun Q => (show DiscreteQuotient X from Q).proj x0
    map_point := by
      intro Q R hQR
      exact DiscreteQuotient.ofLE_proj hQR x0
    profinite_stage := by
      intro Q
      change ProCGroups.InverseSystems.IsProfiniteSpace
        (Quotient (show DiscreteQuotient X from Q).toSetoid)
      letI : Fintype (Quotient (show DiscreteQuotient X from Q).toSetoid) := by
        have : Finite (show DiscreteQuotient X from Q) := inferInstance
        exact Fintype.ofFinite _
      exact
        ProCGroups.InverseSystems.isProfiniteSpace_of_compact_t2_totallyDisconnected
          (Quotient (show DiscreteQuotient X from Q).toSetoid)
  }
  let e : X ≃ₜ Psys.system.inverseLimit :=
    ProCGroups.InverseSystems.homeomorph_inverseLimit_discreteQuotientSystem X
  let P : PointedProfinitePresentation.{u, u} X x0 := {
    inverseSystem := Psys
    homeomorph := e
    map_base := by
      ext Q
      rfl
  }
  refine ⟨P, ?_⟩
  intro Q
  change Finite (Quotient (show DiscreteQuotient X from Q).toSetoid)
  infer_instance

/-- Every pointed profinite space admits a finite inverse-limit presentation, and a pointed
free pro-`C` group on it transports to the inverse-limit space. -/
theorem pointedFreeProCGroup_has_finite_inverseLimitPresentation
    {X : Type u} [TopologicalSpace X] {x0 : X}
    (hX : ProCGroups.InverseSystems.IsProfiniteSpace X)
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hι : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι) :
    ∃ P : PointedProfinitePresentation.{u, u} X x0,
      (∀ i : P.inverseSystem.I, Finite (P.inverseSystem.system.X i)) ∧
        ∃ ιlim : P.inverseSystem.system.inverseLimit → F,
          Continuous ιlim ∧
            ιlim P.inverseSystem.limitPoint = 1 ∧
            IsPointedFreeProCGroupOn (ProC := ProC)
              P.inverseSystem.system.inverseLimit P.inverseSystem.limitPoint F ιlim := by
  rcases exists_pointedProfinitePresentation_of_isProfiniteSpace hX x0 with ⟨P, hfinite⟩
  rcases pointedFreeProCGroup_preserves_inverseLimits (ProC := ProC) P hι with
    ⟨ιlim, hιlim, hbase, _hfac, hfree⟩
  exact ⟨P, hfinite, ιlim, hιlim, hbase, hfree⟩

/-- Raw finite-subset inverse-system construction for a free pro-`C` group on a basis converging
to `1`.  The result is intentionally unbundled; `FiniteSubsetSystem` in
`ProCGroups.FreeProC.FinitelyGenerated` packages this data for ordinary use. -/
theorem exists_finiteSubsetSystem_raw
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hProfinite :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _ →
          InverseSystems.IsProfiniteSpace G)
    (hClosed :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (H : Subgroup G), IsClosed (H : Set G) →
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC H _ _ _)
    (hFiniteQuot :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (U : OpenNormalSubgroup G),
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC (G ⧸ (U : Subgroup G)) _ _ _)
    (hF : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι) :
    ∃ S : TopologicalGroupInverseSystemData (I := FiniteSubset X),
      ∃ basis : ∀ s : FiniteSubset X, ↥s.1 → S.toInverseSystem.X s,
        (∀ s : FiniteSubset X,
          IsFreeProCGroupOnConvergingSet (ProC := ProC)
            ↥s.1 (S.toInverseSystem.X s) (basis s)) ∧
        (∀ {s t : FiniteSubset X} (hst : s ≤ t) (x : ↥t.1),
          S.toInverseSystem.map hst (basis t x) =
            by
              classical
              exact if hx : x.1 ∈ s.1 then basis s ⟨x.1, hx⟩ else 1) ∧
        (∀ s : FiniteSubset X,
          ∃ e : S.toInverseSystem.X s →* F,
            Continuous e ∧
              Function.Injective e ∧
              IsClosed (Set.range e) ∧
              ∀ x : ↥s.1, e (basis s x) = ι x.1) ∧
        Nonempty (F ≃ₜ* S.toInverseSystem.inverseLimit) := by
  classical
  let hFspace : InverseSystems.IsProfiniteSpace F := hProfinite hF.isProC
  let hFprof :
      IsProfiniteGroup F :=
    IsProfiniteGroup.of_isProfiniteSpace hFspace
  letI : CompactSpace F := IsProfiniteGroup.compactSpace hFprof
  letI : T2Space F := IsProfiniteGroup.t2Space hFprof
  letI : TotallyDisconnectedSpace F := IsProfiniteGroup.totallyDisconnectedSpace hFprof
  let stage : FiniteSubset X → Subgroup F :=
    fun s => (Subgroup.closure (Set.range fun x : ↥s.1 => ι x.1)).topologicalClosure
  let stageBasis : ∀ s : FiniteSubset X, ↥s.1 → stage s :=
    fun s x => ⟨ι x.1, Subgroup.le_topologicalClosure _ <| by
      exact Subgroup.subset_closure ⟨x, rfl⟩⟩
  have hstage_closed : ∀ s : FiniteSubset X, IsClosed ((stage s : Set F)) := by
    intro s
    exact Subgroup.isClosed_topologicalClosure _
  have hstage_proC :
      ∀ s : FiniteSubset X, @ProCGroups.ProC.ProCGroupPredicate.holds ProC (stage s) _ _ _ := by
    intro s
    exact hClosed hF.isProC (stage s) (hstage_closed s)
  have hstage_space :
      ∀ s : FiniteSubset X, InverseSystems.IsProfiniteSpace (stage s) := by
    intro s
    exact hProfinite (hstage_proC s)
  have hstage_prof :
      ∀ s : FiniteSubset X, IsProfiniteGroup (stage s) := by
    intro s
    exact IsProfiniteGroup.of_isProfiniteSpace (hstage_space s)
  let stageSet : ∀ s : FiniteSubset X, Set (stage s) :=
    fun s => Set.range (stageBasis s)
  have hstage_generates :
      ∀ s : FiniteSubset X,
        Generation.TopologicallyGenerates (G := stage s) (stageSet s) := by
    intro s
    let H := stage s
    let K : Subgroup H := Subgroup.closure (stageSet s)
    have hclosedSubtype : IsClosedMap (H.subtype : H → F) :=
      (hstage_closed s).isClosedMap_subtype_val
    have hclosure :
        closure (((fun y : H => (y : F)) '' ((K : Set H)))) =
          (fun y : H => (y : F)) '' closure ((K : Set H)) :=
      hclosedSubtype.closure_image_eq_of_continuous continuous_subtype_val _
    have himg :
        ((fun y : H => (y : F)) '' ((K : Set H))) =
          (((Subgroup.closure (Set.range fun x : ↥s.1 => ι x.1)) : Subgroup F) : Set F) := by
      have hstageRange :
          ((fun y : H => (y : F)) '' stageSet s) =
            Set.range (fun x : ↥s.1 => ι x.1) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨stageBasis s x, ⟨x, rfl⟩, rfl⟩
      have hmap :
          K.map H.subtype =
            Subgroup.closure (((fun y : H => (y : F)) '' stageSet s)) := by
        simpa [K, TopologicalGroup.image_subtype_eq_map] using
          (H.subtype.map_closure (stageSet s))
      simpa [hstageRange] using
        congrArg (fun L : Subgroup F => (L : Set F)) hmap
    rw [Generation.topologicallyGenerates_iff_dense, dense_iff_closure_eq]
    ext y
    constructor
    · intro _hy
      simp only [mem_univ]
    · intro _hy
      have hy' : (y : F) ∈ ((fun z : H => (z : F)) '' closure ((K : Set H))) := by
        rw [← hclosure, himg]
        simp only [Subtype.coe_prop, stage]
      rcases hy' with ⟨w, hw, hwEq⟩
      exact (Subtype.ext hwEq) ▸ hw
  have hstage_free :
      ∀ s : FiniteSubset X,
        IsFreeProCGroupOnConvergingSet (ProC := ProC) ↥s.1 (stage s) (stageBasis s) := by
    intro s
    letI : Finite ↥s.1 := s.2.to_subtype
    refine ⟨hstage_proC s, ?_, hstage_generates s, ?_⟩
    · exact FamilyConvergesToOne.of_finite_domain (G := stage s) (stageBasis s)
    · intro G _ _ _ hG φ hφconv hφgen
      let hGspace : InverseSystems.IsProfiniteSpace G := hProfinite hG
      let hGprof : IsProfiniteGroup G := by
        exact IsProfiniteGroup.of_isProfiniteSpace hGspace
      letI : T2Space G := IsProfiniteGroup.t2Space hGprof
      let ψ : X → G := fun x => if hx : x ∈ s.1 then φ ⟨x, hx⟩ else 1
      have hψsub :
          Set.range ψ ⊆ Set.range φ ∪ ({1} : Set G) := by
        intro z hz
        rcases hz with ⟨x, rfl⟩
        by_cases hx : x ∈ s.1
        · left
          exact ⟨⟨x, hx⟩, by simp only [hx, ↓reduceDIte, ψ]⟩
        · right
          simp only [hx, ↓reduceDIte, mem_singleton_iff, ψ]
      have hψconv : FamilyConvergesToOne (G := G) ψ := by
        intro U
        have hsubset : {x : X | ψ x ∉ (U : Set G)} ⊆ s.1 := by
          intro x hx
          by_cases hxs : x ∈ s.1
          · exact hxs
          · exfalso
            exact hx (by simp only [hxs, ↓reduceDIte, SetLike.mem_coe, one_mem, ψ])
        exact s.2.subset hsubset
      have hψgen : Generation.TopologicallyGenerates (G := G) (Set.range ψ) := by
        have hsub : Set.range φ ⊆ Set.range ψ := by
          intro z hz
          rcases hz with ⟨x, rfl⟩
          exact ⟨x.1, by simp only [x.2, ↓reduceDIte, Subtype.coe_eta, ψ]⟩
        exact Generation.topologicallyGenerates_mono (G := G) hφgen hsub
      rcases hF.existsUnique_lift hG ψ hψconv hψgen with ⟨f, hf, huniq⟩
      let fs : stage s →* G := f.comp (stage s).subtype
      refine ⟨fs, ⟨hf.1.comp continuous_subtype_val, ?_⟩, ?_⟩
      · intro x
        simpa [fs, ψ, stageBasis, x.2] using hf.2 x.1
      · intro g hg
        let K : Subgroup (stage s) := Subgroup.closure (stageSet s)
        let E : Subgroup (stage s) := {
          carrier := {x | g x = fs x}
          one_mem' := by
            change g 1 = fs 1
            rw [map_one, map_one]
          mul_mem' := by
            intro a b ha hb
            change g (a * b) = fs (a * b)
            rw [map_mul, map_mul, ha, hb]
          inv_mem' := by
            intro a ha
            change g a⁻¹ = fs a⁻¹
            rw [map_inv, map_inv, ha] }
        have hrangeE : stageSet s ⊆ (E : Set (stage s)) := by
          rintro z ⟨x, rfl⟩
          change g (stageBasis s x) = fs (stageBasis s x)
          calc
            g (stageBasis s x) = φ x := hg.2 x
            _ = f (ι x.1) := by
              simpa [ψ, x.2] using (hf.2 x.1).symm
            _ = fs (stageBasis s x) := rfl
        have hKle : K ≤ E := by
          change Subgroup.closure (stageSet s) ≤ E
          exact (Subgroup.closure_le (K := E)).2 hrangeE
        have hKdense : DenseRange (K.subtype : K → stage s) := by
          rw [DenseRange]
          simpa [K, stageSet, Subgroup.range_subtype] using
            (Generation.topologicallyGenerates_iff_dense (G := stage s) (X := stageSet s)).1 (hstage_generates s)
        have hEqFun : (g : stage s → G) = fs := by
          apply DenseRange.equalizer (f := K.subtype) hKdense
          · exact hg.1
          · exact hf.1.comp continuous_subtype_val
          · funext z
            exact hKle z.2
        ext x
        exact congrFun hEqFun x
  let extendBasis : ∀ s : FiniteSubset X, X → stage s :=
    fun s x => if hx : x ∈ s.1 then stageBasis s ⟨x, hx⟩ else 1
  have hextendBasis_conv :
      ∀ s : FiniteSubset X, FamilyConvergesToOne (G := stage s) (extendBasis s) := by
    intro s
    letI : Finite ↥s.1 := s.2.to_subtype
    intro U
    have hsubset : {x : X | extendBasis s x ∉ (U : Set (stage s))} ⊆ s.1 := by
      intro x hx
      by_cases hxs : x ∈ s.1
      · exact hxs
      · exfalso
        exact hx (by simp only [hxs, ↓reduceDIte, SetLike.mem_coe, one_mem, extendBasis])
    exact s.2.subset hsubset
  have hextendBasis_gen :
      ∀ s : FiniteSubset X,
        Generation.TopologicallyGenerates (G := stage s) (Set.range (extendBasis s)) := by
    intro s
    have hsub : stageSet s ⊆ Set.range (extendBasis s) := by
      intro z hz
      rcases hz with ⟨x, rfl⟩
      exact ⟨x.1, by simp only [x.2, ↓reduceDIte, extendBasis, stageBasis]⟩
    exact Generation.topologicallyGenerates_mono (G := stage s) (hstage_generates s) hsub
  let stageRetraction :
      ∀ s : FiniteSubset X, F →* stage s := fun s =>
        Classical.choose <| ExistsUnique.exists <|
          hF.existsUnique_lift (hstage_proC s) (extendBasis s)
            (hextendBasis_conv s) (hextendBasis_gen s)
  have hstageRetraction_continuous :
      ∀ s : FiniteSubset X, Continuous (stageRetraction s) := by
    intro s
    exact (Classical.choose_spec <| ExistsUnique.exists <|
      hF.existsUnique_lift (hstage_proC s) (extendBasis s)
        (hextendBasis_conv s) (hextendBasis_gen s)).1
  have hstageRetraction_spec :
      ∀ s : FiniteSubset X, ∀ x : X,
        stageRetraction s (ι x) = extendBasis s x := by
    intro s x
    exact (Classical.choose_spec <| ExistsUnique.exists <|
      hF.existsUnique_lift (hstage_proC s) (extendBasis s)
        (hextendBasis_conv s) (hextendBasis_gen s)).2 x
  have hstageRetraction_restrict :
      ∀ s : FiniteSubset X,
        (stageRetraction s).comp (stage s).subtype = MonoidHom.id (stage s) := by
    intro s
    let basis := stageBasis s
    rcases (hstage_free s).existsUnique_lift (hstage_proC s) basis
        (by simpa using (hstage_free s).convergesToOne)
        (by simpa using (hstage_free s).generates_range) with
      ⟨u, hu, huniq⟩
    have hId :
        Continuous (MonoidHom.id (stage s)) ∧
          ∀ x : ↥s.1, (MonoidHom.id (stage s)) (basis x) = basis x := by
      refine ⟨continuous_id, ?_⟩
      intro x
      rfl
    have hRet :
        Continuous ((stageRetraction s).comp (stage s).subtype) ∧
          ∀ x : ↥s.1, ((stageRetraction s).comp (stage s).subtype) (basis x) = basis x := by
      refine ⟨(hstageRetraction_continuous s).comp continuous_subtype_val, ?_⟩
      intro x
      simpa [basis, extendBasis, stageBasis, x.2, MonoidHom.comp_apply] using
        hstageRetraction_spec s x.1
    calc
      (stageRetraction s).comp (stage s).subtype = u := huniq _ hRet
      _ = MonoidHom.id (stage s) := (huniq _ hId).symm
  have hstageRetraction_comp :
      ∀ {s t : FiniteSubset X}, s ≤ t →
        ((stageRetraction s).comp (stage t).subtype).comp (stageRetraction t) =
          stageRetraction s := by
    intro s t hst
    rcases hF.existsUnique_lift (hstage_proC s) (extendBasis s)
        (hextendBasis_conv s) (hextendBasis_gen s) with ⟨u, hu, huniq⟩
    have hStage : stageRetraction s = u :=
      huniq _ ⟨hstageRetraction_continuous s, hstageRetraction_spec s⟩
    have hComp :
        ((stageRetraction s).comp (stage t).subtype).comp (stageRetraction t) = u := by
      refine huniq _ ⟨((hstageRetraction_continuous s).comp continuous_subtype_val).comp
          (hstageRetraction_continuous t), ?_⟩
      intro x
      by_cases hx : x ∈ t.1
      · calc
          (((stageRetraction s).comp (stage t).subtype).comp (stageRetraction t)) (ι x)
              = stageRetraction s ((stage t).subtype (stageBasis t ⟨x, hx⟩)) := by
                  simp only [MonoidHom.comp_apply, hstageRetraction_spec, hx, ↓reduceDIte, Subgroup.subtype_apply, extendBasis]
          _ = stageRetraction s (ι x) := rfl
          _ = extendBasis s x := hstageRetraction_spec s x
      · have hsx : x ∉ s.1 := fun hsx => hx (hst hsx)
        calc
          (((stageRetraction s).comp (stage t).subtype).comp (stageRetraction t)) (ι x)
              = stageRetraction s ((stage t).subtype (1 : stage t)) := by
                  simp only [MonoidHom.comp_apply, hstageRetraction_spec, hx, ↓reduceDIte, map_one,
                    extendBasis]
          _ = stageRetraction s 1 := rfl
          _ = 1 := map_one _
          _ = extendBasis s x := by simp only [hsx, ↓reduceDIte, extendBasis]
    exact hComp.trans hStage.symm
  let stageMap :
      ∀ {s t : FiniteSubset X}, s ≤ t → stage t →* stage s :=
    fun {_s _t} _ => (stageRetraction _s).comp (stage _t).subtype
  let Ssys : InverseSystems.InverseSystem (I := FiniteSubset X) := {
    X := fun s => stage s
    topologicalSpace := fun s => inferInstance
    map := fun {_s _t} hst => stageMap hst
    continuous_map := by
      intro s t hst
      exact (hstageRetraction_continuous s).comp continuous_subtype_val
    map_id := by
      intro s
      funext x
      simpa [stageMap] using congrArg (fun f : stage s →* stage s => f x)
        (hstageRetraction_restrict s)
    map_comp := by
      intro s t u hst htu
      funext x
      change stageRetraction s ((stage t).subtype ((stageRetraction t) ((stage u).subtype x))) =
        stageRetraction s ((stage u).subtype x)
      simpa [stageMap, MonoidHom.comp_apply] using
        congrArg (fun f : F →* stage s => f ((stage u).subtype x)) (hstageRetraction_comp hst)
  }
  let Sdata : TopologicalGroupInverseSystemData (I := FiniteSubset X) := {
    toInverseSystem := Ssys
    group := fun s => inferInstance
    isGroupSystem := {
      map_one := by
        intro s t hst
        exact (stageMap hst).map_one
      map_mul := by
        intro s t hst x y
        exact (stageMap hst).map_mul x y
      map_inv := by
        intro s t hst x
        exact (stageMap hst).map_inv x
    }
    isTopologicalGroup := fun s => inferInstance
    inverseLimit_isTopologicalGroup := by infer_instance
  }
  letI : ∀ s, Group (Ssys.X s) := Sdata.group
  letI : InverseSystems.IsGroupSystem Ssys := Sdata.isGroupSystem
  letI : ∀ s, IsTopologicalGroup (Ssys.X s) := Sdata.isTopologicalGroup
  let limitMap : F → Ssys.inverseLimit :=
    Ssys.inverseLimitLift (fun s => stageRetraction s)
      (by
        intro s t hst
        funext x
        change stageRetraction s ((stage t).subtype (stageRetraction t x)) = stageRetraction s x
        simpa [MonoidHom.comp_apply] using
          congrArg (fun f : F →* stage s => f x) (hstageRetraction_comp hst))
  have hlimitMap_continuous : Continuous limitMap :=
    Ssys.continuous_inverseLimitLift (fun s => stageRetraction s) (fun s => hstageRetraction_continuous s)
      (by
        intro s t hst
        funext x
        change stageRetraction s ((stage t).subtype (stageRetraction t x)) = stageRetraction s x
        simpa [MonoidHom.comp_apply] using
          congrArg (fun f : F →* stage s => f x) (hstageRetraction_comp hst))
  let limitHom : F →* Ssys.inverseLimit := {
    toFun := limitMap
    map_one' := by
      apply Ssys.ext
      intro s
      change stageRetraction s 1 = 1
      exact map_one _
    map_mul' := by
      intro x y
      apply Ssys.ext
      intro s
      change stageRetraction s (x * y) = stageRetraction s x * stageRetraction s y
      exact map_mul _ _ _
  }
  have hlimit_inj : Function.Injective limitHom := by
    intro x y hxy
    by_contra hne
    have hxyne : x * y⁻¹ ≠ 1 := by
      intro h1
      apply hne
      simpa using mul_inv_eq_one.mp h1
    rcases ProCGroups.ProC.exists_openNormalSubgroup_not_mem (G := F) hFprof hxyne with ⟨U, hUxy⟩
    let q : F →* F ⧸ (U : Subgroup F) := QuotientGroup.mk' (U : Subgroup F)
    letI : Finite (F ⧸ (U : Subgroup F)) := by infer_instance
    letI : DiscreteTopology (F ⧸ (U : Subgroup F)) := by infer_instance
    have hquotProC :
        @ProCGroups.ProC.ProCGroupPredicate.holds ProC (F ⧸ (U : Subgroup F)) _ _ _ := by
      exact hFiniteQuot hF.isProC U
    let Uone : OpenSubgroup (F ⧸ (U : Subgroup F)) :=
      ⟨⊥, by
        exact
          isOpen_discrete
            ((⊥ : Subgroup (F ⧸ (U : Subgroup F))) : Set (F ⧸ (U : Subgroup F)))⟩
    have himg :
        Generation.GeneratesAndConvergesToOne (G := F ⧸ (U : Subgroup F))
          (q '' Set.range ι) := by
      exact Generation.GeneratesAndConvergesToOne.image_of_continuousSurjective
          (G := F) hFprof q continuous_quotient_mk'
          (QuotientGroup.mk'_surjective (U : Subgroup F))
        ⟨hF.generates_range, hF.convergesToOne.range⟩
    have hnontriv :
        {x : X | ι x ∉ (U : Set F)}.Finite := by
      exact hF.convergesToOne U.toOpenSubgroup
    let s0 : FiniteSubset X := ⟨{x : X | ι x ∉ (U : Set F)}, hnontriv⟩
    letI : Finite ↥s0.1 := s0.2.to_subtype
    let φ0 : ↥s0.1 → F ⧸ (U : Subgroup F) := fun x => q (ι x.1)
    have hφ0conv : FamilyConvergesToOne (G := F ⧸ (U : Subgroup F)) φ0 := by
      letI : Finite ↥s0.1 := s0.2.to_subtype
      exact FamilyConvergesToOne.of_finite_domain (G := F ⧸ (U : Subgroup F)) φ0
    have hgen0 : Generation.TopologicallyGenerates (G := F ⧸ (U : Subgroup F)) (Set.range φ0) := by
      have hgen' :
          Generation.TopologicallyGenerates (G := F ⧸ (U : Subgroup F))
            (q '' Set.range ι) := by
        simpa [Set.range_comp] using himg.1
      have hsub :
          q '' Set.range ι ⊆ Set.range φ0 ∪ ({1} : Set (F ⧸ (U : Subgroup F))) := by
        rintro z ⟨w, ⟨x, rfl⟩, rfl⟩
        by_cases hx : x ∈ s0.1
        · left
          exact ⟨⟨x, hx⟩, rfl⟩
        · right
          have hxU : ι x ∈ (U : Set F) := by
            exact by
              simp only [s0, Set.mem_setOf_eq, not_not] at hx
              exact hx
          have hq1 : q (ι x) = 1 := by
            simpa [q] using
              (QuotientGroup.eq_one_iff (N := (U : Subgroup F)) (ι x)).2 hxU
          simp only [hq1, mem_singleton_iff]
      have hgenUnion :
          Generation.TopologicallyGenerates (G := F ⧸ (U : Subgroup F))
            (Set.range φ0 ∪ ({1} : Set (F ⧸ (U : Subgroup F)))) := by
        exact Generation.topologicallyGenerates_mono (G := F ⧸ (U : Subgroup F)) hgen' hsub
      rw [Generation.topologicallyGenerates_union_one_iff] at hgenUnion
      exact hgenUnion
    rcases (hstage_free s0).existsUnique_lift hquotProC φ0 hφ0conv hgen0 with
      ⟨fq, hfq, _⟩
    have hqfac : fq.comp (stageRetraction s0) = q := by
      let ψ0 : X → F ⧸ (U : Subgroup F) := fun x =>
        if hx : x ∈ s0.1 then φ0 ⟨x, hx⟩ else 1
      have hψ0sub :
          Set.range ψ0 ⊆ Set.range φ0 ∪ ({1} : Set (F ⧸ (U : Subgroup F))) := by
        intro z hz
        rcases hz with ⟨x, rfl⟩
        by_cases hx : x ∈ s0.1
        · left
          exact ⟨⟨x, hx⟩, by simp only [dite_eq_ite, hx, ↓reduceIte, φ0, ψ0]⟩
        · right
          simp only [hx, ↓reduceDIte, mem_singleton_iff, ψ0]
      have hψ0conv : FamilyConvergesToOne (G := F ⧸ (U : Subgroup F)) ψ0 := by
        intro V
        have hsubset :
            {x : X | ψ0 x ∉ (V : Set (F ⧸ (U : Subgroup F)))} ⊆ s0.1 := by
          intro x hx
          by_cases hxs : x ∈ s0.1
          · exact hxs
          · exfalso
            exact hx (by simp only [hxs, ↓reduceDIte, SetLike.mem_coe, one_mem, ψ0])
        exact s0.2.subset hsubset
      have hψ0gen :
          Generation.TopologicallyGenerates (G := F ⧸ (U : Subgroup F)) (Set.range ψ0) := by
        have hsub : Set.range φ0 ⊆ Set.range ψ0 := by
          intro z hz
          rcases hz with ⟨x, rfl⟩
          exact ⟨x.1, by simp only [dite_eq_ite, x.2, ↓reduceIte, ψ0, φ0]⟩
        exact Generation.topologicallyGenerates_mono (G := F ⧸ (U : Subgroup F)) hgen0 hsub
      rcases hF.existsUnique_lift hquotProC ψ0 hψ0conv hψ0gen with ⟨u, hu, huniq⟩
      have hqeq : q = u := by
        exact huniq _ ⟨continuous_quotient_mk', by
          intro x
          by_cases hx : x ∈ s0.1
          · simp only [dite_eq_ite, hx, ↓reduceIte, ψ0, φ0]
          · have hx1 : q (ι x) = 1 := by
              have hxU : ι x ∈ (U : Set F) := by
                simpa [s0] using hx
              simpa [q] using (QuotientGroup.eq_one_iff (N := (U : Subgroup F)) (ι x)).2 hxU
            simp only [hx1, hx, ↓reduceDIte, ψ0]⟩
      have hcompEq : fq.comp (stageRetraction s0) = u := by
        exact huniq _ ⟨hfq.1.comp (hstageRetraction_continuous s0), by
          intro x
          by_cases hx : x ∈ s0.1
          · calc
              (fq.comp (stageRetraction s0)) (ι x)
                  = fq (stageBasis s0 ⟨x, hx⟩) := by
                      simp only [MonoidHom.comp_apply, hstageRetraction_spec, hx, ↓reduceDIte, extendBasis]
              _ = φ0 ⟨x, hx⟩ := hfq.2 ⟨x, hx⟩
              _ = ψ0 x := by simp only [dite_eq_ite, hx, ↓reduceIte, φ0, ψ0]
          · calc
              (fq.comp (stageRetraction s0)) (ι x)
                  = fq (1 : stage s0) := by
                      simp only [MonoidHom.comp_apply, hstageRetraction_spec, hx, ↓reduceDIte, map_one, extendBasis]
              _ = 1 := map_one _
              _ = ψ0 x := by simp only [hx, ↓reduceDIte, ψ0]⟩
      exact hcompEq.trans hqeq.symm
    have hs0eq :
        stageRetraction s0 x = stageRetraction s0 y := by
      exact congrArg (fun z : Ssys.inverseLimit => Ssys.projection s0 z) hxy
    have hqeq : q x = q y := by
      calc
        q x = fq (stageRetraction s0 x) := by
          simpa [MonoidHom.comp_apply] using
            (congrArg (fun f : F →* F ⧸ (U : Subgroup F) => f x) hqfac).symm
        _ = fq (stageRetraction s0 y) := by rw [hs0eq]
        _ = q y := by
            simpa [MonoidHom.comp_apply] using
              congrArg (fun f : F →* F ⧸ (U : Subgroup F) => f y) hqfac
    have hcontr :
        x * y⁻¹ ∈ (U : Subgroup F) := by
      simpa [div_eq_mul_inv] using
        (QuotientGroup.eq_iff_div_mem (N := (U : Subgroup F))).mp hqeq
    exact hUxy hcontr
  have hlimit_surj : Function.Surjective limitHom := by
    intro z
    let C : FiniteSubset X → Set F := fun s => {x | stageRetraction s x = Ssys.projection s z}
    have hCclosed : ∀ s : FiniteSubset X, IsClosed (C s) := by
      intro s
      simpa [C] using isClosed_singleton.preimage (hstageRetraction_continuous s)
    have hCdir : Directed (· ⊇ ·) C := by
      intro s t
      refine ⟨⟨s.1 ∪ t.1, s.2.union t.2⟩, ?_, ?_⟩
      · intro x hx
        change stageRetraction s x = Ssys.projection s z
        let hsu : s ≤ ⟨s.1 ∪ t.1, s.2.union t.2⟩ := by
          intro y hy
          exact Or.inl hy
        have hcomp := congrArg (fun f : F →* stage s => f x)
          (hstageRetraction_comp hsu)
        have hzcomp :
            stageMap hsu
                (Ssys.projection ⟨s.1 ∪ t.1, s.2.union t.2⟩ z) =
              Ssys.projection s z := by
          exact z.2 s ⟨s.1 ∪ t.1, s.2.union t.2⟩ hsu
        calc
          stageRetraction s x
              = stageRetraction s
                  ((stage ⟨s.1 ∪ t.1, s.2.union t.2⟩).subtype
                    (stageRetraction ⟨s.1 ∪ t.1, s.2.union t.2⟩ x)) := by
                      simpa [MonoidHom.comp_apply] using hcomp.symm
          _ = stageMap hsu (stageRetraction ⟨s.1 ∪ t.1, s.2.union t.2⟩ x) := by
              rfl
          _ = stageMap hsu (Ssys.projection ⟨s.1 ∪ t.1, s.2.union t.2⟩ z) := by
              rw [hx]
          _ = Ssys.projection s z := hzcomp
      · intro x hx
        change stageRetraction t x = Ssys.projection t z
        let htu' : t ≤ ⟨s.1 ∪ t.1, s.2.union t.2⟩ := by
          intro y hy
          exact Or.inr hy
        have hzcomp :
            stageMap htu'
                (Ssys.projection ⟨s.1 ∪ t.1, s.2.union t.2⟩ z) =
              Ssys.projection t z := by
          exact z.2 t ⟨s.1 ∪ t.1, s.2.union t.2⟩ htu'
        calc
          stageRetraction t x
              = stageRetraction t
                  ((stage ⟨s.1 ∪ t.1, s.2.union t.2⟩).subtype
                    (stageRetraction ⟨s.1 ∪ t.1, s.2.union t.2⟩ x)) := by
                      simpa [MonoidHom.comp_apply] using
                        (congrArg (fun f : F →* stage t => f x) (hstageRetraction_comp htu')).symm
          _ = stageMap htu' (stageRetraction ⟨s.1 ∪ t.1, s.2.union t.2⟩ x) := by
              rfl
          _ = stageMap htu' (Ssys.projection ⟨s.1 ∪ t.1, s.2.union t.2⟩ z) := by
              rw [hx]
          _ = Ssys.projection t z := hzcomp
    letI : Nonempty (FiniteSubset X) := ⟨⟨∅, Set.finite_empty⟩⟩
    have hCnonemptyEach : ∀ s : FiniteSubset X, (C s).Nonempty := by
      intro s
      refine ⟨(stage s).subtype (Ssys.projection s z), ?_⟩
      simpa [C, MonoidHom.comp_apply] using
        congrArg (fun f : stage s →* stage s => f (Ssys.projection s z)) (hstageRetraction_restrict s)
    have hCcompact : ∀ s : FiniteSubset X, IsCompact (C s) := by
      intro s
      exact (hCclosed s).isCompact
    have hCnonempty : (⋂ s, C s).Nonempty := by
      exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (t := C) hCdir hCnonemptyEach hCcompact hCclosed
    rcases hCnonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Ssys.ext
    intro s
    exact Set.mem_iInter.1 hx s
  have hlimit_bij : Function.Bijective limitHom := ⟨hlimit_inj, hlimit_surj⟩
  refine ⟨Sdata, stageBasis, hstage_free, ?_, ?_, ?_⟩
  · intro s t hst x
    by_cases hx : x.1 ∈ s.1
    · calc
        Sdata.toInverseSystem.map hst (stageBasis t x)
            = stageRetraction s (ι x.1) := rfl
        _ = stageBasis s ⟨x.1, hx⟩ := by
            simpa [extendBasis, stageBasis, hx]
              using (hstageRetraction_spec s x.1).trans (by simp only [hx, ↓reduceDIte, extendBasis, stageBasis])
        _ = (if hx' : x.1 ∈ s.1 then stageBasis s ⟨x.1, hx'⟩ else 1) := by
            simp only [hx, ↓reduceDIte]
    · calc
        Sdata.toInverseSystem.map hst (stageBasis t x)
            = stageRetraction s (ι x.1) := rfl
        _ = 1 := by
            simpa [extendBasis, hx] using hstageRetraction_spec s x.1
        _ = (if hx' : x.1 ∈ s.1 then stageBasis s ⟨x.1, hx'⟩ else 1) := by
            simp only [hx, ↓reduceDIte]
  · intro s
    refine ⟨(stage s).subtype, continuous_subtype_val, ?_, ?_, ?_⟩
    · exact Subtype.val_injective
    · convert hstage_closed s using 1
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    · intro x
      rfl
  · refine ⟨ContinuousMulEquiv.ofBijectiveCompactToT2 limitHom hlimitMap_continuous hlimit_bij⟩

/-- 3.10(a). For each finite subset of a basis converging to `1`, the corresponding finite-stage
free pro-`C` group embeds as a closed subgroup of the ambient free pro-`C` group. -/
theorem finiteSubset_embeds
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hProfinite :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _ →
          InverseSystems.IsProfiniteSpace G)
    (hClosed :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (H : Subgroup G), IsClosed (H : Set G) →
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC H _ _ _)
    (hFiniteQuot :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (U : OpenNormalSubgroup G),
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC (G ⧸ (U : Subgroup G)) _ _ _)
    (hF : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (s : FiniteSubset X) :
    ∃ (Fs : Type u) (_ : Group Fs) (_ : TopologicalSpace Fs) (_ : IsTopologicalGroup Fs)
      (ιs : ↥s.1 → Fs),
        IsFreeProCGroupOnConvergingSet (ProC := ProC) ↥s.1 Fs ιs ∧
        ∃ e : Fs →* F,
          Continuous e ∧ Function.Injective e ∧ IsClosed (Set.range e) ∧
            ∀ x : ↥s.1, e (ιs x) = ι x.1 := by
  rcases exists_finiteSubsetSystem_raw
      (ProC := ProC) (X := X) (F := F) (ι := ι)
      hProfinite hClosed hFiniteQuot hF with
    ⟨S, basis, hbasis, _hmap, hembed, _hlimit⟩
  rcases hembed s with ⟨e, he, hinj, hclosed, heq⟩
  exact ⟨S.toInverseSystem.X s, inferInstance, inferInstance, inferInstance, basis s,
    hbasis s, e, he, hinj, hclosed, heq⟩

/-- 3.10(b). A free pro-`C` group on a basis converging to `1` is the inverse limit of the
finite-stage free pro-`C` groups attached to its finite subsets. -/
theorem exists_finiteSubsetLimit_raw
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hProfinite :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _ →
          InverseSystems.IsProfiniteSpace G)
    (hClosed :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (H : Subgroup G), IsClosed (H : Set G) →
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC H _ _ _)
    (hFiniteQuot :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (U : OpenNormalSubgroup G),
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC (G ⧸ (U : Subgroup G)) _ _ _)
    (hF : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι) :
    ∃ S : TopologicalGroupInverseSystemData (I := FiniteSubset X),
      ∃ basis : ∀ s : FiniteSubset X, ↥s.1 → S.toInverseSystem.X s,
        (∀ s : FiniteSubset X,
          IsFreeProCGroupOnConvergingSet (ProC := ProC)
            ↥s.1 (S.toInverseSystem.X s) (basis s)) ∧
        (∀ {s t : FiniteSubset X} (hst : s ≤ t) (x : ↥t.1),
          S.toInverseSystem.map hst (basis t x) =
            by
              classical
              exact if hx : x.1 ∈ s.1 then basis s ⟨x.1, hx⟩ else 1) ∧
        (∀ s : FiniteSubset X,
          ∃ e : S.toInverseSystem.X s →* F,
            Continuous e ∧
              Function.Injective e ∧
              IsClosed (Set.range e) ∧
              ∀ x : ↥s.1, e (basis s x) = ι x.1) ∧
        Nonempty (F ≃ₜ* S.toInverseSystem.inverseLimit) := by
  simpa using
    exists_finiteSubsetSystem_raw
      (ProC := ProC) (X := X) (F := F) (ι := ι) hProfinite hClosed hFiniteQuot hF
/-- Restricting a free pro-`C` group from a basis `X` to a sub-basis `Y` gives a split quotient
whose kernel is the smallest closed normal subgroup generated by the complementary basis
elements. -/
theorem restriction_splitExact
    (hProfinite :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _ →
          InverseSystems.IsProfiniteSpace G)
    (hClosed :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (H : Subgroup G), IsClosed (H : Set G) →
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC H _ _ _)
    {X : Type u} (Y : Set X)
    {FX : Type u} [Group FX] [TopologicalSpace FX] [IsTopologicalGroup FX]
    {FY : Type u} [Group FY] [TopologicalSpace FY] [IsTopologicalGroup FY]
    {ιX : X → FX} {ιY : Y → FY}
    (hX : IsFreeProCGroupOnConvergingSet (ProC := ProC) X FX ιX)
    (hY : IsFreeProCGroupOnConvergingSet (ProC := ProC) Y FY ιY) :
    by
      classical
      exact
        ∃ φ : FX →* FY,
          Continuous φ ∧
            (∀ x, φ (ιX x) = if hx : x ∈ Y then ιY ⟨x, hx⟩ else 1) ∧
            Function.Surjective φ ∧
            ∃ σ : FY →* FX,
              Continuous σ ∧
                φ.comp σ = MonoidHom.id FY ∧
                IsSmallestClosedNormalSubgroupContaining
                  (Set.range fun x : {x : X // x ∉ Y} => ιX x.1) φ.ker := by
  classical
  let α : X → FY := fun x => if hx : x ∈ Y then ιY ⟨x, hx⟩ else 1
  have hαsub :
      Set.range α ⊆ Set.range ιY ∪ ({1} : Set FY) := by
    rintro z ⟨x, rfl⟩
    by_cases hx : x ∈ Y
    · left
      exact ⟨⟨x, hx⟩, by simp only [hx, ↓reduceDIte, α]⟩
    · right
      simp only [hx, ↓reduceDIte, mem_singleton_iff, α]
  have hαgen :
      Generation.TopologicallyGenerates (G := FY) (Set.range α) := by
    have hsub : Set.range ιY ⊆ Set.range α := by
      rintro z ⟨y, rfl⟩
      exact ⟨y.1, by simp only [y.2, ↓reduceDIte, Subtype.coe_eta, α]⟩
    exact Generation.topologicallyGenerates_mono (G := FY) hY.generates_range hsub
  have hαconv :
      FamilyConvergesToOne (G := FY) α := by
    intro U
    have hsubset :
        {x : X | α x ∉ (U : Set FY)} ⊆
          (fun y : Y => (y : X)) '' {y : Y | ιY y ∉ (U : Set FY)} := by
      intro x hx
      by_cases hxy : x ∈ Y
      · exact ⟨⟨x, hxy⟩, by simpa [α, hxy] using hx, rfl⟩
      · exfalso
        exact hx (by simp only [hxy, ↓reduceDIte, SetLike.mem_coe, one_mem, α])
    exact (hY.convergesToOne U).image (fun y : Y => (y : X)) |>.subset hsubset
  rcases hX.existsUnique_lift hY.isProC α hαconv hαgen with ⟨φ, hφ, hφuniq⟩
  let K : Subgroup FX :=
    (Subgroup.closure (Set.range fun y : Y => ιX y.1)).topologicalClosure
  let βK : Y → K := fun y => ⟨ιX y.1, Subgroup.le_topologicalClosure _ <|
    Subgroup.subset_closure ⟨y, rfl⟩⟩
  have hKclosed : IsClosed ((K : Set FX)) := by
    exact Subgroup.isClosed_topologicalClosure _
  have hKproC :
      @ProCGroups.ProC.ProCGroupPredicate.holds ProC K _ _ _ := by
    exact hClosed hX.isProC K hKclosed
  have hFXspace : InverseSystems.IsProfiniteSpace FX := hProfinite hX.isProC
  have hFXprof : IsProfiniteGroup FX := by
    exact IsProfiniteGroup.of_isProfiniteSpace hFXspace
  have hβKgen :
      Generation.TopologicallyGenerates (G := K) (Set.range βK) := by
    let L : Subgroup K := Subgroup.closure (Set.range βK)
    have hclosedSubtype : IsClosedMap (K.subtype : K → FX) :=
      hKclosed.isClosedMap_subtype_val
    have hclosure :
        closure (((fun z : K => (z : FX)) '' ((L : Set K)))) =
          (fun z : K => (z : FX)) '' closure ((L : Set K)) :=
      hclosedSubtype.closure_image_eq_of_continuous continuous_subtype_val _
    have himg :
        ((fun z : K => (z : FX)) '' ((L : Set K))) =
          (((Subgroup.closure (Set.range fun y : Y => ιX y.1)) : Subgroup FX) : Set FX) := by
      have hβRange :
          ((fun z : K => (z : FX)) '' Set.range βK) =
            Set.range (fun y : Y => ιX y.1) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨βK y, ⟨y, rfl⟩, rfl⟩
      have hmap :
          L.map K.subtype =
            Subgroup.closure (((fun z : K => (z : FX)) '' Set.range βK)) := by
        simpa [L, TopologicalGroup.image_subtype_eq_map] using
          (K.subtype.map_closure (Set.range βK))
      simpa [hβRange] using
        congrArg (fun J : Subgroup FX => (J : Set FX)) hmap
    rw [Generation.topologicallyGenerates_iff_dense, dense_iff_closure_eq]
    ext z
    constructor
    · intro _hz
      simp only [mem_univ]
    · intro _hz
      have hz' : (z : FX) ∈ ((fun w : K => (w : FX)) '' closure ((L : Set K))) := by
        rw [← hclosure, himg]
        simp only [Subtype.coe_prop, K]
      rcases hz' with ⟨w, hw, hwz⟩
      simpa [L] using ((Subtype.ext hwz) ▸ hw)
  have hβKconv :
      FamilyConvergesToOne (G := K) βK := by
    intro U
    letI : CompactSpace FX := IsProfiniteGroup.compactSpace hFXprof
    letI : TotallyDisconnectedSpace FX := IsProfiniteGroup.totallyDisconnectedSpace hFXprof
    have hUopen : IsOpen (U : Set K) := openSubgroup_isOpen (G := K) U
    rcases isOpen_induced_iff.mp hUopen with ⟨W, hWopen, hWeq⟩
    have h1W : (1 : FX) ∈ W := by
      have h1U : (1 : K) ∈ (U : Set K) := U.one_mem
      have : (⟨1, K.one_mem⟩ : K) ∈ Subtype.val ⁻¹' W := by
        exact hWeq.symm ▸ h1U
      simpa using this
    rcases ProCGroups.ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
        (G := FX) hWopen h1W with
      ⟨V, hVW⟩
    have hbadFinite :
        {y : Y | ιX y.1 ∉ (V.toOpenSubgroup : Set FX)}.Finite := by
      let e : Y ↪ X := ⟨fun y => y.1, Subtype.val_injective⟩
      have hfinite : {x : X | ιX x ∉ (V.toOpenSubgroup : Set FX)}.Finite :=
        hX.convergesToOne V.toOpenSubgroup
      simpa [Set.preimage, e] using hfinite.preimage_embedding e
    have hsubset :
        {y : Y | βK y ∉ (U : Set K)} ⊆
          {y : Y | ιX y.1 ∉ (V.toOpenSubgroup : Set FX)} := by
      intro y hy hyV
      have hyW : ιX y.1 ∈ W := hVW hyV
      have hyPre : βK y ∈ Subtype.val ⁻¹' W := by
        simpa [βK] using hyW
      have hyU : βK y ∈ (U : Set K) := by
        exact hWeq ▸ hyPre
      exact hy hyU
    exact hbadFinite.subset hsubset
  rcases hY.existsUnique_lift hKproC βK hβKconv hβKgen with ⟨σK, hσK, _hσKuniq⟩
  let σ : FY →* FX := K.subtype.comp σK
  have hσcont : Continuous σ := continuous_subtype_val.comp hσK.1
  have hσbasis : ∀ y : Y, σ (ιY y) = ιX y.1 := by
    intro y
    change K.subtype (σK (ιY y)) = ιX y.1
    exact congrArg Subtype.val (hσK.2 y)
  have hsection : φ.comp σ = MonoidHom.id FY := by
    rcases hY.existsUnique_lift hY.isProC ιY hY.convergesToOne hY.generates_range with
      ⟨u, _hu, huniq⟩
    have huId : MonoidHom.id FY = u := by
      exact huniq _ ⟨continuous_id, fun y => rfl⟩
    have huSect : φ.comp σ = u := by
      refine huniq _ ⟨hφ.1.comp hσcont, ?_⟩
      intro y
      change φ (σ (ιY y)) = ιY y
      calc
        φ (σ (ιY y)) = φ (ιX y.1) := congrArg φ (hσbasis y)
        _ = ιY y := by
          simpa [α, y.2] using hφ.2 y.1
    exact huSect.trans huId.symm
  have hφsurj : Function.Surjective φ := by
    intro y
    refine ⟨σ y, ?_⟩
    have hsec := congrArg (fun f : FY →* FY => f y) hsection
    simpa [MonoidHom.comp_apply] using hsec
  have hFYspace : InverseSystems.IsProfiniteSpace FY := hProfinite hY.isProC
  letI : T2Space FY :=
    IsProfiniteGroup.t2Space (IsProfiniteGroup.of_isProfiniteSpace hFYspace)
  have hkerClosed : IsClosed ((φ.ker : Set FX)) := by
    change IsClosed (φ ⁻¹' ({1} : Set FY))
    simpa using isClosed_singleton.preimage hφ.1
  refine ⟨φ, hφ.1, hφ.2, hφsurj, σ, hσcont, hsection, ?_⟩
  refine ⟨by infer_instance, hkerClosed, ?_, ?_⟩
  · rintro z ⟨x, rfl⟩
    change φ (ιX x.1) = 1
    simpa [α, x.2] using hφ.2 x.1
  · intro M hMnorm hMclosed hMgen
    let ρ : FX →* FX := σ.comp φ
    let E : Subgroup FX := {
      carrier := {g : FX | ρ g * g⁻¹ ∈ M}
      one_mem' := by
        simp only [MonoidHom.coe_comp, Function.comp_apply, mem_setOf_eq, map_one, inv_one, mul_one, one_mem, ρ]
      mul_mem' := by
        intro a b ha hb
        have hbconj : a * (ρ b * b⁻¹) * a⁻¹ ∈ M := hMnorm.conj_mem (ρ b * b⁻¹) hb a
        have hprod : (ρ a * a⁻¹) * (a * (ρ b * b⁻¹) * a⁻¹) ∈ M :=
          M.mul_mem ha hbconj
        simpa [ρ, map_mul, mul_assoc] using hprod
      inv_mem' := by
        intro a ha
        have ha' : (ρ a * a⁻¹)⁻¹ ∈ M := M.inv_mem ha
        simpa [ρ, map_inv, mul_assoc] using
          hMnorm.conj_mem ((ρ a * a⁻¹)⁻¹) ha' a⁻¹ }
    have hEclosed : IsClosed ((E : Set FX)) := by
      let δ : FX → FX := fun g => ρ g * g⁻¹
      have hδ : Continuous δ := (hσcont.comp hφ.1).mul continuous_inv
      simpa [E, δ] using hMclosed.preimage hδ
    have hιXsub : Set.range ιX ⊆ (E : Set FX) := by
      rintro z ⟨x, rfl⟩
      by_cases hx : x ∈ Y
      · change ρ (ιX x) * (ιX x)⁻¹ ∈ M
        have hEq : ρ (ιX x) * (ιX x)⁻¹ = 1 := by
          change σ (φ (ιX x)) * (ιX x)⁻¹ = 1
          rw [hφ.2 x]
          simp only [hx, ↓reduceDIte, hσbasis, mul_inv_cancel, α]
        rw [hEq]
        exact M.one_mem
      · change ρ (ιX x) * (ιX x)⁻¹ ∈ M
        have hxM : ιX x ∈ M := hMgen ⟨⟨x, hx⟩, rfl⟩
        have hEq : ρ (ιX x) * (ιX x)⁻¹ = (ιX x)⁻¹ := by
          change σ (φ (ιX x)) * (ιX x)⁻¹ = (ιX x)⁻¹
          rw [hφ.2 x]
          simp only [hx, ↓reduceDIte, map_one, one_mul, α]
        rw [hEq]
        exact M.inv_mem hxM
    have hEtop : E = ⊤ := by
      have hclosureLe : Subgroup.closure (Set.range ιX) ≤ E := by
        show Subgroup.closure (Set.range ιX) ≤ E
        exact (Subgroup.closure_le (K := E)).2 hιXsub
      have htopLe : (⊤ : Subgroup FX) ≤ E := by
        rw [← hX.generates_range]
        exact Subgroup.topologicalClosure_minimal _ hclosureLe hEclosed
      exact top_unique htopLe
    intro x hx
    have hxE : x ∈ E := by
      simp only [hEtop, Subgroup.mem_top]
    change ρ x * x⁻¹ ∈ M at hxE
    have hρx : ρ x = 1 := by
      have hxφ : φ x = 1 := by
        simpa [MonoidHom.mem_ker] using hx
      simp only [MonoidHom.comp_apply, hxφ, map_one, ρ]
    have hxinv : x⁻¹ ∈ M := by
      simpa [hρx] using hxE
    simpa using M.inv_mem hxinv

/-- For an open subgroup of a free pro-`C` group on a basis converging to `1`, there is a cofinal
finite-subset subsystem whose stage indices agree with the original open subgroup, under the same
explicit profiniteness, closed-subgroup permanence, finite-quotient permanence, and injectivity
hypotheses used in the finite-subset approximation theorem. -/
theorem openSubgroup_finiteSubsetApproximation
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hProfinite :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _ →
          InverseSystems.IsProfiniteSpace G)
    (hClosed :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (K : Subgroup G), IsClosed (K : Set G) →
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC K _ _ _)
    (hFiniteQuot :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (_hG : @ProCGroups.ProC.ProCGroupPredicate.holds ProC G _ _ _)
        (U : OpenNormalSubgroup G),
          @ProCGroups.ProC.ProCGroupPredicate.holds ProC (G ⧸ (U : Subgroup G)) _ _ _)
    (hF : IsFreeProCGroupOnConvergingSet (ProC := ProC) X F ι)
    (H : Subgroup F) (hH : IsOpen ((H : Set F))) :
    ∃ S : TopologicalGroupInverseSystemData (I := FiniteSubset X),
      ∃ basis : ∀ s : FiniteSubset X, ↥s.1 → S.toInverseSystem.X s,
        (∀ s : FiniteSubset X,
          IsFreeProCGroupOnConvergingSet (ProC := ProC)
            ↥s.1 (S.toInverseSystem.X s) (basis s)) ∧
        (∀ {s t : FiniteSubset X} (hst : s ≤ t) (x : ↥t.1),
          S.toInverseSystem.map hst (basis t x) =
            by
              classical
              exact if hx : x.1 ∈ s.1 then basis s ⟨x.1, hx⟩ else 1) ∧
          ∃ _limitIso : F ≃ₜ* S.toInverseSystem.inverseLimit,
          ∃ cofinalSubsets : Set (FiniteSubset X),
            (∀ s : FiniteSubset X, ∃ t, t ∈ cofinalSubsets ∧ s ≤ t) ∧
            ∃ stageSubgroup :
                ∀ {t : FiniteSubset X},
                  t ∈ cofinalSubsets → Subgroup (S.toInverseSystem.X t),
              (∀ {t : FiniteSubset X} (ht : t ∈ cofinalSubsets),
                IsOpen ((stageSubgroup ht : Set (S.toInverseSystem.X t)))) ∧
              (∀ {t : FiniteSubset X} (ht : t ∈ cofinalSubsets),
                (stageSubgroup ht).index = H.index) := by
  classical
  rcases exists_finiteSubsetSystem_raw
      (ProC := ProC) (X := X) (F := F) (ι := ι)
      hProfinite hClosed hFiniteQuot hF with
    ⟨S, basis, hbasis, hmap, _hembed, hlimit⟩
  let hFspace : InverseSystems.IsProfiniteSpace F := hProfinite hF.isProC
  let hFprof : IsProfiniteGroup F :=
    IsProfiniteGroup.of_isProfiniteSpace hFspace
  letI : CompactSpace F := IsProfiniteGroup.compactSpace hFprof
  letI : T2Space F := IsProfiniteGroup.t2Space hFprof
  letI : TotallyDisconnectedSpace F := IsProfiniteGroup.totallyDisconnectedSpace hFprof
  let Hopen : OpenSubgroup F := ⟨H, hH⟩
  letI : Finite (F ⧸ H) := openSubgroup_finiteQuotient (G := F) Hopen
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := H)
  let U : OpenNormalSubgroup F :=
    { toSubgroup := H.normalCore
      isOpen' := by
        exact H.normalCore.isOpen_of_isClosed_of_finiteIndex
          (H.normalCore_isClosed (Subgroup.isClosed_of_isOpen H hH))
      isNormal' := by infer_instance }
  have hUleH : (U : Subgroup F) ≤ H := Subgroup.normalCore_le H
  let q : F →* F ⧸ (U : Subgroup F) := QuotientGroup.mk' (U : Subgroup F)
  letI : Finite (F ⧸ (U : Subgroup F)) := openNormalSubgroup_finiteQuotient (G := F) U
  letI : DiscreteTopology (F ⧸ (U : Subgroup F)) :=
    QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := F) U)
  let Q := F ⧸ (U : Subgroup F)
  have hquotProC :
      @ProCGroups.ProC.ProCGroupPredicate.holds ProC Q _ _ _ := by
    exact hFiniteQuot hF.isProC U
  have hQspace : InverseSystems.IsProfiniteSpace Q := hProfinite hquotProC
  have hQprof : IsProfiniteGroup Q :=
    IsProfiniteGroup.of_isProfiniteSpace hQspace
  let Hbar : Subgroup Q := H.map q
  have hHbar_index : Hbar.index = H.index := by
    simpa [Hbar, q] using
      (Subgroup.index_map_eq (H := H) (f := q)
        (QuotientGroup.mk'_surjective (U : Subgroup F)) (by simpa [q] using hUleH))
  let HbarOpen : OpenSubgroup Q :=
    { toSubgroup := Hbar
      isOpen' := by
        exact isOpen_discrete (Hbar : Set Q) }
  have himg :
      Generation.GeneratesAndConvergesToOne (G := Q) (q '' Set.range ι) := by
    exact Generation.GeneratesAndConvergesToOne.image_of_continuousSurjective
      (G := F) hFprof q continuous_quotient_mk'
      (QuotientGroup.mk'_surjective (U : Subgroup F))
      ⟨hF.generates_range, hF.convergesToOne.range⟩
  have hnontriv :
      {x : X | ι x ∉ (U : Set F)}.Finite := by
    exact hF.convergesToOne U.toOpenSubgroup
  let s0 : FiniteSubset X := ⟨{x : X | ι x ∉ (U : Set F)}, hnontriv⟩
  let cofinalSubsets : Set (FiniteSubset X) := {t : FiniteSubset X | s0 ≤ t}
  have hcofinal :
      ∀ s : FiniteSubset X, ∃ t, t ∈ cofinalSubsets ∧ s ≤ t := by
    intro s
    refine ⟨⟨s.1 ∪ s0.1, s.2.union s0.2⟩, ?_, ?_⟩
    · intro x hx
      exact Or.inr hx
    · intro x hx
      exact Or.inl hx
  have stageQuotMap_exists :
      ∀ {t : FiniteSubset X} (ht : t ∈ cofinalSubsets),
        ∃ u : S.toInverseSystem.X t →* Q,
          Continuous u ∧ Function.Surjective u := by
    intro t ht
    let φt : ↥t.1 → Q := fun x => q (ι x.1)
    have hφtconv : FamilyConvergesToOne (G := Q) φt := by
      letI : Finite ↥t.1 := t.2.to_subtype
      exact FamilyConvergesToOne.of_finite_domain (G := Q) φt
    have hφtgen : Generation.TopologicallyGenerates (G := Q) (Set.range φt) := by
      have hgen' : Generation.TopologicallyGenerates (G := Q) (q '' Set.range ι) := by
        simpa [Set.range_comp] using himg.1
      have hsub :
          q '' Set.range ι ⊆ Set.range φt ∪ ({1} : Set Q) := by
        rintro z ⟨w, ⟨x, rfl⟩, rfl⟩
        by_cases hx : x ∈ t.1
        · left
          exact ⟨⟨x, hx⟩, rfl⟩
        · right
          have hx0 : x ∉ s0.1 := by
            intro hx0
            exact hx (ht hx0)
          have hxU : ι x ∈ (U : Set F) := by
            simp only [s0, Set.mem_setOf_eq, not_not] at hx0
            exact hx0
          have hq1 : q (ι x) = 1 := by
            simpa [q] using
              (QuotientGroup.eq_one_iff (N := (U : Subgroup F)) (ι x)).2 hxU
          simp only [hq1, mem_singleton_iff]
      have hgenUnion :
          Generation.TopologicallyGenerates (G := Q)
            (Set.range φt ∪ ({1} : Set Q)) := by
        exact Generation.topologicallyGenerates_mono (G := Q) hgen' hsub
      rw [Generation.topologicallyGenerates_union_one_iff] at hgenUnion
      exact hgenUnion
    rcases (hbasis t).existsUnique_lift hquotProC φt hφtconv hφtgen with ⟨u, hu, _⟩
    have hSspace : InverseSystems.IsProfiniteSpace (S.toInverseSystem.X t) := by
      exact hProfinite (hbasis t).isProC
    have hSprof : IsProfiniteGroup (S.toInverseSystem.X t) := by
      exact
        IsProfiniteGroup.of_isProfiniteSpace hSspace
    have husub : Set.range φt ⊆ (u.range : Set Q) := by
      rintro z ⟨x, rfl⟩
      exact ⟨basis t x, hu.2 x⟩
    have husurj : Function.Surjective u :=
      surjective_of_rangeContainsGeneratingSet
        (G := S.toInverseSystem.X t) (H := Q) hSprof hQprof hφtgen hu.1 husub
    exact ⟨u, hu.1, husurj⟩
  let stageQuotMap :
      ∀ {t : FiniteSubset X}, t ∈ cofinalSubsets → S.toInverseSystem.X t →* Q :=
    fun {t} ht => Classical.choose (stageQuotMap_exists (t := t) ht)
  let stageSubgroup :
      ∀ {t : FiniteSubset X}, t ∈ cofinalSubsets → Subgroup (S.toInverseSystem.X t) :=
    fun {t} ht => Subgroup.comap (stageQuotMap ht) Hbar
  have hstageOpen :
      ∀ {t : FiniteSubset X} (ht : t ∈ cofinalSubsets),
        IsOpen ((stageSubgroup ht : Set (S.toInverseSystem.X t))) := by
    intro t ht
    change IsOpen
      ((stageQuotMap ht) ⁻¹' ((Hbar : Subgroup Q) : Set Q))
    simpa using
      HbarOpen.isOpen'.preimage (Classical.choose_spec (stageQuotMap_exists (t := t) ht)).1
  have hstageIndex :
      ∀ {t : FiniteSubset X} (ht : t ∈ cofinalSubsets),
        (stageSubgroup ht).index = H.index := by
    intro t ht
    have hsurj : Function.Surjective (stageQuotMap ht) :=
      (Classical.choose_spec (stageQuotMap_exists (t := t) ht)).2
    calc
      (stageSubgroup ht).index = Hbar.index := by
        simpa [stageSubgroup] using
          (Subgroup.index_comap_of_surjective
            (H := Hbar) (f := stageQuotMap ht) hsurj)
      _ = H.index := hHbar_index
  refine ⟨S, basis, hbasis, hmap, ?_⟩
  rcases hlimit with ⟨limitIso⟩
  exact ⟨limitIso, cofinalSubsets, hcofinal, stageSubgroup, hstageOpen, hstageIndex⟩

end InverseLimitsAndFiniteSubsets
end ProCGroups.FreeProC
