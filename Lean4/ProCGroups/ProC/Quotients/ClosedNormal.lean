import ProCGroups.Generation.Basic
import ProCGroups.ProC.Quotients.LeftQuotientProjectionSections

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Quotients/ClosedNormal.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups

universe u v

namespace IsProfiniteGroup

open ProCGroups.ProC

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A quotient of a profinite group by a closed normal subgroup is profinite. -/
theorem quotient_closedNormalSubgroup
    (hG : IsProfiniteGroup G) {N : Subgroup G} [N.Normal]
    (hNclosed : IsClosed (N : Set G)) :
    IsProfiniteGroup (G ⧸ N) := by
  exact (isProC_allFinite_iff_isProfiniteGroup (G := G ⧸ N)).1 <|
    ProCGroups.ProC.quotient_closedNormalSubgroup
      (C := FiniteGroupClass.allFinite)
      FiniteGroupClass.allFinite_isomClosed
      FiniteGroupClass.allFinite_formation.quotientClosed
      ((isProC_allFinite_iff_isProfiniteGroup (G := G)).2 hG)
      N hNclosed

/-- The range of a continuous homomorphism from a profinite group to a Hausdorff topological group is
profinite, with the induced subtype topology. -/
theorem range
    (hG : IsProfiniteGroup G)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) :
    IsProfiniteGroup f.toMonoidHom.range := by
  letI : CompactSpace G := hG.compactSpace
  let K : Subgroup G := f.toMonoidHom.ker
  have hKclosed : IsClosed (K : Set G) := by
    dsimp [K]
    exact f.isClosed_ker
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  have hQuot : IsProfiniteGroup (G ⧸ K) :=
    quotient_closedNormalSubgroup hG hKclosed
  have e : (G ⧸ K) ≃ₜ* f.toMonoidHom.range := by
    simpa [K] using ContinuousMonoidHom.quotientKerContinuousMulEquivRange f
  letI : IsTopologicalGroup (G ⧸ K) := hQuot.isTopologicalGroup
  letI : CompactSpace (G ⧸ K) := hQuot.compactSpace
  letI : T2Space (G ⧸ K) := hQuot.t2Space
  letI : TotallyDisconnectedSpace (G ⧸ K) := hQuot.totallyDisconnectedSpace
  letI : CompactSpace f.toMonoidHom.range := e.toHomeomorph.compactSpace
  letI : T2Space f.toMonoidHom.range := e.toHomeomorph.t2Space
  letI : TotallyDisconnectedSpace f.toMonoidHom.range := e.toHomeomorph.totallyDisconnectedSpace
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end IsProfiniteGroup

end ProCGroups

namespace ProCGroups.Generation

universe u v

open ProCGroups.ProC

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A chosen continuous section of the quotient map by a closed normal subgroup of a profinite
group. -/
noncomputable def closedNormalQuotientSection
    (hG : IsProfiniteGroup G) {N : Subgroup G}
    (hNclosed : IsClosed (N : Set G)) :
    G ⧸ N → G :=
  Classical.choose (exists_continuousSection_quotientMk_of_isClosed (G := G) N hG hNclosed)

/-- The chosen closed-normal quotient section is continuous. -/
theorem closedNormalQuotientSection_continuous
    (hG : IsProfiniteGroup G) {N : Subgroup G}
    (hNclosed : IsClosed (N : Set G)) :
    Continuous (closedNormalQuotientSection (G := G) hG (N := N) hNclosed) := by
  exact (Classical.choose_spec
    (exists_continuousSection_quotientMk_of_isClosed (G := G) N hG hNclosed)).1

/-- The chosen closed-normal quotient section is a right inverse to the quotient map. -/
theorem closedNormalQuotientSection_rightInverse
    (hG : IsProfiniteGroup G) {N : Subgroup G}
    (hNclosed : IsClosed (N : Set G)) :
    Function.RightInverse
      (closedNormalQuotientSection (G := G) hG (N := N) hNclosed)
      (QuotientGroup.mk (s := N)) := by
  simpa using (Classical.choose_spec
    (exists_continuousSection_quotientMk_of_isClosed (G := G) N hG hNclosed)).2.1

/-- The chosen closed-normal quotient section sends the identity coset to `1`. -/
theorem closedNormalQuotientSection_one
    (hG : IsProfiniteGroup G) {N : Subgroup G}
    (hNclosed : IsClosed (N : Set G)) :
    closedNormalQuotientSection (G := G) hG (N := N) hNclosed
      (QuotientGroup.mk (s := N) (1 : G)) = 1 := by
  simpa using (Classical.choose_spec
    (exists_continuousSection_quotientMk_of_isClosed (G := G) N hG hNclosed)).2.2

/-- The quotient of a profinite group by a closed normal subgroup is profinite. -/
theorem isProfinite_quotient_closedNormal
    (hG : IsProfiniteGroup G) {N : Subgroup G} [N.Normal]
    (hNclosed : IsClosed (N : Set G)) :
    IsProfiniteGroup (G ⧸ N) :=
  ProCGroups.IsProfiniteGroup.quotient_closedNormalSubgroup hG hNclosed

/-- The quotient by the bottom subgroup is continuously multiplicatively equivalent to the
original profinite group. -/
noncomputable def quotientBotContinuousMulEquiv (hG : IsProfiniteGroup G) :
    G ≃ₜ* G ⧸ (⊥ : Subgroup G) :=
  ContinuousMulEquiv.mk' (quotientBotHomeomorph (G := G) hG) (by
    intro x y
    simp only [quotientBotHomeomorph_apply, QuotientGroup.mk_mul])

/-- Adding a closed normal subgroup to a generating set is equivalent to generating the quotient
from the image of the set. -/
theorem topologicallyGenerates_union_closedNormal_iff_quotient
    (hG : IsProfiniteGroup G) {N : Subgroup G} [N.Normal]
    (hNclosed : IsClosed (N : Set G)) {X : Set G} :
    TopologicallyGenerates (G := G) (X ∪ (N : Set G)) ↔
      TopologicallyGenerates (G := G ⧸ N) ((QuotientGroup.mk' N) '' X) := by
  let hGquot : IsProfiniteGroup (G ⧸ N) :=
    isProfinite_quotient_closedNormal (G := G) hG hNclosed
  constructor
  · intro hX
    have himg :
        (QuotientGroup.mk' N) '' (X ∪ (N : Set G)) =
          ((QuotientGroup.mk' N) '' X) ∪ ({1} : Set (G ⧸ N)) := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨x, hx, rfl⟩
        rcases hx with hxX | hxN
        · exact Or.inl ⟨x, hxX, rfl⟩
        · exact Or.inr ((QuotientGroup.eq_one_iff (N := N) x).2 hxN)
      · intro hq
        rcases hq with hqX | hq1
        · rcases hqX with ⟨x, hxX, rfl⟩
          exact ⟨x, Or.inl hxX, rfl⟩
        · exact ⟨1, Or.inr N.one_mem, by simpa using hq1.symm⟩
    have hquot :
        TopologicallyGenerates (G := G ⧸ N)
          ((QuotientGroup.mk' N) '' (X ∪ (N : Set G))) := by
      exact topologicallyGenerates_image_of_continuousSurjective
        (G := G)
        (H := G ⧸ N)
        (QuotientGroup.mk' N)
        continuous_quotient_mk'
        (QuotientGroup.mk'_surjective N)
        hX
    have hquot' :
        TopologicallyGenerates (G := G ⧸ N)
          ((((QuotientGroup.mk' N) '' X) ∪ ({1} : Set (G ⧸ N)))) := by
      rwa [himg] at hquot
    exact (topologicallyGenerates_union_one_iff (G := G ⧸ N)
      (X := (QuotientGroup.mk' N) '' X)).1
      hquot'
  · intro hX
    let H : Subgroup G := (Subgroup.closure (X ∪ (N : Set G))).topologicalClosure
    have hXleH : X ⊆ (H : Set G) := by
      intro x hx
      exact Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure (Or.inl hx))
    have hNleH : N ≤ H := by
      intro n hn
      exact Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure (Or.inr hn))
    let qH : Subgroup (G ⧸ N) := H.map (QuotientGroup.mk' N)
    have hqHclosed : IsClosed (qH : Set (G ⧸ N)) := by
      letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
      letI : T2Space (G ⧸ N) := IsProfiniteGroup.t2Space hGquot
      have hHcompact : IsCompact (H : Set G) := (Subgroup.isClosed_topologicalClosure _).isCompact
      have himage : IsCompact ((QuotientGroup.mk' N) '' (H : Set G)) :=
        hHcompact.image continuous_quotient_mk'
      have hEq : (QuotientGroup.mk' N) '' (H : Set G) = (qH : Set (G ⧸ N)) := by
        ext q
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
      rw [← hEq]
      exact himage.isClosed
    have himage_le_qH :
        ((QuotientGroup.mk' N) '' X) ⊆ (qH : Set (G ⧸ N)) := by
      intro q hq
      rcases hq with ⟨x, hx, rfl⟩
      exact ⟨x, hXleH hx, rfl⟩
    have hcl_le_qH :
        Subgroup.closure ((QuotientGroup.mk' N) '' X) ≤ qH := by
      exact (Subgroup.closure_le (K := qH)).2 himage_le_qH
    have hclosure_le_qH :
        (Subgroup.closure ((QuotientGroup.mk' N) '' X)).topologicalClosure ≤ qH := by
      exact Subgroup.topologicalClosure_minimal _ hcl_le_qH hqHclosed
    have htop :
        (⊤ : Subgroup (G ⧸ N)) ≤
          (Subgroup.closure ((QuotientGroup.mk' N) '' X)).topologicalClosure := by
      simpa [TopologicallyGenerates] using hX
    have hqHtop :
        qH = ⊤ := by
      apply top_unique
      intro q hq
      exact hclosure_le_qH (htop hq)
    rw [TopologicallyGenerates]
    apply top_unique
    intro g hg
    have hgq : QuotientGroup.mk' N g ∈ qH := by
      rw [hqHtop]
      simp only [QuotientGroup.mk'_apply, Subgroup.mem_top]
    rcases hgq with ⟨h, hhH, hhEq⟩
    have hdivN : h⁻¹ * g ∈ N := by
      exact (QuotientGroup.eq).1 hhEq
    have hdivH : h⁻¹ * g ∈ H := hNleH hdivN
    have hhH' : h ∈ H := hhH
    have hgH : g = h * (h⁻¹ * g) := by simp only [mul_inv_cancel_left]
    rw [hgH]
    exact H.mul_mem hhH' hdivH

/-- The image of a closed subgroup in a quotient by a closed normal subgroup is closed. -/
theorem isClosed_image_closedNormal_quotient
    (hG : IsProfiniteGroup G) {N N' : Subgroup G} [N'.Normal]
    (hNclosed : IsClosed (N : Set G)) (hN'closed : IsClosed (N' : Set G)) :
    IsClosed ((N.map (QuotientGroup.mk' N') : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
  let hGquot : IsProfiniteGroup (G ⧸ N') :=
    isProfinite_quotient_closedNormal (G := G) hG hN'closed
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space (G ⧸ N') := IsProfiniteGroup.t2Space hGquot
  have hNcompact : IsCompact (N : Set G) := hNclosed.isCompact
  have himage : IsCompact ((QuotientGroup.mk' N') '' (N : Set G)) :=
    hNcompact.image continuous_quotient_mk'
  have hEq :
      (QuotientGroup.mk' N') '' (N : Set G) =
        ((N.map (QuotientGroup.mk' N') : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [← hEq]
  exact himage.isClosed

/-- The quotient-of-quotient isomorphism for closed normal subgroups as a continuous
multiplicative equivalence. -/
noncomputable def quotientQuotientContinuousMulEquiv
    (hG : IsProfiniteGroup G) {N N' : Subgroup G} [N.Normal] [N'.Normal]
    (hNclosed : IsClosed (N : Set G)) (hN'closed : IsClosed (N' : Set G))
    (hN'N : N' ≤ N) :
    ((G ⧸ N') ⧸ N.map (QuotientGroup.mk' N')) ≃ₜ* G ⧸ N := by
  let K : Subgroup (G ⧸ N') := N.map (QuotientGroup.mk' N')
  let hGquotN' : IsProfiniteGroup (G ⧸ N') :=
    isProfinite_quotient_closedNormal (G := G) hG hN'closed
  let hGdom : IsProfiniteGroup ((G ⧸ N') ⧸ K) :=
    isProfinite_quotient_closedNormal
      (G := G ⧸ N') hGquotN'
      (isClosed_image_closedNormal_quotient (G := G) hG hNclosed hN'closed)
  letI : CompactSpace ((G ⧸ N') ⧸ K) := IsProfiniteGroup.compactSpace hGdom
  letI : T2Space (G ⧸ N) :=
    IsProfiniteGroup.t2Space (isProfinite_quotient_closedNormal (G := G) hG hNclosed)
  let f : ((G ⧸ N') ⧸ K) →* G ⧸ N :=
    QuotientGroup.quotientQuotientEquivQuotientAux N' N hN'N
  have hfcont : Continuous f := by
    refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
    simpa [Function.comp, K, leftQuotientProjection] using
      (continuous_leftQuotientProjection (G := G) (K := N') (H := N) hN'N)
  have hfbij : Function.Bijective f := by
    exact (QuotientGroup.quotientQuotientEquivQuotient N' N hN'N).bijective
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 f hfcont hfbij

/-- A quotient section together with generators for the kernel generates the intermediate
quotient. -/
theorem topologicallyGenerates_of_quotient_section_union_kernel
    (hG : IsProfiniteGroup G)
    {N N' : Subgroup G} [N.Normal] [N'.Normal]
    (hNclosed : IsClosed (N : Set G)) (hN'closed : IsClosed (N' : Set G))
    (hN'N : N' ≤ N)
    {Y : Set (G ⧸ N)}
    (hYgen : TopologicallyGenerates (G := G ⧸ N) Y)
    {σ : (G ⧸ N) → (G ⧸ N')}
    (hσright : Function.RightInverse σ (leftQuotientProjection N' N hN'N))
    {T : Set G}
    (hTgen : N ≤ Subgroup.closure (T ∪ (N' : Set G))) :
    TopologicallyGenerates (G := G ⧸ N')
      (σ '' Y ∪ ((QuotientGroup.mk' N') '' T)) := by
  classical
  let hGquotN' : IsProfiniteGroup (G ⧸ N') :=
    isProfinite_quotient_closedNormal (G := G) hG hN'closed
  letI : T2Space (G ⧸ N') := IsProfiniteGroup.t2Space hGquotN'
  let K : Subgroup (G ⧸ N') := N.map (QuotientGroup.mk' N')
  letI : K.Normal := by infer_instance
  let X : Set (G ⧸ N') := σ '' Y ∪ ((QuotientGroup.mk' N') '' T)
  have hKclosed : IsClosed (K : Set (G ⧸ N')) := by
    simpa [K] using
      isClosed_image_closedNormal_quotient (G := G) hG hNclosed hN'closed
  let e : ((G ⧸ N') ⧸ K) ≃ₜ* G ⧸ N :=
    quotientQuotientContinuousMulEquiv
      (G := G) hG hNclosed hN'closed hN'N
  have hsright :
      Function.RightInverse
        (fun y : G ⧸ N => QuotientGroup.mk' K (σ y))
        e := by
    intro y
    simpa [e, quotientQuotientContinuousMulEquiv, K, leftQuotientProjection] using hσright y
  have hsleft :
      Function.LeftInverse
        (fun y : G ⧸ N => QuotientGroup.mk' K (σ y))
        e := by
    intro z
    apply e.injective
    simpa using hsright (e z)
  have hs_eq :
      e.symm = (fun y : G ⧸ N => QuotientGroup.mk' K (σ y)) := by
    funext y
    simpa using (hsleft (e.symm y)).symm
  have hgenInv :
      TopologicallyGenerates (G := ((G ⧸ N') ⧸ K)) (e.symm '' Y) := by
    exact topologicallyGenerates_continuousMulEquiv_image
      (G := G ⧸ N) e.symm hYgen
  have hEq :
      e.symm '' Y = (QuotientGroup.mk' K) '' (σ '' Y) := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨σ y, ⟨y, hy, rfl⟩, by simp only [QuotientGroup.mk'_apply, hs_eq]⟩
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp only [hs_eq, QuotientGroup.mk'_apply]⟩
  have hgenQuotY : TopologicallyGenerates (G := ((G ⧸ N') ⧸ K))
      ((QuotientGroup.mk' K) '' (σ '' Y)) := by
    simpa [hEq] using hgenInv
  have hgenQuotX :
      TopologicallyGenerates (G := ((G ⧸ N') ⧸ K))
        ((QuotientGroup.mk' K) '' X) := by
    exact topologicallyGenerates_mono hgenQuotY (by
      intro q hq
      rcases hq with ⟨x, hx, rfl⟩
      exact ⟨x, Or.inl hx, rfl⟩)
  have hgenUnionK :
      TopologicallyGenerates (G := G ⧸ N') (X ∪ (K : Set (G ⧸ N'))) := by
    exact
      (topologicallyGenerates_union_closedNormal_iff_quotient
        (G := G ⧸ N') hGquotN' (N := K) hKclosed (X := X)).2 hgenQuotX
  have hKsubset :
      (K : Set (G ⧸ N')) ⊆ ((Subgroup.closure X : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
    have himgSubset :
        (QuotientGroup.mk' N' '' (T ∪ (N' : Set G))) ⊆
          ((Subgroup.closure X : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
      intro q hq
      rcases hq with ⟨g, hg, rfl⟩
      rcases hg with hgT | hgN'
      · exact Subgroup.subset_closure (Or.inr ⟨g, hgT, rfl⟩)
      · have hg1 : QuotientGroup.mk' N' g = (1 : G ⧸ N') := by
          exact (QuotientGroup.eq_one_iff (N := N') g).2 hgN'
        rw [hg1]
        exact (Subgroup.closure X).one_mem
    have hclosureSubset :
        Subgroup.closure ((QuotientGroup.mk' N') '' (T ∪ (N' : Set G))) ≤
          Subgroup.closure X := by
      exact (Subgroup.closure_le (K := Subgroup.closure X)).2 himgSubset
    intro q hq
    have hq' :
        q ∈ Subgroup.closure ((QuotientGroup.mk' N') '' (T ∪ (N' : Set G))) := by
      rcases hq with ⟨n, hnN, rfl⟩
      have hncl : n ∈ Subgroup.closure (T ∪ (N' : Set G)) := hTgen hnN
      have hmap :
          QuotientGroup.mk' N' n ∈
            (Subgroup.closure (T ∪ (N' : Set G))).map (QuotientGroup.mk' N') := by
        exact ⟨n, hncl, rfl⟩
      have hmapEq :
          (Subgroup.closure (T ∪ (N' : Set G))).map (QuotientGroup.mk' N') =
            Subgroup.closure ((QuotientGroup.mk' N') '' (T ∪ (N' : Set G))) := by
        simpa using
          (MonoidHom.map_closure (QuotientGroup.mk' N') (T ∪ (N' : Set G)))
      exact hmapEq ▸ hmap
    exact hclosureSubset hq'
  exact topologicallyGenerates_of_subset_closure hgenUnionK (by
    intro q hq
    rcases hq with hqX | hqK
    · exact Subgroup.subset_closure hqX
    · exact hKsubset hqK)

end ProCGroups.Generation
