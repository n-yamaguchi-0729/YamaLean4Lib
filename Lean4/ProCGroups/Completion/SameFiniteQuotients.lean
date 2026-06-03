import Mathlib.GroupTheory.Finiteness
import ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Completion/SameFiniteQuotients.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C completion and finite quotient systems

Organizes finite quotient systems, completion maps, finite-target factorization, and the universal property of pro-C completion.
-/

open scoped Topology

namespace ProCGroups.Completion

universe u

/-- Two abstract groups have the same finite quotients when they have exactly the same finite
surjective homomorphic images.
-/
def HasSameFiniteQuotients
    (G₁ : Type u) [Group G₁]
    (G₂ : Type u) [Group G₂] : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    (∃ φ : G₁ →* Q, Function.Surjective φ) ↔
      (∃ ψ : G₂ →* Q, Function.Surjective ψ)

/-- Topological finite quotient predicate using continuous maps to finite discrete groups. -/
def HasSameContinuousFiniteDiscreteQuotients
    (G₁ : Type u) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    (G₂ : Type u) [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] : Prop :=
  ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q],
    (∃ φ : G₁ →ₜ* Q, Function.Surjective φ) ↔
      (∃ ψ : G₂ →ₜ* Q, Function.Surjective ψ)

/-- Auxiliary strong-completeness input: every surjective homomorphism to a finite discrete group
is continuous. This isolates the hypothesis needed to identify abstract finite quotients with
continuous finite quotients. -/
class StronglyCompleteForFiniteDiscreteQuotients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop where
  continuous_of_surjective :
    ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [Finite Q] [DiscreteTopology Q],
      ∀ (φ : G →* Q), Function.Surjective φ → Continuous φ

/-- A bundled profinite completion model for an abstract group, keeping only the finite-quotient
universal property.

Note: finite quotients are taken with their discrete topology, which is the standard profinite
completion interface.
-/
structure AbstractProfiniteCompletionData
    (G : Type u) [Group G] where
  carrier : Type u
  instGroup : Group carrier
  instTopologicalSpace : TopologicalSpace carrier
  instIsTopologicalGroup : IsTopologicalGroup carrier
  instCompactSpace : CompactSpace carrier
  instT2Space : T2Space carrier
  instTotallyDisconnectedSpace : TotallyDisconnectedSpace carrier
  map : G →* carrier
  denseRange_map : DenseRange map
  existsUnique_lift_finite :
    ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [Finite Q] [DiscreteTopology Q],
      ∀ (φ : G →* Q), Function.Surjective φ →
        ∃! φbar : carrier →* Q, Continuous φbar ∧ φbar.comp map = φ

attribute [instance] AbstractProfiniteCompletionData.instGroup
attribute [instance] AbstractProfiniteCompletionData.instTopologicalSpace
attribute [instance] AbstractProfiniteCompletionData.instIsTopologicalGroup
attribute [instance] AbstractProfiniteCompletionData.instCompactSpace
attribute [instance] AbstractProfiniteCompletionData.instT2Space
attribute [instance] AbstractProfiniteCompletionData.instTotallyDisconnectedSpace

/-- The dense image of a finite abstract generating set topologically generates the completion. -/
theorem topologicallyFinitelyGenerated_abstractProfiniteCompletionData
    {G : Type u} [Group G] [Group.FG G]
    (Ghat : AbstractProfiniteCompletionData G) :
    FiniteGeneration.TopologicallyFinitelyGenerated Ghat.carrier := by
  classical
  rcases (Group.fg_iff' (G := G)).1 (inferInstance : Group.FG G) with
    ⟨_n, s, _hscard, hsclosure⟩
  let t : Finset Ghat.carrier := s.image Ghat.map
  have htclosure :
      Subgroup.closure (↑t : Set Ghat.carrier) = Ghat.map.range := by
    calc
      Subgroup.closure (↑t : Set Ghat.carrier)
          = Subgroup.closure (Ghat.map '' (↑s : Set G)) := by
              ext x
              simp only [Finset.coe_image, t]
      _ = (Subgroup.closure (↑s : Set G)).map Ghat.map := by
            symm
            simpa using (MonoidHom.map_closure Ghat.map (↑s : Set G))
      _ = (⊤ : Subgroup G).map Ghat.map := by
            simp only [hsclosure]
      _ = Ghat.map.range := by
            simp only [MonoidHom.range_eq_map]
  have hdense :
      Dense (((Subgroup.closure (↑t : Set Ghat.carrier)) : Subgroup Ghat.carrier) :
        Set Ghat.carrier) := by
    rw [htclosure, dense_iff_closure_eq]
    simpa using Ghat.denseRange_map.closure_range
  refine ⟨t, ?_⟩
  exact
    (Generation.topologicallyGenerates_iff_dense
      (G := Ghat.carrier) (X := (↑t : Set Ghat.carrier))).2 hdense

/-- A finite quotient of `G₂` yields, via the common finite quotient hypothesis and the universal
property of `G₁hat`, a surjective continuous homomorphism from `G₁hat`. -/
theorem exists_surjective_continuousMonoidHom_to_finite_of_sameFiniteQuotients
    {G₁ : Type u} [Group G₁]
    {G₂ : Type u} [Group G₂]
    (hquot : HasSameFiniteQuotients G₁ G₂)
    (G₁hat : AbstractProfiniteCompletionData G₁)
    (G₂hat : AbstractProfiniteCompletionData G₂)
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q]
    (ψ : G₂hat.carrier →* Q) (hψ : Continuous ψ) (hψsurj : Function.Surjective ψ) :
    ∃ φ : ContinuousMonoidHom G₁hat.carrier Q, Function.Surjective φ := by
  have hcompSurj : Function.Surjective (ψ.comp G₂hat.map) := by
    have hDense : Dense (Set.range G₂hat.map) := by
      simpa [DenseRange] using G₂hat.denseRange_map
    rw [dense_iff_inter_open] at hDense
    intro q
    rcases hψsurj q with ⟨x, rfl⟩
    let V : Set G₂hat.carrier := ψ ⁻¹' ({ψ x} : Set Q)
    have hVopen : IsOpen V := by
      have hsingle : IsOpen ({ψ x} : Set Q) := isOpen_discrete _
      simpa [V] using hsingle.preimage hψ
    have hVne : V.Nonempty := ⟨x, by simp only [Set.mem_preimage, Set.mem_singleton_iff, V]⟩
    rcases hDense V hVopen hVne with ⟨y, hyV, hyRange⟩
    let g : G₂ := Classical.choose hyRange
    have hg : G₂hat.map g = y := Classical.choose_spec hyRange
    refine ⟨g, ?_⟩
    have hyEq : ψ y = ψ x := by
      simpa [V] using hyV
    simpa [MonoidHom.comp_apply, hg] using hyEq
  rcases (hquot Q).2 ⟨ψ.comp G₂hat.map, hcompSurj⟩ with ⟨φ₀, hφ₀surj⟩
  rcases G₁hat.existsUnique_lift_finite φ₀ hφ₀surj with ⟨φbar, hφbar, _huniq⟩
  refine ⟨{ toMonoidHom := φbar, continuous_toFun := hφbar.1 }, ?_⟩
  intro q
  rcases hφ₀surj q with ⟨g, rfl⟩
  refine ⟨G₁hat.map g, ?_⟩
  have hfac := congrArg (fun f : G₁ →* Q => f g) hφbar.2
  simpa [MonoidHom.comp_apply] using hfac

/-- The common finite quotient hypothesis yields a surjective continuous homomorphism between the
associated profinite completions. -/
theorem exists_surjective_continuousMonoidHom_between_abstractProfiniteCompletions
    {G₁ : Type u} [Group G₁]
    {G₂ : Type u} [Group G₂]
    [Group.FG G₁]
    (hquot : HasSameFiniteQuotients G₁ G₂)
    (G₁hat : AbstractProfiniteCompletionData G₁)
    (G₂hat : AbstractProfiniteCompletionData G₂) :
    ∃ φ : ContinuousMonoidHom G₁hat.carrier G₂hat.carrier, Function.Surjective φ := by
  classical
  let H₁ := G₁hat.carrier
  let H₂ := G₂hat.carrier
  let C := FiniteGroupClass.allFinite
  have hH₁fg : FiniteGeneration.TopologicallyFinitelyGenerated H₁ :=
    topologicallyFinitelyGenerated_abstractProfiniteCompletionData (G := G₁) G₁hat
  have hH₂prof : IsProfiniteGroup H₂ := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hH₂proC : ProC.IsProCGroup C H₂ := by
    exact (ProC.isProC_allFinite_iff_isProfiniteGroup (G := H₂)).2 hH₂prof
  let S₂ : InverseSystems.InverseSystem
      (I := OrderDual (ProC.OpenNormalSubgroupInClass C H₂)) :=
    ProC.openNormalSubgroupInClassSystem C H₂
  let SurjHom (U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂)) :=
    { φ : ContinuousMonoidHom H₁ (S₂.X U) // Function.Surjective φ }
  letI : Nonempty (ProC.OpenNormalSubgroupInClass C H₂) :=
    ProC.IsProCGroup.openNormalSubgroupInClass_nonempty hH₂proC
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      Group (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    infer_instance
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      IsTopologicalGroup (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    infer_instance
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      Finite (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    exact (OrderDual.ofDual U).2
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      DiscreteTopology (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    exact QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := H₂)
        ((OrderDual.ofDual U).1 : OpenNormalSubgroup H₂))
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      Finite (ContinuousMonoidHom H₁ (S₂.X U)) := fun U => by
    exact
      FiniteGeneration.finite_continuousMonoidHom_to_finite_of_topologicallyFinitelyGenerated
        (G := H₁) (R := S₂.X U) hH₁fg
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      TopologicalSpace (SurjHom U) := fun _ => ⊥
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      DiscreteTopology (SurjHom U) := fun _ => ⟨rfl⟩
  let X₂ : InverseSystems.InverseSystem
      (I := OrderDual (ProC.OpenNormalSubgroupInClass C H₂)) :=
    { X := SurjHom
      topologicalSpace := fun _ => ⊥
      map := fun {U V} hUV φ => by
        have hUV' : ((OrderDual.ofDual V).1 : Subgroup H₂) ≤ (OrderDual.ofDual U).1 := hUV
        let qUV : ContinuousMonoidHom (S₂.X V) (S₂.X U) :=
          { toMonoidHom := by
              dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
              exact ProC.OpenNormalSubgroupInClass.map
                (C := C) (G := H₂)
                (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
            continuous_toFun := continuous_of_discreteTopology }
        refine ⟨qUV.comp φ.1, ?_⟩
        intro x
        rcases (ProC.OpenNormalSubgroupInClass.map_surjective
            (C := C) (G := H₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV') x with ⟨y, hy⟩
        rcases φ.2 y with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        calc
          (qUV.comp φ.1) z = qUV (φ.1 z) := rfl
          _ = qUV y := by rw [hz]
          _ = x := hy
      continuous_map := by
        intro U V hUV
        exact continuous_of_discreteTopology
      map_id := by
        intro U
        funext φ
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        change ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := H₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual U) (le_rfl)
            (φ.1 x) = φ.1 x
        exact congrFun
          (congrArg DFunLike.coe
            (ProC.OpenNormalSubgroupInClass.map_id
              (C := C) (G := H₂) (U := OrderDual.ofDual U)))
          (φ.1 x)
      map_comp := by
        intro U V W hUV hVW
        have hUV' : ((OrderDual.ofDual V).1 : Subgroup H₂) ≤ (OrderDual.ofDual U).1 := hUV
        have hVW' : ((OrderDual.ofDual W).1 : Subgroup H₂) ≤ (OrderDual.ofDual V).1 := hVW
        funext φ
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        change ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := H₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
            (ProC.OpenNormalSubgroupInClass.map
              (C := C) (G := H₂)
              (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW' (φ.1 x)) =
          ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := H₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual W) (hVW'.trans hUV')
            (φ.1 x)
        exact
          congrArg
            (fun f : H₂ ⧸ (((OrderDual.ofDual W).1 : OpenNormalSubgroup H₂) : Subgroup H₂) →*
              H₂ ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup H₂) : Subgroup H₂) =>
              f (φ.1 x))
            (ProC.OpenNormalSubgroupInClass.map_comp
              (C := C) (G := H₂)
              (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
              hUV' hVW') }
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      Nonempty (X₂.X U) := fun U => by
    dsimp [X₂]
    let qU : H₂ →* S₂.X U :=
      ProC.openNormalSubgroupInClassProj
        (C := C) (G := H₂) U
    have hqUcont : Continuous qU := by
      dsimp [qU, S₂, ProC.openNormalSubgroupInClassSystem]
      simpa using
        (continuous_quotient_mk' : Continuous
          (QuotientGroup.mk'
            (((OrderDual.ofDual U).1 : OpenNormalSubgroup H₂) : Subgroup H₂)))
    have hqUsurj : Function.Surjective qU :=
      ProC.openNormalSubgroupInClassProj_surjective
        (C := C) (G := H₂) U
    rcases exists_surjective_continuousMonoidHom_to_finite_of_sameFiniteQuotients
        (G₁ := G₁) (G₂ := G₂) hquot G₁hat G₂hat qU hqUcont hqUsurj with
      ⟨φ, hφsurj⟩
    exact ⟨⟨φ, hφsurj⟩⟩
  have hdir₂ :
      Directed
        (α := OrderDual (ProC.OpenNormalSubgroupInClass C H₂))
        (· ≤ ·) (fun U => U) := by
    intro U V
    let W : ProC.OpenNormalSubgroupInClass C H₂ :=
      ⟨(OrderDual.ofDual U).1 ⊓ (OrderDual.ofDual V).1,
        FiniteGroupClass.Formation.quotient_inf_mem
          (C := C) (G := H₂)
          FiniteGroupClass.allFinite_formation
          (OrderDual.ofDual U).1 (OrderDual.ofDual V).1
          (OrderDual.ofDual U).2 (OrderDual.ofDual V).2⟩
    refine ⟨OrderDual.toDual W, ?_, ?_⟩
    · change ((W.1 : Subgroup H₂) ≤ ((OrderDual.ofDual U).1 : Subgroup H₂))
      exact inf_le_left
    · change ((W.1 : Subgroup H₂) ≤ ((OrderDual.ofDual V).1 : Subgroup H₂))
      exact inf_le_right
  rcases InverseSystems.InverseSystem.nonempty_inverseLimit_of_finite (S := X₂) hdir₂ with ⟨x₂⟩
  let ψ₂ : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C H₂),
      H₁ → S₂.X U := fun U => (x₂.1 U).1
  have hψ₂cont : ∀ U, Continuous (ψ₂ U) := by
    intro U
    exact ((x₂.1 U).1).continuous_toFun
  have hψ₂compat : S₂.CompatibleMaps ψ₂ := by
    intro U V hUV
    funext x
    have hEq : X₂.map hUV (x₂.1 V) = x₂.1 U := x₂.2 U V hUV
    have hEq' : (X₂.map hUV (x₂.1 V)).1 = (x₂.1 U).1 := congrArg Subtype.val hEq
    exact congrArg (fun φ : ContinuousMonoidHom H₁ (S₂.X U) => φ x) hEq'
  have hψ₂surj : ∀ U, Function.Surjective (ψ₂ U) := by
    intro U
    exact (x₂.1 U).2
  let fToInv : ContinuousMonoidHom H₁ S₂.inverseLimit :=
    { toMonoidHom :=
        { toFun := S₂.inverseLimitLift ψ₂ hψ₂compat
          map_one' := by
            apply S₂.ext
            intro U
            calc
              S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat 1) = ψ₂ U 1 := by
                simpa [Function.comp] using congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) (1 : H₁)
              _ = 1 := by simp only [map_one, ψ₂]
          map_mul' := by
            intro x y
            apply S₂.ext
            intro U
            calc
              S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat (x * y)) = ψ₂ U (x * y) := by
                simpa [Function.comp] using
                  congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) (x * y)
              _ = ψ₂ U x * ψ₂ U y := by simp only [map_mul, ψ₂]
              _ = S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat x) *
                    S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat y) := by
                  have hπx :
                      S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat x) = ψ₂ U x := by
                    simpa [Function.comp] using
                      congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) x
                  have hπy :
                      S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat y) = ψ₂ U y := by
                    simpa [Function.comp] using
                      congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) y
                  rw [← hπx, ← hπy] }
      continuous_toFun := S₂.continuous_inverseLimitLift ψ₂ hψ₂cont hψ₂compat }
  have hfToInv_surj : Function.Surjective (S₂.inverseLimitLift ψ₂ hψ₂compat) :=
    S₂.surjective_inverseLimitLift ψ₂ hψ₂cont hψ₂compat hψ₂surj hdir₂
  let e₂ : H₂ ≃ₜ* S₂.inverseLimit :=
    ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := H₂)
      FiniteGroupClass.allFinite_formation hH₂proC
  let e₂symmHom : ContinuousMonoidHom S₂.inverseLimit H₂ :=
    { toMonoidHom := e₂.symm.toMonoidHom
      continuous_toFun := e₂.symm.continuous_toFun }
  refine ⟨e₂symmHom.comp fToInv, ?_⟩
  intro y
  rcases hfToInv_surj (e₂ y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change e₂.symm (S₂.inverseLimitLift ψ₂ hψ₂compat x) = y
  rw [hx]
  exact e₂.symm_apply_apply y

/-- Finitely generated abstract groups with the same finite quotients have isomorphic profinite
completion models. -/
theorem abstractProfiniteCompletions_iso_of_sameFiniteQuotients
    {G₁ : Type u} [Group G₁]
    {G₂ : Type u} [Group G₂]
    [Group.FG G₁] [Group.FG G₂]
    (hquot : HasSameFiniteQuotients G₁ G₂)
    (G₁hat : AbstractProfiniteCompletionData G₁)
    (G₂hat : AbstractProfiniteCompletionData G₂) :
    Nonempty (G₁hat.carrier ≃ₜ* G₂hat.carrier) := by
  classical
  let H₁ := G₁hat.carrier
  let H₂ := G₂hat.carrier
  have hH₁fg : FiniteGeneration.TopologicallyFinitelyGenerated H₁ :=
    topologicallyFinitelyGenerated_abstractProfiniteCompletionData (G := G₁) G₁hat
  rcases exists_surjective_continuousMonoidHom_between_abstractProfiniteCompletions
      (G₁ := G₁) (G₂ := G₂) hquot G₁hat G₂hat with ⟨φ, hφsurj⟩
  rcases exists_surjective_continuousMonoidHom_between_abstractProfiniteCompletions
      (G₁ := G₂) (G₂ := G₁) (by
        intro Q _ _
        exact (hquot Q).symm) G₂hat G₁hat with
    ⟨ψ, hψsurj⟩
  let ψφ : ContinuousMonoidHom H₁ H₁ := ψ.comp φ
  have hψφsurj : Function.Surjective ψφ := by
    simpa [ψφ] using hψsurj.comp hφsurj
  rcases (FiniteGeneration.surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
    (G := H₁) hH₁fg ψφ hψφsurj) with ⟨e, he⟩
  have hψφinj : Function.Injective ψφ := by
    intro x y hxy
    apply e.injective
    calc
      e x = ψφ x := he x
      _ = ψφ y := hxy
      _ = e y := (he y).symm
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hψφinj
    change ψ (φ x) = ψ (φ y)
    exact congrArg ψ hxy
  exact ⟨ContinuousMulEquiv.ofBijectiveCompactToT2
    φ.toMonoidHom φ.continuous_toFun ⟨hφinj, hφsurj⟩⟩

/-- The continuous finite quotient hypothesis yields a surjective continuous homomorphism between
topologically finitely generated profinite groups. -/
theorem exists_surj_continuousMonoidHom_between_profiniteGroups_of_sameContinuousFiniteDiscreteQuotients
    {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {G₂ : Type u} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [CompactSpace G₁]
    [CompactSpace G₂] [T2Space G₂] [TotallyDisconnectedSpace G₂]
    (hG₁fg : FiniteGeneration.TopologicallyFinitelyGenerated G₁)
    (hquot : HasSameContinuousFiniteDiscreteQuotients G₁ G₂) :
    ∃ φ : ContinuousMonoidHom G₁ G₂, Function.Surjective φ := by
  classical
  let C := FiniteGroupClass.allFinite
  have hG₂prof : IsProfiniteGroup G₂ := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hG₂proC : ProC.IsProCGroup C G₂ := by
    exact (ProC.isProC_allFinite_iff_isProfiniteGroup (G := G₂)).2 hG₂prof
  let S₂ : InverseSystems.InverseSystem
      (I := OrderDual (ProC.OpenNormalSubgroupInClass C G₂)) :=
    ProC.openNormalSubgroupInClassSystem C G₂
  let SurjHom (U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂)) :=
    { φ : ContinuousMonoidHom G₁ (S₂.X U) // Function.Surjective φ }
  letI : Nonempty (ProC.OpenNormalSubgroupInClass C G₂) :=
    ProC.IsProCGroup.openNormalSubgroupInClass_nonempty hG₂proC
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Group (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    infer_instance
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      IsTopologicalGroup (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    infer_instance
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Finite (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    exact (OrderDual.ofDual U).2
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      DiscreteTopology (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    exact QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := G₂)
        ((OrderDual.ofDual U).1 : OpenNormalSubgroup G₂))
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Finite (ContinuousMonoidHom G₁ (S₂.X U)) := fun U => by
    exact
      FiniteGeneration.finite_continuousMonoidHom_to_finite_of_topologicallyFinitelyGenerated
        (G := G₁) (R := S₂.X U) hG₁fg
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      TopologicalSpace (SurjHom U) := fun _ => ⊥
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      DiscreteTopology (SurjHom U) := fun _ => ⟨rfl⟩
  let X₂ : InverseSystems.InverseSystem
      (I := OrderDual (ProC.OpenNormalSubgroupInClass C G₂)) :=
    { X := SurjHom
      topologicalSpace := fun _ => ⊥
      map := fun {U V} hUV φ => by
        have hUV' : ((OrderDual.ofDual V).1 : Subgroup G₂) ≤ (OrderDual.ofDual U).1 := hUV
        let qUV : ContinuousMonoidHom (S₂.X V) (S₂.X U) :=
          { toMonoidHom := by
              dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
              exact ProC.OpenNormalSubgroupInClass.map
                (C := C) (G := G₂)
                (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
            continuous_toFun := continuous_of_discreteTopology }
        refine ⟨qUV.comp φ.1, ?_⟩
        intro x
        rcases (ProC.OpenNormalSubgroupInClass.map_surjective
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV') x with ⟨y, hy⟩
        rcases φ.2 y with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        calc
          (qUV.comp φ.1) z = qUV (φ.1 z) := rfl
          _ = qUV y := by rw [hz]
          _ = x := hy
      continuous_map := by
        intro U V hUV
        exact continuous_of_discreteTopology
      map_id := by
        intro U
        funext φ
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        change ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual U) (le_rfl)
            (φ.1 x) = φ.1 x
        exact congrFun
          (congrArg DFunLike.coe
            (ProC.OpenNormalSubgroupInClass.map_id
              (C := C) (G := G₂) (U := OrderDual.ofDual U)))
          (φ.1 x)
      map_comp := by
        intro U V W hUV hVW
        have hUV' : ((OrderDual.ofDual V).1 : Subgroup G₂) ≤ (OrderDual.ofDual U).1 := hUV
        have hVW' : ((OrderDual.ofDual W).1 : Subgroup G₂) ≤ (OrderDual.ofDual V).1 := hVW
        funext φ
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        change ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
            (ProC.OpenNormalSubgroupInClass.map
              (C := C) (G := G₂)
              (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW' (φ.1 x)) =
          ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual W) (hVW'.trans hUV')
            (φ.1 x)
        exact
          congrArg
            (fun f : G₂ ⧸ (((OrderDual.ofDual W).1 : OpenNormalSubgroup G₂) : Subgroup G₂) →*
              G₂ ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G₂) : Subgroup G₂) =>
              f (φ.1 x))
            (ProC.OpenNormalSubgroupInClass.map_comp
              (C := C) (G := G₂)
              (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
              hUV' hVW') }
  letI : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Nonempty (X₂.X U) := fun U => by
    dsimp [X₂]
    let qU : G₂ →ₜ* S₂.X U :=
      { toMonoidHom := ProC.openNormalSubgroupInClassProj
          (C := C) (G := G₂) U
        continuous_toFun := by
          dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
          simpa using
            (continuous_quotient_mk' : Continuous
              (QuotientGroup.mk'
                (((OrderDual.ofDual U).1 : OpenNormalSubgroup G₂) : Subgroup G₂))) }
    have hqUsurj : Function.Surjective qU :=
      ProC.openNormalSubgroupInClassProj_surjective
        (C := C) (G := G₂) U
    rcases (hquot (S₂.X U)).2 ⟨qU, hqUsurj⟩ with ⟨φ, hφsurj⟩
    exact ⟨⟨φ, hφsurj⟩⟩
  have hdir₂ :
      Directed
        (α := OrderDual (ProC.OpenNormalSubgroupInClass C G₂))
        (· ≤ ·) (fun U => U) := by
    intro U V
    let W : ProC.OpenNormalSubgroupInClass C G₂ :=
      ⟨(OrderDual.ofDual U).1 ⊓ (OrderDual.ofDual V).1,
        FiniteGroupClass.Formation.quotient_inf_mem
          (C := C) (G := G₂)
          FiniteGroupClass.allFinite_formation
          (OrderDual.ofDual U).1 (OrderDual.ofDual V).1
          (OrderDual.ofDual U).2 (OrderDual.ofDual V).2⟩
    refine ⟨OrderDual.toDual W, ?_, ?_⟩
    · change ((W.1 : Subgroup G₂) ≤ ((OrderDual.ofDual U).1 : Subgroup G₂))
      exact inf_le_left
    · change ((W.1 : Subgroup G₂) ≤ ((OrderDual.ofDual V).1 : Subgroup G₂))
      exact inf_le_right
  rcases InverseSystems.InverseSystem.nonempty_inverseLimit_of_finite (S := X₂) hdir₂ with ⟨x₂⟩
  let ψ₂ : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      G₁ → S₂.X U := fun U => (x₂.1 U).1
  have hψ₂cont : ∀ U, Continuous (ψ₂ U) := by
    intro U
    exact ((x₂.1 U).1).continuous_toFun
  have hψ₂compat : S₂.CompatibleMaps ψ₂ := by
    intro U V hUV
    funext x
    have hEq : X₂.map hUV (x₂.1 V) = x₂.1 U := x₂.2 U V hUV
    have hEq' : (X₂.map hUV (x₂.1 V)).1 = (x₂.1 U).1 := congrArg Subtype.val hEq
    exact congrArg (fun φ : ContinuousMonoidHom G₁ (S₂.X U) => φ x) hEq'
  have hψ₂surj : ∀ U, Function.Surjective (ψ₂ U) := by
    intro U
    exact (x₂.1 U).2
  let fToInv : ContinuousMonoidHom G₁ S₂.inverseLimit :=
    { toMonoidHom :=
        { toFun := S₂.inverseLimitLift ψ₂ hψ₂compat
          map_one' := by
            apply S₂.ext
            intro U
            calc
              S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat 1) = ψ₂ U 1 := by
                simpa [Function.comp] using congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) (1 : G₁)
              _ = 1 := by simp only [map_one, ψ₂]
          map_mul' := by
            intro x y
            apply S₂.ext
            intro U
            calc
              S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat (x * y)) = ψ₂ U (x * y) := by
                simpa [Function.comp] using
                  congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) (x * y)
              _ = ψ₂ U x * ψ₂ U y := by simp only [map_mul, ψ₂]
              _ = S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat x) *
                    S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat y) := by
                  have hπx :
                      S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat x) = ψ₂ U x := by
                    simpa [Function.comp] using
                      congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) x
                  have hπy :
                      S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat y) = ψ₂ U y := by
                    simpa [Function.comp] using
                      congrFun (S₂.projection_comp_inverseLimitLift ψ₂ hψ₂compat U) y
                  rw [← hπx, ← hπy] }
      continuous_toFun := S₂.continuous_inverseLimitLift ψ₂ hψ₂cont hψ₂compat }
  have hfToInv_surj : Function.Surjective (S₂.inverseLimitLift ψ₂ hψ₂compat) :=
    S₂.surjective_inverseLimitLift ψ₂ hψ₂cont hψ₂compat hψ₂surj hdir₂
  let e₂ : G₂ ≃ₜ* S₂.inverseLimit :=
    ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := G₂)
      FiniteGroupClass.allFinite_formation hG₂proC
  let e₂symmHom : ContinuousMonoidHom S₂.inverseLimit G₂ :=
    { toMonoidHom := e₂.symm.toMonoidHom
      continuous_toFun := e₂.symm.continuous_toFun }
  refine ⟨e₂symmHom.comp fToInv, ?_⟩
  intro y
  rcases hfToInv_surj (e₂ y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change e₂.symm (S₂.inverseLimitLift ψ₂ hψ₂compat x) = y
  rw [hx]
  exact e₂.symm_apply_apply y

/-- Topologically finitely generated profinite groups are determined by their continuous finite
discrete quotients. -/
theorem topologicallyFinitelyGenerated_profiniteGroups_iso_of_sameContinuousFiniteQuotients
    {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {G₂ : Type u} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [CompactSpace G₁] [T2Space G₁] [TotallyDisconnectedSpace G₁]
    [CompactSpace G₂] [T2Space G₂] [TotallyDisconnectedSpace G₂]
    (hfg₁ : FiniteGeneration.TopologicallyFinitelyGenerated G₁)
    (hfg₂ : FiniteGeneration.TopologicallyFinitelyGenerated G₂)
    (hquot : HasSameContinuousFiniteDiscreteQuotients G₁ G₂) :
    Nonempty (G₁ ≃ₜ* G₂) := by
  classical
  rcases exists_surj_continuousMonoidHom_between_profiniteGroups_of_sameContinuousFiniteDiscreteQuotients
      (G₁ := G₁) (G₂ := G₂) hfg₁ hquot with ⟨φ, hφsurj⟩
  have hquot_symm : HasSameContinuousFiniteDiscreteQuotients G₂ G₁ := by
    intro Q _ _ _ _ _
    exact (hquot Q).symm
  rcases exists_surj_continuousMonoidHom_between_profiniteGroups_of_sameContinuousFiniteDiscreteQuotients
      (G₁ := G₂) (G₂ := G₁) hfg₂ hquot_symm with ⟨ψ, hψsurj⟩
  let ψφ : ContinuousMonoidHom G₁ G₁ := ψ.comp φ
  have hψφsurj : Function.Surjective ψφ := by
    simpa [ψφ] using hψsurj.comp hφsurj
  rcases (FiniteGeneration.surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
    (G := G₁) hfg₁ ψφ hψφsurj) with ⟨e, he⟩
  have hψφinj : Function.Injective ψφ := by
    intro x y hxy
    apply e.injective
    calc
      e x = ψφ x := he x
      _ = ψφ y := hxy
      _ = e y := (he y).symm
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hψφinj
    change ψ (φ x) = ψ (φ y)
    exact congrArg ψ hxy
  exact ⟨ContinuousMulEquiv.ofBijectiveCompactToT2
    φ.toMonoidHom φ.continuous_toFun ⟨hφinj, hφsurj⟩⟩

/-- Topologically finitely generated profinite groups are determined by abstract finite
quotients, provided strong completeness identifies abstract finite quotients with continuous
finite discrete quotients. -/
theorem profiniteGroups_iso_of_sameAbstractFiniteQuotients_of_stronglyComplete
    {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {G₂ : Type u} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [CompactSpace G₁] [T2Space G₁] [TotallyDisconnectedSpace G₁]
    [CompactSpace G₂] [T2Space G₂] [TotallyDisconnectedSpace G₂]
    [StronglyCompleteForFiniteDiscreteQuotients G₁]
    [StronglyCompleteForFiniteDiscreteQuotients G₂]
    (hfg₁ : FiniteGeneration.TopologicallyFinitelyGenerated G₁)
    (hfg₂ : FiniteGeneration.TopologicallyFinitelyGenerated G₂)
    (hquot : HasSameFiniteQuotients G₁ G₂) :
    Nonempty (G₁ ≃ₜ* G₂) := by
  apply topologicallyFinitelyGenerated_profiniteGroups_iso_of_sameContinuousFiniteQuotients
    (G₁ := G₁) (G₂ := G₂) hfg₁ hfg₂
  intro Q _ _ _ _ _
  constructor
  · rintro ⟨φ, hφsurj⟩
    rcases (hquot Q).1 ⟨φ.toMonoidHom, hφsurj⟩ with ⟨ψ, hψsurj⟩
    exact
      ⟨{ toMonoidHom := ψ
         continuous_toFun :=
          StronglyCompleteForFiniteDiscreteQuotients.continuous_of_surjective ψ hψsurj },
        hψsurj⟩
  · rintro ⟨ψ, hψsurj⟩
    rcases (hquot Q).2 ⟨ψ.toMonoidHom, hψsurj⟩ with ⟨φ, hφsurj⟩
    exact
      ⟨{ toMonoidHom := φ
         continuous_toFun :=
          StronglyCompleteForFiniteDiscreteQuotients.continuous_of_surjective φ hφsurj },
        hφsurj⟩

end ProCGroups.Completion
