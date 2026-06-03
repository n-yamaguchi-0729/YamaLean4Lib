import ProCGroups.Completion.UniversalProperty
import ProCGroups.ProC.GroupPredicates.Basic
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Completion/FiniteQuotientLifts.lean
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

/-- Unique lifting property against finite discrete `C`-quotients of the source. -/
def HasUniqueFiniteDiscreteQuotientLifts
    (C : ProCGroups.FiniteGroupClass.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Ghat : Type u} [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
    (ι : G →ₜ* Ghat) : Prop :=
  ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q],
    C Q →
    ∀ φ : G →ₜ* Q,
      ∃! φbar : Ghat →ₜ* Q, φbar.comp ι = φ

/-- A compatible family of continuous homomorphisms to finite stages assembles to a continuous
homomorphism to the inverse limit. -/
noncomputable def lift_to_inverseLimit_of_compatible_finite_lifts
    {I : Type u} [Preorder I]
    (S : ProCGroups.InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    {A : Type u} [Group A] [TopologicalSpace A]
    (φ : ∀ i, A →ₜ* S.X i)
    (hcompat : S.CompatibleMaps (fun i => φ i)) :
    A →ₜ* S.inverseLimit :=
  { toMonoidHom :=
      { toFun := S.inverseLimitLift (fun i => φ i) hcompat
        map_one' := by
          apply S.ext
          intro i
          calc
            S.projection i (S.inverseLimitLift (fun i => φ i) hcompat 1) = φ i 1 := by
              simpa [Function.comp] using
                congrFun (S.projection_comp_inverseLimitLift (fun i => φ i) hcompat i) (1 : A)
            _ = 1 := by simp only [map_one]
        map_mul' := by
          intro x y
          apply S.ext
          intro i
          calc
            S.projection i (S.inverseLimitLift (fun i => φ i) hcompat (x * y)) = φ i (x * y) := by
              simpa [Function.comp] using
                congrFun (S.projection_comp_inverseLimitLift (fun i => φ i) hcompat i) (x * y)
            _ = φ i x * φ i y := by simp only [map_mul]
            _ =
                S.projection i (S.inverseLimitLift (fun i => φ i) hcompat x) *
                  S.projection i (S.inverseLimitLift (fun i => φ i) hcompat y) := by
              have hx :
                  S.projection i (S.inverseLimitLift (fun i => φ i) hcompat x) = φ i x := by
                simpa [Function.comp] using
                  congrFun (S.projection_comp_inverseLimitLift (fun i => φ i) hcompat i) x
              have hy :
                  S.projection i (S.inverseLimitLift (fun i => φ i) hcompat y) = φ i y := by
                simpa [Function.comp] using
                  congrFun (S.projection_comp_inverseLimitLift (fun i => φ i) hcompat i) y
              rw [← hx, ← hy] }
    continuous_toFun := S.continuous_inverseLimitLift (fun i => φ i) (fun i => (φ i).continuous_toFun)
      hcompat }

/-- A dense map from a discrete group into a pro-`C` group is a pro-`C` completion as soon as
every finite discrete `C`-quotient of the source lifts uniquely and continuously across it. -/
theorem isProCCompletion_of_finiteQuotientLifts
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G]
    {Ghat : Type u} [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
    (hGhat : ProCGroups.ProC.IsProCGroup C Ghat)
    {ι : G →ₜ* Ghat}
    (hιdense : DenseRange ι)
    (hfinite :
      ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
        [Finite Q] [DiscreteTopology Q],
        C Q →
        ∀ φ : G →ₜ* Q,
          ∃! φbar : Ghat →ₜ* Q, φbar.comp ι = φ) :
    IsProCCompletion
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) G Ghat ι := by
  refine
    { isProC := by simpa using hGhat
      denseRange := hιdense
      existsUnique_lift := ?_ }
  intro H _ _ _ hH ψ
  let hHproC : ProCGroups.ProC.IsProCGroup C H := by
    simpa using hH
  let S := ProCGroups.ProC.openNormalSubgroupInClassSystem C H
  letI : Nonempty (ProCGroups.ProC.OpenNormalSubgroupInClass C H) :=
    ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClass_nonempty hHproC
  letI : Nonempty (OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H)) := inferInstance
  letI :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        Group (S.X U) := fun U => by
    dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
    infer_instance
  letI : ProCGroups.InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  letI :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        IsTopologicalGroup (S.X U) := fun U => by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      infer_instance
  letI :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        Finite (S.X U) := fun U => by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      exact hForm.finiteOnly (OrderDual.ofDual U).2
  letI :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        DiscreteTopology (S.X U) := fun U => by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := H) (OrderDual.ofDual U).1)
  letI : CompactSpace H := ProCGroups.ProC.IsProCGroup.compactSpace hHproC
  letI : T2Space H := ProCGroups.ProC.IsProCGroup.t2Space hHproC
  letI :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        T2Space (S.X U) := fun _ => by infer_instance
  letI : Group S.inverseLimit := by infer_instance
  letI : T2Space S.inverseLimit := S.t2Space_inverseLimit
  let q :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), H →ₜ* S.X U := fun U =>
    { toMonoidHom := ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := H) U
      continuous_toFun := continuous_quotient_mk' }
  let qFun :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), H → S.X U := fun U => q U
  have hqCompat : S.CompatibleMaps qFun := by
    simpa [q, qFun, S] using
      (ProCGroups.ProC.openNormalSubgroupInClassProj_compatible (C := C) (G := H))
  let ψcoord :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), Ghat →ₜ* S.X U := fun U =>
    Classical.choose (hfinite (OrderDual.ofDual U).2 ((q U).comp ψ))
  let ψcoordFun :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), Ghat → S.X U := fun U =>
    ψcoord U
  have hψcoordSpec :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        (ψcoord U).comp ι = (q U).comp ψ := by
    intro U
    exact (Classical.choose_spec (hfinite (OrderDual.ofDual U).2 ((q U).comp ψ))).1
  have hψcoordUnique :
      ∀ (U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H))
        (φbar : Ghat →ₜ* S.X U),
        φbar.comp ι = (q U).comp ψ →
          φbar = ψcoord U := by
    intro U φbar hφbar
    exact (Classical.choose_spec (hfinite (OrderDual.ofDual U).2 ((q U).comp ψ))).2 φbar hφbar
  have hψcoordCompat : S.CompatibleMaps ψcoordFun := by
    intro U V hUV
    have hUV' : ((OrderDual.ofDual V).1 : Subgroup H) ≤ (OrderDual.ofDual U).1 := hUV
    let qUV : S.X V →ₜ* S.X U :=
      { toMonoidHom := by
          dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
          exact ProCGroups.ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := H) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
        continuous_toFun := S.continuous_map hUV }
    have hEqHom : qUV.comp (ψcoord V) = ψcoord U := by
      exact hψcoordUnique U (qUV.comp (ψcoord V)) <| by
        apply ContinuousMonoidHom.toMonoidHom_injective
        ext g
        have hqg :
            qUV ((q V) (ψ g)) = (q U) (ψ g) := by
          simpa [q, S] using
            congrFun
              (ProCGroups.ProC.openNormalSubgroupInClassProj_compatible (C := C) (G := H) U V hUV)
              (ψ g)
        calc
          ((qUV.comp (ψcoord V)).comp ι) g = qUV (ψcoord V (ι g)) := rfl
          _ = qUV ((q V) (ψ g)) := by
            exact congrArg qUV (congrArg (fun f : G →ₜ* S.X V => f g) (hψcoordSpec V))
          _ = (q U) (ψ g) := hqg
          _ = ((q U).comp ψ) g := rfl
    funext x
    exact congrArg (fun f : Ghat →ₜ* S.X U => f x) hEqHom
  let ψInv : Ghat →ₜ* S.inverseLimit :=
    lift_to_inverseLimit_of_compatible_finite_lifts S ψcoord hψcoordCompat
  let eH : H ≃ₜ* S.inverseLimit :=
    ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := H) hForm hHproC
  have hπeH :
      ∀ (U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H)) (h : H),
        S.projection U (eH h) = (q U) h := by
    intro U h
    simpa [eH, q, S, ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit]
      using congrFun (S.projection_comp_inverseLimitLift qFun hqCompat U) h
  let ψbar : Ghat →ₜ* H :=
    { toMonoidHom := eH.symm.toMonoidHom.comp ψInv.toMonoidHom
      continuous_toFun := eH.symm.continuous_toFun.comp ψInv.continuous_toFun }
  have hψbarComp : eH.toMonoidHom.comp ψbar.toMonoidHom = ψInv.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply S.ext
    intro U
    exact congrArg (fun z : S.inverseLimit => S.projection U z) (eH.apply_symm_apply (ψInv x))
  have hψbarFac : ψbar.comp ι = ψ := by
    apply ContinuousMonoidHom.toMonoidHom_injective
    ext g
    apply eH.injective
    apply S.ext
    intro U
    calc
      S.projection U (eH (ψbar (ι g))) = S.projection U (ψInv (ι g)) := by
        exact congrArg (fun z : S.inverseLimit => S.projection U z)
          (congrArg (fun f : Ghat →* S.inverseLimit => f (ι g)) hψbarComp)
      _ = ψcoord U (ι g) := by
        simpa [ψcoordFun, Function.comp] using
          congrFun (S.projection_comp_inverseLimitLift ψcoordFun hψcoordCompat U) (ι g)
      _ = (q U) (ψ g) := by
        exact congrArg (fun f : G →ₜ* S.X U => f g) (hψcoordSpec U)
      _ = S.projection U (eH (ψ g)) := by
        symm
        exact hπeH U (ψ g)
  refine ⟨ψbar, hψbarFac, ?_⟩
  intro χ hχ
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro x
  have hEqFun : (fun z : Ghat => χ z) = fun z : Ghat => ψbar z := by
    apply DenseRange.equalizer (f := ι) hιdense
    · exact χ.continuous_toFun
    · exact ψbar.continuous_toFun
    · funext g
      exact congrArg (fun f : G →ₜ* H => f g) (hχ.trans hψbarFac.symm)
  exact congrArg (fun f : Ghat → H => f x) hEqFun

/-- Finite discrete quotient lifts extend uniquely to any pro-`C` target. -/
theorem finiteQuotientLifts_extend_to_proC_target
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G]
    {Ghat : Type u} [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
    (hGhat : ProCGroups.ProC.IsProCGroup C Ghat)
    {ι : G →ₜ* Ghat}
    (hιdense : DenseRange ι)
    (hfinite :
      ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
        [Finite Q] [DiscreteTopology Q],
        C Q →
        ∀ φ : G →ₜ* Q,
          ∃! φbar : Ghat →ₜ* Q, φbar.comp ι = φ)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hH : ProCGroups.ProC.finiteGroupClassProCPredicate C (G := H))
    (ψ : G →ₜ* H) :
    ∃! ψbar : Ghat →ₜ* H, ψbar.comp ι = ψ :=
  (isProCCompletion_of_finiteQuotientLifts
    (C := C) hForm hGhat hιdense hfinite).existsUnique_lift hH ψ

/-- Name exposing the exact strength of the finite discrete quotient lifting hypothesis. -/
theorem isProCCompletion_of_finiteDiscreteQuotientLifts
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G]
    {Ghat : Type u} [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
    (hGhat : ProCGroups.ProC.IsProCGroup C Ghat)
    {ι : G →ₜ* Ghat}
    (hιdense : DenseRange ι)
    (hfinite : HasUniqueFiniteDiscreteQuotientLifts C (G := G) (Ghat := Ghat) ι) :
    IsProCCompletion
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) G Ghat ι :=
  isProCCompletion_of_finiteQuotientLifts
    (C := C) hForm hGhat hιdense hfinite

end ProCGroups.Completion
