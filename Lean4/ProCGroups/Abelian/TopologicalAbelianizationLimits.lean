import ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import ProCGroups.InverseSystems.Quotients
import ProCGroups.InverseSystems.StagewiseIso
import ProCGroups.ProC.Quotients.ClosedNormal

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Abelian/TopologicalAbelianizationLimits.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topological abelianization and inverse limits

Strong inverse-limit API for topological abelianization of profinite inverse systems.
-/

open scoped Topology

namespace ProCGroups.Abelian

universe u v
/-- The stagewise inverse system obtained by applying topological abelianization. -/
noncomputable def abelianizationInverseSystem
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    InverseSystems.InverseSystem (I := I) where
  X := fun i => TopologicalAbelianization (S.X i)
  topologicalSpace := fun i => inferInstance
  map := fun {i j} hij =>
    TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }
  continuous_map := by
    intro i j hij
    exact (TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }).continuous_toFun
  map_id := by
    intro i
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map (le_rfl : i ≤ i) a) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          a
    exact congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.map_id_apply i a)
  map_comp := by
    intro i j k hij hjk
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map hij (S.map hjk a)) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map (hij.trans hjk) a)
    exact congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.map_comp_apply hij hjk a)

/-- Each stage of the abelianization inverse system inherits its quotient group structure. -/
instance abelianizationInverseSystem_stageGroup
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] (i : I) :
    Group ((abelianizationInverseSystem S).X i) := by
  change Group (TopologicalAbelianization (S.X i))
  infer_instance

/-- The abelianization inverse system is a group-valued inverse system. -/
instance abelianizationInverseSystem_isGroupSystem
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    InverseSystems.IsGroupSystem (abelianizationInverseSystem S) where
  map_one := by
    intro i j hij
    simp only [abelianizationInverseSystem, Lean.Elab.WF.paramLet, map_one]
  map_mul := by
    intro i j hij x y
    simp only [abelianizationInverseSystem, Lean.Elab.WF.paramLet, map_mul]
  map_inv := by
    intro i j hij x
    exact (TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }).map_inv x

/-- The stagewise quotient maps assemble into a morphism from an inverse system to its
stagewise topological abelianization. -/
def toAbelianizationInverseSystem
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    S.Morphism (abelianizationInverseSystem S) where
  map := fun i => TopologicalAbelianization.mk (S.X i)
  continuous_map := fun _ => continuous_quotient_mk'
  comm := by
    intro i j hij
    funext x
    rfl

/-- The stagewise closed commutator subgroups form a compatible closed-normal family in any
group-valued inverse system of topological groups. -/
noncomputable def closedCommutatorCompatibleClosedNormalSubgroups
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    S.CompatibleClosedNormalSubgroups where
  N := fun i => Subgroup.closedCommutator (S.X i)
  normal := fun i => by infer_instance
  closed := fun i => Subgroup.isClosed_closedCommutator (S.X i)
  map_le := by
    intro i j hij x hx
    let f : S.X j →ₜ* S.X i :=
      { toMonoidHom := S.transitionHom hij
        continuous_toFun :=
          InverseSystems.InverseSystem.continuous_transitionHom (S := S) hij }
    have hxmap :
        S.transitionHom hij x ∈
          (Subgroup.closedCommutator (S.X j)).map f.toMonoidHom :=
      Subgroup.mem_map_of_mem f.toMonoidHom hx
    exact Subgroup.closedCommutator_map_le f hxmap

/-- The canonical comparison map from the abelianization of an inverse limit to the inverse limit
of the stagewise abelianizations. -/
noncomputable def topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    TopologicalAbelianization S.inverseLimit →ₜ*
      (abelianizationInverseSystem S).inverseLimit := by
  let T := abelianizationInverseSystem S
  let ψ : ∀ i, TopologicalAbelianization S.inverseLimit →ₜ* T.X i := fun i =>
    TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.projection i
            map_one' := rfl
            map_mul' := by intro x y; rfl }
        continuous_toFun := S.continuous_projection i }
  let ψFun : ∀ i, TopologicalAbelianization S.inverseLimit → T.X i := fun i => ψ i
  have hψ : ∀ i, Continuous (ψFun i) := by
    intro i
    exact (ψ i).continuous_toFun
  have hcompat : T.CompatibleMaps ψFun := by
    intro i j hij
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map hij (S.projection j a)) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.projection i a)
    simpa using congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.projection_compatible a i j hij)
  refine
    { toMonoidHom :=
        { toFun := T.inverseLimitLift ψFun hcompat
          map_one' := by
            apply T.ext
            intro i
            change ψFun i 1 = 1
            exact (ψ i).map_one
          map_mul' := by
            intro x y
            apply T.ext
            intro i
            change ψFun i (x * y) = ψFun i x * ψFun i y
            exact (ψ i).map_mul x y }
      continuous_toFun := T.continuous_inverseLimitLift ψFun hψ hcompat }

/-- The `i`th projection of the canonical comparison map is the abelianization of the `i`th limit
projection. -/
@[simp 900] theorem π_topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    (i : I) :
    (abelianizationInverseSystem S).projection i ∘
        topologicalAbelianizationInverseLimitComparison S =
      TopologicalAbelianization.map
        { toMonoidHom :=
            { toFun := S.projection i
              map_one' := rfl
              map_mul' := by intro x y; rfl }
          continuous_toFun := S.continuous_projection i } := by
  let T := abelianizationInverseSystem S
  let ψ : ∀ i, TopologicalAbelianization S.inverseLimit →ₜ* T.X i := fun i =>
    TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.projection i
            map_one' := rfl
            map_mul' := by intro x y; rfl }
        continuous_toFun := S.continuous_projection i }
  let ψFun : ∀ i, TopologicalAbelianization S.inverseLimit → T.X i := fun i => ψ i
  have hcompat : T.CompatibleMaps ψFun := by
    intro i j hij
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map hij (S.projection j a)) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.projection i a)
    simpa using congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.projection_compatible a i j hij)
  funext x
  change T.projection i (T.inverseLimitLift ψFun hcompat x) = ψFun i x
  rfl

/-- Evaluation of the canonical comparison map on a representative of the inverse limit. -/
@[simp 900] theorem π_topologicalAbelianizationInverseLimitComparison_mk
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    (i : I) (x : S.inverseLimit) :
    (abelianizationInverseSystem S).projection i
        (topologicalAbelianizationInverseLimitComparison S
          (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator S.inverseLimit)) x)) =
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))) (S.projection i x) := by
  simpa [Function.comp] using
    congrFun (π_topologicalAbelianizationInverseLimitComparison (S := S) i)
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator S.inverseLimit)) x)

/-- The induced map on inverse limits from the stagewise quotient morphism is the composite of the
limit quotient map with the canonical comparison map. -/
@[simp 900] theorem limMap_toAbelianizationInverseSystem_apply
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    (x : S.inverseLimit) :
    S.limMap (toAbelianizationInverseSystem S) x =
      topologicalAbelianizationInverseLimitComparison S
        (TopologicalAbelianization.mk S.inverseLimit x) := by
  apply (abelianizationInverseSystem S).ext
  intro i
  calc
    (abelianizationInverseSystem S).projection i (S.limMap (toAbelianizationInverseSystem S) x)
        = (toAbelianizationInverseSystem S).map i (S.projection i x) := by
            simpa [Function.comp] using
              congrFun
                (InverseSystems.InverseSystem.π_comp_limMap
                  (S := S) (Θ := toAbelianizationInverseSystem S) i)
                x
    _ = QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))) (S.projection i x) := rfl
    _ = (abelianizationInverseSystem S).projection i
          (topologicalAbelianizationInverseLimitComparison S
            (TopologicalAbelianization.mk S.inverseLimit x)) := by
            symm
            exact π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x

/-- Proof-level injectivity of the canonical comparison map, used to build the continuous
equivalence.  The public API is `injective_topologicalAbelianizationInverseLimitComparison`. -/
private theorem inj_topologicalAbelianizationInverseLimitComparison_of_profinite_inverse_system
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Injective (topologicalAbelianizationInverseLimitComparison S) := by
  let f := topologicalAbelianizationInverseLimitComparison S
  letI : CompactSpace S.inverseLimit := inferInstance
  letI : T2Space S.inverseLimit := S.t2Space_inverseLimit
  letI : TotallyDisconnectedSpace S.inverseLimit := S.totallyDisconnectedSpace_inverseLimit
  let hProfInv : IsProfiniteGroup S.inverseLimit :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  let hProfAb : IsProfiniteGroup (TopologicalAbelianization S.inverseLimit) :=
    ProCGroups.Generation.isProfinite_quotient_closedNormal
      (G := S.inverseLimit) hProfInv
      (N := Subgroup.topologicalClosure (commutator S.inverseLimit))
      (Subgroup.isClosed_topologicalClosure (s := commutator S.inverseLimit))
  letI : CompactSpace (TopologicalAbelianization S.inverseLimit) :=
    IsProfiniteGroup.compactSpace hProfAb
  letI : T2Space (TopologicalAbelianization S.inverseLimit) :=
    IsProfiniteGroup.t2Space hProfAb
  letI : TotallyDisconnectedSpace (TopologicalAbelianization S.inverseLimit) :=
    IsProfiniteGroup.totallyDisconnectedSpace hProfAb
  have hkerbot : f.toMonoidHom.ker = ⊥ := by
    ext a
    constructor
    · intro ha
      by_contra hane
      rcases ProCGroups.ProC.exists_openNormalSubgroup_not_mem
          (G := TopologicalAbelianization S.inverseLimit) hProfAb (x := a) hane with ⟨U, haU⟩
      let Q := TopologicalAbelianization S.inverseLimit ⧸
        (U : Subgroup (TopologicalAbelianization S.inverseLimit))
      letI : Finite Q := openNormalSubgroup_finiteQuotient
        (G := TopologicalAbelianization S.inverseLimit) U
      letI : DiscreteTopology Q :=
        QuotientGroup.discreteTopology
          (openNormalSubgroup_isOpen (G := TopologicalAbelianization S.inverseLimit) U)
      let qInv : S.inverseLimit →ₜ* TopologicalAbelianization S.inverseLimit :=
        { toMonoidHom := TopologicalAbelianization.mk S.inverseLimit
          continuous_toFun := continuous_quotient_mk' }
      let β : S.inverseLimit →ₜ* Q :=
        { toMonoidHom :=
            (QuotientGroup.mk' (U : Subgroup (TopologicalAbelianization S.inverseLimit))).comp
              qInv.toMonoidHom
          continuous_toFun := continuous_quotient_mk'.comp qInv.continuous_toFun
        }
      rcases InverseSystems.InverseSystem.factors_through_projection_finite_group_hom
          (S := S) hdir β.toMonoidHom β.continuous_toFun with ⟨i, βi, hβi_continuous, hβfac⟩
      let βiCont : S.X i →ₜ* Q :=
        { toMonoidHom := βi
          continuous_toFun := hβi_continuous }
      have hq : QuotientGroup.mk' (U : Subgroup (TopologicalAbelianization S.inverseLimit)) a = 1 := by
        rcases QuotientGroup.mk'_surjective
            (Subgroup.topologicalClosure (commutator S.inverseLimit)) a with ⟨x, rfl⟩
        calc
          QuotientGroup.mk'
              (U : Subgroup (TopologicalAbelianization S.inverseLimit))
              (TopologicalAbelianization.mk S.inverseLimit x)
              = β x := rfl
          _ = βi (S.projection i x) := by
            simpa [Function.comp] using
              congrArg
                (fun g : S.inverseLimit → Q => g x)
                hβfac
          _ = TopologicalAbelianization.lift βiCont
                (TopologicalAbelianization.mk (S.X i) (S.projection i x)) := by
              symm
              exact TopologicalAbelianization.lift_apply_mk βiCont (S.projection i x)
            _ = TopologicalAbelianization.lift βiCont
                  ((abelianizationInverseSystem S).projection i
                    (topologicalAbelianizationInverseLimitComparison S
                      (TopologicalAbelianization.mk S.inverseLimit x))) := by
                simpa [TopologicalAbelianization.mk] using
                  congrArg (TopologicalAbelianization.lift βiCont)
                    (π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x).symm
          _ = TopologicalAbelianization.lift βiCont
                ((abelianizationInverseSystem S).projection i 1) := by
              rw [show topologicalAbelianizationInverseLimitComparison S
                    (TopologicalAbelianization.mk S.inverseLimit x) = 1 by
                    simpa [MonoidHom.mem_ker, f] using ha]
          _ = TopologicalAbelianization.lift βiCont (1 : TopologicalAbelianization (S.X i)) := by
              rfl
          _ = 1 := by simp only [map_one]
      exact haU <| (QuotientGroup.eq_one_iff
        (N := (U : Subgroup (TopologicalAbelianization S.inverseLimit))) a).1 hq
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [MonoidHom.mem_ker]
      simp only [ContinuousMonoidHom.coe_toMonoidHom, hx, map_one]
  exact (MonoidHom.ker_eq_bot_iff (f := f.toMonoidHom)).mp hkerbot

/-- Membership in the closed commutator subgroup of a profinite inverse limit is detected
coordinatewise. -/
theorem mem_closedCommutator_inverseLimit_iff
      {I : Type u} [Preorder I] [Nonempty I]
      (S : InverseSystems.InverseSystem (I := I))
      [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
      [∀ i, IsTopologicalGroup (S.X i)]
      [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
      [∀ i, TotallyDisconnectedSpace (S.X i)]
      (hdir : Directed (· ≤ ·) (id : I → I)) {x : S.inverseLimit} :
      x ∈ Subgroup.closedCommutator S.inverseLimit ↔
        ∀ i, S.projection i x ∈ Subgroup.closedCommutator (S.X i) := by
    constructor
    · intro hx i
      have hxmk :
          TopologicalAbelianization.mk S.inverseLimit x = 1 :=
        (TopologicalAbelianization.mk_eq_one_iff (G := S.inverseLimit) (x := x)).2 hx
      have hcoord :=
        π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x
      have hcoord' :
          (abelianizationInverseSystem S).projection i
              ((topologicalAbelianizationInverseLimitComparison S)
                (TopologicalAbelianization.mk S.inverseLimit x)) =
            TopologicalAbelianization.mk (S.X i) (S.projection i x) := by
        simpa [TopologicalAbelianization.mk] using hcoord
      rw [hxmk] at hcoord'
      have hmk :
          TopologicalAbelianization.mk (S.X i) (S.projection i x) = 1 := by
        simpa using hcoord'.symm
      exact (TopologicalAbelianization.mk_eq_one_iff
        (G := S.X i) (x := S.projection i x)).1 hmk
    · intro hxcoord
      let f := topologicalAbelianizationInverseLimitComparison S
      have hf :
          f (TopologicalAbelianization.mk S.inverseLimit x) = 1 := by
        apply (abelianizationInverseSystem S).ext
        intro i
        have hmk :
            TopologicalAbelianization.mk (S.X i) (S.projection i x) = 1 :=
          (TopologicalAbelianization.mk_eq_one_iff
            (G := S.X i) (x := S.projection i x)).2 (hxcoord i)
        simpa [f, TopologicalAbelianization.mk] using
          (π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x).trans hmk
      have hxmk :
          TopologicalAbelianization.mk S.inverseLimit x = 1 := by
        apply inj_topologicalAbelianizationInverseLimitComparison_of_profinite_inverse_system (S := S) hdir
        simpa [f] using hf
      exact (TopologicalAbelianization.mk_eq_one_iff (G := S.inverseLimit) (x := x)).1 hxmk

/-- The closed commutator subgroup of a profinite inverse limit is the infimum of the
pullbacks of the stagewise closed commutator subgroups. -/
theorem closedCommutator_inverseLimit_eq_iInf_comap
      {I : Type u} [Preorder I] [Nonempty I]
      (S : InverseSystems.InverseSystem (I := I))
      [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
      [∀ i, IsTopologicalGroup (S.X i)]
      [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
      [∀ i, TotallyDisconnectedSpace (S.X i)]
      (hdir : Directed (· ≤ ·) (id : I → I)) :
      Subgroup.closedCommutator S.inverseLimit =
        ⨅ i, (Subgroup.closedCommutator (S.X i)).comap
          ({ toFun := S.projection i
             map_one' := rfl
             map_mul' := by intro x y; rfl } : S.inverseLimit →* S.X i) := by
    ext x
    rw [mem_closedCommutator_inverseLimit_iff (S := S) hdir (x := x)]
    simp only [InverseSystems.InverseSystem.projection_apply, Subgroup.mem_iInf, Subgroup.mem_comap,
  MonoidHom.coe_mk, OneHom.coe_mk]

/-- For the closed-commutator compatible family, the generic quotient-limit kernel is the closed
commutator subgroup of the inverse limit. -/
theorem closedCommutatorCompatibleClosedNormalSubgroups_inverseLimitKernel
      {I : Type u} [Preorder I] [Nonempty I]
      (S : InverseSystems.InverseSystem (I := I))
      [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
      [∀ i, IsTopologicalGroup (S.X i)]
      [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
      [∀ i, TotallyDisconnectedSpace (S.X i)]
      (hdir : Directed (· ≤ ·) (id : I → I)) :
      (closedCommutatorCompatibleClosedNormalSubgroups S).inverseLimitKernel =
        Subgroup.closedCommutator S.inverseLimit := by
  symm
  simpa [closedCommutatorCompatibleClosedNormalSubgroups,
    InverseSystems.InverseSystem.CompatibleClosedNormalSubgroups.inverseLimitKernel,
    InverseSystems.projectionHom]
    using closedCommutator_inverseLimit_eq_iInf_comap (S := S) hdir

/-- The generic quotient inverse-limit theorem specialized to the closed commutator family. -/
noncomputable def closedCommutatorQuotientInverseLimitContinuousMulEquiv
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    TopologicalAbelianization S.inverseLimit ≃ₜ*
      (closedCommutatorCompatibleClosedNormalSubgroups S).quotientInverseSystem.inverseLimit := by
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  have hkernel :
      (Subgroup.closedCommutator S.inverseLimit).map
          (ContinuousMulEquiv.refl S.inverseLimit).toMulEquiv.toMonoidHom =
        Q.inverseLimitKernel := by
    rw [closedCommutatorCompatibleClosedNormalSubgroups_inverseLimitKernel (S := S) hdir]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      simpa using hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact (QuotientGroup.congrₜ
    (Subgroup.closedCommutator S.inverseLimit) Q.inverseLimitKernel
    (ContinuousMulEquiv.refl S.inverseLimit) hkernel).trans
      (Q.quotientInverseLimitContinuousMulEquiv hdir)

@[simp 900] theorem projection_closedCommutatorQuotientInverseLimitContinuousMulEquiv_mk
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (i : I) (x : S.inverseLimit) :
    (closedCommutatorCompatibleClosedNormalSubgroups S).quotientInverseSystem.projection i
        (closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir
          (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x)) =
      QuotientGroup.mk'
        ((closedCommutatorCompatibleClosedNormalSubgroups S).N i)
        (S.projection i x) := by
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  unfold closedCommutatorQuotientInverseLimitContinuousMulEquiv
  dsimp
  change Q.quotientInverseSystem.projection i
      (Q.quotientInverseLimitContinuousMulEquiv hdir
        (QuotientGroup.mk' Q.inverseLimitKernel x)) =
    QuotientGroup.mk' (Q.N i) (S.projection i x)
  unfold InverseSystems.InverseSystem.CompatibleClosedNormalSubgroups.quotientInverseLimitContinuousMulEquiv
  change Q.quotientInverseSystem.projection i
      (Q.quotientInverseLimitComparison (QuotientGroup.mk' Q.inverseLimitKernel x)) =
    QuotientGroup.mk' (Q.N i) (S.projection i x)
  exact Q.projection_quotientInverseLimitComparison_mk i x

/-- Topological abelianization commutes with profinite inverse limits as a topological-group
isomorphism. -/
noncomputable def topologicalAbelianizationInverseLimitContinuousMulEquiv
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    TopologicalAbelianization S.inverseLimit ≃ₜ*
      (abelianizationInverseSystem S).inverseLimit := by
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  let E : InverseSystems.InverseSystem.InverseSystemIso Q.quotientInverseSystem
      (abelianizationInverseSystem S) :=
    { stageEquiv := fun _ => ContinuousMulEquiv.refl _
      comm := by intro i j hij x; rfl }
  exact (closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir).trans
    E.inverseLimitContinuousMulEquiv

@[simp 900] theorem topologicalAbelianizationInverseLimitContinuousMulEquiv_apply
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (x : TopologicalAbelianization S.inverseLimit) :
    topologicalAbelianizationInverseLimitContinuousMulEquiv (S := S) hdir x =
      topologicalAbelianizationInverseLimitComparison S x := by
  refine Quotient.inductionOn' x ?_
  intro g
  apply (abelianizationInverseSystem S).ext
  intro i
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  let E : InverseSystems.InverseSystem.InverseSystemIso Q.quotientInverseSystem
      (abelianizationInverseSystem S) :=
    { stageEquiv := fun _ => ContinuousMulEquiv.refl _
      comm := by intro i j hij x; rfl }
  change (abelianizationInverseSystem S).projection i
      (E.inverseLimitContinuousMulEquiv
        ((closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir)
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))) =
    (abelianizationInverseSystem S).projection i
      (topologicalAbelianizationInverseLimitComparison S
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))
  change (abelianizationInverseSystem S).projection i
      (Q.quotientInverseSystem.limMap E.toMorphism
        ((closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir)
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))) =
    (abelianizationInverseSystem S).projection i
      (topologicalAbelianizationInverseLimitComparison S
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))
  rw [Q.quotientInverseSystem.π_limMap_apply E.toMorphism i]
  change Q.quotientInverseSystem.projection i
      ((closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir)
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g)) =
    (abelianizationInverseSystem S).projection i
      (topologicalAbelianizationInverseLimitComparison S
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))
  rw [projection_closedCommutatorQuotientInverseLimitContinuousMulEquiv_mk]
  rw [π_topologicalAbelianizationInverseLimitComparison_mk]
  rfl

/-- The inverse-limit comparison is injective, as a corollary of the continuous equivalence. -/
theorem injective_topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Injective (topologicalAbelianizationInverseLimitComparison S) := by
  let e := topologicalAbelianizationInverseLimitContinuousMulEquiv (S := S) hdir
  intro x y hxy
  apply e.injective
  simpa [e] using hxy

/-- The inverse-limit comparison is surjective, as a corollary of the continuous equivalence. -/
theorem surjective_topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Surjective (topologicalAbelianizationInverseLimitComparison S) := by
  let e := topologicalAbelianizationInverseLimitContinuousMulEquiv (S := S) hdir
  intro y
  rcases e.surjective y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [e] using hx

end ProCGroups.Abelian
