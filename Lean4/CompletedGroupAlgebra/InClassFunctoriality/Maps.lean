import CompletedGroupAlgebra.InClassFunctoriality.StageMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/InClassFunctoriality/Maps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Functoriality of completed group algebras

The completed group algebra is presented as an inverse limit of finite group algebras, together with canonical augmentation, augmentation ideal, finite-stage maps, functoriality, and profinite module universal properties.
-/
open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism of groups induces a ring homomorphism on `C`-indexed completed
group algebras, when `C` is hereditary. -/
def completedGroupAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (φ : G →* H) (hφ : Continuous φ) :
    CompletedGroupAlgebraInClass C hC R G →+* CompletedGroupAlgebraInClass C hC R H where
  toFun x := ⟨fun V =>
      completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V
        (completedGroupAlgebraProjectionInClass C hC R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x), by
    intro V W hVW
    change completedGroupAlgebraTransitionInClass C R H hVW
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ W
          (completedGroupAlgebraProjectionInClass C hC R G
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ W) x)) =
      completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V
        (completedGroupAlgebraProjectionInClass C hC R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraFunctorialStageMapInClass_transition
          (R := R) (G := G) (H := H) C hHer φ hφ hVW))
      (completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ W) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
    rw [← completedGroupAlgebraProjectionInClass_compatible
      (R := R) (G := G) C hC
      (completedGroupAlgebraComapIndexInClass_mono
        (G := G) (H := H) C hHer φ hφ hVW) x]
    exact hcomp⟩
  map_zero' := by
    apply (completedGroupAlgebraSystemInClass C hC R H).ext
    intro V
    exact map_zero (completedGroupAlgebraFunctorialStageMapInClass
      (G := G) (H := H) C hHer (R := R) φ hφ V)
  map_one' := by
    apply (completedGroupAlgebraSystemInClass C hC R H).ext
    intro V
    exact map_one (completedGroupAlgebraFunctorialStageMapInClass
      (G := G) (H := H) C hHer (R := R) φ hφ V)
  map_add' x y := by
    apply (completedGroupAlgebraSystemInClass C hC R H).ext
    intro V
    exact map_add (completedGroupAlgebraFunctorialStageMapInClass
      (G := G) (H := H) C hHer (R := R) φ hφ V)
      (completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)
      (completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) y)
  map_mul' x y := by
    apply (completedGroupAlgebraSystemInClass C hC R H).ext
    intro V
    exact map_mul (completedGroupAlgebraFunctorialStageMapInClass
      (G := G) (H := H) C hHer (R := R) φ hφ V)
      (completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)
      (completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) y)

/-- The in-class completed group-algebra map is characterized by its finite-stage projections. -/
@[simp 900]
theorem completedGroupAlgebraProjectionInClass_map
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndexInClass H C) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjectionInClass C hC R H V
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x) =
      completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V
        (completedGroupAlgebraProjectionInClass C hC R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x) :=
  rfl

/-- Algebra form of `completedGroupAlgebraMapInClass`. -/
def completedGroupAlgebraMapAlgHomInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (φ : G →* H) (hφ : Continuous φ) :
    CompletedGroupAlgebraInClass C hC R G →ₐ[R] CompletedGroupAlgebraInClass C hC R H where
  toRingHom := completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
  commutes' := by
    intro r
    apply (completedGroupAlgebraSystemInClass C hC R H).ext
    intro V
    change completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V
        (algebraMap R
          (CompletedGroupAlgebraStageInClass C R G
            (completedGroupAlgebraComapIndexInClass
              (G := G) (H := H) C hHer φ hφ V)) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R H V) r
    exact completedGroupAlgebraFunctorialStageMapInClass_algebraMap
      (R := R) (G := G) (H := H) C hHer φ hφ V r

/-- The algebra-hom version of the in-class map has the same underlying function. -/
@[simp]
theorem completedGroupAlgebraMapAlgHomInClass_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hC hHer R φ hφ x =
      completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x :=
  rfl

/-- The induced `C`-indexed completed-group-algebra map is continuous. -/
theorem continuous_completedGroupAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    Continuous (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ) := by
  let A := CompletedGroupAlgebraInClass C hC R G
  let S := completedGroupAlgebraSystemInClass C hC R H
  letI : ∀ V : CompletedGroupAlgebraIndexInClass H C,
      TopologicalSpace (CompletedGroupAlgebraStageInClass C R H V) :=
    fun V => S.topologicalSpace V
  have hval : Continuous fun x : A =>
      ((completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x) :
        (V : CompletedGroupAlgebraIndexInClass H C) → S.X V) := by
    change Continuous fun x : A =>
      fun V : CompletedGroupAlgebraIndexInClass H C =>
        completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V
          (completedGroupAlgebraProjectionInClass C hC R G
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)
    apply continuous_pi
    intro V
    letI : TopologicalSpace
        (CompletedGroupAlgebraStageInClass C R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) :=
      (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)
    exact (continuous_completedGroupAlgebraFunctorialStageMapInClass
      (R := R) (G := G) (H := H) C hC hHer φ hφ V).comp
        ((completedGroupAlgebraSystemInClass C hC R G).continuous_projection
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V))
  exact Continuous.subtype_mk hval fun x =>
    (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x).2

/-- The in-class completed group-algebra map composes with the dense abstract map as expected. -/
theorem completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ).comp
        (toCompletedGroupAlgebraInClassRingHom C hC R G) =
      (toCompletedGroupAlgebraInClassRingHom C hC R H).comp
        (MonoidAlgebra.mapDomainRingHom R φ) := by
  apply RingHom.ext
  intro x
  apply (completedGroupAlgebraSystemInClass C hC R H).ext
  intro V
  have hstage := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraFunctorialStageMapInClass_comp_stageMap
        (R := R) (G := G) (H := H) C hHer φ hφ V))
    x
  change completedGroupAlgebraFunctorialStageMapInClass
      (G := G) (H := H) C hHer (R := R) φ hφ V
      (completedGroupAlgebraStageMapInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x) =
    completedGroupAlgebraStageMapInClass C R H V (MonoidAlgebra.mapDomainRingHom R φ x)
  exact hstage

/-- A surjective continuous homomorphism onto a pro-`C` group induces a surjective map on
`C`-indexed completed group algebras. -/
theorem completedGroupAlgebraMapInClass_surjective_of_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ) :
    Function.Surjective
      (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ) := by
  let f := completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
  letI : CompactSpace (CompletedGroupAlgebraInClass C hC R G) :=
    completedGroupAlgebraInClass_compactSpace (R := R) (G := G) C hC hR
  letI : T2Space (CompletedGroupAlgebraInClass C hC R H) :=
    completedGroupAlgebraInClass_t2Space (R := R) (G := H) C hC hR
  have hfcont : Continuous f :=
    continuous_completedGroupAlgebraMapInClass (R := R) (G := G) (H := H)
      C hC hHer φ hφ
  have hclosed : IsClosed (Set.range f) := (isCompact_range hfcont).isClosed
  have hdense : DenseRange (toCompletedGroupAlgebraInClassRingHom C hC R H) := by
    change DenseRange (toCompletedGroupAlgebraInClass C hC R H)
    exact denseRange_toCompletedGroupAlgebraInClass (R := R) (G := H) C hC hForm hH
  have hcanonical_subset :
      Set.range (toCompletedGroupAlgebraInClassRingHom C hC R H) ⊆ Set.range f := by
    intro y hy
    rcases hy with ⟨a, rfl⟩
    rcases (show Function.Surjective (MonoidAlgebra.mapDomainRingHom R φ) from by
      simpa [MonoidAlgebra.mapDomainRingHom_apply] using
        (Finsupp.mapDomain_surjective (M := R) hφsurj)) a with
      ⟨b, hb⟩
    refine ⟨toCompletedGroupAlgebraInClassRingHom C hC R G b, ?_⟩
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
          (R := R) (G := G) (H := H) C hC hHer φ hφ))
      b
    simpa [f, RingHom.comp_apply, hb] using hcomp
  intro y
  have hycanonical :
      y ∈ closure (Set.range (toCompletedGroupAlgebraInClassRingHom C hC R H)) := by
    rw [hdense.closure_range]
    exact Set.mem_univ y
  have hyf : y ∈ closure (Set.range f) :=
    closure_mono hcanonical_subset hycanonical
  exact hclosed.closure_subset_iff.2 (fun z hz => hz) hyf

/-- Continuous ring homomorphisms out of `[[R G]]_C` are determined by their values on the
dense abstract group algebra. -/
theorem completedGroupAlgebraInClassRingHom_ext_of_comp_toCompleted
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G)
    {f g : CompletedGroupAlgebraInClass C hC R G →+*
      CompletedGroupAlgebraInClass C hC R H}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f.comp (toCompletedGroupAlgebraInClassRingHom C hC R G) =
      g.comp (toCompletedGroupAlgebraInClassRingHom C hC R G)) :
    f = g := by
  letI : T2Space (CompletedGroupAlgebraInClass C hC R H) :=
    completedGroupAlgebraInClass_t2Space (R := R) (G := H) C hC hR
  have hdense : DenseRange (toCompletedGroupAlgebraInClassRingHom C hC R G) := by
    change DenseRange (toCompletedGroupAlgebraInClass C hC R G)
    exact denseRange_toCompletedGroupAlgebraInClass (R := R) (G := G) C hC hForm hG
  have hcomp : (f : CompletedGroupAlgebraInClass C hC R G →
        CompletedGroupAlgebraInClass C hC R H) ∘
        (toCompletedGroupAlgebraInClassRingHom C hC R G) =
      (g : CompletedGroupAlgebraInClass C hC R G →
        CompletedGroupAlgebraInClass C hC R H) ∘
        (toCompletedGroupAlgebraInClassRingHom C hC R G) := by
    funext x
    exact congrFun (congrArg DFunLike.coe hfg) x
  have hfun : (f : CompletedGroupAlgebraInClass C hC R G →
        CompletedGroupAlgebraInClass C hC R H) = g :=
    DenseRange.equalizer hdense hf hg hcomp
  exact RingHom.ext fun x => congrFun hfun x

/-- Identity law for the `C`-indexed completed-group-algebra functor. -/
theorem completedGroupAlgebraMapInClass_id
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) :
    completedGroupAlgebraMapInClass (G := G) (H := G) C hC hHer R
        (MonoidHom.id G) continuous_id =
      RingHom.id (CompletedGroupAlgebraInClass C hC R G) := by
  apply completedGroupAlgebraInClassRingHom_ext_of_comp_toCompleted
    (R := R) (G := G) (H := G) C hC hForm hR hG
  · exact continuous_completedGroupAlgebraMapInClass (R := R) (G := G) (H := G)
      C hC hHer (MonoidHom.id G) continuous_id
  · exact continuous_id
  · rw [completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass,
      finiteGroupAlgebra_mapDomainRingHom_id]
    rfl

/-- Identity law for the `C`-indexed completed-group-algebra functor, as an `R`-algebra
homomorphism. -/
theorem completedGroupAlgebraMapAlgHomInClass_id
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) :
    completedGroupAlgebraMapAlgHomInClass (G := G) (H := G) C hC hHer R
        (MonoidHom.id G) continuous_id =
      AlgHom.id R (CompletedGroupAlgebraInClass C hC R G) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMapInClass_id (R := R) (G := G) C hC hForm hHer hR hG))
    x
  simpa using h

/-- Composition law for the `C`-indexed completed-group-algebra functor. -/
theorem completedGroupAlgebraMapInClass_comp
    {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G)
    (φ : G →* H) (hφ : Continuous φ) (ψ : H →* K) (hψ : Continuous ψ) :
    (completedGroupAlgebraMapInClass (G := H) (H := K) C hC hHer R ψ hψ).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ) =
      completedGroupAlgebraMapInClass (G := G) (H := K) C hC hHer R
        (ψ.comp φ) (hψ.comp hφ) := by
  apply completedGroupAlgebraInClassRingHom_ext_of_comp_toCompleted
    (R := R) (G := G) (H := K) C hC hForm hR hG
  · exact (continuous_completedGroupAlgebraMapInClass (R := R) (G := H) (H := K)
      C hC hHer ψ hψ).comp
        (continuous_completedGroupAlgebraMapInClass (R := R) (G := G) (H := H)
          C hC hHer φ hφ)
  · exact continuous_completedGroupAlgebraMapInClass (R := R) (G := G) (H := K)
      C hC hHer (ψ.comp φ) (hψ.comp hφ)
  · apply RingHom.ext
    intro x
    have hφdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
          (R := R) (G := G) (H := H) C hC hHer φ hφ))
      x
    have hψdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
          (R := R) (G := H) (H := K) C hC hHer ψ hψ))
      (MonoidAlgebra.mapDomainRingHom R φ x)
    have hdomain := congrFun
      (congrArg DFunLike.coe
        (finiteGroupAlgebra_mapDomainRingHom_comp R G H K φ ψ))
      x
    have hcompdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
          (R := R) (G := G) (H := K) C hC hHer (ψ.comp φ) (hψ.comp hφ)))
      x
    calc
      (((completedGroupAlgebraMapInClass (G := H) (H := K) C hC hHer R ψ hψ).comp
          (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ)).comp
          (toCompletedGroupAlgebraInClassRingHom C hC R G)) x
          =
        completedGroupAlgebraMapInClass (G := H) (H := K) C hC hHer R ψ hψ
          (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
            (toCompletedGroupAlgebraInClassRingHom C hC R G x)) := rfl
      _ =
        completedGroupAlgebraMapInClass (G := H) (H := K) C hC hHer R ψ hψ
          (toCompletedGroupAlgebraInClassRingHom C hC R H
            (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          have hφdense' :
              completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
                  (toCompletedGroupAlgebraInClassRingHom C hC R G x) =
                toCompletedGroupAlgebraInClassRingHom C hC R H
                  (MonoidAlgebra.mapDomainRingHom R φ x) := by
            simpa [RingHom.comp_apply] using hφdense
          exact congrArg (completedGroupAlgebraMapInClass (G := H) (H := K)
            C hC hHer R ψ hψ) hφdense'
      _ =
        toCompletedGroupAlgebraInClassRingHom C hC R K
          (MonoidAlgebra.mapDomainRingHom R ψ (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          simpa [RingHom.comp_apply] using hψdense
      _ =
        toCompletedGroupAlgebraInClassRingHom C hC R K
          (MonoidAlgebra.mapDomainRingHom R (ψ.comp φ) x) := by
          exact congrArg (toCompletedGroupAlgebraInClassRingHom C hC R K) (by
            change (MonoidAlgebra.mapDomainRingHom R ψ)
                ((MonoidAlgebra.mapDomainRingHom R φ) x) =
              (MonoidAlgebra.mapDomainRingHom R (ψ.comp φ)) x at hdomain
            exact hdomain)
      _ =
        ((completedGroupAlgebraMapInClass (G := G) (H := K) C hC hHer R
          (ψ.comp φ) (hψ.comp hφ)).comp
          (toCompletedGroupAlgebraInClassRingHom C hC R G)) x := by
          simpa [RingHom.comp_apply] using hcompdense.symm

/-- Composition law for the `C`-indexed completed-group-algebra functor, as an `R`-algebra
homomorphism. -/
theorem completedGroupAlgebraMapAlgHomInClass_comp
    {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G)
    (φ : G →* H) (hφ : Continuous φ) (ψ : H →* K) (hψ : Continuous ψ) :
    (completedGroupAlgebraMapAlgHomInClass (G := H) (H := K) C hC hHer R ψ hψ).comp
        (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hC hHer R φ hφ) =
      completedGroupAlgebraMapAlgHomInClass (G := G) (H := K) C hC hHer R
        (ψ.comp φ) (hψ.comp hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMapInClass_comp (R := R) (G := G) (H := H) (K := K)
        C hC hForm hHer hR hG φ hφ ψ hψ))
    x
  simpa using h

/-- The in-class completed group-algebra map sends group-like elements to group-like elements. -/
@[simp]
theorem completedGroupAlgebraMapInClass_toCompletedGroupAlgebraInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
        (toCompletedGroupAlgebraInClass C hC R G (MonoidAlgebra.of R G g)) =
      toCompletedGroupAlgebraInClass C hC R H (MonoidAlgebra.of R H (φ g)) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
        (R := R) (G := G) (H := H) C hC hHer φ hφ))
    (MonoidAlgebra.of R G g)
  simpa [RingHom.comp_apply, finiteGroupAlgebra_mapDomainRingHom_of] using h

/-- The in-class completed group-algebra map sends group-like augmentation generators to their images. -/
@[simp]
theorem completedGroupAlgebraMapInClass_toCompletedGroupAlgebraInClass_sub_one_of
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
        (toCompletedGroupAlgebraInClass C hC R G (MonoidAlgebra.of R G g) - 1) =
      toCompletedGroupAlgebraInClass C hC R H (MonoidAlgebra.of R H (φ g)) - 1 := by
  rw [map_sub, completedGroupAlgebraMapInClass_toCompletedGroupAlgebraInClass_of, map_one]

end

end CompletedGroupAlgebra
