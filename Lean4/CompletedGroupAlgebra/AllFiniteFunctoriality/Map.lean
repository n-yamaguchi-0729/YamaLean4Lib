import CompletedGroupAlgebra.AllFiniteFunctoriality.StageMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteFunctoriality/Map.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebra functorial maps
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Lemma 5.3.5(e), map construction: a continuous homomorphism of profinite groups
`φ : G -> H` induces a continuous ring homomorphism `[[R G]] -> [[R H]]`. -/
def completedGroupAlgebraMap
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) :
    Carrier R G →+* Carrier R H where
  toFun x := ⟨fun V =>
      completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x), by
    intro V W hVW
    change completedGroupAlgebraTransition R H hVW
        (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ W
          (completedGroupAlgebraProjection R G
            (completedGroupAlgebraComapIndex (G := G) hG φ hφ W) x)) =
      completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x)
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraFunctorialStageMap_transition (R := R) (G := G) (H := H)
          hG φ hφ hVW))
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ W) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
    rw [← completedGroupAlgebraProjection_compatible (R := R) (G := G) x
      (completedGroupAlgebraComapIndex_mono (G := G) hG φ hφ hVW)]
    exact hcomp⟩
  map_zero' := by
    apply (completedGroupAlgebraSystem R H).ext
    intro V
    exact map_zero (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      hG φ hφ V)
  map_one' := by
    apply (completedGroupAlgebraSystem R H).ext
    intro V
    exact map_one (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      hG φ hφ V)
  map_add' x y := by
    apply (completedGroupAlgebraSystem R H).ext
    intro V
    exact map_add (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      hG φ hφ V)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) y)
  map_mul' x y := by
    apply (completedGroupAlgebraSystem R H).ext
    intro V
    exact map_mul (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      hG φ hφ V)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) y)

/-- Projection of the completed functorial map is computed by the corresponding stage map. -/
@[simp]
theorem completedGroupAlgebraProjection_map
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) (x : Carrier R G) :
    completedGroupAlgebraProjection R H V
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x) =
      completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x) :=
  rfl

/-- Lemma 5.3.5(e), algebra form: a continuous homomorphism of profinite groups induces an
`R`-algebra homomorphism on completed group algebras. -/
def completedGroupAlgebraMapAlgHom
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) :
    Carrier R G →ₐ[R] Carrier R H where
  toRingHom := completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
  commutes' := by
    intro r
    apply (completedGroupAlgebraSystem R H).ext
    intro V
    change completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
        (algebraMap R
          (CompletedGroupAlgebraStage R G
            (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) r) =
      algebraMap R (CompletedGroupAlgebraStage R H V) r
    exact completedGroupAlgebraFunctorialStageMap_algebraMap
      (R := R) (G := G) (H := H) hG φ hφ V r

/-- The algebra-hom version of the completed functorial map has the same underlying function. -/
@[simp]
theorem completedGroupAlgebraMapAlgHom_apply
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (x : Carrier R G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG φ hφ x =
      completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x :=
  rfl

/-- The induced completed map is continuous. -/
theorem continuous_completedGroupAlgebraMap
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) :
    Continuous (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ) := by
  let A := Carrier R G
  letI : ∀ V : CompletedGroupAlgebraIndex H,
      TopologicalSpace (CompletedGroupAlgebraStage R H V) :=
    fun V => (completedGroupAlgebraSystem R H).topologicalSpace V
  have hval : Continuous fun x : A =>
      ((completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x) :
        (V : CompletedGroupAlgebraIndex H) → (completedGroupAlgebraSystem R H).X V) := by
    change Continuous fun x : A =>
      fun V : CompletedGroupAlgebraIndex H =>
        completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
          (completedGroupAlgebraProjection R G
            (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x)
    apply continuous_pi
    intro V
    letI : TopologicalSpace
        (CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) :=
      (completedGroupAlgebraSystem R G).topologicalSpace
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)
    exact (continuous_completedGroupAlgebraFunctorialStageMap (R := R) (G := G) (H := H)
      hG φ hφ V).comp
        ((completedGroupAlgebraSystem R G).continuous_projection
          (completedGroupAlgebraComapIndex (G := G) hG φ hφ V))
  exact Continuous.subtype_mk hval fun x =>
    (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x).2

/-- The completed functorial map agrees with the abstract group-algebra map on the dense map. -/
theorem completedGroupAlgebraMap_comp_toCompletedGroupAlgebra
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ).comp
        (toCompletedGroupAlgebraRingHom R G) =
      (toCompletedGroupAlgebraRingHom R H).comp (MonoidAlgebra.mapDomainRingHom R φ) := by
  apply RingHom.ext
  intro x
  apply (completedGroupAlgebraSystem R H).ext
  intro V
  have hstage := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraFunctorialStageMap_comp_stageMap (R := R) (G := G) (H := H)
        hG φ hφ V))
    x
  change completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
      (completedGroupAlgebraStageMap R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x) =
    completedGroupAlgebraStageMap R H V (MonoidAlgebra.mapDomainRingHom R φ x)
  exact hstage

end

end CompletedGroupAlgebra
