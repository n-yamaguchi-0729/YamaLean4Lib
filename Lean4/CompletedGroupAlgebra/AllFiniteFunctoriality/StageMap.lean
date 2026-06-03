import CompletedGroupAlgebra.AllFiniteFunctoriality.Comap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteFunctoriality/StageMap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage maps for completed group algebra functoriality
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The finite-stage map `R[G/φ⁻¹(V)] -> R[H/V]` induced by `φ : G -> H`. -/
def completedGroupAlgebraFunctorialStageMap
    (R : Type u) [CommRing R] (hG : ProCGroups.IsProfiniteGroup G)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndex H) :
    CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) →+*
      CompletedGroupAlgebraStage R H V :=
  MonoidAlgebra.mapDomainRingHom R
    (completedGroupAlgebraComapQuotientMap (G := G) hG φ hφ V)

/-- A surjective group homomorphism induces a surjective finite-stage algebra map. -/
theorem completedGroupAlgebraFunctorialStageMap_surjective_of_surjective
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) (V : CompletedGroupAlgebraIndex H) :
    Function.Surjective
      (completedGroupAlgebraFunctorialStageMap
        (G := G) (H := H) (R := R) hG φ hφ V) := by
  simpa [completedGroupAlgebraFunctorialStageMap, MonoidAlgebra.mapDomainRingHom_apply] using
    (Finsupp.mapDomain_surjective (M := R)
      (completedGroupAlgebraComapQuotientMap_surjective
        (G := G) hG φ hφ hφsurj V))

/-- The finite-stage functorial map sends singleton coefficients to singleton coefficients. -/
@[simp]
theorem completedGroupAlgebraFunctorialStageMap_single
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H)
    (q : CompletedGroupAlgebraQuotient G
      (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) (r : R) :
    completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (completedGroupAlgebraComapQuotientMap (G := G) hG φ hφ V q) r := by
  classical
  simp only [completedGroupAlgebraFunctorialStageMap, MonoidAlgebra.single,
  MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]

/-- The finite-stage functorial map preserves scalar algebra-map elements. -/
theorem completedGroupAlgebraFunctorialStageMap_algebraMap
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) (r : R) :
    completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
        (algebraMap R
          (CompletedGroupAlgebraStage R G
            (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) r) =
      algebraMap R (CompletedGroupAlgebraStage R H V) r := by
  simp only [completedGroupAlgebraFunctorialStageMap, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

/-- The finite-stage functorial map is continuous for the finite-stage topologies. -/
theorem continuous_completedGroupAlgebraFunctorialStageMap
    [TopologicalSpace R] [IsTopologicalRing R]
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    letI : TopologicalSpace
        (CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) :=
      (completedGroupAlgebraSystem R G).topologicalSpace
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)
    letI : TopologicalSpace (CompletedGroupAlgebraStage R H V) :=
      (completedGroupAlgebraSystem R H).topologicalSpace V
    Continuous (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      hG φ hφ V) := by
  letI : TopologicalSpace
      (CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) :=
    (completedGroupAlgebraSystem R G).topologicalSpace
      (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)
  letI : TopologicalSpace (CompletedGroupAlgebraStage R H V) :=
    (completedGroupAlgebraSystem R H).topologicalSpace V
  exact finiteGroupAlgebra_mapDomainRingHom_continuous R
    (CompletedGroupAlgebraQuotient G (completedGroupAlgebraComapIndex (G := G) hG φ hφ V))
    (CompletedGroupAlgebraQuotient H V)
    (completedGroupAlgebraComapQuotientMap (G := G) hG φ hφ V)

/-- Finite-stage functorial maps commute with transition maps. -/
@[simp]
theorem completedGroupAlgebraFunctorialStageMap_transition
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndex H} (hVW : V ≤ W) :
    (completedGroupAlgebraTransition R H hVW).comp
        (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ W) =
      (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V).comp
        (completedGroupAlgebraTransition R G
          (completedGroupAlgebraComapIndex_mono (G := G) hG φ hφ hVW)) := by
  rw [completedGroupAlgebraTransition, completedGroupAlgebraFunctorialStageMap,
    completedGroupAlgebraFunctorialStageMap, completedGroupAlgebraTransition,
    ← MonoidAlgebra.mapDomainRingHom_comp, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1
  apply MonoidHom.ext
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) hG φ hφ W)).1 :
        OpenNormalSubgroup G) : Subgroup G)) q with
    ⟨g, rfl⟩
  rfl

/-- The finite-stage functorial map agrees with the dense stage map after applying `φ`. -/
@[simp]
theorem completedGroupAlgebraFunctorialStageMap_comp_stageMap
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V).comp
        (completedGroupAlgebraStageMap R G
          (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)) =
      (completedGroupAlgebraStageMap R H V).comp
        (MonoidAlgebra.mapDomainRingHom R φ) := by
  rw [completedGroupAlgebraFunctorialStageMap, completedGroupAlgebraStageMap,
    completedGroupAlgebraStageMap, ← MonoidAlgebra.mapDomainRingHom_comp,
    ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

end

end CompletedGroupAlgebra
