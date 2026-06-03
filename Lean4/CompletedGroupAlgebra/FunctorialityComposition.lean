import CompletedGroupAlgebra.Separation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/FunctorialityComposition.lean
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

variable {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Lemma 5.3.5(e), composition law for the completed-group-algebra functor. -/
theorem completedGroupAlgebraMap_comp
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    (hH : ProCGroups.IsProfiniteGroup H)
    (φ : G →* H) (hφ : Continuous φ) (ψ : H →* K) (hψ : Continuous ψ) :
    (completedGroupAlgebraMap (G := H) (H := K) R hH ψ hψ).comp
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ) =
      completedGroupAlgebraMap (G := G) (H := K) R hG (ψ.comp φ) (hψ.comp hφ) := by
  apply completedGroupAlgebraRingHom_ext_of_comp_toCompleted (R := R) (G := G) (H := K)
    hR hG
  · exact (continuous_completedGroupAlgebraMap (R := R) (G := H) (H := K) hH ψ hψ).comp
      (continuous_completedGroupAlgebraMap (R := R) (G := G) (H := H) hG φ hφ)
  · exact continuous_completedGroupAlgebraMap (R := R) (G := G) (H := K)
      hG (ψ.comp φ) (hψ.comp hφ)
  · apply RingHom.ext
    intro x
    have hφdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := G) (H := H)
          hG φ hφ))
      x
    have hψdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := H) (H := K)
          hH ψ hψ))
      (MonoidAlgebra.mapDomainRingHom R φ x)
    have hdomain := congrFun
      (congrArg DFunLike.coe
        (finiteGroupAlgebra_mapDomainRingHom_comp R G H K φ ψ))
      x
    have hcompdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := G) (H := K)
          hG (ψ.comp φ) (hψ.comp hφ)))
      x
    calc
      (((completedGroupAlgebraMap (G := H) (H := K) R hH ψ hψ).comp
          (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ)).comp
          (toCompletedGroupAlgebraRingHom R G)) x
          =
        completedGroupAlgebraMap (G := H) (H := K) R hH ψ hψ
          (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
            (toCompletedGroupAlgebraRingHom R G x)) := rfl
      _ =
        completedGroupAlgebraMap (G := H) (H := K) R hH ψ hψ
          (toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          have hφdense' :
              completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
                  (toCompletedGroupAlgebraRingHom R G x) =
                toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x) := by
            simpa [RingHom.comp_apply] using hφdense
          exact congrArg (completedGroupAlgebraMap (G := H) (H := K) R hH ψ hψ) hφdense'
      _ =
        toCompletedGroupAlgebraRingHom R K
          (MonoidAlgebra.mapDomainRingHom R ψ (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          simpa [RingHom.comp_apply] using hψdense
      _ =
        toCompletedGroupAlgebraRingHom R K
          (MonoidAlgebra.mapDomainRingHom R (ψ.comp φ) x) := by
          exact congrArg (toCompletedGroupAlgebraRingHom R K) (by
            change (MonoidAlgebra.mapDomainRingHom R ψ)
                ((MonoidAlgebra.mapDomainRingHom R φ) x) =
              (MonoidAlgebra.mapDomainRingHom R (ψ.comp φ)) x at hdomain
            exact hdomain)
      _ =
        ((completedGroupAlgebraMap (G := G) (H := K) R hG (ψ.comp φ) (hψ.comp hφ)).comp
          (toCompletedGroupAlgebraRingHom R G)) x := by
          simpa [RingHom.comp_apply] using hcompdense.symm

/-- Lemma 5.3.5(e), composition law for the completed-group-algebra functor, as an `R`-algebra
homomorphism. -/
theorem completedGroupAlgebraMapAlgHom_comp
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    (hH : ProCGroups.IsProfiniteGroup H)
    (φ : G →* H) (hφ : Continuous φ) (ψ : H →* K) (hψ : Continuous ψ) :
    (completedGroupAlgebraMapAlgHom (G := H) (H := K) R hH ψ hψ).comp
        (completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG φ hφ) =
      completedGroupAlgebraMapAlgHom (G := G) (H := K) R hG (ψ.comp φ) (hψ.comp hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMap_comp (R := R) (G := G) (H := H) (K := K)
        hR hG hH φ hφ ψ hψ))
    x
  simpa [RingHom.comp_apply] using h
end

end CompletedGroupAlgebra
