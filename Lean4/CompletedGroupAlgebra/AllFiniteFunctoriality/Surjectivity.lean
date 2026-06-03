import CompletedGroupAlgebra.AllFiniteFunctoriality.Map

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteFunctoriality/Surjectivity.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Surjectivity for completed group algebra functorial maps
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

/-- A surjective continuous homomorphism of profinite groups induces a surjective map on
completed group algebras. -/
theorem completedGroupAlgebraMap_surjective_of_surjective
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    (hH : ProCGroups.IsProfiniteGroup H) (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) :
    Function.Surjective (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ) := by
  let f := completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
  letI : CompactSpace (Carrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G) hR
  letI : T2Space (Carrier R H) :=
    completedGroupAlgebra_t2Space (R := R) (G := H) hR
  have hfcont : Continuous f :=
    continuous_completedGroupAlgebraMap (R := R) (G := G) (H := H) hG φ hφ
  have hclosed : IsClosed (Set.range f) := (isCompact_range hfcont).isClosed
  have hdense : DenseRange (toCompletedGroupAlgebraRingHom R H) :=
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := H) hH
  have hcanonical_subset :
      Set.range (toCompletedGroupAlgebraRingHom R H) ⊆ Set.range f := by
    intro y hy
    rcases hy with ⟨a, rfl⟩
    rcases (show Function.Surjective (MonoidAlgebra.mapDomainRingHom R φ) from by
      simpa [MonoidAlgebra.mapDomainRingHom_apply] using
        (Finsupp.mapDomain_surjective (M := R) hφsurj)) a with
      ⟨b, hb⟩
    refine ⟨toCompletedGroupAlgebraRingHom R G b, ?_⟩
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra
          (R := R) (G := G) (H := H) hG φ hφ))
      b
    simpa [f, RingHom.comp_apply, hb] using hcomp
  intro y
  have hycanonical : y ∈ closure (Set.range (toCompletedGroupAlgebraRingHom R H)) := by
    rw [hdense.closure_range]
    exact Set.mem_univ y
  have hyf : y ∈ closure (Set.range f) :=
    closure_mono hcanonical_subset hycanonical
  exact hclosed.closure_subset_iff.2 (fun z hz => hz) hyf

end

end CompletedGroupAlgebra
