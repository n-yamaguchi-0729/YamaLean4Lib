import CompletedGroupAlgebra.AllFiniteFunctoriality.Map

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteFunctoriality/GroupLike.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Group-like formulas for completed group algebra functoriality
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

/-- The completed functorial map sends the group-like element of `g` to that of `φ g`. -/
theorem completedGroupAlgebraMap_of
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ (completedGroupAlgebraOf R G g) =
      completedGroupAlgebraOf R H (φ g) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := G) (H := H)
        hG φ hφ))
      (MonoidAlgebra.of R G g)
  simpa [completedGroupAlgebraOf, finiteGroupAlgebra_mapDomainRingHom_of] using h

/-- The algebra-hom completed functorial map sends group-like elements to their images. -/
@[simp]
theorem completedGroupAlgebraMapAlgHom_of
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG φ hφ
        (completedGroupAlgebraOf R G g) =
      completedGroupAlgebraOf R H (φ g) :=
  completedGroupAlgebraMap_of (R := R) (G := G) (H := H) hG φ hφ g
end

end CompletedGroupAlgebra
