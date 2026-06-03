import CompletedGroupAlgebra.Augmentation.Functoriality

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteFunctoriality/Comap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Comap finite quotients for completed group algebra functoriality
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The inverse image of an open finite quotient of `H` along a continuous homomorphism
`G -> H`, regarded as an open finite quotient of the profinite group `G`. This is the
index-level operation underlying Lemma 5.3.5(e)'s functoriality in the group variable. -/
def completedGroupAlgebraComapIndex
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) : CompletedGroupAlgebraIndex G :=
  OrderDual.toDual
    ⟨ProCGroups.OpenNormalSubgroup.comap φ hφ ((OrderDual.ofDual V).1 : OpenNormalSubgroup H), by
      letI : CompactSpace G := ProCGroups.IsProfiniteGroup.compactSpace hG
      exact ProCGroups.openNormalSubgroup_finiteQuotient (G := G)
        (ProCGroups.OpenNormalSubgroup.comap φ hφ ((OrderDual.ofDual V).1 : OpenNormalSubgroup H))⟩

/-- The subgroup underlying the comap index is the subgroup-theoretic comap. -/
@[simp]
theorem completedGroupAlgebraComapIndex_subgroup
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    (((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)).1 :
        OpenNormalSubgroup G) : Subgroup G) =
      (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H).comap φ :=
  rfl

/-- Comap of all-finite completed-group-algebra indices is monotone. -/
theorem completedGroupAlgebraComapIndex_mono
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndex H} (hVW : V ≤ W) :
    completedGroupAlgebraComapIndex (G := G) hG φ hφ V ≤
      completedGroupAlgebraComapIndex (G := G) hG φ hφ W := by
  change (((OrderDual.ofDual W).1 : OpenNormalSubgroup H) : Subgroup H).comap φ ≤
    (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H).comap φ
  exact Subgroup.comap_mono hVW

/-- The quotient homomorphism `G/φ⁻¹(V) -> H/V` induced by a continuous homomorphism
`φ : G -> H`. -/
def completedGroupAlgebraComapQuotientMap
    [IsTopologicalGroup H]
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    CompletedGroupAlgebraQuotient G (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) →*
      CompletedGroupAlgebraQuotient H V :=
  QuotientGroup.map _ _ φ (by
    intro g hg
    exact hg)

/-- The comap quotient map sends the class of `g` to the class of its image. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMap_mk
    [IsTopologicalGroup H]
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) (g : G) :
    completedGroupAlgebraComapQuotientMap (G := G) hG φ hφ V
        (QuotientGroup.mk'
          ((((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)).1 :
            OpenNormalSubgroup G) : Subgroup G)) g) =
      QuotientGroup.mk'
        ((((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H)) (φ g) :=
  rfl

/-- A surjective homomorphism induces a surjective map on the comap quotients. -/
theorem completedGroupAlgebraComapQuotientMap_surjective
    [IsTopologicalGroup H]
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) (V : CompletedGroupAlgebraIndex H) :
    Function.Surjective (completedGroupAlgebraComapQuotientMap (G := G) hG φ hφ V) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H)) q with
    ⟨h, rfl⟩
  rcases hφsurj h with ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
      ((((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)).1 :
        OpenNormalSubgroup G) : Subgroup G)) g, ?_⟩
  rw [completedGroupAlgebraComapQuotientMap_mk]

end

end CompletedGroupAlgebra
