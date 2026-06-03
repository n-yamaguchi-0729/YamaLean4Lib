import FoxDifferential.Completed.DifferentialModule.Identity

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/Map/Comap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed differential modules

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Definition of completedGroupAlgebraComapIndex. -/
def completedGroupAlgebraComapIndex
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G := by
  let V : OpenNormalSubgroup H := (OrderDual.ofDual U).1
  let W : OpenNormalSubgroup G := OpenNormalSubgroup.comap ψ.toMonoidHom ψ.continuous_toFun V
  refine OrderDual.toDual ⟨W, ?_⟩
  let q : G →* H ⧸ (V : Subgroup H) :=
    (QuotientGroup.mk' (V : Subgroup H)).comp ψ.toMonoidHom
  let f : G ⧸ (W : Subgroup G) → H ⧸ (V : Subgroup H) :=
    QuotientGroup.map _ _ ψ.toMonoidHom (by
      intro g hg
      simpa [W] using hg)
  have hf : Function.Injective f := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) x with ⟨a, rfl⟩
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) y with ⟨b, rfl⟩
    apply QuotientGroup.eq.2
    change ψ (a⁻¹ * b) ∈ (V : Subgroup H)
    have hv : (ψ a)⁻¹ * ψ b ∈ (V : Subgroup H) := QuotientGroup.eq.1 hxy
    simpa using hv
  letI : Finite (H ⧸ (V : Subgroup H)) := (OrderDual.ofDual U).2
  exact Finite.of_injective f hf

omit [IsTopologicalGroup G] in
/-- 標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem completedGroupAlgebraComapIndex_subgroup
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    (((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U)).1 :
        OpenNormalSubgroup G) : Subgroup G) =
      Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) := by
  rfl

/-- Definition of completedGroupAlgebraComapQuotientMap. -/
def completedGroupAlgebraComapQuotientMap
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U) →*
      _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H U :=
  QuotientGroup.map _ _ ψ.toMonoidHom (by
    intro g hg
    simpa [completedGroupAlgebraComapIndex] using hg)

/-- Evaluation formula for completedGroupAlgebraComapQuotientMap_mk. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMap_mk
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) (g : G) :
    completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ U
        (QuotientGroup.mk' _ g) =
      QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) (ψ g) := by
  rfl


/-- If `ψ : G → H` is surjective, the induced map from the pulled-back finite quotient
`G / ψ⁻¹(U)` to `H / U` is surjective.  This is the finite-quotient input used later to
lift coefficients in the completed free-derivative construction. -/
theorem completedGroupAlgebraComapQuotientMap_surjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    Function.Surjective
      (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ U) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)) q with
    ⟨h, rfl⟩
  rcases hψ h with ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U)).1 :
          OpenNormalSubgroup G) : Subgroup G)) g, ?_⟩
  rw [completedGroupAlgebraComapQuotientMap_mk]

omit [IsTopologicalGroup G] in
/-- 標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem completedGroupAlgebraComapIndex_mono
    (ψ : ContinuousMonoidHom G H) {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H} (hUV : U ≤ V) :
    completedGroupAlgebraComapIndex (G := G) (H := H) ψ U ≤
      completedGroupAlgebraComapIndex (G := G) (H := H) ψ V := by
  change
    Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H) ≤
      Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)
  exact Subgroup.comap_mono hUV

/-- Compatibility lemma completedGroupAlgebraComapQuotientMap_compatible. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMap_compatible
    (ψ : ContinuousMonoidHom G H) {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H} (hUV : U ≤ V) :
    (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ V) =
      (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ U).comp
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual
            (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U))
          (V := OrderDual.ofDual
            (completedGroupAlgebraComapIndex (G := G) (H := H) ψ V))
          (completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hUV)) := by
  ext q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ V)).1 :
          OpenNormalSubgroup G) : Subgroup G)) q with ⟨g, rfl⟩
  rfl

end

end FoxDifferential
