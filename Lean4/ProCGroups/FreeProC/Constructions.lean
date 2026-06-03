import ProCGroups.NormalSubgroups.SimpleQuotients.Compactness
import ProCGroups.ProC.MaximalQuotients.Definitions

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Constructions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

open Set
open ProCGroups.ProC

namespace ProCGroups.FreeProC

universe u

section CoreResults

variable {ProC : ProCGroupPredicate}

/-- A maximal pro-`C'` quotient of a pointed free pro-`C` group is again pointed free
on the same pointed space.

This version fixes a chosen maximal quotient map `π : F →* Q` and includes the explicit
class-inclusion hypothesis `ProC' ⇒ ProC`. -/
theorem maximalQuotientOfPointedFree_is_pointedFree
    {ProC' : ProCGroupPredicate}
    (hmono :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC' (G := G) → ProC (G := G))
    {X : Type u} [TopologicalSpace X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    {ι : X → F}
    (hF : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι)
    (π : F →* Q) (hπ : IsMaximalProCQuotient ProC' π) :
    IsPointedFreeProCGroupOn (ProC := ProC') X x0 Q (fun x => π (ι x)) := by
  refine ⟨hπ.isProC, hπ.continuous_π.comp hF.continuous_ι, ?_, ?_, ?_⟩
  · simp only [hF.map_base, map_one]
  · have himage : π '' Set.range ι = Set.range (fun x => π (ι x)) := by
      simpa [Function.comp] using (Set.range_comp π ι).symm
    simpa [himage] using
      (Generation.topologicallyGenerates_image_of_continuousSurjective
        (G := F) (H := Q) π hπ.continuous_π hπ.surjective_π hF.generates_range)
  · intro G _ _ _ hG φ hφ hφ0 hgen
    have hG' : ProC (G := G) := hmono hG
    rcases hF.existsUnique_lift hG' φ hφ hφ0 hgen with ⟨f, hfprop, hfuniq⟩
    rcases hπ.existsUnique_lift hG f hfprop.1 with ⟨q, hqprop, hquniq⟩
    refine ⟨q, ?_, ?_⟩
    · refine ⟨hqprop.1, ?_⟩
      intro x
      have hcomp_eval := congrArg (fun ψ : F →* G => ψ (ι x)) hqprop.2
      simpa [MonoidHom.comp_apply, hfprop.2 x] using hcomp_eval
    · intro q' hq'
      have hq'comp :
          q'.comp π = f := by
        apply hfuniq
        refine ⟨hq'.1.comp hπ.continuous_π, ?_⟩
        intro x
        simpa [MonoidHom.comp_apply] using hq'.2 x
      exact hquniq q' ⟨hq'.1, hq'comp⟩

/-- Lemma-level perfect-kernel statement with an explicit quotient hypothesis.

With the current abstract `ProC` interface, the standard argument needs two extra inputs made
explicit here:
- the comparison `ProC ⇒ ProCe`, so the `pro-`C quotient may also be used as a `pro-`C_e` target;
- the hypothesis that the quotient `Fe / ⁅ker φ, ker φ⁆` is already `pro-`C`.

Under those assumptions, the universal-property proof shows that the kernel of the natural map
from a pointed free `pro-`C_e` model to a pointed free `pro-`C` model is perfect. -/
theorem kernel_of_pointedFree_map_isPerfect
    {ProCe : ProCGroupPredicate}
    (hmono :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC (G := G) → ProCe (G := G))
    {X : Type u} [TopologicalSpace X] {x0 : X}
    {Fe : Type u} [Group Fe] [TopologicalSpace Fe] [IsTopologicalGroup Fe]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ιe : X → Fe} {ι : X → F}
    (hFe : IsPointedFreeProCGroupOn (ProC := ProCe) X x0 Fe ιe)
    (hF : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι)
    (φ : Fe →* F) (hφ : Continuous φ)
    (hcompat : ∀ x, φ (ιe x) = ι x)
    (hquot : ProC (G := Fe ⧸ ⁅φ.ker, φ.ker⁆)) :
    ProCGroups.NormalSubgroups.IsPerfectSubgroup φ.ker := by
  let K : Subgroup Fe := φ.ker
  let q : Fe →* Fe ⧸ ⁅K, K⁆ := QuotientGroup.mk' ⁅K, K⁆
  let ψ : X → Fe ⧸ ⁅K, K⁆ := fun x => q (ιe x)
  have hψ : Continuous ψ := continuous_quotient_mk'.comp hFe.continuous_ι
  have hψ0 : ψ x0 = 1 := by
    simp only [QuotientGroup.mk'_apply, hFe.map_base, QuotientGroup.mk_one, ψ, q]
  have himage : q '' Set.range ιe = Set.range ψ := by
    simpa [ψ, q, Function.comp] using (Set.range_comp q ιe).symm
  have hgenψ : Generation.TopologicallyGenerates (G := Fe ⧸ ⁅K, K⁆) (Set.range ψ) := by
    simpa [himage] using
      (Generation.topologicallyGenerates_image_of_continuousSurjective
        (G := Fe) (H := Fe ⧸ ⁅K, K⁆) q continuous_quotient_mk'
        (QuotientGroup.mk'_surjective ⁅K, K⁆) hFe.generates_range)
  rcases hF.existsUnique_lift hquot ψ hψ hψ0 hgenψ with ⟨σ, hσ, _⟩
  have hquot_e : ProCe (G := Fe ⧸ ⁅K, K⁆) := hmono hquot
  rcases hFe.existsUnique_lift hquot_e ψ hψ hψ0 hgenψ with ⟨τ, hτ, hτuniq⟩
  have hq_eq : q = τ := by
    exact hτuniq q ⟨continuous_quotient_mk', fun x => rfl⟩
  have hσφ_eq : σ.comp φ = τ := by
    refine hτuniq (σ.comp φ) ⟨hσ.1.comp hφ, ?_⟩
    intro x
    calc
      (σ.comp φ) (ιe x) = σ (ι x) := by
        simp only [MonoidHom.comp_apply, hcompat x]
      _ = ψ x := hσ.2 x
  have hfac : σ.comp φ = q := hσφ_eq.trans hq_eq.symm
  have hKle : K ≤ ⁅K, K⁆ := by
    intro k hk
    have hkφ : φ k = 1 := by
      simpa [K, MonoidHom.mem_ker] using hk
    have hqk : q k = 1 := by
      rw [← DFunLike.congr_fun hfac k]
      simp only [MonoidHom.comp_apply, hkφ, map_one]
    exact (QuotientGroup.eq_one_iff (N := ⁅K, K⁆) k).1 hqk
  simpa [K, ProCGroups.NormalSubgroups.IsPerfectSubgroup] using
    (le_antisymm (Subgroup.commutator_le_self K) hKle)

/-- Perfect-kernel statement using pro-`C` permanence data to build the commutator-kernel
quotient internally. -/
theorem kernel_of_pointedFree_map_isPerfect_of_closedUnderCommutatorKernelQuotientsFrom
    {ProCe : ProCGroupPredicate}
    [ProC.ClosedUnderCommutatorKernelQuotientsFrom ProCe]
    (hmono :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC (G := G) → ProCe (G := G))
    {X : Type u} [TopologicalSpace X] {x0 : X}
    {Fe : Type u} [Group Fe] [TopologicalSpace Fe] [IsTopologicalGroup Fe]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ιe : X → Fe} {ι : X → F}
    (hFe : IsPointedFreeProCGroupOn (ProC := ProCe) X x0 Fe ιe)
    (hF : IsPointedFreeProCGroupOn (ProC := ProC) X x0 F ι)
    (φ : Fe →* F) (hφ : Continuous φ)
    (hcompat : ∀ x, φ (ιe x) = ι x) :
    ProCGroups.NormalSubgroups.IsPerfectSubgroup φ.ker := by
  let φₜ : Fe →ₜ* F := { toMonoidHom := φ, continuous_toFun := hφ }
  have hquot : ProC (G := Fe ⧸ ⁅φ.ker, φ.ker⁆) := by
    simpa [φₜ] using
      (ProCGroupPredicate.quotient_by_kernel_commutator
        (Target := ProC) (Source := ProCe) φₜ hFe.isProC hF.isProC)
  exact
    kernel_of_pointedFree_map_isPerfect
      (ProC := ProC) (ProCe := ProCe) hmono hFe hF φ hφ hcompat hquot

end CoreResults

end ProCGroups.FreeProC
