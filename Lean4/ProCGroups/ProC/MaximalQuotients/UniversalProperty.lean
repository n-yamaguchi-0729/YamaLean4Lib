import Mathlib.GroupTheory.QuotientGroup.Basic
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.Topologies.QuotientMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/MaximalQuotients/UniversalProperty.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set

namespace ProCGroups.ProC

universe u

variable {ProC : ProCGroupPredicate}

/-- Any normal subgroup with pro-`C` quotient contains the residual core. -/
theorem proCResidualCore_le_of_proCQuotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) [K.Normal]
    (hK : ProC (G := G ⧸ K)) :
    proCResidualCore ProC G ≤ K := by
  let N : ProCQuotientKernel ProC G :=
    { toSubgroup := K
      normal := inferInstance
      quotient_isProC := hK }
  have hle : proCResidualCore ProC G ≤ N.toSubgroup := by
    simpa [proCResidualCore] using
      (sInf_le (Set.mem_range_self N) :
        sInf (Set.range fun N : ProCQuotientKernel ProC G => N.toSubgroup) ≤ N.toSubgroup)
  intro x hx
  exact hle hx

private theorem map_proCResidualCore_le
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →* H) (hφ : Continuous φ) :
    (proCResidualCore ProC G).map φ ≤ proCResidualCore ProC H := by
  refine le_sInf ?_
  intro N hN
  rw [Set.mem_range] at hN
  rcases hN with ⟨N, rfl⟩
  refine Subgroup.map_le_iff_le_comap.2 ?_
  let α : G →* H ⧸ N.toSubgroup :=
    (QuotientGroup.mk' N.toSubgroup).comp φ
  have hα : Continuous α := QuotientGroup.continuous_mk.comp hφ
  have hkerLift :
      Continuous (QuotientGroup.kerLift α : G ⧸ α.ker →* H ⧸ N.toSubgroup) := by
    simpa [QuotientGroup.kerLift, QuotientGroup.lift] using
      hα.quotient_lift (fun a b hab => by
        simpa [QuotientGroup.con_ker_eq_conKer α, Con.ker_rel] using hab)
  have hαker_proC : ProC (G := G ⧸ α.ker) :=
    hsub.of_injective
      (QuotientGroup.kerLift α)
      hkerLift
      (QuotientGroup.kerLift_injective α)
      N.quotient_isProC
  have hαker_eq : α.ker = Subgroup.comap φ N.toSubgroup := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
  QuotientGroup.eq_one_iff, Subgroup.mem_comap, α]
  have hcore_le : proCResidualCore ProC G ≤ α.ker :=
    proCResidualCore_le_of_proCQuotient (ProC := ProC) α.ker hαker_proC
  rw [hαker_eq] at hcore_le
  exact hcore_le

/-- Under subgroup closure, arbitrary continuous homomorphisms send the residual core into the
residual core. -/
theorem map_proCResidualCore_le_of_hom
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →* H) (hφ : Continuous φ) :
    (proCResidualCore ProC G).map φ ≤ proCResidualCore ProC H :=
  map_proCResidualCore_le (ProC := ProC) hsub φ hφ

/-- Continuous-homomorphism form of residual-core functoriality. -/
theorem map_proCResidualCore_le_of_continuousMonoidHom
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →ₜ* H) :
    (proCResidualCore ProC G).map φ.toMonoidHom ≤ proCResidualCore ProC H :=
  map_proCResidualCore_le (ProC := ProC) hsub φ.toMonoidHom φ.continuous_toFun

/-- Any continuous homomorphism to a pro-`C` group kills the residual core, provided the
pro-`C` predicate is closed under injective continuous homomorphisms. -/
theorem proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →ₜ* H) (hH : ProC (G := H)) :
    proCResidualCore ProC G ≤ φ.toMonoidHom.ker := by
  let K : Subgroup G := φ.toMonoidHom.ker
  letI : K.Normal := MonoidHom.normal_ker φ.toMonoidHom
  have hkerLift :
      Continuous (QuotientGroup.kerLift φ.toMonoidHom : G ⧸ K →* H) := by
    simpa [K, QuotientGroup.kerLift, QuotientGroup.lift] using
      φ.continuous_toFun.quotient_lift (fun a b hab => by
        have hrel : a⁻¹ * b ∈ φ.toMonoidHom.ker := by
          simpa [K] using (QuotientGroup.leftRel_apply.mp hab)
        have hEq : (φ a)⁻¹ * φ b = 1 := by
          simpa [MonoidHom.mem_ker, map_mul, map_inv] using hrel
        exact inv_mul_eq_one.mp hEq)
  have hquot : ProC (G := G ⧸ K) :=
    hsub.of_injective
      (QuotientGroup.kerLift φ.toMonoidHom)
      hkerLift
      (QuotientGroup.kerLift_injective φ.toMonoidHom)
      hH
  simpa [K] using proCResidualCore_le_of_proCQuotient (ProC := ProC) (G := G) K hquot

/-- Universal map out of the maximal pro-`C` quotient: every continuous homomorphism from `G`
to a pro-`C` group factors through `G / proCResidualCore`. -/
noncomputable def lift_proCResidualCoreQuotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →ₜ* H) (hH : ProC (G := H)) :
    G ⧸ proCResidualCore ProC G →ₜ* H := by
  let R : Subgroup G := proCResidualCore ProC G
  letI : R.Normal := proCResidualCore_normal ProC G
  have hRker : R ≤ φ.toMonoidHom.ker := by
    simpa [R] using
      proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
        (ProC := ProC) hsub φ hH
  exact QuotientGroup.liftₜ R φ hRker

/-- The lifted map from the residual-core quotient agrees with the original map on quotient
classes. -/
@[simp] theorem lift_proCResidualCoreQuotient_mk
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →ₜ* H) (hH : ProC (G := H)) (x : G) :
    lift_proCResidualCoreQuotient (ProC := ProC) hsub φ hH
      (QuotientGroup.mk' (proCResidualCore ProC G) x) = φ x := by
  dsimp [lift_proCResidualCoreQuotient]
  rfl

/-- The lift from the residual-core quotient is unique among continuous homomorphisms agreeing on
all quotient classes. -/
theorem lift_proCResidualCoreQuotient_unique
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (φ : G →ₜ* H) (hH : ProC (G := H))
    (ψ : G ⧸ proCResidualCore ProC G →ₜ* H)
    (hψ : ∀ x : G, ψ (QuotientGroup.mk' (proCResidualCore ProC G) x) = φ x) :
    ψ = lift_proCResidualCoreQuotient (ProC := ProC) hsub φ hH := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  calc
    ψ (QuotientGroup.mk' (proCResidualCore ProC G) x) = φ x := hψ x
    _ = lift_proCResidualCoreQuotient (ProC := ProC) hsub φ hH
        (QuotientGroup.mk' (proCResidualCore ProC G) x) := by
          exact (lift_proCResidualCoreQuotient_mk (ProC := ProC) hsub φ hH x).symm

/-- Continuous epimorphisms carry the residual core onto the residual core when the predicate is
closed under subgroups and surjective continuous images, and the source residual quotient is
pro-`C`. -/
theorem map_proCResidualCore_eq_of_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hsub : IsSubgroupClosedProC ProC)
    (hquotClosed :
      ∀ {A B : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
        [Group B] [TopologicalSpace B] [IsTopologicalGroup B],
        (f : A →* B) → Continuous f → Function.Surjective f →
          ProC (G := A) → ProC (G := B))
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ)
    (hcoreQuot :
      letI : (proCResidualCore ProC G).Normal := proCResidualCore_normal ProC G
      ProC (G := G ⧸ proCResidualCore ProC G)) :
    (proCResidualCore ProC G).map φ = proCResidualCore ProC H := by
  let R : Subgroup G := proCResidualCore ProC G
  letI : R.Normal := proCResidualCore_normal ProC G
  let N : Subgroup H := R.map φ
  have hNnormal : N.Normal := by
    refine ⟨?_⟩
    intro y hy h
    rcases hy with ⟨x, hx, rfl⟩
    rcases hφsurj h with ⟨g, rfl⟩
    exact (Subgroup.mem_map).2 ⟨g * x * g⁻¹, (show R.Normal from inferInstance).conj_mem x hx g, by
      simp only [mul_assoc, map_mul, map_inv]⟩
  letI : N.Normal := hNnormal
  have hmap_le :
      R.map φ ≤ proCResidualCore ProC H :=
    map_proCResidualCore_le (ProC := ProC) hsub φ hφ
  have hRle : R ≤ Subgroup.comap φ N := by
    intro x hx
    exact (Subgroup.mem_comap).2 <| (Subgroup.mem_map).2 ⟨x, hx, rfl⟩
  let φₜ : G →ₜ* H :=
    { toMonoidHom := φ
      continuous_toFun := hφ }
  let βₜ : G ⧸ R →ₜ* H ⧸ N := QuotientGroup.mapₜ R N φₜ hRle
  let β : G ⧸ R →* H ⧸ N := βₜ.toMonoidHom
  have hβcont : Continuous β := βₜ.continuous_toFun
  have hβsurj : Function.Surjective β := by
    have hmkφ_surj : Function.Surjective (QuotientGroup.mk ∘ φ : G → H ⧸ N) := by
      intro y
      rcases QuotientGroup.mk'_surjective N y with ⟨h, rfl⟩
      rcases hφsurj h with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    exact QuotientGroup.map_surjective_of_surjective (N := R) (M := N) φ hmkφ_surj hRle
  have hNquot : ProC (G := H ⧸ N) := by
    exact hquotClosed β hβcont hβsurj hcoreQuot
  have hcoreH_le : proCResidualCore ProC H ≤ N :=
    proCResidualCore_le_of_proCQuotient (ProC := ProC) N hNquot
  exact le_antisymm hmap_le hcoreH_le

/-- Inside the residual core, any pro-`C` quotient is trivial once the relevant residual-core
stability equality is available. -/
theorem proCResidualCore_subgroup_eq_top_of_quotient_isProC
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {R : Subgroup G} [R.Normal]
    (hR : R = proCResidualCore ProC G)
    {L : Subgroup ↥R} [L.Normal]
    (hquot : ProC (G := ↥R ⧸ L))
    (hmap_eq :
      (proCResidualCore ProC ↥R).map (R.subtype : ↥R →* G) = proCResidualCore ProC G) :
    L = ⊤ := by
  subst hR
  have hcore_le :
      proCResidualCore ProC ↥(proCResidualCore ProC G) ≤ L :=
    proCResidualCore_le_of_proCQuotient (ProC := ProC) L hquot
  have hcore_map_le :
      proCResidualCore ProC G ≤
        L.map ((proCResidualCore ProC G).subtype : ↥(proCResidualCore ProC G) →* G) := by
    simpa [hmap_eq] using
      (Subgroup.map_mono
        (f := ((proCResidualCore ProC G).subtype : ↥(proCResidualCore ProC G) →* G))
        hcore_le)
  have htop_map :
      (⊤ : Subgroup ↥(proCResidualCore ProC G)).map
          ((proCResidualCore ProC G).subtype : ↥(proCResidualCore ProC G) →* G) =
        proCResidualCore ProC G := by
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (proCResidualCore ProC G))
  have htop_le :
      (⊤ : Subgroup ↥(proCResidualCore ProC G)).map
          ((proCResidualCore ProC G).subtype : ↥(proCResidualCore ProC G) →* G) ≤
        L.map ((proCResidualCore ProC G).subtype : ↥(proCResidualCore ProC G) →* G) := by
    rw [htop_map]
    exact hcore_map_le
  exact top_le_iff.mp <|
    (Subgroup.map_subtype_le_map_subtype.1 htop_le)

/-- The residual core admits no nontrivial pro-`C` quotient once the residual-core stability
equality for the core subgroup is supplied. -/
theorem proCResidualCore_eq_top_of_quotient_isProC
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {L : Subgroup ↥(proCResidualCore ProC G)} [L.Normal]
    (hquot : ProC (G := ↥(proCResidualCore ProC G) ⧸ L))
    (hmap_eq :
      (proCResidualCore ProC ↥(proCResidualCore ProC G)).map
          ((proCResidualCore ProC G).subtype :
            ↥(proCResidualCore ProC G) →* G) =
        proCResidualCore ProC G) :
    L = ⊤ := by
  letI : (proCResidualCore ProC G).Normal := by
    classical
    change
      (sInf (Set.range fun N : ProCQuotientKernel ProC G => N.toSubgroup)).Normal
    simpa [proCResidualCore, sInf_range] using
      (Subgroup.normal_iInf_normal
        (a := fun N : ProCQuotientKernel ProC G => N.toSubgroup)
        (norm := fun N => N.normal))
  simpa using
    (proCResidualCore_subgroup_eq_top_of_quotient_isProC
      (ProC := ProC) (G := G) (R := proCResidualCore ProC G) rfl hquot hmap_eq)

end ProCGroups.ProC
