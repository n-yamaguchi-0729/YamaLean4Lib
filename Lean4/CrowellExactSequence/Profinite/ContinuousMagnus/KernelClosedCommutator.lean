import CrowellExactSequence.Discrete.MagnusComparison
import CrowellExactSequence.Profinite.ContinuousMagnus.FiniteStageKernel
import ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/ContinuousMagnus/KernelClosedCommutator.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite Crowell exact sequence

Crowell-specific material is kept separate from general Fox calculus: relation modules, kernel boundaries, Blanchfield-Lyndon maps, and discrete/profinite exactness statements are assembled here.
-/
namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {ProC : ProCGroupPredicate.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass]

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- Concrete continuous Magnus kernel for the closed-generated completed Fox vector.

This is the paper's injectivity step for
`d_N : N^ab(C) -> Z_C[[H]]^r`: a kernel element killed by the continuous Fox derivative vector
already lies in `closure([N,N])`. -/
theorem freeProC_closedGeneratedFoxVector_kernel_le_closedCommutator
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))) :
    ∀ n : ProfiniteKernelSubgroup psi,
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi htarget n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi) := by
  classical
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  letI : CompactSpace sourceData.carrier := ProCGroup.compactSpace ProC sourceData.carrier
  letI : ProCGroup ProC (ProfiniteKernelSubgroup psi) :=
    proCGroup_profiniteKernelSubgroup
      (G := sourceData.carrier) (H := H) ProC psi
  intro n hnD
  refine
    ProCGroup.mem_closedCommutator_of_forall_exists_openNormalSubgroupInClass_le_quotient_commutator
      (G := ProfiniteKernelSubgroup psi) ProC ?_
  intro U
  let Nclosed : ClosedSubgroup sourceData.carrier :=
    ⟨ProfiniteKernelSubgroup psi, isClosed_profiniteKernelSubgroup psi⟩
  rcases exists_openNormalSubgroupInClass_inter_closedSubgroup_le
      (C := ProC.finiteQuotientClass)
      (G := sourceData.carrier) sourceData.proCGroup.isProCGroup
      Nclosed U.1.toOpenSubgroup with
    ⟨V₀, hV₀U⟩
  have hV₀U_sub :
      ∀ m : ProfiniteKernelSubgroup psi,
        m.1 ∈ (V₀.1 : Subgroup sourceData.carrier) → m ∈ (U.1 : Subgroup (ProfiniteKernelSubgroup psi)) := by
    intro m hm
    exact hV₀U (by
      change m.1 ∈ (V₀.1 : Subgroup sourceData.carrier)
      exact hm)
  let hfopen : IsOpenMap psi :=
    ContinuousMonoidHom.isOpenMap_of_surjective_compact_t2 psi hpsi
  let W₀ : OpenNormalSubgroupInClass ProC.finiteQuotientClass H :=
    OpenNormalSubgroupInClass.mapOpenNormal_of_formation
      (C := ProC.finiteQuotientClass) (G := sourceData.carrier)
      ProC.finiteQuotientFormation psi hfopen hpsi V₀
  let Q₀ : Type u := sourceData.carrier ⧸ (V₀.1 : Subgroup sourceData.carrier)
  let K₀ : Type u := H ⧸ (W₀.1 : Subgroup H)
  letI : Finite Q₀ := ProC.finiteQuotientFormation.finiteOnly V₀.2
  letI : Finite K₀ := ProC.finiteQuotientFormation.finiteOnly W₀.2
  letI : DiscreteTopology K₀ :=
    QuotientGroup.discreteTopology W₀.1.toOpenSubgroup.isOpen'
  let qH₀ : H →ₜ* K₀ :=
    OpenNormalSubgroupInClass.quotientProj
      (C := ProC.finiteQuotientClass) W₀
  have hV₀W₀ :
      (V₀.1 : Subgroup sourceData.carrier) ≤
        (W₀.1 : Subgroup H).comap psi.toMonoidHom := by
    intro g hg
    change psi g ∈ (W₀.1 : Subgroup H)
    change psi g ∈
      ((OpenNormalSubgroup.map psi hfopen hpsi V₀.1 : OpenNormalSubgroup H) :
        Subgroup H)
    exact (Subgroup.mem_map).2 ⟨g, hg, rfl⟩
  let α₀ : FreeGroup X →* Q₀ :=
    (QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier)).comp
      (FreeGroup.lift ι)
  let β : Q₀ →* K₀ :=
    QuotientGroup.map
      (N := (V₀.1 : Subgroup sourceData.carrier))
      (M := (W₀.1 : Subgroup H))
      (f := psi.toMonoidHom) hV₀W₀
  have hα₀_surj : Function.Surjective α₀ := by
    simpa [α₀, X, ι] using
      freeProCChosenULiftFamilyOfBasisCard_quotient_lift_surjective
        (ProC := ProC) sourceData hbasis V₀
  have hβ_surj : Function.Surjective β := by
    intro y
    rcases QuotientGroup.mk'_surjective (W₀.1 : Subgroup H) y with ⟨h, rfl⟩
    rcases hpsi h with ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) g, rfl⟩
  have hCker : ProC.finiteQuotientClass β.ker :=
    ProC.finiteQuotientHereditary.subgroupClosed β.ker V₀.2
  letI : Finite β.ker := ProC.finiteQuotientFormation.finiteOnly hCker
  rcases ProCGroups.Completion.ProCIntegerIndex.exists_index_kills_finite_group_of_mem
      (C := ProC.finiteQuotientClass)
      ProC.finiteQuotientFormation ProC.finiteQuotientHereditary hCker with
    ⟨j, hpow⟩
  let ψstage : FreeGroup X →* K₀ := β.comp α₀
  let Nstage : Subgroup (FreeGroup X) := ψstage.ker
  let Qstage : Type u := FoxDifferential.zcFiniteStageTarget X Nstage
  letI : TopologicalSpace Qstage := ⊥
  letI : DiscreteTopology Qstage := ⟨rfl⟩
  letI : IsTopologicalGroup Qstage := inferInstance
  have hψstage_surj : Function.Surjective ψstage := by
    intro k
    rcases hβ_surj k with ⟨q, rfl⟩
    rcases hα₀_surj q with ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  let e : Qstage ≃* K₀ :=
    QuotientGroup.quotientKerEquivOfSurjective ψstage hψstage_surj
  have hCstage : ProC.finiteQuotientClass Qstage :=
    ProC.finiteQuotientIsomClosed ⟨e.symm⟩ W₀.2
  let eSymm : K₀ →ₜ* Qstage :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  let η : H →ₜ* Qstage :=
    eSymm.comp qH₀
  have he_apply (w : FreeGroup X) :
      e (QuotientGroup.mk' Nstage w) = ψstage w := by
    change QuotientGroup.quotientKerEquivOfSurjective ψstage hψstage_surj
        (QuotientGroup.mk' ψstage.ker w) = ψstage w
    rfl
  have hη :
      (η : H →* Qstage).comp
          ((psi : sourceData.carrier →* H).comp (FreeGroup.lift ι)) =
        QuotientGroup.mk' Nstage := by
    apply MonoidHom.ext
    intro w
    apply e.injective
    change e (η (psi ((FreeGroup.lift ι) w))) =
      e (QuotientGroup.mk' Nstage w)
    rw [he_apply]
    change e (e.symm (qH₀ (psi ((FreeGroup.lift ι) w)))) = β (α₀ w)
    rw [e.apply_symm_apply]
    change QuotientGroup.mk' (W₀.1 : Subgroup H) (psi ((FreeGroup.lift ι) w)) =
      β (QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) ((FreeGroup.lift ι) w))
    rw [QuotientGroup.map_mk']
    rfl
  let J : FoxDifferential.ZCCompletedGroupAlgebraIndex
      ProC.finiteQuotientClass Qstage :=
    (j, FoxDifferential.identityCompletedGroupAlgebraIndexInClassOfMem
      ProC.finiteQuotientClass Qstage ProC.finiteQuotientIsomClosed hCstage)
  rcases exists_openNormalSubgroupInClass_eq_on_right_coset_closedGenFoxVector_proj
      (H := H) (ProC := ProC) ProC.finiteQuotientHereditary
      sourceData hbasis psi htarget η J n.1 with
    ⟨Vloc, hloc⟩
  let Vfinal : OpenNormalSubgroupInClass ProC.finiteQuotientClass sourceData.carrier :=
    OpenNormalSubgroupInClass.inf
      (C := ProC.finiteQuotientClass) (G := sourceData.carrier)
      ProC.finiteQuotientFormation V₀ Vloc
  let αfinal : FreeGroup X →*
      sourceData.carrier ⧸ (Vfinal.1 : Subgroup sourceData.carrier) :=
    (QuotientGroup.mk' (Vfinal.1 : Subgroup sourceData.carrier)).comp
      (FreeGroup.lift ι)
  have hαfinal_surj : Function.Surjective αfinal := by
    simpa [αfinal, X, ι] using
      freeProCChosenULiftFamilyOfBasisCard_quotient_lift_surjective
        (ProC := ProC) sourceData hbasis Vfinal
  rcases hαfinal_surj
      (QuotientGroup.mk' (Vfinal.1 : Subgroup sourceData.carrier) n.1) with
    ⟨w, hwfinal⟩
  have hfinal_le_V₀ :
      (Vfinal.1 : Subgroup sourceData.carrier) ≤ (V₀.1 : Subgroup sourceData.carrier) := by
    intro g hg
    change g ∈ ((V₀.1 ⊓ Vloc.1 : OpenNormalSubgroup sourceData.carrier) : Subgroup sourceData.carrier) at hg
    exact hg.1
  have hfinal_le_Vloc :
      (Vfinal.1 : Subgroup sourceData.carrier) ≤ (Vloc.1 : Subgroup sourceData.carrier) := by
    intro g hg
    change g ∈ ((V₀.1 ⊓ Vloc.1 : OpenNormalSubgroup sourceData.carrier) : Subgroup sourceData.carrier) at hg
    exact hg.2
  have hα₀w :
      α₀ w = QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) n.1 := by
    let τ : sourceData.carrier ⧸ (Vfinal.1 : Subgroup sourceData.carrier) →*
        sourceData.carrier ⧸ (V₀.1 : Subgroup sourceData.carrier) :=
      QuotientGroup.map
        (N := (Vfinal.1 : Subgroup sourceData.carrier))
        (M := (V₀.1 : Subgroup sourceData.carrier))
        (f := MonoidHom.id sourceData.carrier) hfinal_le_V₀
    have hτ := congrArg τ hwfinal
    simpa [τ, αfinal, α₀] using hτ
  have hdiff_final :
      ((FreeGroup.lift ι) w) * n.1⁻¹ ∈
        (Vfinal.1 : Subgroup sourceData.carrier) := by
    have hwq :
        QuotientGroup.mk' (Vfinal.1 : Subgroup sourceData.carrier)
            ((FreeGroup.lift ι) w) =
          QuotientGroup.mk' (Vfinal.1 : Subgroup sourceData.carrier) n.1 := by
      simpa [αfinal] using hwfinal
    simpa [div_eq_mul_inv] using
      (QuotientGroup.eq_iff_div_mem
        (N := (Vfinal.1 : Subgroup sourceData.carrier))).1 hwq
  have hdiff_loc :
      ((FreeGroup.lift ι) w) * n.1⁻¹ ∈
        (Vloc.1 : Subgroup sourceData.carrier) :=
    hfinal_le_Vloc hdiff_final
  have hproj_n :
      (fun i : X =>
        FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass
          Qstage J
          ((FoxDifferential.zcFreeFoxCoordinatesMap
            (X := X) ProC.finiteQuotientClass ProC.finiteQuotientHereditary η
            (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
              (H := H) (ProC := ProC) sourceData hbasis psi htarget n.1)) i)) = 0 := by
    funext i
    simp only [hnD, FoxDifferential.zcFreeFoxCoordinatesMap_apply, Pi.zero_apply, map_zero,
  FoxDifferential.zcCompletedGroupAlgebraProjection_zero]
  have hproj_w :
      (fun i : X =>
        FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass
          Qstage J
          ((FoxDifferential.zcFreeFoxCoordinatesMap
            (X := X) ProC.finiteQuotientClass ProC.finiteQuotientHereditary η
            (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
              (H := H) (ProC := ProC) sourceData hbasis psi htarget
              ((FreeGroup.lift ι) w))) i)) = 0 := by
    have heq := hloc ((FreeGroup.lift ι) w) hdiff_loc
    exact (by
      simpa [X, ι, J] using
        heq.trans (by
          simpa [X, ι, J] using hproj_n))
  have hder :
      FoxDifferential.finiteFoxStageDerivativeVector
        (X := X) Nstage j.modulus w = 0 :=
    finiteFoxStageDerivativeVector_eq_zero_of_closedGenFoxVector_proj_eq_zero
      (H := H) (ProC := ProC) ProC.finiteQuotientHereditary
      ProC.finiteQuotientIsomClosed sourceData hbasis psi hpsi htarget
      Nstage hCstage η hη j hproj_w
  have hwker : w ∈ (β.comp α₀).ker := by
    change β (α₀ w) = 1
    rw [hα₀w]
    change QuotientGroup.mk' (W₀.1 : Subgroup H) (psi n.1) = 1
    exact (QuotientGroup.eq_one_iff
      (N := (W₀.1 : Subgroup H)) (psi n.1)).2 (by
        have hnpsi : psi n.1 = 1 := by
          change psi n.1 = 1
          exact n.2
        rw [hnpsi]
        exact (W₀.1 : Subgroup H).one_mem)
  have hcommβ :
      (⟨α₀ w, by
        change β (α₀ w) = 1
        simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
        commutator β.ker :=
    mem_commutator_ker_of_finiteFoxStageDerivativeVector_eq_zero_finite
      (X := X) α₀ β j.modulus j.positive hpow hwker
      (by simpa [Nstage, ψstage] using hder)
  let κ : ProfiniteKernelSubgroup psi →* β.ker :=
    { toFun := fun m =>
        ⟨QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) m.1, by
          change β (QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) m.1) = 1
          change QuotientGroup.mk' (W₀.1 : Subgroup H) (psi m.1) = 1
          exact (QuotientGroup.eq_one_iff
            (N := (W₀.1 : Subgroup H)) (psi m.1)).2 (by
              have hmpsi : psi m.1 = 1 := by
                change psi m.1 = 1
                exact m.2
              rw [hmpsi]
              exact (W₀.1 : Subgroup H).one_mem)⟩
      map_one' := by
        apply Subtype.ext
        simp only [OneMemClass.coe_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, QuotientGroup.mk'_apply, MulMemClass.mk_mul_mk]}
  have hκ_surj : Function.Surjective κ := by
    intro y
    rcases QuotientGroup.mk'_surjective
        (V₀.1 : Subgroup sourceData.carrier) y.1 with
      ⟨g, hg⟩
    have hψgW : psi g ∈ (W₀.1 : Subgroup H) := by
      have hβg : β (QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) g) = 1 := by
        have hyβ : β y.1 = 1 := by
          change β y.1 = 1
          exact y.2
        simpa [hg] using hyβ
      change QuotientGroup.mk' (W₀.1 : Subgroup H) (psi g) = 1 at hβg
      exact (QuotientGroup.eq_one_iff
        (N := (W₀.1 : Subgroup H)) (psi g)).1 hβg
    have hψgWmap :
        psi g ∈
          ((OpenNormalSubgroup.map psi hfopen hpsi V₀.1 : OpenNormalSubgroup H) :
            Subgroup H) := by
      simpa [W₀] using hψgW
    rcases (Subgroup.mem_map).1 hψgWmap with ⟨v, hvV₀, hvψ⟩
    let m : ProfiniteKernelSubgroup psi :=
      ⟨g * v⁻¹, by
        change psi (g * v⁻¹) = 1
        rw [map_mul, map_inv]
        have hvψ' : psi v = psi g := hvψ
        rw [hvψ', mul_inv_cancel]⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) (g * v⁻¹) = y.1
    rw [← hg]
    have hvq :
        QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) v = 1 :=
      (QuotientGroup.eq_one_iff
        (N := (V₀.1 : Subgroup sourceData.carrier)) v).2 hvV₀
    rw [map_mul, map_inv, hvq]
    simp only [QuotientGroup.mk'_apply, inv_one, mul_one]
  have hκkerU :
      κ.ker ≤ (U.1 : Subgroup (ProfiniteKernelSubgroup psi)) := by
    intro m hm
    have hq : QuotientGroup.mk' (V₀.1 : Subgroup sourceData.carrier) m.1 = 1 := by
      exact congrArg Subtype.val hm
    exact hV₀U_sub m
      ((QuotientGroup.eq_one_iff
        (N := (V₀.1 : Subgroup sourceData.carrier)) m.1).1 hq)
  have hκn_eq :
      κ n =
        (⟨α₀ w, by
          change β (α₀ w) = 1
          simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) := by
    apply Subtype.ext
    exact hα₀w.symm
  have hκn_comm : κ n ∈ commutator β.ker := by
    simpa [hκn_eq] using hcommβ
  have hquotU :
      QuotientGroup.mk' (U.1 : Subgroup (ProfiniteKernelSubgroup psi)) n ∈
        commutator (ProfiniteKernelSubgroup psi ⧸ (U.1 : Subgroup (ProfiniteKernelSubgroup psi))) :=
    quotient_mk_mem_commutator_of_surjective_image_mem_commutator
      κ hκ_surj (U.1 : Subgroup (ProfiniteKernelSubgroup psi)) hκkerU hκn_comm
  exact ⟨U, le_rfl, hquotU⟩

end

end CrowellExactSequence
