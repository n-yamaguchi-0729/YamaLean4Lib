import CrowellExactSequence.Profinite.ContinuousMagnus.ClosedGeneratedVector
import FoxDifferential.Completed.Comparison.FiniteStage
import FoxDifferential.Completed.Continuous.Naturality

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/ContinuousMagnus/FiniteStageKernel.lean
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
/-- Free-group comparison for the concrete closed-generated continuous Fox vector, with the
right component already identified with the presentation map. -/
theorem freeFoxDerivVec_eq_freeProCClosedGenFoxVectorZC_comp_lift_mapTarget
    [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (hC : ProCGroups.FiniteGroupClass.Hereditary ProC.finiteQuotientClass)
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
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H))))
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (η : H →ₜ* K) (w : FreeGroup (ULift.{u} (Fin r))) :
    FoxDifferential.zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
        (η.toMonoidHom.comp
          (psi.toMonoidHom.comp
            (FreeGroup.lift
              (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis)))) w =
      FoxDifferential.zcFreeFoxCoordinatesMap
        (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
        (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi htarget
          ((FreeGroup.lift
            (freeProCChosenULiftFamilyOfBasisCard
              (ProC := ProC) sourceData hbasis)) w)) := by
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let hfree := freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis
  let φ : X → H := fun i => psi (ι i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOne_of_finite
      (ProC := ProC) φ
  have hH : ProC (G := H) :=
    (ProCGroup.of_surjective (G := sourceData.carrier) ProC psi hpsi).isProC
  have hφHconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOne
        (ProC := ProC) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  have hright :
      FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    have hright_lift :=
      FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_lift
        (ProC := ProC) X H hfree hH φ htarget hφconv hφHconv hφHgen
    have hliftHom :=
      freeProCChosenULiftFamilyOfBasisCard_liftHom_eq_of_surjective
        (ProC := ProC) sourceData hbasis hH psi hpsi
    have hlift :
        hfree.lift hH φ hφHconv hφHgen = psi.toMonoidHom := by
      simpa [hfree, φ, ι] using congrArg ContinuousMonoidHom.toMonoidHom hliftHom
    exact hright_lift.trans hlift
  have hcomp :=
    FoxDifferential.zcFreeFoxDerivVec_eq_freeProCDerivVecViaClosedGen_comp_lift_mapTarget
      (ProC := ProC) hfree φ htarget hφconv hC η w
  simpa [freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger, X, ι, hfree, φ,
    hφconv, hright] using hcomp

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- A finite projection of the concrete closed-generated continuous Fox vector gives zero of the
corresponding finite Fox derivative vector for a free-group representative. -/
theorem finiteFoxStageDerivativeVector_eq_zero_of_closedGenFoxVector_proj_eq_zero
    [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (hC : ProCGroups.FiniteGroupClass.Hereditary ProC.finiteQuotientClass)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed ProC.finiteQuotientClass)
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
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H))))
    (N : Subgroup (FreeGroup (ULift.{u} (Fin r)))) [N.Normal]
    [TopologicalSpace (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)]
    [IsTopologicalGroup (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)]
    [DiscreteTopology (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)]
    (hCN : ProC.finiteQuotientClass
      (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N))
    (η : H →ₜ* FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
    (hη :
      (η : H →* FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N).comp
          ((psi : sourceData.carrier →* H).comp
            (FreeGroup.lift
              (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis))) =
        QuotientGroup.mk' N)
    (j : ProCGroups.Completion.ProCIntegerIndex ProC.finiteQuotientClass)
    {w : FreeGroup (ULift.{u} (Fin r))}
    (hproj :
      (fun i : ULift.{u} (Fin r) =>
        FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass
          (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
          (j, FoxDifferential.identityCompletedGroupAlgebraIndexInClassOfMem
            ProC.finiteQuotientClass
            (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
            hIso hCN)
          ((FoxDifferential.zcFreeFoxCoordinatesMap
            (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
            (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
              (H := H) (ProC := ProC) sourceData hbasis psi htarget
              ((FreeGroup.lift
                (freeProCChosenULiftFamilyOfBasisCard
                  (ProC := ProC) sourceData hbasis)) w))) i)) = 0) :
    FoxDifferential.finiteFoxStageDerivativeVector
        (X := ULift.{u} (Fin r)) N j.modulus w = 0 := by
  have hcompare :=
    freeFoxDerivVec_eq_freeProCClosedGenFoxVectorZC_comp_lift_mapTarget
      (H := H) (ProC := ProC) hC sourceData hbasis psi hpsi htarget η w
  have hcompare' :
      FoxDifferential.zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
          (QuotientGroup.mk' N) w =
        FoxDifferential.zcFreeFoxCoordinatesMap
          (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
          (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (ProC := ProC) sourceData hbasis psi htarget
            ((FreeGroup.lift
              (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis)) w)) := by
    simpa [hη] using hcompare
  have hproj' :
      (fun i : ULift.{u} (Fin r) =>
        FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass
          (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
          (j, FoxDifferential.identityCompletedGroupAlgebraIndexInClassOfMem
            ProC.finiteQuotientClass
            (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
            hIso hCN)
          (FoxDifferential.zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
            (QuotientGroup.mk' N) w i)) = 0 := by
    simpa [hcompare'] using hproj
  exact
    FoxDifferential.finiteFoxStageDerivativeVector_eq_zero_of_zcFreeFoxDerivVec_identityProj_eq_zero
      (C := ProC.finiteQuotientClass) (X := ULift.{u} (Fin r)) N hIso hCN j hproj'

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- Local constancy of a finite target/coefficent projection of the concrete closed-generated
continuous Fox vector. -/
theorem exists_openNormalSubgroupInClass_eq_on_right_coset_closedGenFoxVector_proj
    [ProC.HasFiniteQuotientFinite]
    (hC : ProCGroups.FiniteGroupClass.Hereditary ProC.finiteQuotientClass)
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H))))
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (η : H →ₜ* K)
    (j : FoxDifferential.ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass K)
    (g₀ : sourceData.carrier) :
    ∃ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass sourceData.carrier,
      ∀ g : sourceData.carrier,
        g * g₀⁻¹ ∈ (U.1 : Subgroup sourceData.carrier) →
          (fun i : ULift.{u} (Fin r) =>
            FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass K j
              ((FoxDifferential.zcFreeFoxCoordinatesMap
                (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
                (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
                  (H := H) (ProC := ProC) sourceData hbasis psi htarget g)) i)) =
          (fun i : ULift.{u} (Fin r) =>
            FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass K j
              ((FoxDifferential.zcFreeFoxCoordinatesMap
                (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
                (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
                  (H := H) (ProC := ProC) sourceData hbasis psi htarget g₀)) i)) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass) :=
    ⟨by
      intro Q _ hQ
      exact ProCGroupPredicate.finiteQuotientFinite ProC hQ⟩
  let f : sourceData.carrier →
      (ULift.{u} (Fin r) →
        FoxDifferential.ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass K j) :=
    fun g i =>
      FoxDifferential.zcCompletedGroupAlgebraProjection ProC.finiteQuotientClass K j
        ((FoxDifferential.zcFreeFoxCoordinatesMap
          (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
          (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (ProC := ProC) sourceData hbasis psi htarget g)) i)
  have hf : Continuous f := by
    have hD :
        Continuous
          (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (ProC := ProC) sourceData hbasis psi htarget) :=
      continuous_freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi htarget
    have hmap :
        Continuous (fun g : sourceData.carrier =>
          FoxDifferential.zcFreeFoxCoordinatesMap
            (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
            (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
              (H := H) (ProC := ProC) sourceData hbasis psi htarget g)) :=
      (FoxDifferential.continuous_zcFreeFoxCoordinatesMap
        ProC.finiteQuotientClass hC η).comp hD
    refine continuous_pi fun i => ?_
    change Continuous (fun g : sourceData.carrier =>
      ((FoxDifferential.zcFreeFoxCoordinatesMap
        (X := ULift.{u} (Fin r)) ProC.finiteQuotientClass hC η
        (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (ProC := ProC) sourceData hbasis psi htarget g)) i).1 j)
    exact (continuous_apply j).comp
      (continuous_subtype_val.comp ((continuous_apply i).comp hmap))
  have hdisc :
      DiscreteTopology
        (ULift.{u} (Fin r) →
          FoxDifferential.ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass K j) := by
    infer_instance
  letI :
      DiscreteTopology
        (ULift.{u} (Fin r) →
          FoxDifferential.ZCCompletedGroupAlgebraStage ProC.finiteQuotientClass K j) := hdisc
  simpa [f] using
    ProCGroups.ProC.IsProCGroup.exists_openNormalSubgroupInClass_eq_on_right_coset_of_continuous_discrete
      (C := ProC.finiteQuotientClass) sourceData.proCGroup.isProCGroup f hf g₀

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- The chosen lifted finite free basis surjects onto every finite open-normal quotient of the
free pro-`C` source. -/
theorem freeProCChosenULiftFamilyOfBasisCard_quotient_lift_surjective
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (V : OpenNormalSubgroupInClass ProC.finiteQuotientClass sourceData.carrier) :
    Function.Surjective
      ((QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)).comp
        (FreeGroup.lift
          (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis))) := by
  classical
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let Q : Type u := sourceData.carrier ⧸ (V.1 : Subgroup sourceData.carrier)
  letI : DiscreteTopology Q :=
    QuotientGroup.discreteTopology V.1.toOpenSubgroup.isOpen'
  let g : X → Q :=
    fun i => QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier) (ι i)
  have hsource :
      ProCGroups.Generation.TopologicallyGenerates
        (G := sourceData.carrier) (Set.range ι) := by
    simpa [X, ι] using
      freeProCChosenULiftFamilyOfBasisCard_generates (ProC := ProC) sourceData hbasis
  have hquot_image :
      ProCGroups.Generation.TopologicallyGenerates
        (G := Q)
        ((QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)) '' Set.range ι) :=
    ProCGroups.Generation.topologicallyGenerates_quotient_image
      (G := sourceData.carrier) (N := (V.1 : Subgroup sourceData.carrier)) hsource
  have hrange :
      (QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)) '' Set.range ι =
        Set.range g := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ι i, ⟨i, rfl⟩, rfl⟩
  have hg :
      ProCGroups.Generation.TopologicallyGenerates (G := Q) (Set.range g) := by
    rw [← hrange]
    exact hquot_image
  have hsurj :
      Function.Surjective (FreeGroup.lift g) :=
    ProCGroups.FiniteGeneration.freeGroup_lift_surjective_of_topologicallyGenerates_discrete
      (G := Q) g hg
  have hlift :
      FreeGroup.lift g =
        (QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)).comp
          (FreeGroup.lift ι) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  simpa [hlift, X, ι] using hsurj

end

end CrowellExactSequence
